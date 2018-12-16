#include "xdebug.cppo"
open Globals

module SBCast = Libsongbird.Cast
module SBGlobals = Libsongbird.Globals
module SBProver = Libsongbird.Prover
module SBDebug = Libsongbird.Debug
module SBProof = Libsongbird.Proof
module CP = Cpure
module CF = Cformula
module CPR = Cprinter
module MCP = Mcpure

(* translation of HIP's data structures to Songbird's data structures
   will be done here *)

let add_str = Gen.Basic.add_str
let no_pos = VarGen.no_pos
let report_error = Gen.Basic.report_error
let pr_formula = CPR.string_of_formula
let pr_struc_f = CPR.string_of_struc_formula
let pr_svs = CPR.string_of_spec_var_list
let pr_pf = Cprinter.string_of_pure_formula

let pr_validity tvl = match tvl with
  | SBGlobals.MvlFalse -> "Invalid"
  | SBGlobals.MvlTrue -> "Valid"
  | SBGlobals.MvlUnkn -> "Unknown"
  | SBGlobals.MvlInfer -> "Infer"

let translate_loc (location:VarGen.loc) : SBGlobals.pos =
  {
    pos_begin = location.start_pos;
    pos_end = location.end_pos;
  }

let translate_back_pos (pos:SBGlobals.pos) : VarGen.loc =
  let no_pos1 = { Lexing.pos_fname = "";
                  Lexing.pos_lnum = 0;
                  Lexing.pos_bol = 0;
                  Lexing.pos_cnum = 0 } in
  {
    start_pos = pos.SBGlobals.pos_begin;
    mid_pos = no_pos1;
    end_pos = pos.SBGlobals.pos_end;
  }
let translate_type (typ: Globals.typ) : SBGlobals.typ =
  match typ with
  | Int -> TInt
  | Bool -> TBool
  | UNK -> TUnk
  | Void -> TVoid
  | Named str -> TData str
  | _ -> report_error no_pos
           ("translate_type:" ^ (Globals.string_of_typ typ) ^ " is not handled")

let translate_back_type (typ) = match typ with
  | SBGlobals.TInt -> Globals.Int
  | SBGlobals.TBool -> Globals.Bool
  | SBGlobals.TUnk -> Globals.UNK
  | SBGlobals.TVoid -> Globals.Void
  | SBGlobals.TData str -> Globals.Named str
  | _ -> report_error no_pos "translate_back_type: this type is not handled"


let translate_var_x (var: CP.spec_var): SBGlobals.var =
  let CP.SpecVar (typ, ident, primed) = var in
  match primed with
  | VarGen.Primed -> (ident ^ "'", translate_type typ)
  | _ -> (ident, translate_type typ)

let translate_var var =
  let pr1 = CPR.string_of_spec_var in
  let pr2 = SBCast.pr_var in
  Debug.no_1 "translate_var" pr1 pr2
    (fun _ -> translate_var_x var) var

let translate_back_var (var : SBGlobals.var) =
  let (str, typ) = var in
  if String.length str = 0 then
    CP.SpecVar (translate_back_type typ, str, VarGen.Unprimed)
  else
    let len = String.length str in
    let last_char = String.sub str (len - 1) 1 in
    if String.compare last_char "'" == 0
    then
      let str2 = String.sub str 0 (len - 1)  in
      CP.SpecVar (translate_back_type typ, str2, VarGen.Primed)
    else
      CP.SpecVar (translate_back_type typ, str, VarGen.Unprimed)

let rec translate_exp (exp: CP.exp) =
  match exp with
  | CP.Null loc -> SBCast.Null (translate_loc loc)
  | CP.Var (var, loc) -> SBCast.Var (translate_var var, translate_loc loc)
  | CP.IConst (num, loc) -> SBCast.IConst (num, translate_loc loc)
  | CP.Add (exp1, exp2, loc) ->
        let t_exp1 = translate_exp exp1 in
        let t_exp2 = translate_exp exp2 in
        SBCast.BinExp (Add, t_exp1, t_exp2, translate_loc loc)
  | CP.Subtract (exp1, exp2, loc) ->
        let t_exp1 = translate_exp exp1 in
        let t_exp2 = translate_exp exp2 in
        SBCast.BinExp (Sub, t_exp1, t_exp2, translate_loc loc)
  | CP.Mult (exp1, exp2, loc) ->
        let t_exp1 = translate_exp exp1 in
        let t_exp2 = translate_exp exp2 in
        SBCast.BinExp (Mul, t_exp1, t_exp2, translate_loc loc)
  | CP.Div (exp1, exp2, loc) ->
        let t_exp1 = translate_exp exp1 in
        let t_exp2 = translate_exp exp2 in
        SBCast.BinExp (Div, t_exp1, t_exp2, translate_loc loc)
  | CP.Template templ ->
    if (!Globals.translate_funcs) then
      let fun_name = CP.name_of_sv templ.templ_id in
      let args = templ.templ_args |> List.map translate_exp in
      SBCast.mk_func (SBCast.FuncName fun_name) args
    else report_error no_pos "translate_funcs not activated"
  | _ -> report_error no_pos "this exp is not handled"

let rec translate_back_exp (exp: SBCast.exp) = match exp with
  | SBCast.Null pos -> CP.Null (translate_back_pos pos)
  | SBCast.Var (var, pos) -> CP.Var (translate_back_var var, translate_back_pos
                                      pos)
  | SBCast.IConst (num, pos) -> CP.IConst (num, translate_back_pos pos)
  | SBCast.BinExp (bin_op, exp1, exp2, pos) ->
    begin
      match bin_op with
      | SBCast.Add -> CP.Add (translate_back_exp exp1, translate_back_exp exp2,
               translate_back_pos pos)
      | SBCast.Sub -> CP.Subtract (translate_back_exp exp1, translate_back_exp exp2,
               translate_back_pos pos)
      | SBCast.Mul -> CP.Mult (translate_back_exp exp1, translate_back_exp exp2,
               translate_back_pos pos)
      | SBCast.Div -> CP.Div (translate_back_exp exp1, translate_back_exp exp2,
               translate_back_pos pos)
    end
  | SBCast.LTerm (lterm, pos) ->
    let n_exp = SBCast.convert_lterm_to_binary_exp pos lterm in
    translate_back_exp n_exp
  | SBCast.PTerm (pterm, pos) ->
    let n_exp = SBCast.convert_pterm_to_binary_exp pos pterm in
    translate_back_exp n_exp
  | SBCast.Func _ ->
    report_error no_pos
      ("translate_back_exp:" ^ (SBCast.pr_exp exp) ^ " this Func is not handled")
  | _ -> report_error no_pos
           ("this exp formula not handled: " ^ (SBCast.pr_exp exp))

let rec translate_pf (pure_f: CP.formula)  =
  match pure_f with
  | CP.BForm (b_formula, _) ->
    let (p_formula, _) = b_formula in
    begin
      match p_formula with
      | BVar (var, loc) ->
        SBCast.BVar (translate_var var, translate_loc loc)
      | BConst (b, loc) ->
        SBCast.BConst (b, translate_loc loc)
      | Eq (exp1, exp2, loc) ->
        let sb_exp1 = translate_exp exp1 in
        let sb_exp2 = translate_exp exp2 in
        let sb_loc = translate_loc loc in
        SBCast.BinRel (Eq, sb_exp1, sb_exp2, sb_loc)
      | Neq (exp1, exp2, loc) ->
        let sb_exp1 = translate_exp exp1 in
        let sb_exp2 = translate_exp exp2 in
        let sb_loc = translate_loc loc in
        SBCast.BinRel (Ne, sb_exp1, sb_exp2, sb_loc)
      | Gt (exp1, exp2, loc) ->
        let sb_exp1 = translate_exp exp1 in
        let sb_exp2 = translate_exp exp2 in
        let sb_loc = translate_loc loc in
        SBCast.BinRel (Gt, sb_exp1, sb_exp2, sb_loc)
      | Gte (exp1, exp2, loc) ->
        let sb_exp1 = translate_exp exp1 in
        let sb_exp2 = translate_exp exp2 in
        let sb_loc = translate_loc loc in
        SBCast.BinRel (Ge, sb_exp1, sb_exp2, sb_loc)
      | Lt (exp1, exp2, loc) ->
        let sb_exp1 = translate_exp exp1 in
        let sb_exp2 = translate_exp exp2 in
        let sb_loc = translate_loc loc in
        SBCast.BinRel (Lt, sb_exp1, sb_exp2, sb_loc)
      | Lte (exp1, exp2, loc) ->
        let sb_exp1 = translate_exp exp1 in
        let sb_exp2 = translate_exp exp2 in
        let sb_loc = translate_loc loc in
        SBCast.BinRel (Le, sb_exp1, sb_exp2, sb_loc)
      | LexVar lex ->
        SBCast.BConst (true, translate_loc lex.lex_loc)
      | _ -> report_error no_pos
               ("this p_formula is not handled" ^ (CPR.string_of_p_formula p_formula))
    end
  | And (f1, f2, loc) ->
    let n_f1 = translate_pf f1 in
    let n_f2 = translate_pf f2 in
    SBCast.PConj ([n_f1; n_f2], translate_loc loc)
  | Or (f1, f2, _, loc) ->
    let n_f1 = translate_pf f1 in
    let n_f2 = translate_pf f2 in
    SBCast.PDisj ([n_f1; n_f2], translate_loc loc)
  | Not (f, _, loc) ->
    let n_f = translate_pf f in
    SBCast.PNeg (n_f, translate_loc loc)
  | Exists (sv, pf, _, loc) ->
    let sb_var = translate_var sv in
    let sb_pf = translate_pf pf in
    let sb_loc = translate_loc loc in
    SBCast.mk_pexists ~pos:sb_loc [sb_var] sb_pf
  | _ -> report_error no_pos
      ("this pure formula not handled" ^ (CPR.string_of_pure_formula pure_f))

let rec translate_back_pf (pf : SBCast.pure_form) = match pf with
  | SBCast.BConst (b, pos)
    -> CP.BForm ((CP.BConst (b, translate_back_pos pos), None), None)
  | SBCast.BVar (var, pos) ->
    let hip_var = translate_back_var var in
    let loc = translate_back_pos pos in
    CP.BForm ((CP.BVar (hip_var, loc), None), None)
  | SBCast.BinRel (br, exp1, exp2, pos) ->
    let exp1_hip = translate_back_exp exp1 in
    let exp2_hip = translate_back_exp exp2 in
    let loc = translate_back_pos pos in
    begin
      match br with
      | SBCast.Lt -> CP.BForm((CP.Lt (exp1_hip, exp2_hip, loc), None), None)
      | SBCast.Le -> CP.BForm((CP.Lte (exp1_hip, exp2_hip, loc), None), None)
      | SBCast.Gt -> CP.BForm((CP.Gt (exp1_hip, exp2_hip, loc), None), None)
      | SBCast.Ge -> CP.BForm((CP.Gte (exp1_hip, exp2_hip, loc), None), None)
      | SBCast.Eq -> CP.BForm((CP.Eq (exp1_hip, exp2_hip, loc), None), None)
      | SBCast.Ne -> CP.BForm((CP.Neq (exp1_hip, exp2_hip, loc), None), None)
    end
  | SBCast.PNeg (pf, pos) -> let loc = translate_back_pos pos in
    let hip_pf = translate_back_pf pf in
    CP.mkNot hip_pf None loc
  | SBCast.PExists (vars, pf, pos) ->
    let loc = translate_back_pos pos in
    let hip_pf = translate_back_pf pf in
    let hip_vars = List.map translate_back_var vars in
    CP.mkExists hip_vars hip_pf None loc
  | SBCast.PDisj (pfs, pos) ->
    let hip_pfs = List.map translate_back_pf pfs in
    let rec list_to_or pfs = match pfs with
      | [] -> report_error no_pos "empty"
      | [h] -> h
      | h::t -> let t_f = list_to_or t in
        CP.mkOr h t_f None no_pos
    in
    list_to_or hip_pfs
  | SBCast.PConj (pfs, pos) ->
    let hip_pfs = List.map translate_back_pf pfs in
    let rec list_to_and pfs = match pfs with
      | [] -> report_error no_pos "empty"
      | [h] -> h
      | h::t -> let t_f = list_to_and t in
        CP.mkAnd h t_f no_pos
    in
    list_to_and hip_pfs
  | _ -> report_error no_pos "translate_back_pf: this type of lhs not handled"

let rec translate_hf hf = match hf with
  | CF.HTrue
  | CF.HEmp -> (SBCast.HEmp (translate_loc no_pos), [], [])
  | CF.DataNode dnode ->
    let ann = dnode.CF.h_formula_data_imm in
    let holes = match ann with
      | CP.ConstAnn Lend -> [hf]
      | _ -> [] in
    let root = dnode.CF.h_formula_data_node in
    let sb_root_var = translate_var root in
    let sb_no_pos = translate_loc no_pos in
    let sb_root = SBCast.Var (sb_root_var, sb_no_pos) in
    let name = dnode.CF.h_formula_data_name in
    let args = dnode.CF.h_formula_data_arguments in
    let sb_arg_vars = List.map translate_var args in
    let sb_args = List.map (fun x -> SBCast.Var (x, sb_no_pos)) sb_arg_vars in
    let data_form = SBCast.mk_data_form sb_root name sb_args in
    (SBCast.mk_hform_df data_form, [], holes)
  | CF.Star star_hf ->
    let hf1 = star_hf.h_formula_star_h1 in
    let hf2 = star_hf.h_formula_star_h2 in
    let loc = star_hf.h_formula_star_pos in
    let pos = translate_loc loc in
    let (sb_hf1, sb_pf1, hole1) = translate_hf hf1 in
    let (sb_hf2, sb_pf2, hole2) = translate_hf hf2 in
    (SBCast.mk_hstar ~pos:pos sb_hf1 sb_hf2, sb_pf1@sb_pf2, hole1@hole2)
  | CF.ViewNode view ->
    let ann = view.CF.h_formula_view_imm in
    let holes = match ann with
      | CP.ConstAnn Lend -> [hf]
      | _ -> [] in
    let root = view.h_formula_view_node in
    let name = view.h_formula_view_name in
    let args = view.h_formula_view_arguments in
    let () = x_tinfo_hp (add_str "root: " CP.string_of_spec_var) root no_pos in
    let () = x_tinfo_hp (add_str "args: " (pr_list CP.string_of_spec_var)) args no_pos in
    let args = [root] @ args in
    let sb_vars = List.map translate_var args in
    let sb_exps = List.map SBCast.mk_exp_var sb_vars in
    let loc = view.h_formula_view_pos in
    let pos = translate_loc loc in
    let view_form = SBCast.mk_view_form ~pos:pos name sb_exps in
    (SBCast.mk_hform_vf view_form, [], holes)
  | CF.HFalse ->
    let sb_no_pos = translate_loc no_pos in
    let sb_false = SBCast.mk_false sb_no_pos in
    (SBCast.HEmp sb_no_pos, [sb_false], [])
  | _ -> report_error no_pos ("this hf is not supported: "
                              ^ (Cprinter.string_of_h_formula hf))

let exp_to_var sb_exp_var = match sb_exp_var with
  | CP.Var (sv, _) -> sv
  | _ -> report_error no_pos (CPR.string_of_formula_exp sb_exp_var)

let translate_back_df df =
  let root = translate_back_exp df.SBCast.dataf_root in
  let hip_root = exp_to_var root in
  let hip_args = List.map translate_back_exp df.SBCast.dataf_args in
  let hip_args = List.map exp_to_var hip_args in
  let hip_name = df.SBCast.dataf_name in
  let loc = translate_back_pos df.SBCast.dataf_pos in
  CF.mkDataNode hip_root hip_name hip_args loc

let translate_back_vf vf =
  let hip_args = List.map translate_back_exp vf.SBCast.viewf_args in
  let hip_args = List.map exp_to_var hip_args in
  let hip_root = List.hd hip_args in
  let hip_args = List.tl hip_args in
  let hip_name = vf.SBCast.viewf_name in
  let loc = translate_back_pos vf.SBCast.viewf_pos in
  CF.mkViewNode hip_root hip_name hip_args loc

let rec mkStarHList list = match list with
    | [] -> CF.HEmp
    | [h] -> h
    | h::t ->
      let tail = mkStarHList t in
      CF.mkStarH h tail no_pos

let translate_back_hf sb_hf holes =
  let rec helper sb_hf =
    match sb_hf with
    | SBCast.HEmp _ -> CF.HEmp
    | SBCast.HAtom (dfs, vfs, pos) ->
      let loc = translate_back_pos pos in
      let hip_dfs = List.map translate_back_df dfs in
      let hip_vfs = List.map translate_back_vf vfs in
      let h_formulas = hip_dfs @ hip_vfs in
      mkStarHList h_formulas
    | SBCast.HStar (hf1, hf2, pos) ->
      let hip_hf1 = helper hf1 in
      let hip_hf2 = helper hf2 in
      let loc = translate_back_pos pos in
      CF.mkStarH hip_hf1 hip_hf2 loc
    | _ -> report_error no_pos "un-handled cases"
  in
  let hip_hf = helper sb_hf in
  mkStarHList ([hip_hf]@holes)

let rec translate_formula formula =
  match formula with
  | CF.Base bf ->
    let hf = bf.CF.formula_base_heap in
    let (sb_hf, sb_pf1, holes) = translate_hf hf in
    let pf = CF.get_pure formula in
    let sb_pf2 = translate_pf pf in
    let sb_pf = SBCast.mk_pconj (sb_pf1@[sb_pf2]) in
    ([SBCast.mk_fbase sb_hf sb_pf], holes)
  | CF.Exists ef ->
    let hf = ef.CF.formula_exists_heap in
    let (sb_hf, sb_pf1, holes) = translate_hf hf in
    let pf = (Mcpure.pure_of_mix ef.CF.formula_exists_pure) in
    let sb_pf2 = translate_pf pf in
    let sb_pf = SBCast.mk_pconj (sb_pf1@[sb_pf2]) in
    let vars = ef.CF.formula_exists_qvars in
    let sb_vars = List.map translate_var vars in
    let sb_f = SBCast.mk_fbase sb_hf sb_pf in
    ([SBCast.mk_fexists sb_vars sb_f], holes)
  | CF.Or f ->
    let (sb_f1, hole1) = translate_formula f.CF.formula_or_f1 in
    let (sb_f2, hole2) = translate_formula f.CF.formula_or_f2 in
    (sb_f1@ sb_f2, hole1@hole2)

let rec translate_back_formula sb_f holes = match sb_f with
  | SBCast.FBase (hf, pf, pos) ->
    let hip_hf = translate_back_hf hf holes in
    let loc = translate_back_pos pos in
    let hip_pf = translate_back_pf pf in
    CF.mkBase_w_lbl hip_hf (Mcpure.mix_of_pure hip_pf)
      CvpermUtils.empty_vperm_sets CF.TypeTrue (CF.mkNormalFlow()) [] loc None
  | SBCast.FExists (vars, f, pos) ->
    let loc = translate_back_pos pos in
    let hip_f = translate_back_formula f holes in
    let hip_vars = List.map translate_back_var vars in
    CF.add_quantifiers hip_vars hip_f
  | _ -> report_error no_pos "un-handled case in translate_back_formula"

let rec translate_back_fs (fs: SBCast.formula list) holes =
  match fs with
  | [] -> report_error no_pos "songbird.ml cannot be empty list"
  | [h] -> translate_back_formula h holes
  | h::t -> let hip_h = translate_back_formula h holes in
    let hip_t = translate_back_fs t holes in
    CF.mkOr hip_h hip_t no_pos

let create_templ_prog prog ents
  =
  let program = SBCast.mk_program "hip_input" in
  let exp_decl = List.hd (prog.Cast.prog_exp_decls) in
  let fun_name = exp_decl.Cast.exp_name in
  let args = exp_decl.Cast.exp_params |> List.map translate_var in
  let f_defn = SBCast.mk_func_defn_unknown fun_name args in
  let ifr_typ = SBGlobals.IfrStrong in
  let infer_func = {
    SBCast.ifr_typ = ifr_typ;
    SBCast.ifr_pents = ents
  }
  in
  let nprog = {program with
             prog_funcs = [f_defn];
             prog_commands = [SBCast.InferFuncs infer_func]
            }
  in
  let () = x_tinfo_hp (add_str "nprog: " SBCast.pr_program) nprog no_pos in
  let sb_res =
    Libsongbird.Prover.infer_unknown_functions_with_false_rhs ifr_typ nprog
      ents in
  let inferred_prog = if sb_res = [] then nprog
      else snd (List.hd sb_res)
  in
  let () = x_tinfo_hp (add_str "inferred prog: " SBCast.pr_program) inferred_prog no_pos in
  inferred_prog.SBCast.prog_funcs

let translate_ent ent =
  let (lhs, rhs) = ent in
  let () = x_tinfo_hp (add_str "lhs: " pr_pf) lhs no_pos in
  let () = x_tinfo_hp (add_str "rhs: " pr_pf) rhs no_pos in

  let sb_lhs = translate_pf lhs in
  let sb_rhs = translate_pf  rhs in
  let () = x_tinfo_hp (add_str "lhs: " (SBCast.pr_pure_form)) sb_lhs no_pos in
  let () = x_tinfo_hp (add_str "rhs: " (SBCast.pr_pure_form)) sb_rhs no_pos in

  SBCast.mk_pure_entail sb_lhs sb_rhs

let get_vars_in_fault_ents ents =
  let pr_vars = Cprinter.string_of_spec_var_list in
  let pr_ents = pr_list (pr_pair pr_pf pr_pf) in
  let sb_ents = List.map translate_ent ents in
  let () = x_tinfo_hp (add_str "entails: " (pr_list SBCast.pr_pent)) sb_ents no_pos in
  let sb_vars = List.map Libsongbird.Prover.norm_entail sb_ents |> List.concat in
  let vars = List.map translate_back_var sb_vars in
  let () = x_tinfo_hp (add_str "vars: " pr_vars) vars no_pos in
  vars

let get_repair_candidate prog ents cond_op =
  let pr_ents = pr_list (pr_pair pr_pf pr_pf) in
  let () = x_tinfo_hp (add_str "entails: " pr_ents) ents no_pos in
  let sb_ents = List.map translate_ent ents in
  let fun_defs = create_templ_prog prog sb_ents in
  let get_func_exp fun_defs exp_decls =
    let exp_decl = List.hd exp_decls in
    let ident = exp_decl.Cast.exp_name in
    let vars = exp_decl.Cast.exp_params in
    try
      let fun_def = List.find (fun fun_def -> String.compare ident fun_def.SBCast.func_name == 0)
          fun_defs in
      match fun_def.SBCast.func_body with
      | SBCast.FuncTemplate _
      | SBCast.FuncUnknown -> None
      | SBCast.FuncForm exp ->
        let sb_vars = fun_def.SBCast.func_params in
        let translated_vars = List.map translate_back_var sb_vars in
        let translated_exp = translate_back_exp exp in
        (* let exp_vars = List.map Cpure.mk_exp_var vars in *)
        let substs = List.combine translated_vars vars in
        let n_exp = Cpure.e_apply_subs substs translated_exp in
        Some n_exp
    with Not_found -> None
  in
  let fun_def_exp = get_func_exp fun_defs prog.Cast.prog_exp_decls in
  match fun_def_exp with
  | Some fun_def_cexp ->
    let pr_exp = Cprinter.poly_string_of_pr Cprinter.pr_formula_exp in
      let () = x_tinfo_hp (add_str "exp: " pr_exp) fun_def_cexp no_pos in
      let exp_decl = List.hd prog.Cast.prog_exp_decls in
      let n_exp_decl = {exp_decl with exp_body = fun_def_cexp} in
      let n_prog = {prog with prog_exp_decls = [n_exp_decl]} in
        begin
          match cond_op with
          | Some cond ->
            let neg_cexp =
              begin
                match cond with
                | Iast.OpGt
                | Iast.OpLte ->
                  let n_exp = CP.mkMult_minus_one fun_def_cexp in
                  CP.mkAdd n_exp (CP.mkIConst 2 VarGen.no_pos) VarGen.no_pos
                | Iast.OpGte
                | Iast.OpLt ->
                  let n_exp = CP.mkMult_minus_one fun_def_cexp in
                  CP.mkSubtract n_exp (CP.mkIConst 1 VarGen.no_pos)
                    VarGen.no_pos
                | _ -> fun_def_cexp
              end
            in
            let neg_exp_decl = {exp_decl with exp_body = neg_cexp} in
            let neg_prog = {prog with prog_exp_decls = [neg_exp_decl]} in
            Some (n_prog, fun_def_cexp, Some neg_prog, Some neg_cexp)
          | None -> Some (n_prog, fun_def_cexp, None, None)
      end
    | None ->
      let () = x_tinfo_pp "No expression \n" VarGen.no_pos in
      None

let translate_data_decl (data:Cast.data_decl) =
  let ident = data.Cast.data_name in
  let loc = data.Cast.data_pos in
  let fields = data.Cast.data_fields in
  let fields = List.map (fun (x, y) -> x) fields in
  let sb_pos = translate_loc loc in
  let sb_fields = List.map (fun (a,b) -> (translate_type a, b)) fields in
  SBCast.mk_data_defn ident sb_fields sb_pos

let translate_view_decl (view:Cast.view_decl) =
  let ident = view.Cast.view_name in
  let loc = view.Cast.view_pos in
  let sb_pos = translate_loc loc in
  let vars = [Cpure.SpecVar (Named view.view_data_name, "self", VarGen.Unprimed)]
             @ view.Cast.view_vars in
  let typed_vars = List.map (fun x -> (Cpure.name_of_sv x, Cpure.typ_of_sv x)) vars in
  let sb_vars = List.map (fun (x,y) -> (x, translate_type y)) typed_vars in
  let formulas = view.Cast.view_un_struc_formula in
  let formulas = List.map (fun (x,y) -> x) formulas in
  let sb_formula, _ = formulas |> List.map translate_formula |> List.split in
  let sb_formula = List.concat sb_formula in
  let view_defn_cases = List.map SBCast.mk_view_defn_case sb_formula in
  SBCast.mk_view_defn ident sb_vars view_defn_cases sb_pos

let translate_prog (prog:Cast.prog_decl) =
  let data_decls = prog.Cast.prog_data_decls in
  let data_decls = List.filter
      (fun x -> String.compare x.Cast.data_name "node" = 0) data_decls in
  let pr1 = CPR.string_of_data_decl_list in
  let () = x_tinfo_hp (add_str "data decls" pr1) data_decls no_pos in
  let sb_data_decls = List.map translate_data_decl data_decls in
  let view_decls = prog.Cast.prog_view_decls in
  let view_decls = List.filter
      (fun x -> String.compare x.Cast.view_name "ll" = 0) view_decls in
  let pr2 = CPR.string_of_view_decl_list in
  let () = x_tinfo_hp (add_str "view decls" pr2) view_decls no_pos in
  let sb_view_decls = List.map translate_view_decl view_decls in
  let prog = SBCast.mk_program "heap_entail" in
  let n_prog = {prog with SBCast.prog_datas = sb_data_decls;
                        SBCast.prog_views = sb_view_decls}
  in
  let pr3 = SBCast.pr_program in
  let n_prog = Libsongbird.Transform.normalize_prog n_prog in
  let () = x_tinfo_hp (add_str "prog" pr3) n_prog no_pos in
  n_prog


let rec heap_entail_after_sat_struc_x (prog:Cast.prog_decl)
    (ctx:CF.context) (conseq:CF.struc_formula) ?(pf=None)=
  let () = x_tinfo_hp (add_str "ctx" CPR.string_of_context) ctx no_pos in
  let () = x_tinfo_hp (add_str "conseq" pr_struc_f) conseq no_pos in
  match ctx with
  | Ctx es ->
    (
      match conseq with
      | CF.EBase bf -> hentail_after_sat_ebase prog ctx es bf ~pf:pf
      | CF.ECase cases ->
        let branches = cases.CF.formula_case_branches in
        let results = List.map (fun (pf, struc) ->
            heap_entail_after_sat_struc_x prog ctx struc ~pf:(Some pf)) branches
        in
        let rez1, _ = List.split results in
        let rez1 = List.fold_left (fun a c -> CF.or_list_context a c)
            (List.hd rez1) (List.tl rez1) in
        (rez1, Prooftracer.TrueConseq)
      | EList b ->
        let _, struc_list = List.split b in
        let res_list =
          List.map (fun x -> heap_entail_after_sat_struc_x prog ctx x ~pf:pf)
            struc_list in
        let ctx_lists = res_list |> List.split |> fst in
        let res = CF.fold_context_left 41 ctx_lists in
        (res, Prooftracer.TrueConseq)
      | EAssume assume ->
        let assume_f = assume.CF.formula_assume_simpl in
        let f = es.CF.es_formula in
        let combine_f f1 f2 =
          let heaps_f1 = CF.heap_of f1 in
          let pure_f1 = CF.get_pure f1 in
          let heaps_f2 = CF.heap_of f2 in
          let pure_f2 = CF.get_pure f2 in
          let pure = CP.mkAnd pure_f1 pure_f2 no_pos in
          let heap = mkStarHList (heaps_f1 @ heaps_f2) in
          let mix = Mcpure.mix_of_pure pure in
          CF.mkBase_simp heap mix in
        let new_f = combine_f f assume_f in
        let new_ctx = CF.Ctx {es with CF.es_formula = new_f} in
        let new_conseq = assume.CF.formula_assume_struc in
        heap_entail_after_sat_struc_x prog new_ctx new_conseq ~pf:None
      | _ -> report_error no_pos ("unhandle " ^ (pr_struc_f conseq))
    )
  | OCtx (c1, c2) ->
    let rs1, proof1 = heap_entail_after_sat_struc_x prog c1 conseq ~pf:None in
    let rs2, proof2 = heap_entail_after_sat_struc_x prog c2 conseq ~pf:None in
    (CF.or_list_context rs1 rs2, Prooftracer.TrueConseq)

and heap_entail_after_sat_struc prog ctx conseq ?(pf=None) =
  Debug.no_2 "heap_entail_after_sat_struc" Cprinter.string_of_context
    Cprinter.string_of_struc_formula
    (fun (lctx, _) -> Cprinter.string_of_list_context lctx)
    (fun _ _ -> heap_entail_after_sat_struc_x prog ctx conseq ~pf:None) ctx conseq

and hentail_after_sat_ebase prog ctx es bf ?(pf=None) =
  let n_prog = translate_prog prog in
  let evars = bf.CF.formula_struc_implicit_inst
              @ bf.CF.formula_struc_explicit_inst
              @ bf.CF.formula_struc_exists
              @ es.CF.es_evars in
  let () = x_tinfo_hp (add_str "exists var" pr_svs) evars no_pos in
  let () = x_tinfo_hp (add_str "es" CPR.string_of_entail_state) es no_pos in
  let conseqs, holes = if Gen.is_empty evars
    then translate_formula bf.CF.formula_struc_base
    else
      let sb_f, holes = translate_formula bf.CF.formula_struc_base in
      let pos = translate_loc bf.CF.formula_struc_pos in
      let sb_vars = List.map translate_var evars in
      (List.map (fun x -> SBCast.mk_fexists ~pos:pos sb_vars x) sb_f, holes) in
  let holes = List.map CF.disable_imm_h_formula holes in
  let formula = es.CF.es_formula in
  let formula = match pf with
    | None -> formula
    | Some pf -> CF.add_pure_formula_to_formula pf formula in
  let sb_ante, _ = translate_formula formula in
  let sb_conseq = List.hd conseqs in
  let ents = List.map (fun x -> SBCast.mk_entailment ~mode:PrfEntailHip x sb_conseq)
      sb_ante in
  let () = x_tinfo_hp (add_str "ents" SBCast.pr_ents) ents no_pos in
  let ptrees = List.map (fun ent -> SBProver.check_entailment ~interact:false n_prog ent) ents in
  let validities = List.map (fun ptree -> Libsongbird.Proof.get_ptree_validity
                                ptree) ptrees in
  let () = x_tinfo_hp (add_str "validities" (pr_list pr_validity)) validities no_pos in
  if List.for_all (fun x -> x = SBGlobals.MvlTrue) validities
  then
    let residues = List.map (fun ptree ->
        let residue_fs = Libsongbird.Proof.get_ptree_residues ptree in
        let pr_rsd = SBCast.pr_fs in
        let () = x_tinfo_hp (add_str "residues" pr_rsd) residue_fs no_pos in
        List.hd residue_fs
      ) ptrees in
    let residue = translate_back_fs residues holes in
    let () = x_tinfo_hp (add_str "residue" pr_formula) residue no_pos in
    let n_ctx = CF.Ctx {es with
                        CF.es_evars = CF.get_exists es.CF.es_formula;
                        CF.es_formula = residue;
                       } in
    let conti = bf.CF.formula_struc_continuation in
    match conti with
    | None -> (CF.SuccCtx [n_ctx], Prooftracer.TrueConseq)
    | Some struc -> heap_entail_after_sat_struc_x prog n_ctx struc ~pf:None
  else
    let msg = "songbird result is Failed." in
    (CF.mkFailCtx_simple msg es bf.CF.formula_struc_base (CF.mk_cex true) no_pos
     , Prooftracer.Failure)
    (* report_error no_pos "No residue not handled" *)
