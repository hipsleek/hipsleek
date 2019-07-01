#include "xdebug.cppo"
open Globals
open Gen.Basic

module SBC = Libsongbird.Cast
module SBD = Libsongbird.Debug
module SBG = Libsongbird.Globals
module SBPP = Libsongbird.Prover_pure
module SBPH = Libsongbird.Prover_hip
module SBPA = Libsongbird.Prover_all
module SBPU = Libsongbird.Prover_unkentail
module SBPFE = Libsongbird.Proof_entail
module SBPFU = Libsongbird.Proof_unkentail
module SBE = Libsongbird.Exportc
module CA = Cast
module CP = Cpure
module CF = Cformula
module CPR = Cprinter
module MCP = Mcpure
module Syn = Synthesis

(* translation of HIP's data structures to Songbird's data structures
   will be done here *)

let add_str = Gen.Basic.add_str
let no_pos = VarGen.no_pos
let report_error = Gen.Basic.report_error
let pr_formula = CPR.string_of_formula
let pr_hf = CPR.string_of_h_formula
let pr_vars = CPR.string_of_spec_var_list
let pr_hps = pr_list CPR.string_of_hp_decl
let pr_struc_f = CPR.string_of_struc_formula
let pr_svs = CPR.string_of_spec_var_list
let pr_pf = Cprinter.string_of_pure_formula
let pr_entail = SBC.pr_entailment
let pre_list = ref ([] : CF.formula list)
let sb_program = ref (None: SBC.program option)
let pr_ents = pr_list (pr_pair pr_pf pr_pf)
let pr_pos = string_of_loc

(*********************************************************************
 * Global variables
 *********************************************************************)

let index_export_ent = ref 0
let index_export_fml = ref 0
let export_songbird_proof = ref false

(*********************************************************************
 * Translate Formulas
 *********************************************************************)

let pr_validity tvl = match tvl with
  | SBG.MvlFalse -> "Invalid"
  | SBG.MvlTrue -> "Valid"
  | SBG.MvlUnkn -> "Unknown"
  | SBG.MvlInfer -> "Infer"

let rec check_hp_hf_x hp_names hf = match hf with
  | CF.HVar _ | CF.DataNode _ | CF.ViewNode _ | CF.HEmp | CF.HTrue
  | CF.HFalse -> false
  | CF.HRel (sv, args, _) -> let sv_name = CP.name_of_sv sv in
    if List.exists (fun x -> eq_str x sv_name) hp_names
    then true else false
  | CF.Star sf -> (check_hp_hf_x hp_names sf.CF.h_formula_star_h1) ||
               (check_hp_hf_x hp_names sf.CF.h_formula_star_h2)
  | _ -> report_error no_pos "unhandled case of check_conseq_hp"

let check_hp_hf hp_names hf =
  Debug.no_1 "check_hp_hf" pr_hf string_of_bool
    (fun _ -> check_hp_hf_x hp_names hf) hf

let rec check_hp_formula_x hp_names formula = match (formula:CF.formula) with
  | CF.Base bf -> check_hp_hf hp_names bf.CF.formula_base_heap
  | CF.Exists ef -> check_hp_hf hp_names ef.CF.formula_exists_heap
  | CF.Or f -> (check_hp_formula_x hp_names f.CF.formula_or_f1) ||
               (check_hp_formula_x hp_names f.CF.formula_or_f2)

let check_hp_formula hp_names formula =
  Debug.no_1 "check_hp_formula" pr_formula string_of_bool
    (fun _ -> check_hp_formula_x hp_names formula) formula

let rec var_closure_hf hf vars = match (hf:CF.h_formula) with
  | CF.HTrue  | CF.HFalse | CF.HEmp -> hf
  | CF.Star shf ->
    let svars = CF.get_all_sv hf in
    if not(List.exists (fun x -> List.mem x vars) svars) then CF.HEmp
    else
      let h1 = shf.CF.h_formula_star_h1 in
      let h2 = shf.CF.h_formula_star_h2 in
      CF.Star {shf with CF.h_formula_star_h1 = var_closure_hf h1 vars;
                        CF.h_formula_star_h2 = var_closure_hf h2 vars}
  | CF.DataNode dnode ->
    let svs = [dnode.CF.h_formula_data_node]@dnode.CF.h_formula_data_arguments in
    let svs = CP.remove_dups_svl svs in
    if not(List.exists (fun x -> List.mem x vars) svs) then CF.HEmp
    else hf
  | _ -> report_error no_pos "var_closure_hf: unhandled"

let rec var_closure_pf puref vars =
  match puref with
  | CP.BForm (bf, label) ->
    let bf_vars = CP.bfv bf in
    if List.exists (fun x -> List.mem x vars) bf_vars
    then puref
    else CP.mkTrue no_pos
  | CP.And (f1, f2, loc) ->
    let n_f1 = var_closure_pf f1 vars in
    let n_f2 = var_closure_pf f2 vars in
    CP.And (n_f1, n_f2, loc)
  | CP.Or (f1, f2, ops, loc) ->
    let n_f1 = var_closure_pf f1 vars in
    let n_f2 = var_closure_pf f2 vars in
    CP.Or (n_f1, n_f2, ops, loc)
  | _ -> report_error no_pos ("var_closure_pf unhandled"
                              ^ (pr_pf puref))

let rec var_closure f vars =
  let rec helper f vars = match f with
  | CF.Base bf ->
    let hf = bf.CF.formula_base_heap in
    let pf = Mcpure.pure_of_mix bf.CF.formula_base_pure in
    CF.Base {bf with CF.formula_base_heap = var_closure_hf hf vars;
                  formula_base_pure = Mcpure.mix_of_pure (var_closure_pf pf vars)}
  | CF.Exists ef ->
    let n_hf = var_closure_hf ef.CF.formula_exists_heap vars in
    let pf =  ef.CF.formula_exists_pure in
    let n_pf = var_closure_pf (Mcpure.pure_of_mix pf) vars in
    CF.Exists {ef with CF.formula_exists_heap = n_hf;
                       CF.formula_exists_pure = Mcpure.mix_of_pure n_pf}
  | CF.Or df ->
    let f1 = df.CF.formula_or_f1 in
    let f2 = df.CF.formula_or_f2 in
    let n_f1 = helper f1 vars in
    let n_f2 = helper f2 vars in
    CF.Or {df with CF.formula_or_f1 = n_f1;
                   CF.formula_or_f2 = n_f2} in
  let n_f = helper f vars in
  let n_vars = n_f |> CF.all_vars in
  if List.length n_vars = List.length vars then n_f
  else var_closure f n_vars


let translate_loc (location:VarGen.loc) : SBG.pos =
  {
    SBG.pos_begin = location.VarGen.start_pos;
    SBG.pos_end = location.VarGen.end_pos;}

let translate_back_pos (pos:SBG.pos) : VarGen.loc =
  let no_pos1 = { Lexing.pos_fname = "";
                  Lexing.pos_lnum = 0;
                  Lexing.pos_bol = 0;
                  Lexing.pos_cnum = 0 } in
  { VarGen.start_pos = pos.SBG.pos_begin;
    VarGen.mid_pos = no_pos1;
    VarGen.end_pos = pos.SBG.pos_end;}

let translate_type (typ: Globals.typ) : SBG.typ =
  match typ with
  | NUM
  | Int -> SBG.TInt
  | TVar num -> SBG.TVar num
  | Bool -> SBG.TBool
  | UNK -> SBG.TUnk
  | Void -> SBG.TVoid
  | Named str -> SBG.TData str
  | _ -> report_error no_pos
           ("translate_type:" ^ (Globals.string_of_typ typ) ^ " is not handled")

let translate_back_type typ = match typ with
  | SBG.TInt -> Globals.Int
  | SBG.TBool -> Globals.Bool
  | SBG.TUnk -> Globals.UNK
  | SBG.TVoid -> Globals.Void
  | SBG.TData str -> Globals.Named str
  | SBG.TNull -> Globals.Named "null"
  | SBG.TVar num -> Globals.TVar num

let translate_var_x (var: CP.spec_var): SBG.var =
  let CP.SpecVar (typ, ident, primed) = var in
  match primed with
  | VarGen.Primed -> (ident ^ "'", translate_type typ)
  | _ -> (ident, translate_type typ)

let translate_var var =
  let pr1 = CPR.string_of_spec_var in
  let pr2 = SBG.pr_var in
  Debug.no_1 "translate_var" pr1 pr2
    (fun _ -> translate_var_x var) var

let translate_back_var (var : SBG.var) =
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
  | CP.Null loc -> SBC.Null (translate_loc loc)
  | CP.Var (var, loc) -> SBC.Var (translate_var var, translate_loc loc)
  | CP.IConst (num, loc) -> SBC.IConst (num, translate_loc loc)
  | CP.TypeCast (_, e, _) -> translate_exp e
  | CP.Add (exp1, exp2, loc) ->
        let t_exp1 = translate_exp exp1 in
        let t_exp2 = translate_exp exp2 in
        SBC.BinExp (SBC.Add, t_exp1, t_exp2, translate_loc loc)
  | CP.Subtract (exp1, exp2, loc) ->
        let t_exp1 = translate_exp exp1 in
        let t_exp2 = translate_exp exp2 in
        SBC.BinExp (SBC.Sub, t_exp1, t_exp2, translate_loc loc)
  | CP.Mult (exp1, exp2, loc) ->
        let t_exp1 = translate_exp exp1 in
        let t_exp2 = translate_exp exp2 in
        SBC.BinExp (SBC.Mul, t_exp1, t_exp2, translate_loc loc)
  | CP.Div (exp1, exp2, loc) ->
        let t_exp1 = translate_exp exp1 in
        let t_exp2 = translate_exp exp2 in
        SBC.BinExp (SBC.Div, t_exp1, t_exp2, translate_loc loc)
  | CP.Template templ ->
    if (!Globals.translate_funcs) then
      let fun_name = CP.name_of_sv templ.CP.templ_id in
      let args = templ.CP.templ_args |> List.map translate_exp in
      SBC.mk_func (SBC.FuncName fun_name) args
    else report_error no_pos "translate_funcs not activated"
  | CP.Max (e1, e2, loc) ->
    let sb_e1 = translate_exp e1 in
    let sb_e2 = translate_exp e2 in
    let pos = translate_loc loc in
    SBC.mk_func ~pos:pos SBC.Max [sb_e1; sb_e2]
  | CP.Min (e1, e2, loc) ->
    let sb_e1 = translate_exp e1 in
    let sb_e2 = translate_exp e2 in
    let pos = translate_loc loc in
    SBC.mk_func ~pos:pos SBC.Min [sb_e1; sb_e2]
  | _ -> report_error no_pos ("this exp is not handled"
                              ^ (Cprinter.string_of_formula_exp exp))

let rec translate_back_exp (exp: SBC.exp) = match exp with
  | SBC.Null pos -> CP.Null (translate_back_pos pos)
  | SBC.Var (var, pos) -> CP.Var (translate_back_var var, translate_back_pos
                                      pos)
  | SBC.IConst (num, pos) -> CP.IConst (num, translate_back_pos pos)
  | SBC.BinExp (bin_op, exp1, exp2, pos) ->
    begin
      match bin_op with
      | SBC.Add -> CP.Add (translate_back_exp exp1, translate_back_exp exp2,
               translate_back_pos pos)
      | SBC.Sub -> CP.Subtract (translate_back_exp exp1, translate_back_exp exp2,
               translate_back_pos pos)
      | SBC.Mul -> CP.Mult (translate_back_exp exp1, translate_back_exp exp2,
               translate_back_pos pos)
      | SBC.Div -> CP.Div (translate_back_exp exp1, translate_back_exp exp2,
               translate_back_pos pos)
    end
  | SBC.LTerm (lterm, pos) ->
    let n_exp = SBC.convert_lterm_to_binary_exp pos lterm in
    translate_back_exp n_exp
  | SBC.PTerm (pterm, pos) ->
    let n_exp = SBC.convert_pterm_to_binary_exp pos pterm in
    translate_back_exp n_exp
  | SBC.Func (func, exps, pos) ->
    begin
      match func with
      | SBC.Max ->
        let args = List.map translate_back_exp exps in
        if List.length args = 2 then
          let exp1 = List.hd args in
          let exp2 = args |> List.tl |> List.hd in
          let loc = translate_back_pos pos in
          CP.Max (exp1, exp2, loc)
        else report_error no_pos "number of args in max wrong"
      | SBC.Min ->
        let args = List.map translate_back_exp exps in
        if List.length args = 2 then
          let exp1 = List.hd args in
          let exp2 = args |> List.tl |> List.hd in
          let loc = translate_back_pos pos in
          CP.Min (exp1, exp2, loc)
        else report_error no_pos "number of args in min wrong"
      | _ -> report_error no_pos
        ("translate_back_exp:" ^ (SBC.pr_exp exp) ^ " is not handled")
    end
  | _ -> report_error no_pos
           ("this exp formula not handled: " ^ (SBC.pr_exp exp))

let rec translate_pf (pure_f: CP.formula)  =
  match pure_f with
  | CP.BForm (b_formula, _) ->
    let (p_formula, _) = b_formula in
    begin
      match (p_formula:CP.p_formula) with
      | CP.BVar (var, loc) ->
        SBC.BVar (translate_var var, translate_loc loc)
      | CP.BConst (b, loc) ->
        SBC.BConst (b, translate_loc loc)
      | CP.Eq (exp1, exp2, loc) ->
        let sb_exp1 = translate_exp exp1 in
        let sb_exp2 = translate_exp exp2 in
        let sb_loc = translate_loc loc in
        SBC.BinRel (SBC.Eq, sb_exp1, sb_exp2, sb_loc)
      | CP.Neq (exp1, exp2, loc) ->
        let sb_exp1 = translate_exp exp1 in
        let sb_exp2 = translate_exp exp2 in
        let sb_loc = translate_loc loc in
        SBC.BinRel (SBC.Ne, sb_exp1, sb_exp2, sb_loc)
      | CP.Gt (exp1, exp2, loc) ->
        let sb_exp1 = translate_exp exp1 in
        let sb_exp2 = translate_exp exp2 in
        let sb_loc = translate_loc loc in
        SBC.BinRel (SBC.Gt, sb_exp1, sb_exp2, sb_loc)
      | CP.Gte (exp1, exp2, loc) ->
        let sb_exp1 = translate_exp exp1 in
        let sb_exp2 = translate_exp exp2 in
        let sb_loc = translate_loc loc in
        SBC.BinRel (SBC.Ge, sb_exp1, sb_exp2, sb_loc)
      | CP.Lt (exp1, exp2, loc) ->
        let sb_exp1 = translate_exp exp1 in
        let sb_exp2 = translate_exp exp2 in
        let sb_loc = translate_loc loc in
        SBC.BinRel (SBC.Lt, sb_exp1, sb_exp2, sb_loc)
      | CP.Lte (exp1, exp2, loc) ->
        let sb_exp1 = translate_exp exp1 in
        let sb_exp2 = translate_exp exp2 in
        let sb_loc = translate_loc loc in
        SBC.BinRel (SBC.Le, sb_exp1, sb_exp2, sb_loc)
      | CP.EqMax (e1, e2, e3, loc) ->
        let sb_exp1 = translate_exp e1 in
        let sb_exp2 = translate_exp e2 in
        let sb_exp3 = translate_exp e3 in
        let sb_loc = translate_loc loc in
        let max = SBC.mk_func SBC.Max [sb_exp2; sb_exp3] in
        SBC.BinRel (SBC.Eq, sb_exp1, max, sb_loc)
      | CP.EqMin (e1, e2, e3, loc) ->
        let sb_exp1 = translate_exp e1 in
        let sb_exp2 = translate_exp e2 in
        let sb_exp3 = translate_exp e3 in
        let sb_loc = translate_loc loc in
        let max = SBC.mk_func SBC.Min [sb_exp2; sb_exp3] in
        SBC.BinRel (SBC.Eq, sb_exp1, max, sb_loc)
      | CP.LexVar lex ->
        SBC.BConst (true, translate_loc lex.CP.lex_loc)
      | _ -> report_error no_pos
               ("this p_formula is not handled" ^ (CPR.string_of_p_formula p_formula))
    end
  | CP.And (f1, f2, loc) ->
    let n_f1 = translate_pf f1 in
    let n_f2 = translate_pf f2 in
    SBC.PConj ([n_f1; n_f2], translate_loc loc)
  | CP.Or (f1, f2, _, loc) ->
    let n_f1 = translate_pf f1 in
    let n_f2 = translate_pf f2 in
    SBC.PDisj ([n_f1; n_f2], translate_loc loc)
  | CP.Not (f, _, loc) ->
    let n_f = translate_pf f in
    SBC.PNeg (n_f, translate_loc loc)
  | CP.Exists (sv, pf, _, loc) ->
    let sb_var = translate_var sv in
    let sb_pf = translate_pf pf in
    let sb_loc = translate_loc loc in
    SBC.mk_pexists ~pos:sb_loc [sb_var] sb_pf
  | _ -> report_error no_pos
           ("this pure formula not handled" ^ (CPR.string_of_pure_formula pure_f))

let translate_pf_wrapper pf =
  Debug.no_1 "translate_pf" pr_pf (SBC.pr_pf)
    (fun _ -> translate_pf pf) pf

let rec translate_back_pf (pf : SBC.pure_form) = match pf with
  | SBC.BConst (b, pos)
    -> CP.BForm ((CP.BConst (b, translate_back_pos pos), None), None)
  | SBC.BVar (var, pos) -> let hip_var = translate_back_var var in
    let loc = translate_back_pos pos in
    CP.BForm ((CP.BVar (hip_var, loc), None), None)
  | SBC.BinRel (br, exp1, exp2, pos) ->
    let exp1_hip = translate_back_exp exp1 in
    let exp2_hip = translate_back_exp exp2 in
    let loc = translate_back_pos pos in
    begin
      match br with
      | SBC.Lt -> CP.BForm((CP.Lt (exp1_hip, exp2_hip, loc), None), None)
      | SBC.Le -> CP.BForm((CP.Lte (exp1_hip, exp2_hip, loc), None), None)
      | SBC.Gt -> CP.BForm((CP.Gt (exp1_hip, exp2_hip, loc), None), None)
      | SBC.Ge -> CP.BForm((CP.Gte (exp1_hip, exp2_hip, loc), None), None)
      | SBC.Eq ->
        begin
          match exp2_hip with
          | CP.Max (max1, max2, _) ->
            CP.BForm((CP.EqMax (exp1_hip, max1, max2, loc), None), None)
          | _ ->
            CP.BForm((CP.Eq (exp1_hip, exp2_hip, loc), None), None)
        end
      | SBC.Ne -> CP.BForm((CP.Neq (exp1_hip, exp2_hip, loc), None), None)
    end
  | SBC.PNeg (pf, pos) -> let loc = translate_back_pos pos in
    let hip_pf = translate_back_pf pf in
    CP.mkNot hip_pf None loc
  | SBC.PExists (vars, pf, pos) ->
    let loc = translate_back_pos pos in
    let hip_pf = translate_back_pf pf in
    let hip_vars = List.map translate_back_var vars in
    CP.mkExists hip_vars hip_pf None loc
  | SBC.PDisj (pfs, pos) ->
    let hip_pfs = List.map translate_back_pf pfs in
    let rec list_to_or pfs = match pfs with
      | [] -> report_error no_pos "empty"
      | [h] -> h
      | h::t -> let t_f = list_to_or t in
        CP.mkOr h t_f None no_pos
    in
    list_to_or hip_pfs
  | SBC.PConj (pfs, pos) ->
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
  | CF.HTrue | CF.HEmp -> (SBC.HEmp (translate_loc no_pos), [], [])
  | CF.DataNode dnode -> let ann = dnode.CF.h_formula_data_imm in
    let holes = match ann with
      | CP.ConstAnn Lend -> [hf]
      | _ -> [] in
    let root = dnode.CF.h_formula_data_node in
    let sb_root_var = translate_var root in
    let sb_no_pos = translate_loc no_pos in
    let sb_root = SBC.Var (sb_root_var, sb_no_pos) in
    let name, args = dnode.CF.h_formula_data_name, dnode.CF.h_formula_data_arguments in
    let sb_arg_vars = List.map translate_var args in
    let sb_args = List.map (fun x -> SBC.Var (x, sb_no_pos)) sb_arg_vars in
    let data_form = SBC.mk_data_form sb_root name sb_args in
    (SBC.mk_hform_df data_form, [], holes)
  | CF.Star shf ->
    let hf1, hf2 = shf.CF.h_formula_star_h1, shf.CF.h_formula_star_h2 in
    let pos = shf.CF.h_formula_star_pos |> translate_loc in
    let (sb_hf1, sb_pf1, hole1) = translate_hf hf1 in
    let (sb_hf2, sb_pf2, hole2) = translate_hf hf2 in
    (SBC.mk_hstar ~pos:pos sb_hf1 sb_hf2, sb_pf1@sb_pf2, hole1@hole2)
  | CF.ViewNode vf ->
    let ann = vf.CF.h_formula_view_imm in
    let holes = match ann with
      | CP.ConstAnn Lend -> [hf]
      | _ -> [] in
    let root, name = vf.CF.h_formula_view_node, vf.CF.h_formula_view_name in
    let args = vf.CF.h_formula_view_arguments in
    let () = x_tinfo_hp (add_str "root: " CP.string_of_spec_var) root no_pos in
    let () = x_tinfo_hp (add_str "args: " (pr_list CP.string_of_spec_var)) args no_pos in
    let args = [root] @ args in
    let sb_vars = List.map translate_var args in
    let sb_exps = List.map SBC.mk_exp_var sb_vars in
    let pos = vf.CF.h_formula_view_pos |> translate_loc in
    let view_form = SBC.mk_view_form ~pos:pos name sb_exps in
    (SBC.mk_hform_vf view_form, [], holes)
  | CF.HFalse -> let sb_no_pos = translate_loc no_pos in
    let sb_false = SBC.mk_false sb_no_pos in
    (SBC.HEmp sb_no_pos, [sb_false], [])
  | CF.HRel (sv, exps, loc) -> let sb_pos = translate_loc loc in
    let sb_args = List.map translate_exp exps in
    let name = CP.name_of_sv sv in
    let view_form = SBC.mk_view_form ~pos:sb_pos name sb_args in
    (SBC.mk_hform_vf view_form, [], [])
  | _ -> report_error no_pos ("this hf is not supported: "
                              ^ (Cprinter.string_of_h_formula hf))

let exp_to_var exp = match exp with
  | CP.Var (sv, _) -> (sv, [], [])
  | _ ->
    let name = fresh_name() in
    let var = CP.mk_typed_sv Int name in
    let var_exp = CP.mkVar var no_pos in
    let pf = CP.mkEqExp var_exp exp no_pos in
    (var, [pf], [var])

let translate_back_df df =
  match df.SBC.dataf_root with
  | SBC.Null _ -> (CF.HEmp, [], [])
  | _ ->
    let h_root, pf1, e_var = translate_back_exp df.SBC.dataf_root |> exp_to_var in
    let triples = List.map translate_back_exp df.SBC.dataf_args
                  |> List.map exp_to_var in
    let h_args = triples |> List.map (fun (x,_,_) -> x) in
    let pf2 = triples |> List.map (fun (_, x,_) -> x) |> List.concat in
    let e_var2 = triples |> List.map (fun (_,_, x) -> x) |> List.concat in
    let h_name = df.SBC.dataf_name in
    let loc = translate_back_pos df.SBC.dataf_pos in
    (CF.mkDataNode h_root h_name h_args loc, pf1 @ pf2, e_var@e_var2)

let translate_back_vf vf =
  let hp_name = vf.SBC.viewf_name in
  let hp_names = !Synthesis.unk_hps |> List.map (fun x -> x.CA.hp_name) in
  let () = x_tinfo_hp (add_str "hp_name" pr_id) hp_name no_pos in
  let () = x_tinfo_hp (add_str "hp_names" (pr_list pr_id)) hp_names no_pos in
  if List.mem hp_name hp_names then
    let hp_name = CP.mk_spec_var hp_name in
    let hp_args = List.map translate_back_exp vf.SBC.viewf_args in
    let loc = translate_back_pos vf.SBC.viewf_pos in
    (CF.HRel (hp_name, hp_args, loc), [], [])
  else
    let vargs = vf.SBC.viewf_args in
    if List.exists (fun x -> match x with SBC.Null _ -> true
                                        | _ -> false) vargs
    then (CF.HEmp, [], [])
    else let h_triples = List.map translate_back_exp vargs
                         |> List.map exp_to_var in
      let h_all_args = h_triples |> List.map (fun (x,_,_) -> x) in
      let e_vars = h_triples |> List.map (fun (_,_,x) -> x) |> List.concat in
      let pfs = h_triples |> List.map (fun (_,x,_) -> x) |> List.concat in
      let h_root, h_args = List.hd h_all_args, List.tl h_all_args in
      let loc = translate_back_pos vf.SBC.viewf_pos in
      (CF.mkViewNode h_root hp_name h_args loc, pfs, e_vars)

let rec mkStarHList list = match list with
  | [] -> CF.HEmp    | [h] -> h
  | h::t -> let tail = mkStarHList t in
    CF.mkStarH h tail no_pos

let translate_back_hf sb_hf holes =
  let rec helper sb_hf =
    match sb_hf with
    | SBC.HEmp _ -> (CF.HEmp, [], [])
    | SBC.HAtom (dfs, vfs, pos) ->
      let df_triples = List.map translate_back_df dfs in
      let h_dfs = List.map (fun (x,_,_) -> x) df_triples in
      let df_pf = df_triples |> List.map (fun (_,x,_) -> x) |> List.concat in
      let df_evars = df_triples |> List.map (fun (_,_,x) -> x) |> List.concat in
      let vf_triples = List.map translate_back_vf vfs in
      let h_vfs = vf_triples |> List.map (fun (x,_,_) -> x) in
      let vf_pf = vf_triples |> List.map (fun (_,x,_) -> x) |> List.concat in
      let vf_evars = vf_triples |> List.map (fun (_,_,x) -> x) |> List.concat in
      let h_formulas = h_dfs @ h_vfs in
      (mkStarHList h_formulas, df_pf @ vf_pf, df_evars@vf_evars) in
    (* | SBC.HStar (hf1, hf2, pos) ->
     *   let h_hf1, pf1, evars1 = helper hf1 in
     *   let h_hf2, pf2, evars2 = helper hf2 in
     *   let loc = translate_back_pos pos in
     *   (CF.mkStarH h_hf1 h_hf2 loc, pf1@pf2, evars1@evars2) in *)
  let h_hf, pf, evars = helper sb_hf in
  (mkStarHList ([h_hf]@holes), pf, evars)

let rec translate_formula formula =
  let () = x_tinfo_hp (add_str "formula" pr_formula) formula no_pos in
  match formula with
  | CF.Base bf ->
    let hf = bf.CF.formula_base_heap in
    let (sb_hf, sb_pf1, holes) = translate_hf hf in
    let pf = CF.get_pure formula in
    let sb_pf2 = translate_pf_wrapper pf in
    let sb_pf = SBC.mk_pconj (sb_pf1@[sb_pf2]) in
    ([SBC.mk_fbase sb_hf sb_pf], holes)
  | CF.Exists ef ->
    let hf = ef.CF.formula_exists_heap in
    let (sb_hf, sb_pf1, holes) = translate_hf hf in
    let pf = (Mcpure.pure_of_mix ef.CF.formula_exists_pure) in
    let sb_pf2 = translate_pf_wrapper pf in
    let sb_pf = SBC.mk_pconj (sb_pf1@[sb_pf2]) in
    let vars = ef.CF.formula_exists_qvars in
    let sb_vars = List.map translate_var vars in
    let sb_f = SBC.mk_fbase sb_hf sb_pf in
    ([SBC.mk_fexists sb_vars sb_f], holes)
  | CF.Or f ->
    let (sb_f1, hole1) = translate_formula f.CF.formula_or_f1 in
    let (sb_f2, hole2) = translate_formula f.CF.formula_or_f2 in
    (sb_f1@ sb_f2, hole1@hole2)

let translate_single_formula formula =
  let formula_list,_ = translate_formula formula in
  if List.length formula_list = 1 then
    List.hd formula_list
  else report_error no_pos "translate_formula: multiple return formula"

let translate_entailment entailment =
  let ante, conseq = fst entailment, snd entailment in
  let sb_ante, _ = translate_formula ante in
  let sb_conseq, _ = translate_formula conseq in
  if List.length sb_ante = 1 && List.length sb_conseq = 1 then
    let sb_ante = List.hd sb_ante in
    let sb_conseq = List.hd sb_conseq in
    SBC.mk_entailment sb_ante sb_conseq
  else report_error no_pos "disjunctive formulas not allowed"

let rec translate_back_formula_x sb_f holes = match sb_f with
  | SBC.FBase (hf, pf, pos) ->
    let rec helper pfs = match pfs with
      | [] -> CP.mkTrue no_pos
      | [h] -> h
      | h::t -> let t_pf = helper t in
        CP.mkAnd h t_pf no_pos in
    let h_hf, pfs, evars = translate_back_hf hf holes in
    let h_pf = translate_back_pf pf in
    let n_pf = match pfs with
      | [] -> h_pf
      | _ -> let n_pf = helper pfs in
        CP.mkAnd h_pf n_pf no_pos in
    let base = CF.mkBase_simp h_hf (Mcpure.mix_of_pure n_pf) in
    CF.add_quantifiers evars base
  | SBC.FExists (vars, f, pos) ->
    let hip_f = translate_back_formula_x f holes in
    let hip_vars = List.map translate_back_var vars in
    CF.add_quantifiers hip_vars hip_f

let translate_back_formula sb_f holes =
  Debug.no_1 "translate_back_formula" SBC.pr_formula pr_formula
    (fun _ -> translate_back_formula_x sb_f holes) sb_f

let rec translate_back_fs (fs: SBC.formula list) holes =
  match fs with
  | [] -> report_error no_pos "songbird.ml cannot be empty list"
  | [h] -> translate_back_formula h holes
  | h::t -> let hip_h = translate_back_formula h holes in
    let hip_t = translate_back_fs t holes in
    CF.mkOr hip_h hip_t no_pos

let create_templ_prog prog ents =
  let program = SBC.mk_program "hip_input" in
  let exp_decl = List.hd (prog.CA.prog_exp_decls) in
  let fun_name = exp_decl.CA.exp_name in
  let args = exp_decl.CA.exp_params |> List.map translate_var in
  let f_defn = SBC.mk_func_defn_unknown fun_name args in
  let ifp_typ = SBG.IfrStrong in
  let infer_func = {SBC.ifp_typ = ifp_typ;
                    SBC.ifp_ents = ents} in
  let nprog = {program with
               SBC.prog_funcs = [f_defn];
               SBC.prog_commands = [SBC.InferFuncs infer_func]} in
  let () = x_tinfo_hp (add_str "nprog: " SBC.pr_program) nprog no_pos in
  let sb_res =
    SBPH.infer_unknown_functions_w_false_rhs ifp_typ nprog
      ents in
  let inferred_prog = if sb_res = [] then nprog
    else snd (List.hd sb_res)
  in
  let () = x_tinfo_hp (add_str "inferred prog: " SBC.pr_program) inferred_prog no_pos in
  inferred_prog.SBC.prog_funcs

let translate_ent ent =
  let (lhs, rhs) = ent in
  let () = x_tinfo_hp (add_str "lhs: " pr_pf) lhs no_pos in
  let () = x_tinfo_hp (add_str "rhs: " pr_pf) rhs no_pos in
  let sb_lhs = translate_pf_wrapper lhs in
  let sb_rhs = translate_pf_wrapper rhs in
  let () = x_tinfo_hp (add_str "lhs: " (SBC.pr_pure_form)) sb_lhs no_pos in
  let () = x_tinfo_hp (add_str "rhs: " (SBC.pr_pure_form)) sb_rhs no_pos in
  SBC.mk_pure_entail sb_lhs sb_rhs


let translate_data_decl (data:CA.data_decl) =
  let ident = data.CA.data_name in
  let loc = data.CA.data_pos in
  let fields = data.CA.data_fields in
  let fields = List.map (fun (x, y) -> x) fields in
  let sb_pos = translate_loc loc in
  let sb_fields = List.map (fun (a,b) -> (translate_type a, b)) fields in
  SBC.mk_data_defn ident sb_fields sb_pos

let translate_view_decl (view:CA.view_decl) =
  let ident = view.CA.view_name in
  let vars = [CP.SpecVar (Named view.CA.view_data_name, "self", VarGen.Unprimed)]
             @ view.CA.view_vars in
  let sb_vars = List.map translate_var vars in
  let formulas = view.CA.view_un_struc_formula in
  let formulas = List.map (fun (x,y) -> x) formulas in
  let invariant = view.CA.view_user_inv |> Mcpure.pure_of_mix in
  let formulas = List.map (CF.add_pure_formula_to_formula invariant) formulas in
  let sb_formula, _ = formulas |> List.map translate_formula |> List.split in
  let sb_formula = List.concat sb_formula in
  let view_defn_cases = List.map SBC.mk_view_defn_case sb_formula in
  SBC.mk_view_defn ident sb_vars (SBC.VbDefnCases view_defn_cases)

let translate_hp hp =
  let ident = hp.CA.hp_name in
  let vars = List.map fst hp.CA.hp_vars_inst in
  let sb_vars = List.map translate_var vars in
  SBC.mk_view_defn ident sb_vars SBC.VbUnknown

let translate_back_vdefns prog (vdefns: SBC.view_defn list) =
  let hps = prog.CA.prog_hp_decls @ !Synthesis.unk_hps
            |> Gen.BList.remove_dups_eq Synthesis.eq_hp_decl in
  let hp_names = hps |> List.map (fun x ->  x.CA.hp_name) in
  let rec helper_f formulas = match formulas with
    | [] -> report_error no_pos "could not be applied"
    | [h] -> h
    | h::t -> CF.mkOr h (helper_f t) no_pos in
  let vdefns = List.filter (fun x ->
      List.exists (fun y -> eq_str x.SBC.view_name y) hp_names) vdefns in
  let helper hps vdefn =
    let hp = List.find (fun x -> x.CA.hp_name = vdefn.SBC.view_name) hps in
    let body = vdefn.SBC.view_body in
    let args = List.map translate_back_var vdefn.SBC.view_params in
    let hip_args = hp.CA.hp_vars_inst |> List.map fst in
    let body = match body with
      | SBC.VbUnknown -> CF.mkBase_simp (CF.HEmp) (MCP.mkMTrue no_pos)
      | SBC.VbDefnCases cases ->
        let formulas = List.map (fun x ->
            translate_back_formula x.SBC.vdc_form []) cases in
        helper_f formulas in
    let () = x_tinfo_hp (add_str "body" pr_formula) body no_pos in
    let body = body |> CF.subst (List.combine args hip_args) in
    {hp with CA.hp_formula = body} in
  vdefns |> List.map (helper hps)

let translate_lemma lemma =
  let status = SBG.LmsValid in
  let origin = SBC.LorgUser in
  let name = lemma.CA.coercion_name in
  let lhs = lemma.CA.coercion_head in
  let rhs = lemma.CA.coercion_body in
  let sb_lhs = translate_single_formula lhs in
  let sb_rhs = translate_single_formula rhs in
  SBC.mk_lemma name sb_lhs sb_rhs status origin

let translate_prog ?(no_unk_views = false) (prog:CA.prog_decl) =
  if !sb_program = None || !enable_repair || !enable_repair_template then
    let lemmas = (Lem_store.all_lemma # get_left_coercion) @
                 (Lem_store.all_lemma # get_right_coercion) in
    let sb_lemmas = List.map translate_lemma lemmas in
    let data_decls = prog.CA.prog_data_decls in
    let prelude = ["__Exc"; "__Error"; "__MayError"; "__Fail"; "char_star";
                   "int_ptr"; "int_ptr_ptr"; "lock"; "barrier"; "thrd"; "__RET";
                   "__ArrBoundErr"; "__DivByZeroErr"; "Object"; "String"] in
    let data_decls = data_decls |> List.filter (fun x ->
        not(Gen.BList.mem_eq eq_str x.CA.data_name prelude)) in
    let pr1 = CPR.string_of_data_decl_list in
    let () = x_tinfo_hp (add_str "data decls" pr1) data_decls no_pos in
    let sb_data_decls = List.map translate_data_decl data_decls in
    let view_decls = prog.CA.prog_view_decls in
    let pre_views = ["WFSegN"; "WFSeg"; "WSSN"; "WSS"; "MEM"; "memLoc"; "size"] in
    let view_decls = view_decls |> List.filter (fun x ->
        not(Gen.BList.mem_eq eq_str x.CA.view_name pre_views)) in
    let pr2 = CPR.string_of_view_decl_list in
    let () = x_tinfo_hp (add_str "view decls" pr2) view_decls no_pos in
    let hps = if no_unk_views then prog.CA.prog_hp_decls
          else prog.CA.prog_hp_decls @ !Synthesis.unk_hps in
    let hps = Gen.BList.remove_dups_eq Synthesis.eq_hp_decl hps in
    let () = x_tinfo_hp (add_str "hp decls" pr_hps) hps no_pos in
    let sb_hp_views = List.map translate_hp hps in
    let sb_view_decls = List.map translate_view_decl view_decls in
    let sb_view_decls = sb_view_decls @ sb_hp_views in
    let prog = SBC.mk_program (List.hd !source_files) in
    let n_prog = {prog with SBC.prog_datas = sb_data_decls;
                            SBC.prog_lemmas = sb_lemmas;
                            SBC.prog_views = sb_view_decls} in
    let pr3 = SBC.pr_program in
    let n_prog = Libsongbird.Transform.normalize_prog ~fast:true n_prog in
    let () = x_tinfo_hp (add_str "prog" pr3) n_prog no_pos in
    let () = sb_program := Some n_prog in
    n_prog
  else Gen.unsome !sb_program

(*********************************************************************
 * export
 *********************************************************************)

let enable_export_entailments () =
  if !songbird_export_all_entails then
    export_songbird_proof := true
  else
    export_songbird_proof := false

let disable_export_entailments () =
  if !songbird_export_all_entails then
    export_songbird_proof := false
  else
    export_songbird_proof := false

let export_songbird_entailments prog ents =
  if !export_songbird_proof then (
    List.iter (fun ent ->
      let _ = index_export_ent := !index_export_ent + 1 in
      let filename = (Filename.remove_extension prog.SBC.prog_filename) ^
                     "_ent_" ^ (string_of_int !index_export_ent) ^ ".sb" in
      let file = open_out filename in
      let cmds = prog.SBC.prog_commands @ [SBC.CheckEntail (ent, SBG.StsNone)] in
      let prog = {prog with SBC.prog_commands = cmds} in
      let _ = Printf.fprintf file "%s\n" (SBE.Songbird.dump_prog prog) in
      let _ = close_out file in
      x_binfo_pp ("Export entailment to file: " ^ filename ^ "\n") no_pos) ents)
  else ()

let export_songbird_entailments_results ?(always=false) prog ents results =
  if !export_songbird_proof || always then (
    List.iter2 (fun ent res ->
      let _ = index_export_ent := !index_export_ent + 1 in
      let filename = (Filename.remove_extension prog.SBC.prog_filename) ^
                     "_ent_" ^ (string_of_int !index_export_ent) ^ ".sb" in
      let file = open_out filename in
      let sts = match res with
        | SBG.MvlTrue -> SBG.StsValid
        | SBG.MvlFalse -> SBG.StsInvalid
        | SBG.MvlUnkn -> SBG.StsUnkn
        | _ -> SBG.StsNone in
      let cmds = prog.SBC.prog_commands @ [SBC.CheckEntail (ent, sts)] in
      let prog = {prog with SBC.prog_commands = cmds} in
      let _ = Printf.fprintf file "%s\n" (SBE.Songbird.dump_prog prog) in
      let _ = close_out file in
      x_binfo_pp ("Export entailment to file: " ^ filename ^ "\n") no_pos
    ) ents results)
  else ()

let export_songbird_satisfiability_results prog fs results =
  if !export_songbird_proof then (
    List.iter2 (fun f res ->
        let _ = index_export_ent := !index_export_ent + 1 in
        let filename = (Filename.remove_extension prog.SBC.prog_filename) ^
                       "_sat_" ^ (string_of_int !index_export_ent) ^ ".sb" in
        let file = open_out filename in
        let sts = match res with
          | SBG.MvlTrue -> SBG.StsInvalid
          | SBG.MvlFalse -> SBG.StsValid
          | _ -> SBG.StsNone in
        let ent = SBC.mk_entailment f (SBC.mk_ffalse SBG.no_pos) in
        let cmds = prog.SBC.prog_commands @ [SBC.CheckEntail (ent, sts)] in
        let prog = {prog with SBC.prog_commands = cmds} in
        let _ = Printf.fprintf file "%s\n" (SBE.Songbird.dump_prog prog) in
        let _ = close_out file in
        x_binfo_pp ("Export formula to file: " ^ filename ^ "\n") no_pos
      ) fs results)
  else ()

(*********************************************************************
 * other
 *********************************************************************)

let solve_entailments prog entails =
  let entails = List.map (fun (x, y) -> (Syn.remove_exists x, y)) entails in
  let pr_ents = pr_list (pr_pair pr_formula pr_formula) in
  x_tinfo_hp (add_str "entailments" pr_ents) entails no_pos;
  let sb_ents = List.map translate_entailment entails in
  let sb_prog = translate_prog prog in
  x_tinfo_hp (add_str "sb_prog" SBC.pr_prog) sb_prog no_pos;
  x_binfo_hp (add_str "sb_ents" SBC.pr_ents) sb_ents no_pos;
  let ptree = SBPU.solve_entailments ~pre:"PP" ~post:"QQ" ~timeout:(Some 3) sb_prog sb_ents in
  let res = SBPFU.get_ptree_validity ptree in
  let () = x_binfo_hp (add_str "sb_res" pr_validity) res no_pos in
  if res = SBG.MvlTrue then
    let vdefns_list = SBPFU.get_solved_vdefns ptree in
    x_tinfo_hp (add_str "vdefns" (pr_list SBC.pr_vdfs)) vdefns_list no_pos;
    let hps_list = List.map (translate_back_vdefns prog) vdefns_list in
    Some hps_list
  else None

let get_vars_in_fault_ents ents =
  let pr_vars = Cprinter.string_of_spec_var_list in
  let sb_ents = List.map translate_ent ents in
  let () = x_tinfo_hp (add_str "entails: " (pr_list SBC.pr_pent)) sb_ents no_pos in
  let sb_vars = List.map SBPH.norm_entail sb_ents |> List.concat in
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
    let ident = exp_decl.CA.exp_name in
    let vars = exp_decl.CA.exp_params in
    try
      let fun_def = List.find (fun fun_def -> String.compare ident fun_def.SBC.func_name == 0)
          fun_defs in
      match fun_def.SBC.func_body with
      | SBC.FbTemplate _
      | SBC.FbUnkn -> None
      | SBC.FbForm exp ->
        let sb_vars = fun_def.SBC.func_params in
        let translated_vars = List.map translate_back_var sb_vars in
        let translated_exp = translate_back_exp exp in
        let substs = List.combine translated_vars vars in
        let n_exp = CP.e_apply_subs substs translated_exp in
        Some n_exp
    with Not_found -> None in
  let fun_def_exp = get_func_exp fun_defs prog.CA.prog_exp_decls in
  match fun_def_exp with
  | Some fun_def_cexp ->
    let pr_exp = Cprinter.poly_string_of_pr Cprinter.pr_formula_exp in
    let () = x_tinfo_hp (add_str "exp: " pr_exp) fun_def_cexp no_pos in
    let exp_decl = List.hd prog.CA.prog_exp_decls in
    let n_exp_decl = {exp_decl with CA.exp_body = fun_def_cexp} in
    let n_prog = {prog with CA.prog_exp_decls = [n_exp_decl]} in
    begin
      match cond_op with
      | Some cond ->
        let neg_cexp = match cond with
          | Iast.OpGt | Iast.OpLte ->
            let n_exp = CP.mkMult_minus_one fun_def_cexp in
            CP.mkAdd n_exp (CP.mkIConst 2 VarGen.no_pos) VarGen.no_pos
          | Iast.OpGte | Iast.OpLt ->
            let n_exp = CP.mkMult_minus_one fun_def_cexp in
            CP.mkSubtract n_exp (CP.mkIConst 1 VarGen.no_pos) VarGen.no_pos
          | _ -> fun_def_cexp in
        let neg_exp_decl = {exp_decl with CA.exp_body = neg_cexp} in
        let neg_prog = {prog with CA.prog_exp_decls = [neg_exp_decl]} in
        Some (n_prog, fun_def_cexp, Some neg_prog, Some neg_cexp)
      | None -> Some (n_prog, fun_def_cexp, None, None)
    end
  | None -> let () = x_tinfo_pp "No expression \n" VarGen.no_pos in
    None

let check_entail_exact_x prog ante conseq =
  let () = Syn.check_entail_num := !Syn.check_entail_num + 1 in
  let sb_prog = translate_prog prog in
  let sb_ante, _ = translate_formula ante in
  let sb_conseq, _ = translate_formula conseq in
  if List.length sb_ante != 1 && List.length sb_conseq != 1 then
    report_error no_pos "more than one constraint in ante/conseq"
  else
    let sb_ante = List.hd sb_ante in
    let sb_conseq = List.hd sb_conseq in
    let ent = SBC.mk_entailment ~mode:SBG.PrfEntail sb_ante sb_conseq in
    let () = x_tinfo_hp (add_str "ENT EXACT: " SBC.pr_ent) ent no_pos in
    let ptree = SBPH.check_entailment ~timeout:5 sb_prog ent in
    let res = ptree.SBPA.enr_validity in
    (* let () = export_songbird_entailments_results sb_prog [ent] [res] in *)
    match res with
    | SBG.MvlTrue -> true
    | _ -> false

let check_entail_exact prog ante conseq =
  Debug.no_2 "SB.check_entail_exact" pr_formula pr_formula string_of_bool
    (fun _ _ -> check_entail_exact_x prog ante conseq) ante conseq

let check_entail_residue_x prog ante conseq =
  let () = Syn.check_entail_num := !Syn.check_entail_num + 1 in
  let sb_prog = translate_prog prog in
  let sb_ante, _ = translate_formula ante in
  let sb_conseq, _ = translate_formula conseq in
  if List.length sb_ante != 1 && List.length sb_conseq != 1 then
    report_error no_pos "more than one constraint in ante/conseq"
  else
    let sb_ante = List.hd sb_ante in
    let sb_conseq = List.hd sb_conseq in
    let ent = SBC.mk_entailment ~mode:SBG.PrfEntailResidue sb_ante sb_conseq in
    let () = x_tinfo_hp (add_str "ENT RESIDUE: " SBC.pr_ent) ent no_pos in
    let ptree = SBPH.check_entailment ~timeout:5 ~interact:false sb_prog ent in
    let res = ptree.SBPA.enr_validity in
    (* let () = export_songbird_entailments_results sb_prog [ent] [res] in *)
    let () = x_tinfo_hp (add_str "sb_ents" pr_validity) res no_pos in
    match res with
    | SBG.MvlTrue ->
      let residue_fs = ptree.SBPA.enr_residues in
      let red = residue_fs |> List.rev |> List.hd in
      let hip_red = translate_back_formula red [] in
      true, Some hip_red
    | _ -> false, None

let check_entail_residue prog ante conseq =
  Debug.no_2 "SB.check_entail_residue" pr_formula pr_formula
    (fun (x, _) -> string_of_bool x)
    (fun _ _ -> check_entail_residue_x prog ante conseq) ante conseq

let output_sb_ent sb_prog sb_ent =
  let file = List.hd !source_files in
  let () = x_tinfo_hp (add_str "source" pr_id) file no_pos in
  let file_name, dir = Filename.basename file, Filename.dirname file in
  let dir = dir ^ "/songbird" in
  let filename = file_name ^ (string_of_int !Synthesis.sb_num) ^ ".sb" in
  let filename = dir ^ Filename.dir_sep ^ filename in
  let oc = open_out filename in
  let str = (SBC.pr_program sb_prog) ^ "\n\n"
            ^ "checkentail[residue]\n"
            ^ (SBC.pr_ent sb_ent) ^ ";" in
  let () = Synthesis.sb_num := !Synthesis.sb_num + 1 in
  Printf.fprintf oc "%s\n" str;
  close_out oc

let check_entail_prog_state prog ?(pf=None) (es:CF.entail_state)
                            (bf:CF.struc_base_formula)  =
  let ante = match pf with
    | None -> es.CF.es_formula
    | Some pf -> CF.add_pure_formula_to_formula pf es.CF.es_formula in
  let n_prog = translate_prog prog in
  let evars = bf.CF.formula_struc_implicit_inst
              @ bf.CF.formula_struc_explicit_inst
              @ bf.CF.formula_struc_exists @ es.CF.es_evars in
  let () = x_tinfo_hp (add_str "exists var" pr_svs) evars no_pos in
  let () = x_tinfo_hp (add_str "es" CPR.string_of_entail_state) es no_pos in
  let () = x_tinfo_hp (add_str "conseq" pr_formula) bf.CF.formula_struc_base no_pos in
  let hps = prog.CA.prog_hp_decls @ !Synthesis.unk_hps in
  let hps = Gen.BList.remove_dups_eq Synthesis.eq_hp_decl hps in
  let hp_names = List.map (fun x -> x.CA.hp_name) hps in
  let conseq_hps = check_hp_formula hp_names bf.CF.formula_struc_base in
  let ante_hps = check_hp_formula hp_names ante in
  if conseq_hps || ante_hps then false, None
  else
    let conseqs, holes = if Gen.is_empty evars
      then translate_formula bf.CF.formula_struc_base
      else
        let sb_f, holes = translate_formula bf.CF.formula_struc_base in
        let pos = translate_loc bf.CF.formula_struc_pos in
        let sb_vars = List.map translate_var evars in
        (List.map (fun x -> SBC.mk_fexists ~pos:pos sb_vars x) sb_f, holes) in
    let holes = List.map CF.disable_imm_h_formula holes in
    let sb_ante, _ = translate_formula ante in
    let sb_conseq = List.hd conseqs in
    let ents = List.map (fun x ->
        SBC.mk_entailment ~mode:SBG.PrfEntailResidue x sb_conseq) sb_ante in
    let check_fun =
      let interact = false in
      SBPH.check_entailment ~interact:interact ~disproof:!disproof n_prog in
    let ptrees = List.map (fun ent -> check_fun ent) ents in
    let results = List.map (fun p -> p.SBPA.enr_validity) ptrees in
    (* let () = export_songbird_entailments_results n_prog ents results in *)
    let is_valid x = x.SBPA.enr_validity = SBG.MvlTrue in
    if List.for_all is_valid ptrees then
      let () = if !disproof then
          valid_num := !valid_num + (List.length ents)
        else () in
      let residues = List.map (fun x -> List.hd x.SBPA.enr_residues) ptrees in
      let () = x_tinfo_hp (add_str "ENTS PROG: " SBC.pr_ents) ents no_pos in
      let residue = translate_back_fs residues holes in
      let () = x_tinfo_hp (add_str "RESIDUE" pr_formula) residue no_pos in
      (true, Some residue)
    else
      let is_valid (x, y) = y.SBPA.enr_validity = SBG.MvlTrue in
      let is_invalid (x, y) = y.SBPA.enr_validity = SBG.MvlFalse in
      let is_unkn (x, y) = y.SBPA.enr_validity = SBG.MvlUnkn in
      let pairs = List.combine ents ptrees in
      let invalid_ents = pairs |> List.filter is_invalid |> List.map fst in
      let unkn_ents = pairs |> List.filter is_unkn |> List.map fst in
      let valid_ents = pairs |> List.filter is_valid |> List.map fst in
      let () = if invalid_ents != [] then
          List.iter (fun ent ->
              let _ = x_tinfo_hp (add_str "Invalid Ent: " SBC.pr_ent) ent no_pos in
              (* let _ = SBPH.check_entailment ~interact:true n_prog ent in *)
              ()) invalid_ents in
      let () = if unkn_ents != [] then
          List.iter (fun ent ->
              let _ = x_tinfo_hp (add_str "Unkn Ent: " SBC.pr_ent) ent no_pos in
              (* let _ = SBPH.check_entailment ~interact:true n_prog ent in *)
              ()) unkn_ents in
      let () = if !songbird_export_invalid_entails then
          let _ = List.map (output_sb_ent n_prog) invalid_ents in
          let _ = List.map (output_sb_ent n_prog) unkn_ents in
          () else () in
      let () = if !disproof then
          let () = invalid_num := !invalid_num + (List.length invalid_ents) in
          let () = unkn_num := !unkn_num + (List.length unkn_ents) in
          valid_num := !valid_num + (List.length valid_ents)
        else () in
      false, None

let check_equal prog first second =
  let forward = check_entail_exact prog first second in
  let backward = check_entail_exact prog second first in
  forward && backward

let eq_h_formula prog (f1:CF.formula) (f2:CF.formula) =
  let get_h_formula (f:CF.formula) = match f with
    | CF.Base bf -> bf.CF.formula_base_heap
    | CF.Exists bf -> bf.CF.formula_exists_heap
    | CF.Or _ -> report_error no_pos "get_h_formula: unhandled" in
  let h1, h2 = get_h_formula f1, get_h_formula f2 in
  let n_f1 = CF.mkBase_simp h1 (MCP.mix_of_pure (CP.mkTrue no_pos)) in
  let n_f2 = CF.mkBase_simp h2 (MCP.mix_of_pure (CP.mkTrue no_pos)) in
  let res1 = check_entail_exact prog n_f1 n_f2 in
  let res2 = check_entail_exact prog n_f2 n_f1 in
  res1 && res2

let check_sat_x prog (f:CF.formula) =
  let sb_prog = translate_prog ~no_unk_views:true prog in
  let sb_f,_ = translate_formula f in
  if List.length sb_f != 1 then report_error no_pos "SB.check_sat invalid input"
  else
    let sb_formula = List.hd sb_f in
    let sb_res = SBPH.check_sat sb_prog sb_formula in
    match sb_res with
    | SBG.MvlTrue -> true
    | _ -> false

let check_sat prog (formula:CF.formula) =
  Debug.no_1 "SB.check_sat" pr_formula string_of_bool
    (fun _ -> check_sat_x prog formula) formula

(* let check_sat_pf prog (pf : CP.formula) = *)

let check_unsat_x prog (f:CF.formula) =
  let sb_prog = translate_prog ~no_unk_views:true prog in
  let sb_f,_ = translate_formula f in
  if List.length sb_f != 1 then report_error no_pos "SB.check_sat invalid input"
  else
    let sb_formula = List.hd sb_f in
    x_tinfo_hp (add_str "prog" SBC.pr_program) sb_prog no_pos;
    x_tinfo_hp (add_str "ent" SBC.pr_formula) sb_formula no_pos;
    let sb_res = SBPH.check_sat sb_prog sb_formula in
    match sb_res with
    | SBG.MvlFalse -> true
    | _ -> false

let check_unsat prog (formula:CF.formula) =
  Debug.no_1 "SB.check_unsat" pr_formula string_of_bool
    (fun _ -> check_unsat_x prog formula) formula

let check_pure_entail_x ante conseq =
  let sb_ante = translate_pf ante in
  let sb_conseq = translate_pf conseq in
  let sb_ante_f = SBC.mk_fpure sb_ante in
  let sb_conseq_f = SBC.mk_fpure sb_conseq in
  let sb_prog = SBC.mk_program "check_pure_entail" in
  let ent = SBC.mk_entailment sb_ante_f sb_conseq_f in
  let ptree = SBPH.check_entailment ~timeout:5 sb_prog ent in
  let res = ptree.SBPA.enr_validity in
    match res with
    | SBG.MvlTrue -> true
    | _ -> false

let check_pure_entail ante conseq =
  Debug.no_2 "check_pure_entail" pr_pf pr_pf string_of_bool
    (fun _ _ -> check_pure_entail_x ante conseq) ante conseq

let infer_templ_defn prog pre post fun_name args =
  let sb_prog = translate_prog prog in
  let sb_args = List.map translate_var args in
  let f_defn = SBC.mk_func_defn_unknown fun_name sb_args in
  let ifp_typ = SBG.IfrStrong in
  let sb_pre, sb_post = translate_pf pre, translate_pf post in
  let ent = SBC.mk_pure_entail sb_pre sb_post in
  let infer_func = {SBC.ifp_typ = ifp_typ;
                    SBC.ifp_ents = [ent]} in
  let nprog = {sb_prog with
               SBC.prog_funcs = [f_defn];
               SBC.prog_commands = [SBC.InferFuncs infer_func]} in
  let () = x_tinfo_hp (add_str "ent" SBC.pr_pure_entail) ent no_pos in
  let sb_res = SBPP.infer_unknown_functions ifp_typ nprog ent in
  let ifds = fst sb_res in
  let () = x_tinfo_hp (add_str "re" (SBPP.pr_ifds)) ifds no_pos in
  let func_defns = ifds |> List.map (fun x -> x.SBPP.ifd_fdefns)
                   |> List.concat in
  try
    let func_defn = func_defns
                    |> List.find (fun x -> x.SBC.func_name = tmpl_name) in
    let fdefn_body = match func_defn.SBC.func_body with
      | SBC.FbForm e ->
        let hip_exp = translate_back_exp e in
        let () = x_tinfo_hp (add_str "hip_exp" Cprinter.string_of_formula_exp) hip_exp no_pos in
        Some hip_exp
      | _ -> None in
    fdefn_body
  with _ -> None

let contains_hps_x prog ctx (conseq:CF.struc_formula) =
  let hps = prog.CA.prog_hp_decls @ !Synthesis.unk_hps in
  let hps = Gen.BList.remove_dups_eq Synthesis.eq_hp_decl hps in
  let hp_names = List.map (fun x -> x.CA.hp_name) hps in
  let () = x_tinfo_hp (add_str "hps" (pr_list pr_id)) hp_names no_pos in
  let rec check_conseq_hps (conseq:CF.struc_formula) =
    match conseq with
    | CF.EBase bf -> check_hp_formula hp_names bf.CF.formula_struc_base
    | CF.ECase cases ->
      let branches = cases.CF.formula_case_branches |> List.map snd in
      List.exists check_conseq_hps branches
    | CF.EList b ->
      let _, struc_list = List.split b in
      List.exists check_conseq_hps struc_list
    | CF.EAssume assume ->
      let assume_f = assume.CF.formula_assume_simpl in
      check_hp_formula hp_names assume_f
    | _ -> false in
  let rec check_ante_hps (ante:CF.context) =
    match ante with
    | CF.Ctx es -> check_hp_formula hp_names es.CF.es_formula
    | CF.OCtx (c1, c2) ->
      (check_ante_hps c1) && (check_ante_hps c2) in
  (check_conseq_hps conseq) || (check_ante_hps ctx)

let contains_hps prog ctx (conseq:CF.struc_formula) =
  Debug.no_2 "contains_hps" Cprinter.string_of_context
    Cprinter.string_of_struc_formula string_of_bool
    (fun _ _ -> contains_hps_x prog ctx conseq) ctx conseq

let get_residues ptrees =
  List.map (fun ptree ->
    let residue_fs = SBPFE.get_ptree_residues ptree in
    let pr_rsd = SBC.pr_fs in
    let () = x_tinfo_hp (add_str "residues" pr_rsd) residue_fs no_pos in
    residue_fs |> List.rev |> List.hd
  ) ptrees

let rec heap_entail_after_sat_struc_x ?(pf=None) (prog:CA.prog_decl)
    (ctx:CF.context) (conseq:CF.struc_formula) =
  let () = x_tinfo_hp (add_str "ctx" CPR.string_of_context) ctx no_pos in
  let () = x_tinfo_hp (add_str "conseq" pr_struc_f) conseq no_pos in
  match ctx with
  | CF.Ctx es ->
    (
      match conseq with
      | CF.EBase bf -> hentail_after_sat_ebase ~pf:pf prog ctx es bf
      | CF.ECase cases ->
        let branches = cases.CF.formula_case_branches in
        let results = List.map (fun (pf, struc) ->
            heap_entail_after_sat_struc ~pf:(Some pf) prog ctx struc) branches in
        let rez1, _ = List.split results in
        let rez1 = List.fold_left (fun a c -> CF.or_list_context a c)
            (List.hd rez1) (List.tl rez1) in
        (rez1, Prooftracer.TrueConseq)
      | CF.EList b ->
        let _, struc_list = List.split b in
        let res_list =
          List.map (fun x -> heap_entail_after_sat_struc ~pf:pf prog ctx x)
            struc_list in
        let ctx_lists = res_list |> List.split |> fst in
        let res = CF.fold_context_left 41 ctx_lists in
        (res, Prooftracer.TrueConseq)
      | CF.EAssume assume ->
        let assume_f = assume.CF.formula_assume_simpl in
        let assume_f = CF.rename_bound_vars assume_f in
        let f = es.CF.es_formula in
        let assume_f =
          let hps = prog.CA.prog_hp_decls @ !Synthesis.unk_hps in
          let hps = Gen.BList.remove_dups_eq Synthesis.eq_hp_decl hps in
          let hp_names = List.map (fun x -> x.CA.hp_name) hps in
          let has_pred = check_hp_formula hp_names assume_f in
          if has_pred then
            let syn_pre_vars = !Syn.syn_pre |> Gen.unsome |> CF.fv in
            let n_args = (f |> CF.fv) @ syn_pre_vars in
            let n_args = if !Syn.is_return_cand then
                n_args @ (!Syn.syn_res_vars)
              else n_args in
            let n_args = n_args |> List.filter
                           (fun x -> Syn.is_int_var x || Syn.is_node_var x)
                         |> CP.remove_dups_svl in
            let var_decls = !Syn.block_var_decls
                      |> List.filter (fun x -> not(CP.mem_svl x n_args))
                      |> List.map CP.to_primed in
            let n_args = n_args @ var_decls |> CP.remove_dups_svl in
            let n_pred_f = Syn.create_spec_pred n_args "QQ" in
            n_pred_f
          else assume_f in
        let new_f = CF.mkStar_combine f assume_f CF.Flow_combine no_pos in
        let () = x_tinfo_hp (add_str "new_f" CPR.string_of_formula) new_f no_pos in
        let n_ctx = CF.Ctx {es with CF.es_formula = new_f} in
        (CF.SuccCtx [n_ctx], Prooftracer.TrueConseq)
      | _ -> report_error no_pos ("unhandle " ^ (pr_struc_f conseq))
    )
  | CF.OCtx (c1, c2) ->
    let rs1, proof1 = heap_entail_after_sat_struc ~pf:pf prog c1 conseq in
    let rs2, proof2 = heap_entail_after_sat_struc ~pf:pf prog c2 conseq in
    (CF.or_list_context rs1 rs2, Prooftracer.TrueConseq)

and hentail_after_sat_ebase ?(pf=None) prog ctx es bf =
  let conti = bf.CF.formula_struc_continuation in
  let ent_res, residue = check_entail_prog_state prog es bf ~pf:pf in
  let aux_conti n_ctx = match conti with
    | None -> (CF.SuccCtx [n_ctx], Prooftracer.TrueConseq)
    | Some struc -> heap_entail_after_sat_struc ~pf:pf prog n_ctx struc in
  if ent_res then
    let residue = Gen.unsome residue in
    let () = x_tinfo_hp (add_str "residue" pr_formula) residue no_pos in
    let () = pre_list := [es.CF.es_formula] @ !pre_list in
    let n_ctx = CF.Ctx {es with CF.es_evars = CF.get_exists es.CF.es_formula;
                                CF.es_formula = residue} in
    aux_conti n_ctx
  else
    let hps = prog.CA.prog_hp_decls @ !Synthesis.unk_hps in
    let hps = Gen.BList.remove_dups_eq Synthesis.eq_hp_decl hps in
    let hp_names = List.map (fun x -> x.CA.hp_name) hps in
    let conseq_hps = check_hp_formula hp_names bf.CF.formula_struc_base in
    let ante_hps = check_hp_formula hp_names es.CF.es_formula in
    if conseq_hps then
      let ante = es.CF.es_formula in
      let () = Syn.syn_pre := Some ante in
      let ante_vars = ante |> CF.fv |> List.filter
                        (fun x -> Syn.is_int_var x || Syn.is_node_var x) in
      let var_decls = !Syn.block_var_decls
                      |> List.filter (fun x -> not(CP.mem_svl x ante_vars))
                      |> List.map CP.to_primed in
      let ante_vars = ante_vars @ var_decls |> CP.remove_dups_svl in
      let n_conseq = Syn.create_spec_pred ante_vars "PP" in
      let pure_ante = CF.mkEmp_formula ante in
      (* let n_conseq, residue =
       *   let n_conseq = Syn.add_formula_to_formula pure_ante n_conseq in
       *   n_conseq, pure_ante in *)
      let n_conseq, residue =
        let residue = Syn.create_pred ante_vars in
        x_tinfo_hp (add_str "ante vars" pr_vars) ante_vars no_pos;
        let residue = Syn.add_formula_to_formula residue pure_ante in
        let conseq = Syn.add_formula_to_formula residue n_conseq in
        (conseq, residue) in
      let () = Syn.entailments := [(ante, n_conseq)] @ !Syn.entailments in
      let n_ctx = CF.Ctx {es with CF.es_formula = residue} in
      aux_conti n_ctx
    else if Syn.is_emp_conseq bf.CF.formula_struc_base then
      aux_conti ctx
    else if ante_hps then
      let ante = es.CF.es_formula |> Syn.remove_exists in
      let vars = ante |> CF.fv |> CP.remove_dups_svl in
      let exists_vars = bf.CF.formula_struc_exists
                        @ bf.CF.formula_struc_explicit_inst
                        @ bf.CF.formula_struc_implicit_inst
                        |> CP.remove_dups_svl in
      let filter_var x = Syn.is_int_var x || Syn.is_node_var x in
      let vars = vars @ exists_vars |> List.filter filter_var in
      let conseq = bf.CF.formula_struc_base in
      x_tinfo_hp (add_str "conseq" pr_formula) conseq no_pos;
      let conseq = Syn.add_exists_vars conseq exists_vars in
      let n_es, n_conseq = Syn.create_residue vars prog conseq in
      let pure_ante = ante |> CF.get_pure in
      let n_conseq = CF.add_pure_formula_to_formula pure_ante n_conseq in
      let n_es = CF.add_pure_formula_to_formula pure_ante n_es in
      let () = Syn.entailments := [(ante, n_conseq)] @ !Syn.entailments in
      let () = x_tinfo_hp (add_str "n_es" pr_formula) n_es no_pos in
      let n_ctx = CF.Ctx {es with CF.es_formula = n_es;} in
      aux_conti n_ctx
    else
      let () = if !start_repair then
          repair_loc := Some VarGen.proving_loc#get in
      let () = x_tinfo_hp (add_str "es_f" pr_formula) es.CF.es_formula no_pos in
      let () = x_tinfo_hp (add_str "conseq" pr_formula) bf.CF.formula_struc_base no_pos in
      let msg = "songbird result is Failed." in
      (CF.mkFailCtx_simple msg es bf.CF.formula_struc_base (CF.mk_cex true) no_pos
      , Prooftracer.Failure)

and heap_entail_after_sat_struc ?(pf=None) prog ctx conseq =
  let () = x_tinfo_pp "SONGBIRD Prover activated" no_pos in
  Debug.no_2 "SB.heap_entail_after_sat_struc" Cprinter.string_of_context
  Cprinter.string_of_struc_formula
  (fun (lctx, _) -> Cprinter.string_of_list_context lctx)
  (fun _ _ -> heap_entail_after_sat_struc_x ~pf:pf prog ctx conseq) ctx conseq

