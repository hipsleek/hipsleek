#include "xdebug.cppo"
open Globals
open Gen.Basic

module SBCast = Libsongbird.Cast
module SBGlobals = Libsongbird.Globals
module SBProverP = Libsongbird.Prover_pure
module SBProverE = Libsongbird.Prover_entail
module SBDebug = Libsongbird.Debug
module SBPFE = Libsongbird.Proof_entail
module SBPFU = Libsongbird.Proof_unkentail
module SBPU = Libsongbird.Prover_unkentail
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
let pr_entail = SBCast.pr_entailment
let pre_list = ref ([] : CF.formula list)
let pr_ents = pr_list (pr_pair pr_pf pr_pf)
(*********************************************************************
 * Translate Formulas
 *********************************************************************)
let pr_validity tvl = match tvl with
  | SBGlobals.MvlFalse -> "Invalid"
  | SBGlobals.MvlTrue -> "Valid"
  | SBGlobals.MvlUnkn -> "Unknown"
  | SBGlobals.MvlInfer -> "Infer"

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
  let pr_exp = Cprinter.string_of_formula_exp in
  Debug.no_1 "check_hp_hf" pr_hf string_of_bool
    (fun _ -> check_hp_hf_x hp_names hf) hf

let rec check_hp_formula_x hp_names formula = match (formula:CF.formula) with
  | CF.Base bf -> check_hp_hf hp_names bf.CF.formula_base_heap
  | CF.Exists ef -> check_hp_hf hp_names ef.CF.formula_exists_heap
  | CF.Or f -> (check_hp_formula_x hp_names f.CF.formula_or_f1) ||
               (check_hp_formula_x hp_names f.CF.formula_or_f2)

let check_hp_formula hp_names formula =
  let pr_exp = Cprinter.string_of_formula_exp in
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


let translate_loc (location:VarGen.loc) : SBGlobals.pos =
  {
    SBGlobals.pos_begin = location.VarGen.start_pos;
    SBGlobals.pos_end = location.VarGen.end_pos;}

let translate_back_pos (pos:SBGlobals.pos) : VarGen.loc =
  let no_pos1 = { Lexing.pos_fname = "";
                  Lexing.pos_lnum = 0;
                  Lexing.pos_bol = 0;
                  Lexing.pos_cnum = 0 } in
  { VarGen.start_pos = pos.SBGlobals.pos_begin;
    VarGen.mid_pos = no_pos1;
    VarGen.end_pos = pos.SBGlobals.pos_end;}

let translate_type (typ: Globals.typ) : SBGlobals.typ =
  match typ with
  | NUM
  | Int -> SBGlobals.TInt
  | TVar num -> SBGlobals.TVar num
  | Bool -> SBGlobals.TBool
  | UNK -> SBGlobals.TUnk
  | Void -> SBGlobals.TVoid
  | Named str -> SBGlobals.TData str
  | _ -> report_error no_pos
           ("translate_type:" ^ (Globals.string_of_typ typ) ^ " is not handled")

let translate_back_type typ = match typ with
  | SBGlobals.TInt -> Globals.Int
  | SBGlobals.TBool -> Globals.Bool
  | SBGlobals.TUnk -> Globals.UNK
  | SBGlobals.TVoid -> Globals.Void
  | SBGlobals.TData str -> Globals.Named str
  | SBGlobals.TNull -> Globals.Named "null"
  | _ -> report_error no_pos ("translate_back_type:"
         ^ (SBGlobals.pr_typ typ) ^ " is not handled")


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
        SBCast.BinExp (SBCast.Add, t_exp1, t_exp2, translate_loc loc)
  | CP.Subtract (exp1, exp2, loc) ->
        let t_exp1 = translate_exp exp1 in
        let t_exp2 = translate_exp exp2 in
        SBCast.BinExp (SBCast.Sub, t_exp1, t_exp2, translate_loc loc)
  | CP.Mult (exp1, exp2, loc) ->
        let t_exp1 = translate_exp exp1 in
        let t_exp2 = translate_exp exp2 in
        SBCast.BinExp (SBCast.Mul, t_exp1, t_exp2, translate_loc loc)
  | CP.Div (exp1, exp2, loc) ->
        let t_exp1 = translate_exp exp1 in
        let t_exp2 = translate_exp exp2 in
        SBCast.BinExp (SBCast.Div, t_exp1, t_exp2, translate_loc loc)
  | CP.Template templ ->
    if (!Globals.translate_funcs) then
      let fun_name = CP.name_of_sv templ.CP.templ_id in
      let args = templ.CP.templ_args |> List.map translate_exp in
      SBCast.mk_func (SBCast.FuncName fun_name) args
    else report_error no_pos "translate_funcs not activated"
  | _ -> report_error no_pos ("this exp is not handled"
                              ^ (Cprinter.string_of_formula_exp exp))

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
      match (p_formula:CP.p_formula) with
      | CP.BVar (var, loc) ->
        SBCast.BVar (translate_var var, translate_loc loc)
      | CP.BConst (b, loc) ->
        SBCast.BConst (b, translate_loc loc)
      | CP.Eq (exp1, exp2, loc) ->
        let sb_exp1 = translate_exp exp1 in
        let sb_exp2 = translate_exp exp2 in
        let sb_loc = translate_loc loc in
        SBCast.BinRel (SBCast.Eq, sb_exp1, sb_exp2, sb_loc)
      | CP.Neq (exp1, exp2, loc) ->
        let sb_exp1 = translate_exp exp1 in
        let sb_exp2 = translate_exp exp2 in
        let sb_loc = translate_loc loc in
        SBCast.BinRel (SBCast.Ne, sb_exp1, sb_exp2, sb_loc)
      | CP.Gt (exp1, exp2, loc) ->
        let sb_exp1 = translate_exp exp1 in
        let sb_exp2 = translate_exp exp2 in
        let sb_loc = translate_loc loc in
        SBCast.BinRel (SBCast.Gt, sb_exp1, sb_exp2, sb_loc)
      | CP.Gte (exp1, exp2, loc) ->
        let sb_exp1 = translate_exp exp1 in
        let sb_exp2 = translate_exp exp2 in
        let sb_loc = translate_loc loc in
        SBCast.BinRel (SBCast.Ge, sb_exp1, sb_exp2, sb_loc)
      | CP.Lt (exp1, exp2, loc) ->
        let sb_exp1 = translate_exp exp1 in
        let sb_exp2 = translate_exp exp2 in
        let sb_loc = translate_loc loc in
        SBCast.BinRel (SBCast.Lt, sb_exp1, sb_exp2, sb_loc)
      | CP.Lte (exp1, exp2, loc) ->
        let sb_exp1 = translate_exp exp1 in
        let sb_exp2 = translate_exp exp2 in
        let sb_loc = translate_loc loc in
        SBCast.BinRel (SBCast.Le, sb_exp1, sb_exp2, sb_loc)
      | CP.LexVar lex ->
        SBCast.BConst (true, translate_loc lex.lex_loc)
      | _ -> report_error no_pos
               ("this p_formula is not handled" ^ (CPR.string_of_p_formula p_formula))
    end
  | CP.And (f1, f2, loc) ->
    let n_f1 = translate_pf f1 in
    let n_f2 = translate_pf f2 in
    SBCast.PConj ([n_f1; n_f2], translate_loc loc)
  | CP.Or (f1, f2, _, loc) ->
    let n_f1 = translate_pf f1 in
    let n_f2 = translate_pf f2 in
    SBCast.PDisj ([n_f1; n_f2], translate_loc loc)
  | CP.Not (f, _, loc) ->
    let n_f = translate_pf f in
    SBCast.PNeg (n_f, translate_loc loc)
  | CP.Exists (sv, pf, _, loc) ->
    let sb_var = translate_var sv in
    let sb_pf = translate_pf pf in
    let sb_loc = translate_loc loc in
    SBCast.mk_pexists ~pos:sb_loc [sb_var] sb_pf
  | _ -> report_error no_pos
      ("this pure formula not handled" ^ (CPR.string_of_pure_formula pure_f))

let rec translate_back_pf (pf : SBCast.pure_form) = match pf with
  | SBCast.BConst (b, pos)
    -> CP.BForm ((CP.BConst (b, translate_back_pos pos), None), None)
  | SBCast.BVar (var, pos) -> let hip_var = translate_back_var var in
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
  | CF.HTrue | CF.HEmp -> (SBCast.HEmp (translate_loc no_pos), [], [])
  | CF.DataNode dnode -> let ann = dnode.CF.h_formula_data_imm in
    let holes = match ann with
      | CP.ConstAnn Lend -> [hf]
      | _ -> [] in
    let root = dnode.CF.h_formula_data_node in
    let sb_root_var = translate_var root in
    let sb_no_pos = translate_loc no_pos in
    let sb_root = SBCast.Var (sb_root_var, sb_no_pos) in
    let name, args = dnode.CF.h_formula_data_name, dnode.CF.h_formula_data_arguments in
    let sb_arg_vars = List.map translate_var args in
    let sb_args = List.map (fun x -> SBCast.Var (x, sb_no_pos)) sb_arg_vars in
    let data_form = SBCast.mk_data_form sb_root name sb_args in
    (SBCast.mk_hform_df data_form, [], holes)
  | CF.Star star_hf ->
    let hf1, hf2 = star_hf.h_formula_star_h1, star_hf.h_formula_star_h2 in
    let pos = star_hf.h_formula_star_pos |> translate_loc in
    let (sb_hf1, sb_pf1, hole1) = translate_hf hf1 in
    let (sb_hf2, sb_pf2, hole2) = translate_hf hf2 in
    (SBCast.mk_hstar ~pos:pos sb_hf1 sb_hf2, sb_pf1@sb_pf2, hole1@hole2)
  | CF.ViewNode view ->  let ann = view.CF.h_formula_view_imm in
    let holes = match ann with
      | CP.ConstAnn Lend -> [hf]
      | _ -> [] in
    let root, name = view.h_formula_view_node, view.h_formula_view_name in
    let args = view.h_formula_view_arguments in
    let () = x_tinfo_hp (add_str "root: " CP.string_of_spec_var) root no_pos in
    let () = x_tinfo_hp (add_str "args: " (pr_list CP.string_of_spec_var)) args no_pos in
    let args = [root] @ args in
    let sb_vars = List.map translate_var args in
    let sb_exps = List.map SBCast.mk_exp_var sb_vars in
    let pos = view.h_formula_view_pos |> translate_loc in
    let view_form = SBCast.mk_view_form ~pos:pos name sb_exps in
    (SBCast.mk_hform_vf view_form, [], holes)
  | CF.HFalse -> let sb_no_pos = translate_loc no_pos in
    let sb_false = SBCast.mk_false sb_no_pos in
    (SBCast.HEmp sb_no_pos, [sb_false], [])
  | CF.HRel (sv, exps, loc) -> let sb_pos = translate_loc loc in
    let sb_args = List.map translate_exp exps in
    let name = CP.name_of_sv sv in
    let view_form = SBCast.mk_view_form ~pos:sb_pos name sb_args in
    (SBCast.mk_hform_vf view_form, [], [])
  | _ -> report_error no_pos ("this hf is not supported: "
                              ^ (Cprinter.string_of_h_formula hf))

let exp_to_var exp = match exp with
  | CP.Var (sv, _) -> (sv, [], [])
  | CP.Add _ | CP.Subtract _ | CP.Mult _ | CP.Div _ ->
    let name = fresh_name() in
    let var = CP.mk_typed_sv Int name in
    let var_exp = CP.mkVar var no_pos in
    let pf = CP.mkEqExp var_exp exp no_pos in
    (var, [pf], [var])
  | _ -> report_error no_pos ("exp_to_var:" ^ CPR.string_of_formula_exp exp)

let translate_back_df df =
  match df.SBCast.dataf_root with
  | SBCast.Null _ -> (CF.HEmp, [], [])
  | _ ->
    let h_root, pf1, e_var = translate_back_exp df.SBCast.dataf_root |> exp_to_var in
    let triples = List.map translate_back_exp df.SBCast.dataf_args
                  |> List.map exp_to_var in
    let h_args = triples |> List.map (fun (x,_,_) -> x) in
    let pf2 = triples |> List.map (fun (_, x,_) -> x) |> List.concat in
    let e_var2 = triples |> List.map (fun (_,_, x) -> x) |> List.concat in
    let h_name = df.SBCast.dataf_name in
    let loc = translate_back_pos df.SBCast.dataf_pos in
    (CF.mkDataNode h_root h_name h_args loc, pf1 @ pf2, e_var@e_var2)

let translate_back_vf vf =
  let hp_name = vf.SBCast.viewf_name in
  let hp_names = !Synthesis.unk_hps |> List.map (fun x -> x.Cast.hp_name) in
  if List.mem hp_name hp_names then
    let hp_name = CP.mk_spec_var hp_name in
    let hp_args = List.map translate_back_exp vf.SBCast.viewf_args in
    let loc = translate_back_pos vf.SBCast.viewf_pos in
    (CF.HRel (hp_name, hp_args, loc), [], [])
  else
    let vargs = vf.SBCast.viewf_args in
    if List.exists (fun x -> match x with SBCast.Null _ -> true
                                        | _ -> false) vargs
    then (CF.HEmp, [], [])
    else let h_triples = List.map translate_back_exp vargs
                         |> List.map exp_to_var in
      let h_all_args = h_triples |> List.map (fun (x,_,_) -> x) in
      let e_vars = h_triples |> List.map (fun (_,_,x) -> x) |> List.concat in
      let pfs = h_triples |> List.map (fun (_,x,_) -> x) |> List.concat in
      let h_root, h_args = List.hd h_all_args, List.tl h_all_args in
      let loc = translate_back_pos vf.SBCast.viewf_pos in
      (CF.mkViewNode h_root hp_name h_args loc, pfs, e_vars)

let rec mkStarHList list = match list with
  | [] -> CF.HEmp    | [h] -> h
  | h::t -> let tail = mkStarHList t in
    CF.mkStarH h tail no_pos

let translate_back_hf sb_hf holes =
  let rec helper sb_hf =
    match sb_hf with
    | SBCast.HEmp _ -> (CF.HEmp, [], [])
    | SBCast.HAtom (dfs, vfs, pos) ->
      let df_triples = List.map translate_back_df dfs in
      let h_dfs = List.map (fun (x,_,_) -> x) df_triples in
      let df_pf = df_triples |> List.map (fun (_,x,_) -> x) |> List.concat in
      let df_evars = df_triples |> List.map (fun (_,_,x) -> x) |> List.concat in
      let vf_triples = List.map translate_back_vf vfs in
      let h_vfs = vf_triples |> List.map (fun (x,_,_) -> x) in
      let vf_pf = vf_triples |> List.map (fun (_,x,_) -> x) |> List.concat in
      let vf_evars = vf_triples |> List.map (fun (_,_,x) -> x) |> List.concat in
      let h_formulas = h_dfs @ h_vfs in
      (mkStarHList h_formulas, df_pf @ vf_pf, df_evars@vf_evars)
    | SBCast.HStar (hf1, hf2, pos) ->
      let h_hf1, pf1, evars1 = helper hf1 in
      let h_hf2, pf2, evars2 = helper hf2 in
      let loc = translate_back_pos pos in
      (CF.mkStarH h_hf1 h_hf2 loc, pf1@pf2, evars1@evars2) in
  let h_hf, pf, evars = helper sb_hf in
  (mkStarHList ([h_hf]@holes), pf, evars)

let rec translate_formula formula =
  let () = x_tinfo_hp (add_str "formula" pr_formula) formula no_pos in
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

let translate_entailment entailment =
  let ante, conseq = fst entailment, snd entailment in
  let sb_ante, _ = translate_formula ante in
  let sb_conseq, _ = translate_formula conseq in
  if List.length sb_ante = 1 && List.length sb_conseq = 1 then
    let sb_ante = List.hd sb_ante in
    let sb_conseq = List.hd sb_conseq in
    SBCast.mk_entailment sb_ante sb_conseq
  else report_error no_pos "disjunctive formulas not allowed"

let rec translate_back_formula_x sb_f holes = match sb_f with
  | SBCast.FBase (hf, pf, pos) ->
    let rec helper pfs = match pfs with
      | [] -> CP.mkTrue no_pos
      | [h] -> h
      | h::t -> let t_pf = helper t in
        CP.mkAnd h t_pf no_pos in
    let h_hf, pfs, evars = translate_back_hf hf holes in
    let loc = translate_back_pos pos in
    let h_pf = translate_back_pf pf in
    let n_pf = match pfs with
      | [] -> h_pf
      | _ -> let n_pf = helper pfs in
        CP.mkAnd h_pf n_pf no_pos in
    let base = CF.mkBase_simp h_hf (Mcpure.mix_of_pure n_pf) in
    CF.add_quantifiers evars base
  | SBCast.FExists (vars, f, pos) ->
    let loc = translate_back_pos pos in
    let hip_f = translate_back_formula_x f holes in
    let hip_vars = List.map translate_back_var vars in
    CF.add_quantifiers hip_vars hip_f
  | _ -> report_error no_pos "un-handled case in translate_back_formula"

let translate_back_formula sb_f holes =
  Debug.no_1 "translate_back_formula" SBCast.pr_formula pr_formula
    (fun _ -> translate_back_formula_x sb_f holes) sb_f

let rec translate_back_fs (fs: SBCast.formula list) holes =
  match fs with
  | [] -> report_error no_pos "songbird.ml cannot be empty list"
  | [h] -> translate_back_formula h holes
  | h::t -> let hip_h = translate_back_formula h holes in
    let hip_t = translate_back_fs t holes in
    CF.mkOr hip_h hip_t no_pos

let create_templ_prog prog ents =
  let program = SBCast.mk_program "hip_input" in
  let exp_decl = List.hd (prog.Cast.prog_exp_decls) in
  let fun_name = exp_decl.Cast.exp_name in
  let args = exp_decl.Cast.exp_params |> List.map translate_var in
  let f_defn = SBCast.mk_func_defn_unknown fun_name args in
  let ifp_typ = SBGlobals.IfrStrong in
  let infer_func = {SBCast.ifp_typ = ifp_typ;
                    SBCast.ifp_ents = ents} in
  let nprog = {program with
               prog_funcs = [f_defn];
               prog_commands = [SBCast.InferFuncs infer_func]} in
  let () = x_tinfo_hp (add_str "nprog: " SBCast.pr_program) nprog no_pos in
  let sb_res =
    SBProverP.infer_unknown_functions_with_false_rhs ifp_typ nprog
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
  let vars = [Cpure.SpecVar (Named view.view_data_name, "self", VarGen.Unprimed)]
             @ view.Cast.view_vars in
  let sb_vars = List.map translate_var vars in
  let formulas = view.Cast.view_un_struc_formula in
  let formulas = List.map (fun (x,y) -> x) formulas in
  let sb_formula, _ = formulas |> List.map translate_formula |> List.split in
  let sb_formula = List.concat sb_formula in
  let view_defn_cases = List.map SBCast.mk_view_defn_case sb_formula in
  SBCast.mk_view_defn ident sb_vars (SBCast.VbDefnCases view_defn_cases)

let translate_hp hp =
  let ident = hp.Cast.hp_name in
  let vars = List.map fst hp.Cast.hp_vars_inst in
  let sb_vars = List.map translate_var vars in
  SBCast.mk_view_defn ident sb_vars SBCast.VbUnknown

let translate_back_vdefns prog (vdefns: SBCast.view_defn list) =
  let hps = prog.Cast.prog_hp_decls @ !Synthesis.unk_hps
            |> Gen.BList.remove_dups_eq Synthesis.eq_hp_decl in
  let hp_names = hps |> List.map (fun x ->  x.Cast.hp_name) in
  let rec helper_f formulas = match formulas with
    | [] -> report_error no_pos "could not be applied"
    | [h] -> h
    | h::t -> CF.mkOr h (helper_f t) no_pos in
  let vdefns = List.filter (fun x ->
      List.exists (fun y -> eq_str x.SBCast.view_name y) hp_names) vdefns in
  let helper hps vdefn =
    let hp = List.find (fun x -> x.Cast.hp_name = vdefn.SBCast.view_name) hps in
    let body = vdefn.SBCast.view_body in
    let args = List.map translate_back_var vdefn.SBCast.view_params in
    let hip_args = hp.Cast.hp_vars_inst |> List.map fst in
    let body = match body with
      | SBCast.VbUnknown -> CF.mkBase_simp (CF.HEmp) (MCP.mkMTrue no_pos)
      | SBCast.VbDefnCases cases ->
        let formulas = List.map (fun x ->
            translate_back_formula x.SBCast.vdc_form []) cases in
        helper_f formulas in
    let () = x_tinfo_hp (add_str "body" pr_formula) body no_pos in
    let body = body |> CF.subst (List.combine args hip_args) in
    {hp with Cast.hp_formula = body} in
  vdefns |> List.map (helper hps)

let translate_prog (prog:Cast.prog_decl) =
  let data_decls = prog.Cast.prog_data_decls in
  let pr1 = CPR.string_of_data_decl_list in
  let () = x_tinfo_hp (add_str "data decls" pr1) data_decls no_pos in
  let sb_data_decls = List.map translate_data_decl data_decls in
  let view_decls = prog.Cast.prog_view_decls in
  let pr2 = CPR.string_of_view_decl_list in
  let () = x_tinfo_hp (add_str "view decls" pr2) view_decls no_pos in
  let hps = prog.Cast.prog_hp_decls @ !Synthesis.unk_hps in
  let hps = Gen.BList.remove_dups_eq Synthesis.eq_hp_decl hps in
  let () = x_tinfo_hp (add_str "hp decls" pr_hps) hps no_pos in
  let sb_hp_views = List.map translate_hp hps in
  let sb_view_decls = List.map translate_view_decl view_decls in
  let pr_hps = pr_list SBCast.pr_view_defn in
  let sb_view_decls = sb_view_decls @ sb_hp_views in
  let prog = SBCast.mk_program "heap_entail" in
  let n_prog = {prog with SBCast.prog_datas = sb_data_decls;
                        SBCast.prog_views = sb_view_decls} in
  let pr3 = SBCast.pr_program in
  let n_prog = Libsongbird.Transform.normalize_prog n_prog in
  let () = x_tinfo_hp (add_str "prog" pr3) n_prog no_pos in
  n_prog

let solve_entailments prog entailments =
  let pr_ents = pr_list (pr_pair pr_formula pr_formula) in
  let () = x_tinfo_hp (add_str "entailments" pr_ents) entailments no_pos in
  let sb_ents = List.map translate_entailment entailments in
  let () = x_tinfo_hp (add_str "sb_ents" SBCast.pr_ents) sb_ents no_pos in
  let sb_prog = translate_prog prog in
  let ptree = SBPU.solve_entailments sb_prog sb_ents in
  let res = SBPFU.get_ptree_validity ptree in
  let () = x_tinfo_hp (add_str "sb_res" pr_validity) res no_pos in
  if res = SBGlobals.MvlTrue then
    let vdefns = SBPFU.get_solved_vdefns ptree in
    let () = x_tinfo_hp (add_str "vdefns" SBCast.pr_vdfs) vdefns no_pos in
    let hps = translate_back_vdefns prog vdefns in
    let () = x_tinfo_hp (add_str "hps" pr_hps) hps no_pos in
    Some hps
  else None

let get_vars_in_fault_ents ents =
  let pr_vars = Cprinter.string_of_spec_var_list in
  let sb_ents = List.map translate_ent ents in
  let () = x_tinfo_hp (add_str "entails: " (pr_list SBCast.pr_pent)) sb_ents no_pos in
  let sb_vars = List.map SBProverE.norm_entail sb_ents |> List.concat in
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
      | SBCast.FbTemplate _
      | SBCast.FbUnkn -> None
      | SBCast.FbForm exp ->
        let sb_vars = fun_def.SBCast.func_params in
        let translated_vars = List.map translate_back_var sb_vars in
        let translated_exp = translate_back_exp exp in
        let substs = List.combine translated_vars vars in
        let n_exp = Cpure.e_apply_subs substs translated_exp in
        Some n_exp
    with Not_found -> None in
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
        let neg_cexp = match cond with
          | Iast.OpGt | Iast.OpLte ->
            let n_exp = CP.mkMult_minus_one fun_def_cexp in
            CP.mkAdd n_exp (CP.mkIConst 2 VarGen.no_pos) VarGen.no_pos
          | Iast.OpGte | Iast.OpLt ->
            let n_exp = CP.mkMult_minus_one fun_def_cexp in
            CP.mkSubtract n_exp (CP.mkIConst 1 VarGen.no_pos) VarGen.no_pos
          | _ -> fun_def_cexp in
        let neg_exp_decl = {exp_decl with exp_body = neg_cexp} in
        let neg_prog = {prog with prog_exp_decls = [neg_exp_decl]} in
        Some (n_prog, fun_def_cexp, Some neg_prog, Some neg_cexp)
      | None -> Some (n_prog, fun_def_cexp, None, None)
    end
  | None -> let () = x_tinfo_pp "No expression \n" VarGen.no_pos in
    None

let check_entail_x ?(residue=false) prog ante conseq =
  let sb_prog = translate_prog prog in
  let sb_ante, _ = translate_formula ante in
  let sb_conseq, _ = translate_formula conseq in
  if List.length sb_ante != 1 && List.length sb_conseq != 1 then
    report_error no_pos "more than one constraint in ante/conseq"
  else
    let sb_ante = List.hd sb_ante in
    let sb_conseq = List.hd sb_conseq in
    if not(residue) then
      let ent = SBCast.mk_entailment sb_ante sb_conseq in
      let () = if !Globals.pr_songbird then
          x_binfo_hp (add_str "entailment" pr_entail) ent no_pos
        else () in
      let ptree = SBProverE.check_entailment sb_prog ent in
      let res = SBPFE.get_ptree_validity ptree in
      match res with
      | SBGlobals.MvlTrue -> true, None
      | _ -> false, None
    else let ent = SBCast.mk_entailment ~mode:PrfEntailHip sb_ante sb_conseq in
      let () = if !Globals.pr_songbird then
          x_binfo_hp (add_str "entailment" pr_entail) ent no_pos
        else () in
      let ptree = SBProverE.check_entailment sb_prog ent in
      let res = SBPFE.get_ptree_validity ptree in
      match res with
      | SBGlobals.MvlTrue ->
        let residue_fs = SBPFE.get_ptree_residues ptree in
        let red = residue_fs |> List.rev |> List.hd in
        let hip_red = translate_back_formula red [] in
        true, Some hip_red
      | _ -> false, None

let check_entail ?(residue=false) prog ante conseq =
  Debug.no_2 "SB.check_entail" pr_formula pr_formula
    (fun (x, _) -> string_of_bool x)
    (fun _ _ -> check_entail_x ~residue:residue prog ante conseq) ante conseq

let check_equal prog first second =
  let forward, _ = check_entail prog first second in
  let backward, _ = check_entail prog second first in
  forward && backward

let eq_h_formula prog (f1:CF.formula) (f2:CF.formula) =
  let get_h_formula (f:CF.formula) = match f with
    | CF.Base bf -> bf.formula_base_heap
    | CF.Exists bf -> bf.formula_exists_heap
    | CF.Or _ -> report_error no_pos "get_h_formula: unhandled" in
  let h1, h2 = get_h_formula f1, get_h_formula f2 in
  let n_f1 = CF.mkBase_simp h1 (MCP.mix_of_pure (CP.mkTrue no_pos)) in
  let n_f2 = CF.mkBase_simp h2 (MCP.mix_of_pure (CP.mkTrue no_pos)) in
  let res1, _ = check_entail prog n_f1 n_f2 in
  let res2, _ = check_entail prog n_f2 n_f1 in
  res1 && res2

let check_unsat_x prog (f:CF.formula) =
  let sb_prog = translate_prog prog in
  let sb_f,_ = translate_formula f in
  if List.length sb_f != 1 then report_error no_pos "SB.check_sat invalid input"
  else
    let sb_formula = List.hd sb_f in
    let sb_res = SBProverE.check_sat sb_prog sb_formula in
    match sb_res with
    | MvlFalse -> true
    | _ -> false

let check_unsat prog (formula:CF.formula) =
  Debug.no_1 "SB.check_unsat" pr_formula string_of_bool
    (fun _ -> check_unsat_x prog formula) formula


let check_pure_entail ante conseq =
  let sb_ante = translate_pf ante in
  let sb_conseq = translate_pf conseq in
  let sb_ante_f = SBCast.mk_fpure sb_ante in
  let sb_conseq_f = SBCast.mk_fpure sb_conseq in
  let sb_prog = SBCast.mk_program "check_pure_entail" in
  let ent = SBCast.mk_entailment sb_ante_f sb_conseq_f in
  let ptree = SBProverE.check_entailment sb_prog ent in
  let res = SBPFE.get_ptree_validity ptree in
    match res with
    | SBGlobals.MvlTrue -> true
    | _ -> false

let get_residues ptrees =
  List.map (fun ptree ->
    let residue_fs = SBPFE.get_ptree_residues ptree in
    let pr_rsd = SBCast.pr_fs in
    let () = x_tinfo_hp (add_str "residues" pr_rsd) residue_fs no_pos in
    residue_fs |> List.rev |> List.hd
  ) ptrees

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
        (* let es_hf = CF.xpure_for_hnodes es.CF.es_heap in *)
        let new_f = CF.mkStar_combine f assume_f CF.Flow_combine no_pos in
        let () = x_tinfo_hp (add_str "new_f" CPR.string_of_formula) new_f no_pos in
        let n_ctx = CF.Ctx {es with CF.es_formula = new_f} in
        (CF.SuccCtx [n_ctx], Prooftracer.TrueConseq)
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
  let hps = prog.Cast.prog_hp_decls @ !Synthesis.unk_hps in
  let hps = Gen.BList.remove_dups_eq Synthesis.eq_hp_decl hps in
  let hp_names = List.map (fun x -> x.Cast.hp_name) hps in
  let () = x_tinfo_hp (add_str "hp names" (pr_list pr_id)) hp_names no_pos in
  let conseq_hps = check_hp_formula hp_names bf.CF.formula_struc_base in
  let ante_hps = check_hp_formula hp_names es.CF.es_formula in
  let n_prog = translate_prog prog in
  let evars = bf.CF.formula_struc_implicit_inst @ bf.CF.formula_struc_explicit_inst
              @ bf.CF.formula_struc_exists @ es.CF.es_evars in
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
  let ante = match pf with
    | None -> es.CF.es_formula
    | Some pf -> CF.add_pure_formula_to_formula pf es.CF.es_formula in
  let sb_ante, _ = translate_formula ante in
  let sb_conseq = List.hd conseqs in
  let ents = List.map (fun x -> SBCast.mk_entailment ~mode:SBGlobals.PrfEntailHip x sb_conseq)
      sb_ante in
  let () = x_tinfo_hp (add_str "ents" SBCast.pr_ents) ents no_pos in
  let interact = if !Globals.enable_sb_interactive then true else false in
  let () = if !Globals.pr_songbird then
      x_binfo_hp (add_str "entailment" (pr_list pr_entail)) ents no_pos
    else () in
  let ptrees = List.map (fun ent -> SBProverE.check_entailment ~interact:interact n_prog ent) ents in
  let validities = List.map (fun ptree -> SBPFE.get_ptree_validity ptree) ptrees in
  let () = x_tinfo_hp (add_str "validities" (pr_list pr_validity)) validities no_pos in
  let conti = bf.CF.formula_struc_continuation in
  if List.for_all (fun x -> x = SBGlobals.MvlTrue) validities
  then
    let residues = get_residues ptrees in
    let residue = translate_back_fs residues holes in
    let () = x_tinfo_hp (add_str "residue" pr_formula) residue no_pos in
    let () = pre_list := [es.CF.es_formula] @ !pre_list in
    let n_ctx = CF.Ctx {es with CF.es_evars = CF.get_exists es.CF.es_formula;
                                CF.es_formula = residue} in
    let conti = bf.CF.formula_struc_continuation in
    match conti with
    | None -> (CF.SuccCtx [n_ctx], Prooftracer.TrueConseq)
    | Some struc -> heap_entail_after_sat_struc_x prog n_ctx struc ~pf:None
  else if conseq_hps then
    let () = Syn.syn_pre := Some es.CF.es_formula in
    let () = x_tinfo_hp (add_str "es_f" pr_formula) es.CF.es_formula no_pos in
    let n_ante = CF.get_pure es.CF.es_formula in
    let n_ante = CF.mkBase_simp (CF.HEmp) (MCP.mix_of_pure n_ante) in
    let n_ctx = CF.Ctx {es with CF.es_formula = n_ante} in
    match conti with
    | None -> (CF.SuccCtx [n_ctx], Prooftracer.TrueConseq)
    | Some struc -> heap_entail_after_sat_struc_x prog n_ctx struc ~pf:None
  else if ante_hps then
    let vars = CF.fv es.CF.es_formula |> CP.remove_dups_svl in
    let vars = vars |> List.filter (fun x -> match CP.type_of_sv x with
        | Int | Named _ -> true
        | _ -> false) in
    let exists_vars = bf.CF.formula_struc_exists
                      @ bf.CF.formula_struc_explicit_inst
                      @ bf.CF.formula_struc_implicit_inst
                    |> CP.remove_dups_svl in
    let conseq = Syn.add_exists_vars bf.CF.formula_struc_base exists_vars in
    let () = x_tinfo_hp (add_str "conseq" pr_struc_f) (CF.EBase bf) no_pos in
    let () = x_tinfo_hp (add_str "ante" pr_formula) (es.CF.es_formula) no_pos in
    let () = x_tinfo_hp (add_str "conseq" pr_formula) conseq no_pos in
    let n_es_f, n_conseq = Syn.create_residue vars prog conseq in
    let n_es_f = CF.add_pure_formula_to_formula (CF.get_pure es.CF.es_formula) n_es_f in
    let () = Syn.entailments := [(es.CF.es_formula, n_conseq)] @ !Syn.entailments in
    let () = x_tinfo_hp (add_str "n_es_f" pr_formula) n_es_f no_pos in
    let n_ctx = CF.Ctx {es with CF.es_formula = n_es_f;} in
    match conti with
    | None -> (CF.SuccCtx [n_ctx], Prooftracer.TrueConseq)
    | Some struc -> heap_entail_after_sat_struc_x prog n_ctx struc ~pf:None
  else
    let msg = "songbird result is Failed." in
    (CF.mkFailCtx_simple msg es bf.CF.formula_struc_base (CF.mk_cex true) no_pos
    , Prooftracer.Failure)

let infer_templ_defn prog pre post fun_name args =
  let sb_prog = translate_prog prog in
  let sb_args = List.map translate_var args in
  let f_defn = SBCast.mk_func_defn_unknown fun_name sb_args in
  let ifp_typ = SBGlobals.IfrStrong in
  let sb_pre, sb_post = translate_pf pre, translate_pf post in
  let ent = SBCast.mk_pure_entail sb_pre sb_post in
  let infer_func = {SBCast.ifp_typ = ifp_typ;
                    SBCast.ifp_ents = [ent]} in
  let nprog = {sb_prog with
               SBCast.prog_funcs = [f_defn];
               SBCast.prog_commands = [SBCast.InferFuncs infer_func]} in
  let () = x_tinfo_hp (add_str "nprog: " SBCast.pr_program) nprog no_pos in
  let sb_res = SBProverP.infer_unknown_functions ifp_typ nprog ent in
  let ifd = fst sb_res in
  let () = x_tinfo_hp (add_str "re" SBProverP.pr_ifds) ifd no_pos in
  let func_defns = ifd |> List.map (fun x -> x.SBProverP.ifd_fdefns)
                   |> List.concat in
  try
    let func_defn = func_defns
                    |> List.find (fun x -> x.SBCast.func_name = tmpl_name) in
    let fdefn_body = match func_defn.SBCast.func_body with
      | SBCast.FbForm e ->
        let hip_exp = translate_back_exp e in
        let () = x_tinfo_hp (add_str "hip_exp" Cprinter.string_of_formula_exp) hip_exp no_pos in
        Some hip_exp
      | _ -> None in
    fdefn_body
  with _ -> None
