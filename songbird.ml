#include "xdebug.cppo"

module SBCast = Libsongbird.Cast
module SBGlobals = Libsongbird.Globals
module SBDebug = Libsongbird.Debug
module CP = Cpure

(* translation of HIP's data structures to Songbird's data structures
   will be done here *)


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
  | Bool -> TInt
  | UNK -> TUnk
  | Void -> TVoid
  | Named str -> TData str
  | _ -> Gen.Basic.report_error VarGen.no_pos
           ("translate_type:" ^ (Globals.string_of_typ typ) ^ " is not handled")

let translate_back_type (typ) = match typ with
  | SBGlobals.TInt -> Globals.Int
  | SBGlobals.TBool -> Globals.Bool
  | SBGlobals.TUnk -> Globals.UNK
  | SBGlobals.TVoid -> Globals.Void
  | _ -> Gen.Basic.report_error VarGen.no_pos "translate_back_type: this type is not handled"


let translate_var (var: CP.spec_var): SBGlobals.var =
  match var with
  | SpecVar (typ, ident, primed) -> (ident, translate_type typ)

let translate_back_var (var : SBGlobals.var) =
  let (str, typ) = var in
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
    let fun_name = CP.name_of_sv templ.templ_id in
    let args = templ.templ_args |> List.map translate_exp in
    SBCast.mk_func (SBCast.FuncName fun_name) args
  | _ -> Gen.Basic.report_error VarGen.no_pos "this exp is not handled"

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
  | SBCast.Func _ -> Gen.Basic.report_error VarGen.no_pos
                       ("translate_back_exp:" ^ (SBCast.pr_exp exp)
                        ^ " this Func is not handled")
  | _ -> Gen.Basic.report_error VarGen.no_pos ("this exp formula not handled: "
         ^ (SBCast.pr_exp exp))

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
      | _ -> Gen.Basic.report_error VarGen.no_pos "this p_formula is not handled"
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
  | _ -> Gen.Basic.report_error VarGen.no_pos "this pure formula not handled"

let translate_back_pf (pf : SBCast.pure_form) = match pf with
  | SBCast.BConst (b, pos)
    -> CP.BForm ((CP.BConst (b, translate_back_pos pos), None), None)
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
  | _ -> Gen.Basic.report_error VarGen.no_pos "this type of lhs not handled"

(* Input: lhs and rhs
   Create template for lhs
   Adding template f(args) = ?
   Output: Input for songbird infer_unknown_functions
*)


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
  let () = x_tinfo_hp (Gen.Basic.add_str "nprog: " SBCast.pr_program) nprog VarGen.no_pos in
  let sb_res =
    Libsongbird.Prover.infer_unknown_functions_with_false_rhs ifr_typ nprog
      ents in
  let inferred_prog = if sb_res = [] then nprog
      else snd (List.hd sb_res)
  in
  let () = x_tinfo_hp (Gen.Basic.add_str "inferred prog: " SBCast.pr_program)
      inferred_prog VarGen.no_pos in
  inferred_prog.SBCast.prog_funcs

let translate_ent ent =
  let (lhs, rhs) = ent in
  let () = x_tinfo_hp (Gen.Basic.add_str "lhs: " (Cprinter.string_of_pure_formula))
      lhs VarGen.no_pos in
  let () = x_tinfo_hp (Gen.Basic.add_str "rhs: " (Cprinter.string_of_pure_formula))
      rhs VarGen.no_pos in

  let sb_lhs = translate_pf lhs in
  let sb_rhs = translate_pf  rhs in
  let () = x_tinfo_hp (Gen.Basic.add_str "lhs: " (SBCast.pr_pure_form))
      sb_lhs VarGen.no_pos in
  let () = x_tinfo_hp (Gen.Basic.add_str "rhs: " (SBCast.pr_pure_form))
      sb_rhs VarGen.no_pos in

  SBCast.mk_pure_entail sb_lhs sb_rhs

let get_vars_in_fault_ents ents =
  let sb_ents = List.map translate_ent ents in
  let sb_vars = List.map Libsongbird.Prover.norm_entail sb_ents |> List.concat in
  let vars = List.map translate_back_var sb_vars in
  vars

let get_repair_candidate prog ents cond_op =
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
      let () = x_tinfo_hp (Gen.Basic.add_str "exp: " (Cprinter.poly_string_of_pr
                                                        Cprinter.pr_formula_exp)
                          ) fun_def_cexp VarGen.no_pos in
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
            (* let n_exp = CP.mkMult_minus_one fun_def_cexp in
             * let neg_cexp = CP.simp_mult n_exp in *)
            let neg_exp_decl = {exp_decl with exp_body = neg_cexp} in
            let neg_prog = {prog with prog_exp_decls = [neg_exp_decl]} in
            Some (n_prog, fun_def_cexp, Some neg_prog, Some neg_cexp)
          | None -> Some (n_prog, fun_def_cexp, None, None)
      end
    | None ->
      let () = x_tinfo_pp "No expression \n" VarGen.no_pos in
      None
