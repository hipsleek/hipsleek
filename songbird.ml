#include "xdebug.cppo"

module SBCast = Libsongbird.Cast
module SBGlobals = Libsongbird.Globals

(* translation of HIP's data structures to Songbird's data structures
   will be done here *)


let translate_loc (location:VarGen.loc) : SBGlobals.pos =
  {
    pos_begin = location.start_pos;
    pos_end = location.end_pos;
  }

let translate_type (typ: Globals.typ) : SBGlobals.typ =
  match typ with
  | Int -> TInt
  | Bool -> TInt
  | UNK -> TUnk
  | Void -> TVoid
  | _ -> Gen.Basic.report_error VarGen.no_pos "this type is not handled"

let translate_var (var: Cpure.spec_var): SBGlobals.var =
  match var with
  | SpecVar (typ, ident, primed) -> (ident, translate_type typ)

let rec translate_exp (exp: Cpure.exp): SBCast.exp =
  match exp with
  | Cpure.Null loc -> SBCast.Null (translate_loc loc)
  | Cpure.Var (var, loc) -> SBCast.Var (translate_var var, translate_loc loc)
  | Cpure.IConst (num, loc) -> SBCast.IConst (num, translate_loc loc)
  | Cpure.Add (exp1, exp2, loc) -> SBCast.BinOp (Add, translate_exp exp1, translate_exp exp2,
  translate_loc loc)
  | _ -> Gen.Basic.report_error VarGen.no_pos "this exp is not handled"

let translate_pure_formula (pure_f: Cpure.formula) : (SBCast.pure_form) =
  match pure_f with
  | Cpure.BForm (b_formula, _) ->
    let (p_formula, _) = b_formula in
    begin
    match p_formula with
      | Eq (exp1, exp2, loc) ->
        let sb_exp1 = translate_exp exp1 in
        let sb_exp2 = translate_exp exp2 in
        let sb_loc = translate_loc loc in
         SBCast.BinRel (Eq, sb_exp1, sb_exp2, sb_loc)
     | _ -> Gen.Basic.report_error VarGen.no_pos "this p_formula is not handled"
  end

  | _ -> Gen.Basic.report_error VarGen.no_pos "this pure formula not handled"

(* calls to Songbird's functions in songbird/src/prover.ml
   will be done here *)

(* Input: 2 pure formulas: lhs and rhs of type SBCast.pure_form
   Output: using Farkas and templates to infer to model*)

(* let infer_model (lhs: SBCast.pure_form) (rhs: SBCast.pure_form) =
 *   let pure_entail = SBCast.mk_entailment lhs rhs in
 *   let entail_list = [pure_entail] in
 *   () *)

(* let create_rel_with_var var =
 *   let f_var = SBCast.mk_var "f" SBGlobals.TInt *)

(* translate lhs of the entalment e.g. res = x + 1 to template form: res = f(x)*)
(* let translate_lhs_to_templ (lhs: SBCast.pure_form) (\* : SBCast.pure_form *\) =
 *   match lhs with
 *   | BinRel (rel, exp1, exp2, pos) ->
 *     let exp2_vars = SBCast.fv_exp exp2 in
 *       let exp2_args = List.map (SBCast.mk_exp_var) exp2_vars in
 *       let func_exp = SBCast.mk_func (SBCast.FuncName "f") exp2_args in
 *       (SBCast.BinRel (rel, exp1, func_exp, pos), exp2_vars)
 *   | _ -> Gen.Basic.report_error VarGen.no_pos "this type of lhs not handled" *)


(* Input: lhs and rhs
   Create template for lhs
   Adding template f(args) = ?
   Output: Input for songbird infer_unknown_functions
*)
(* let create_templ_prog (lhs: SBCast.pure_form) (rhs: SBCast.pure_form)=
 *   let (lhs_templ, args) = translate_lhs_to_templ lhs in
 *   let program = SBCast.mk_program "hip_input" in
 *   let f_defn = SBCast.mk_func_defn_unknown "f" args in
 *   let ifr_typ = SBGlobals.IfrStrong in
 *   let entail = SBCast.mk_pure_entail lhs_templ rhs in
 *   let infer_func = {
 *     SBCast.ifr_typ = ifr_typ;
 *     SBCast.ifr_rels = [entail]
 *   }
 *   in
 *   let nprog = {program with
 *              prog_funcs = [f_defn];
 *              prog_commands = [SBCast.InferFuncs infer_func]
 *             }
 *   in
 *   let _ = SBProver.infer_unknown_functions ifr_typ program [entail] in
 *   () *)

