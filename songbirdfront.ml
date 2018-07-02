#include "xdebug.cppo"

open Gen.Basic
open VarGen

module SBCast = Libsongbird.Cast
module SBGlobals = Libsongbird.Globals
module SBDebug = Libsongbird.Debug

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
  | _ -> Gen.Basic.report_error VarGen.no_pos "translate_type: this type is not handled"

let translate_back_type (typ) = match typ with
  | SBGlobals.TInt -> Globals.Int
  | SBGlobals.TBool -> Globals.Bool
  | SBGlobals.TUnk -> Globals.UNK
  | SBGlobals.TVoid -> Globals.Void
  | _ -> Gen.Basic.report_error VarGen.no_pos "translate_back_type: this type is not handled"


let translate_var (var: Cpure.spec_var): SBGlobals.var =
  match var with
  | SpecVar (typ, ident, primed) -> (ident, translate_type typ)

let translate_back_var (var : SBGlobals.var) =
  let (str, typ) = var in
  Cpure.SpecVar (translate_back_type typ, str, VarGen.Unprimed)

let rec translate_exp (exp: Cpure.exp): SBCast.exp =
  match exp with
  | Cpure.Null loc -> SBCast.Null (translate_loc loc)
  | Cpure.Var (var, loc) -> SBCast.Var (translate_var var, translate_loc loc)
  | Cpure.IConst (num, loc) -> SBCast.IConst (num, translate_loc loc)
  | Cpure.Add (exp1, exp2, loc) -> SBCast.BinOp (Add, translate_exp exp1, translate_exp exp2,
  translate_loc loc)
  | _ -> Gen.Basic.report_error VarGen.no_pos "this exp is not handled"

let rec translate_back_exp (exp: SBCast.exp) = match exp with
  | SBCast.Null pos -> Cpure.Null (translate_back_pos pos)
  | SBCast.Var (var, pos) -> Cpure.Var (translate_back_var var, translate_back_pos
                                      pos)
  | SBCast.IConst (num, pos) -> Cpure.IConst (num, translate_back_pos pos)
  | SBCast.BinOp (Add, exp1, exp2, pos) ->
    Cpure.Add (translate_back_exp exp1, translate_back_exp exp2,
               translate_back_pos pos)
  | _ -> Gen.Basic.report_error VarGen.no_pos "translate_back_exp: this exp is not handled"

let translate_pf (pure_f: Cpure.formula) : (SBCast.pure_form) =
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

let translate_back_pf (pf : SBCast.pure_form) = match pf with
  | SBCast.BConst (b, pos)
    -> Cpure.BForm ((Cpure.BConst (b, translate_back_pos pos), None), None)
  | SBCast.BinRel (br, exp1, exp2, pos) ->
    let exp1_hip = translate_back_exp exp1 in
    let exp2_hip = translate_back_exp exp2 in
    let loc = translate_back_pos pos in
    begin
      match br with
      | SBCast.Lt -> Cpure.BForm((Cpure.Lt (exp1_hip, exp2_hip, loc), None), None)
      | SBCast.Le -> Cpure.BForm((Cpure.Lte (exp1_hip, exp2_hip, loc), None), None)
      | SBCast.Gt -> Cpure.BForm((Cpure.Gt (exp1_hip, exp2_hip, loc), None), None)
      | SBCast.Ge -> Cpure.BForm((Cpure.Gte (exp1_hip, exp2_hip, loc), None), None)
      | SBCast.Eq -> Cpure.BForm((Cpure.Eq (exp1_hip, exp2_hip, loc), None), None)
      | SBCast.Ne -> Cpure.BForm((Cpure.Neq (exp1_hip, exp2_hip, loc), None), None)
    end
  | _ -> Gen.Basic.report_error VarGen.no_pos "this type of lhs not handled"


(* translate lhs of the entalment e.g. res = x + 1 to template form: res = f(x)*)
let translate_rhs_to_fdefn (lhs: Libsongbird.Cast.pure_form) (* : SBCast.pure_form *) =
  match lhs with
  | BinRel (rel, exp1, exp2, pos) ->
    let exp2_vars = SBCast.fv_exp exp2 in
      let exp2_args = List.map (SBCast.mk_exp_var) exp2_vars in
      let func_exp = SBCast.mk_func (SBCast.FuncName "f") exp2_args in
      (Libsongbird.Cast.BinRel (rel, exp1, func_exp, pos), exp2_vars)
  | _ -> Gen.Basic.report_error VarGen.no_pos "this type of lhs not handled"


(* Input: lhs and rhs
   Create template for lhs
   Adding template f(args) = ?
   Output: Input for songbird infer_unknown_functions
*)
let create_templ_prog (lhs: SBCast.pure_form) (rhs: SBCast.pure_form)=
  let (lhs_templ, args) = translate_rhs_to_fdefn lhs in
  let program = SBCast.mk_program "hip_input" in
  let f_defn = SBCast.mk_func_defn_unknown "f" args in
  let ifr_typ = SBGlobals.IfrStrong in
  let entail = SBCast.mk_pure_entail lhs_templ rhs in
  let infer_func = {
    SBCast.ifr_typ = ifr_typ;
    SBCast.ifr_rels = [entail]
  }
  in
  let nprog = {program with
             prog_funcs = [f_defn];
             prog_commands = [SBCast.InferFuncs infer_func]
            }
  in
  let () = Libsongbird.Debug.hprint "prog: " Libsongbird.Cast.pr_program nprog in
  let () = Libsongbird.Debug.hprint "pure entails: " Libsongbird.Cast.pr_pent entail in
  let ifds = Libsongbird.Prover.infer_unknown_functions ifr_typ nprog [entail] in
  let () = Libsongbird.Debug.rhprint " ==> Result: \n" Libsongbird.Proof.pr_ifds
      ifds in
  let func_defns = ifds |> List.map (fun ifd -> Libsongbird.Proof.get_ifd_fdefns
                                        ifd) |> List.concat in
  let lhs_repaired = Libsongbird.Cast.unfold_func_pf func_defns lhs in
  lhs_repaired

let get_repair_candidate (lhs: Cpure.formula) (rhs: Cpure.formula) =
  let sb_lhs = translate_pf lhs in
  let sb_rhs = translate_pf rhs in
  let repaired_lhs = create_templ_prog sb_lhs sb_rhs in
  (* let () = SBDebug.hprint "repaired pf: " SBCast.pr_pf repaired_lhs in *)
  translate_back_pf repaired_lhs
