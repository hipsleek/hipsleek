#include "xdebug.cppo"
open VarGen
open Globals
open Gen
open Cpure
open Tlutils

exception Piecewise_Infer_Failure of string 

type piecewise_template = {
  ptempl_id: spec_var;
  ptempl_params: spec_var list;
  ptempl_pieces: (formula * template) list;  
}

let gen_def_ptempl prog ptempl =
  let templ_defs = prog.Cast.prog_templ_decls in
  let ptempl_name = name_of_spec_var ptempl.ptempl_id in
  try
    let templ_def = List.find (fun td -> td.Cast.templ_name = ptempl_name) templ_defs in
    List.map (fun (_, t) -> {
          Cast.templ_name = name_of_spec_var t.templ_id;
          Cast.templ_ret_typ = templ_def.Cast.templ_ret_typ;
          Cast.templ_params = ptempl.ptempl_params;
          Cast.templ_body = Some (exp_of_template t);
          Cast.templ_pos = no_pos; }) ptempl.ptempl_pieces
  with _ -> raise (Piecewise_Infer_Failure (ptempl_name ^ " is not defined.")) 

let pr_ptempl pt =
  (pr_spec_var pt.ptempl_id) ^ (pr_list pr_spec_var pt.ptempl_params) ^ " = {\n\t" ^
  (String.concat ";\n\t" (List.map (fun (c, t) -> 
       (pr_formula c) ^ " -> " ^ (pr_exp (Template t))) pt.ptempl_pieces)) ^ "}" 

let get_var_exp e =
  match e with
  | Var (v, _) -> v
  | _ -> raise (Piecewise_Infer_Failure 
                  "Unexpected error: Cannot determine (rank/template's arguments) 
       variable expression.")

let get_src_rank_var f = 
  let r = match f with
    | BForm ((Gt (r, _, _), _), _) -> r
    | BForm ((Lt (_, r, _), _), _) -> r
    | _ -> raise (Piecewise_Infer_Failure 
                    "Unexpected error: Ranking constraint is not decreasing.")
  in get_var_exp r

let get_rank_template v f =
  match f with 
  | BForm ((Eq (e1, e2, _), _), _) -> 
    begin match e1 with 
      | Var (v, _) -> begin match e2 with
          | Template t -> Some t
          | _ -> None end
      | Template t -> begin match e2 with
          | Var (v, _) -> Some t
          | _ -> None end
      | _ -> None end
  | _ -> None

let search_templ_def_dec_templ_assume v f = 
  let fs = split_conjunctions f in
  let templ = List.fold_left (fun a f -> match a with
      | None -> get_rank_template v f
      | Some _ -> a) None fs in
  match templ with
  | None -> raise (Piecewise_Infer_Failure 
                     "Unexpected error: Cannot find a template assumption for rank variable.")
  | Some t -> t

let get_cond_templ_args ctx vs =
  let exists_ctx = mkExists 
      (Gen.BList.difference_eq eq_spec_var (fv ctx) vs) 
      ctx None (pos_of_formula ctx) in 
  let pr_weak, pr_strong = drop_complex_ops in
  x_add Omega.simplify_ops pr_weak pr_strong exists_ctx

(* Get the condition of the template's *)
(* arguments in the current context *)
(* f(e1, e2) -> f(x, y) & x = e1 & x = e2 *)
let get_cond_dec_templ_assume templ_assume = 
  let ante = templ_assume.ass_ante in
  let cons = templ_assume.ass_cons in
  let src_rank_var = get_src_rank_var cons in
  let templ = search_templ_def_dec_templ_assume src_rank_var ante in
  let templ_args, _ = List.fold_left (fun (a, i) ta -> 
      (a @ [(ta, i)], i + 1)) ([], 0) templ.templ_args in
  let ante, cond_args = List.fold_left (fun (a, vs) (e, i) ->
      let pos = pos_of_exp e in
      let v = SpecVar(Int, (name_of_spec_var templ.templ_id) ^ "_c" ^ (string_of_int i), Unprimed) in
      let eq = mkPure (mkEq (mkVar v pos) e pos) in
      (mkAnd a eq pos, vs @ [v])) (ante, []) templ_args in 
  let cond = get_cond_templ_args ante cond_args in
  (* let () = print_endline ("COND ARGS: " ^ (pr_spec_var templ.templ_id) ^ *)
  (*   (pr_list pr_spec_var cond_args) ^ " -> " ^                          *)
  (*   (pr_formula cond)) in                                               *)
  ((templ, cond_args), cond)

let construct_piecewise_template templ args conds =
  let pos = templ.templ_pos in
  let ptempl_args = List.map (fun v -> mkVar v pos) args in
  {
    ptempl_id = templ.templ_id;
    ptempl_params = args;
    ptempl_pieces = List.map (fun c ->
        let templ_id = fresh_spec_var templ.templ_id in
        (c, mkTemplate_sv templ_id ptempl_args pos)) conds;
  }

let rec combine_pair mk f1l f2l pos =
  match f1l with
  | [] -> []
  | (f1, c1)::f1s -> 
    let comb_s = combine_pair mk f1s f2l pos in
    (List.map (fun (f2, c2) -> mk f1 f2, mkAnd c1 c2 pos) f2l) @ comb_s

(* let rec combine_ls ls = match ls with                                            *)
(*   | [] -> []                                                                     *)
(*   | l::ls ->                                                                     *)
(*     let rs = combine_ls ls in                                                    *)
(*     let r = List.concat (List.map (fun ((t, f), c) -> List.map (fun (fs, cs) ->  *)
(*       (t, f)::fs, mkAnd c cs (pos_of_formula f)) rs) l)                          *)
(*     in r                                                                         *)

let rec subst_piecewise_templ_exp pts e = 
  match e with
  | Add (e1, e2, pos) ->
    let ne1_w_cond_ls = subst_piecewise_templ_exp pts e1 in
    let ne2_w_cond_ls = subst_piecewise_templ_exp pts e2 in
    let mkA = fun e1 e2 -> mkAdd e1 e2 pos in
    combine_pair mkA ne1_w_cond_ls ne2_w_cond_ls pos
  | Subtract (e1, e2, pos) ->
    let ne1_w_cond_ls = subst_piecewise_templ_exp pts e1 in
    let ne2_w_cond_ls = subst_piecewise_templ_exp pts e2 in
    let mkS = fun e1 e2 -> mkSubtract e1 e2 pos in
    combine_pair mkS ne1_w_cond_ls ne2_w_cond_ls pos
  | Mult (e1, e2, pos) ->
    let ne1_w_cond_ls = subst_piecewise_templ_exp pts e1 in
    let ne2_w_cond_ls = subst_piecewise_templ_exp pts e2 in
    let mkM = fun e1 e2 -> mkMult e1 e2 pos in
    combine_pair mkM ne1_w_cond_ls ne2_w_cond_ls pos
  | Div (e1, e2, pos) ->
    let ne1_w_cond_ls = subst_piecewise_templ_exp pts e1 in
    let ne2_w_cond_ls = subst_piecewise_templ_exp pts e2 in
    let mkD = fun e1 e2 -> mkDiv e1 e2 pos in
    combine_pair mkD ne1_w_cond_ls ne2_w_cond_ls pos
  | Template t -> begin try
        let pt = List.find (fun pt -> eq_spec_var t.templ_id pt.ptempl_id) pts in
        let targs = t.templ_args in
        let ptparams = pt.ptempl_params in
        let sst = List.combine ptparams targs in
        List.map (fun (c, t) -> 
            a_apply_par_term sst (Template t), 
            subst_term_par sst c) pt.ptempl_pieces
      with _ -> [(e, mkTrue (pos_of_exp e))] end
  | _ -> [(e, mkTrue (pos_of_exp e))]

let subst_piecewise_templ_b_formula pts bf = 
  let pf, ann = bf in
  let npf = match pf with
    | Lt (e1, e2, pos) ->
      let ne1_w_cond_ls = subst_piecewise_templ_exp pts e1 in
      let ne2_w_cond_ls = subst_piecewise_templ_exp pts e2 in
      let mkL = fun e1 e2 -> mkLt e1 e2 pos in
      combine_pair mkL ne1_w_cond_ls ne2_w_cond_ls pos
    | Lte (e1, e2, pos) ->
      let ne1_w_cond_ls = subst_piecewise_templ_exp pts e1 in
      let ne2_w_cond_ls = subst_piecewise_templ_exp pts e2 in
      let mkLe = fun e1 e2 -> mkLte e1 e2 pos in
      combine_pair mkLe ne1_w_cond_ls ne2_w_cond_ls pos
    | Gt (e1, e2, pos) ->
      let ne1_w_cond_ls = subst_piecewise_templ_exp pts e1 in
      let ne2_w_cond_ls = subst_piecewise_templ_exp pts e2 in
      let mkG = fun e1 e2 -> mkGt e1 e2 pos in
      combine_pair mkG ne1_w_cond_ls ne2_w_cond_ls pos
    | Gte (e1, e2, pos) ->
      let ne1_w_cond_ls = subst_piecewise_templ_exp pts e1 in
      let ne2_w_cond_ls = subst_piecewise_templ_exp pts e2 in
      let mkGe = fun e1 e2 -> mkGte e1 e2 pos in
      combine_pair mkGe ne1_w_cond_ls ne2_w_cond_ls pos
    | Eq (e1, e2, pos) ->
      let ne1_w_cond_ls = subst_piecewise_templ_exp pts e1 in
      let ne2_w_cond_ls = subst_piecewise_templ_exp pts e2 in
      let mkE = fun e1 e2 -> mkEq e1 e2 pos in
      combine_pair mkE ne1_w_cond_ls ne2_w_cond_ls pos
    | Neq (e1, e2, pos) ->
      let ne1_w_cond_ls = subst_piecewise_templ_exp pts e1 in
      let ne2_w_cond_ls = subst_piecewise_templ_exp pts e2 in
      let mkN = fun e1 e2 -> mkNeq e1 e2 pos in
      combine_pair mkN ne1_w_cond_ls ne2_w_cond_ls pos
    | _ -> [(pf, mkTrue (pos_of_b_formula bf))]
  in List.map (fun (p, c) -> ((p, ann), c)) npf

let subst_piecewise_templ_formula pts f =
  let rec helper pts f = match f with 
    | BForm (bf, lbl) -> 
      let nbf_w_cond_ls = subst_piecewise_templ_b_formula pts bf in
      let nf_w_cond_ls = List.map (fun (bf, c) ->
          BForm (bf, lbl), c) nbf_w_cond_ls in
      nf_w_cond_ls
    | And (f1, f2, pos) ->
      let nf1_w_cond_ls = helper pts f1 in
      let nf2_w_cond_ls = helper pts f2 in
      let mkA = fun f1 f2 -> mkAnd f1 f2 pos in    
      combine_pair mkA nf1_w_cond_ls nf2_w_cond_ls pos
    | Or (f1, f2, lbl, pos) ->
      let nf1_w_cond_ls = helper pts f1 in
      let nf2_w_cond_ls = helper pts f2 in
      let mkO = fun f1 f2 -> mkOr f1 f2 lbl pos in    
      combine_pair mkO nf1_w_cond_ls nf2_w_cond_ls pos
    | Not (f, lbl, pos) ->
      let nf_w_cond_ls = helper pts f in
      List.map (fun (nf, c) -> (mkNot nf lbl pos, c)) nf_w_cond_ls
    (* | AndList fl ->                                                                         *)
    (*   let nfl_w_cond_ls = List.map (fun (t, f) ->                                           *)
    (*     List.map (fun (nf, c) -> ((t, nf), c)) (subst_piecewise_templ_formula pts f)) fl in *)
    (*   List.map (fun (nfl, c) -> AndList nfl, c) (combine_ls nfl_w_cond_ls)                  *)
    | _ -> raise (Piecewise_Infer_Failure ("Formula " ^ (pr_formula f) ^ "is not supported."))
  in
  let nf = helper pts f in
  List.filter is_sat (List.map (fun (f, c) -> mkAnd f c (pos_of_formula f)) nf)

let infer_piecewise_main prog templ_assumes = 
  let dec_assumes, bnd_assumes = List.partition (fun ta -> 
      is_strict_formula ta.ass_cons) templ_assumes in
  (* print_endline ("DEC: " ^ (pr_list pr_templ_assume dec_assumes)); *)
  (* print_endline ("BND: " ^ (pr_list pr_templ_assume bnd_assumes)); *)
  let cond_templ_defs = List.map get_cond_dec_templ_assume dec_assumes in
  let grp_templ_defs = partition_by_assoc_to_pair 
      (fun (t1, _) (t2, _) -> eq_templ t1 t2) cond_templ_defs in
  let ptempl_ls = List.map (fun ((t, args), conds) -> 
      construct_piecewise_template t args conds) grp_templ_defs in
  let inf_ptempls = List.concat (List.map (fun pt -> 
      List.map (fun (_, t) -> t.templ_id) pt.ptempl_pieces) ptempl_ls) in
  let ptempl_defs = List.concat (List.map (gen_def_ptempl prog) ptempl_ls) in
  let ptempl_assumes = List.concat (List.map (fun ta ->
      let ante = ta.ass_ante in
      let cons = ta.ass_cons in
      List.map (fun f -> (f, cons)) 
        (subst_piecewise_templ_formula ptempl_ls ante)) templ_assumes) in 
  print_endline_quiet ("Piecewise template definition:\n" ^ (pr_list pr_ptempl ptempl_ls));
  (* print_endline "\n**** PIECEWISE TEMPLATE ASSUMPTION(S) ****";                                     *)
  (* print_endline (pr_list (fun pta -> (Cprinter.string_of_templ_assume pta) ^ "\n") ptempl_assumes); *)
  ptempl_assumes, inf_ptempls, ptempl_defs

