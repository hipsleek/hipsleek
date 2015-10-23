#include "xdebug.cppo"
open VarGen
module DD = Debug
open Globals
open Wrapper
open Others
open Stat_global
open Global_var
open Exc.GTable
open Solver
open Cast
open Gen.Basic
open Label

module CF = Cformula
module CP = Cpure
module TP = Tpdispatcher


(*1. pick up
     R(x) --> x>=2
     R(x) --> x!=1 /\ x>=2 --> R(x)
  2. subst into rhs
  3. go to 1
  *)
let classify_ni prog rels=
  let pure_I x=
    let p = CP.Lte((CP.mkIConst 2 no_pos), CP.mkVar x no_pos,no_pos) in
    let f = CP.mk_bform p in
    f
  in
  let pure_I_norm x=
    let p = CP.Gte(CP.mkVar x no_pos,(CP.mkIConst 2 no_pos),no_pos) in
    let f = CP.mk_bform p in
    f
  in
  let pure_I_cond x=
    let p = CP.Neq(CP.mkVar x no_pos,(CP.mkIConst 1 no_pos),no_pos) in
    let f = CP.mk_bform p in
    f
  in
  let is_gte (f:CP.formula) sv cons = match f with
    | BForm (bf,_) ->
          (match bf with
            | (CP.Gte (CP.Var (sv1,_), CP.IConst (i,_), _),_)
            | (CP.Lte (CP.IConst (i,_), CP.Var (sv1,_), _),_) -> CP.eq_spec_var sv sv1 && cons=i
            | _ ->  false)
    | _ ->  false
  in
  let is_neq (f:CP.formula) sv cons = match f with
    | BForm (bf,_) ->
          (match bf with
            | (CP.Neq (CP.Var (sv1,_), CP.IConst (i,_), _),_)
            | (CP.Neq (CP.IConst (i,_), CP.Var (sv1,_), _),_) -> CP.eq_spec_var sv sv1 && cons=i
            | _ ->  false)
    | _ ->  false
  in
  let replace_with_def ((id,svl),def) p =
    let ps = CP.list_of_conjs p in
    let ps1 = List.map (fun p -> match p with
      | CP.BForm (bf,_) ->
            (match bf with
              | (CP.RelForm(id1,eargs,_),_) ->
                    if CP.eq_spec_var id id1 then
                      let svl1 =  List.concat (List.map CP.afv eargs) in
                      CP.subst (List.combine svl svl1) def
                    else p
              | _ -> p)
      | _ -> p
    ) ps in
    CP.conj_of_list ps1 (CP.pos_of_formula p)
  in
  let look_up_I rels=
    let check_I_rel (rel_Is, rest) ((_,lhs, rhs) as rel) =
        match CP.get_relargs_opt lhs with
          | Some (id, svl) -> begin
              let () = x_tinfo_hp (add_str "svl" pr_svl) svl no_pos in
              match svl with
                | [sv] -> if is_gte rhs sv 2 then
                    (rel_Is@[((id, svl), rhs)], rest)
                  else (rel_Is, rest@[rel])
                | _ -> (rel_Is, rest@[rel])
            end
          | None -> (rel_Is, rest@[rel])
    in
    List.fold_left check_I_rel ([],[]) rels
  in
  let look_up_I rel_Is=
    let pr1 = pr_list_ln CP.string_of_infer_rel in
    let pr2 = pr_list (pr_pair (pr_pair !CP.print_sv !CP.print_svl) !CP.print_formula) in
    Debug.no_1 "look_up_I" pr1 (pr_pair pr2 pr1)
        (fun _ -> look_up_I rel_Is) rel_Is
  in
  let rec look_up_reduced id sv rest_defs done_defs=
    match rest_defs with
      | [] -> false, done_defs
      | ((_,lhs,rhs) as rel)::rest -> begin
          match CP.get_relargs_opt rhs with
            | Some (id, svl) -> begin
                match svl with
                | [sv] -> if is_gte lhs sv 2 then
                    true, done_defs@rest
                  else look_up_reduced id sv rest (done_defs@[rel])
                | _ -> look_up_reduced id sv rest (done_defs@[rel])
              end
            | None -> look_up_reduced id sv rest (done_defs@[rel])
        end
  in
  let look_up_I_cond rels reldefs=
    let check_I_rel (rel_Is, rest_const, rest_defs) ((_,lhs, rhs) as rel) =
        match CP.get_relargs_opt lhs with
          | Some (id, svl) -> begin
              let () = x_tinfo_hp (add_str "svl" pr_svl) svl no_pos in
              match svl with
                | [sv] -> if is_neq rhs sv 1 then
                    let is_reduced, rest = look_up_reduced id sv rest_defs [] in
                    if is_reduced then
                      (rel_Is@[((id, svl), pure_I sv)], rest_const,rest)
                    else (rel_Is, rest_const@[rel],rest_defs)
                  else (rel_Is, rest_const@[rel],rest_defs)
                | _ -> (rel_Is, rest_const@[rel],rest_defs)
            end
          | None -> (rel_Is, rest_const@[rel],rest_defs)
    in
    List.fold_left check_I_rel ([],[],reldefs) rels
  in
  let look_up_I_cond rel_Is reldefs=
    let pr1 = pr_list_ln CP.string_of_infer_rel in
    let pr2 = pr_list (pr_pair (pr_pair !CP.print_sv !CP.print_svl) !CP.print_formula) in
    Debug.no_2 "look_up_I_cond" pr1 pr1 (pr_triple pr2 pr1 pr1)
        (fun _ _ -> look_up_I_cond rel_Is reldefs) rel_Is reldefs
  in
  (* unfold into rhs *)
  let subst rel_const rels=
    let rels1 = List.map (fun (a,lhs,rhs) -> (a, lhs, replace_with_def rel_const rhs)) rels in
    rels1
  in
  let rec comp_fix rels_const reldefs pred_Is=
    let pr_pred_Is_1,rest_const = look_up_I rels_const in
    let pr_pred_Is_2,rest,rest_reldefs = look_up_I_cond rest_const reldefs in
    let pr_pred_Is = pr_pred_Is_1@pr_pred_Is_2 in
    if pr_pred_Is = [] then pred_Is
    else
      (* subst *)
      let n_reldefs = List.fold_left (fun acc (rel, p) -> subst (rel, p) acc) rest_reldefs pr_pred_Is in
      let n_reldefs1 = List.fold_left (fun acc (a, lhs,rhs) ->
          match CP.get_rel_id_list rhs with
            | [] -> begin
                 match CP.get_rel_id_list lhs with
                   | [] -> (*TOFIX: check impl*) acc
                   | ls -> acc@[(CP.RelAssume ls, lhs,rhs)]
              end
            | _ -> acc@[(a, lhs,rhs)]
      ) [] n_reldefs in
      let () = x_tinfo_hp (add_str "n_reldefs1" (pr_list_ln CP.string_of_infer_rel)) n_reldefs1 no_pos in
      let reloblgs, reldefns = List.partition (fun (rt,_,_) -> CP.is_rel_assume rt) n_reldefs1 in
      let n_pred_Is = List.map (fun ((id,_),_) -> id) pr_pred_Is in
      comp_fix reloblgs reldefns (CP.remove_dups_svl (pred_Is@n_pred_Is))
  in
  let reloblgs_init, reldefns = List.partition (fun (rt,_,_) -> CP.is_rel_assume rt) rels in
  comp_fix reloblgs_init reldefns []

let classify_ni prog rels=
  let pr1 = pr_list_ln CP.string_of_infer_rel in
  Debug.no_1 "classify_ni" pr1 !CP.print_svl
      (fun _ -> classify_ni prog rels) rels

let get_ni proc_name from_scc=
  let from_proc = List.find (fun from_p -> string_eq proc_name from_p.Cast.proc_name) from_scc in
  from_proc.Cast.proc_args_wi

let update_ni_scc scc from_scc=
  List.map (fun proc ->
      try
        let () = proc.Cast.proc_args_wi <- (get_ni proc.Cast.proc_name from_scc) in
        proc
      with _ -> proc
  ) scc
