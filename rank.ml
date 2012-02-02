open Globals
module DD = Debug
open Gen
open Context
open Cpure

module Err = Error
module CP = Cpure
module MCP = Mcpure
module TP = Tpdispatcher

type rel_typ =
  | PosConst of exp
  | NegConst of exp
  | Zero
  | ConstVar of exp
  | NonLinear of formula
  | Undefined

let print_rel_typ rt = match rt with
  | PosConst e -> "DEC(" ^ (!print_exp e) ^ ")"
  | NegConst e -> "INC(" ^ (!print_exp e) ^ ")"
  | Zero -> "NC"
  | ConstVar e -> "VAR(" ^ (!print_exp e) ^ ")"
  | NonLinear _ -> "NONLINEAR"
  | Undefined -> "UNK"

let compute_rel (v1: exp) (v2: exp) (fml: formula) : rel_typ =
  Debug.ninfo_hprint (add_str "LHS: " !print_formula) fml no_pos;
  Debug.ninfo_hprint (add_str "v1: " !print_exp) v1 no_pos;
  Debug.ninfo_hprint (add_str "v2: " !print_exp) v2 no_pos;
  let eq_fml = mkEqExp v1 v2 no_pos in
  let check_zero = TP.imply_raw fml eq_fml in
  if check_zero then (Debug.ninfo_pprint "Zero" no_pos; Zero)
  else
    let disjs = list_of_disjs fml in
    let fml_ls = list_of_conjs (List.hd disjs) in
    let var_of_interest = (afv v1)@(afv v2) in
    let fml_of_interest = 
      List.filter (fun f -> (subset var_of_interest (fv f) && is_eq_fml f) || is_eq_const f var_of_interest) fml_ls in
    let fml_of_interest =
      List.filter (fun f -> List.for_all (fun d -> TP.imply_raw d f) (List.tl disjs)) fml_of_interest in
    Debug.ninfo_hprint (add_str "FML of interest: " (pr_list !print_formula)) fml_of_interest no_pos;
    match fml_of_interest with
      | [] -> (Debug.ninfo_pprint "Undefined" no_pos; Undefined)
      | [f] -> 
        let sv = SpecVar (Int, "Unknown", Unprimed) in
        let res = CP.mkAnd f (mkEqExp v1 (mkAdd v2 (mkVar sv no_pos) no_pos) no_pos) no_pos in
        let res = TP.simplify_raw (mkExists var_of_interest res None no_pos) in
        Debug.ninfo_hprint (add_str "RES: " !print_formula) res no_pos;
        let r = (match res with
          | CP.BForm (bf,_) ->
            (match bf with
            | (Eq (CP.Var (sv1,_), CP.IConst (i,p),_),_)
            | (Eq (CP.IConst (i,p), CP.Var (sv1,_),_),_) -> 
              if sv1 = sv & i > 0 then PosConst (CP.IConst (i,p)) else 
              if sv1 = sv & i < 0 then NegConst (CP.IConst (i,p)) else NonLinear res
            | (Eq (CP.Var (sv1,_), Subtract (IConst (0,_),CP.IConst (i,p),_),_),_)
            | (Eq (Subtract (IConst (0,_),CP.IConst (i,p),_), CP.Var (sv1,_),_),_) -> 
              if sv1 = sv & i > 0 then NegConst (CP.IConst (i,p)) else NonLinear res
            | (Eq (CP.Var (sv1,p1), CP.Var (sv2,p2),_),_) ->
              if sv1 = sv then ConstVar (CP.Var (sv2,p2)) else
              if sv2 = sv then ConstVar (CP.Var (sv1,p1)) else NonLinear res
            | _ -> NonLinear res)
          | _ -> NonLinear res
        ) in r
      | fs -> 
        if List.exists (fun f -> not (is_eq_const f var_of_interest)) fs then (Debug.ninfo_pprint "Undefined" no_pos; Undefined)
        else
          let sv = SpecVar (Int, "Unknown", Unprimed) in
          let res = conj_of_list (fs @ [(mkEqExp v1 (mkAdd v2 (mkVar sv no_pos) no_pos) no_pos)]) no_pos in
          let res = TP.simplify_raw (mkExists var_of_interest res None no_pos) in
          Debug.ninfo_hprint (add_str "RES: " !print_formula) res no_pos;
          let r = (match res with
            | CP.BForm (bf,_) ->
              (match bf with
              | (Eq (CP.Var (sv1,_), CP.IConst (i,p),_),_)
              | (Eq (CP.IConst (i,p), CP.Var (sv1,_),_),_) -> 
                if sv1 = sv & i > 0 then PosConst (CP.IConst (i,p)) else 
                if sv1 = sv & i < 0 then NegConst (CP.IConst (i,p)) else NonLinear res
              | (Eq (CP.Var (sv1,_), Subtract (IConst (0,_),CP.IConst (i,p),_),_),_)
              | (Eq (Subtract (IConst (0,_),CP.IConst (i,p),_), CP.Var (sv1,_),_),_) -> 
                if sv1 = sv & i > 0 then NegConst (CP.IConst (i,p)) else NonLinear res
              | (Eq (CP.Var (sv1,p1), CP.Var (sv2,p2),_),_) ->
                if sv1 = sv then ConstVar (CP.Var (sv2,p2)) else
                if sv2 = sv then ConstVar (CP.Var (sv1,p1)) else NonLinear res
              | _ -> NonLinear res)
            | _ -> NonLinear res
          ) in r

let compute_rank rhs lhs = match rhs with
  | CP.BForm (bf,_) ->
    (match bf with
    | (CP.Gt (CP.Func (_,args1,_), CP.Func (_,args2,_),_),_)
    | (CP.Lt (CP.Func (_,args2,_), CP.Func (_,args1,_),_),_) -> 
      if List.length args1 = List.length args2 then
        (* TODO: Add corresponding alias names for each pair of args sent to compute_rel *)
        (rhs, List.map2 (fun a1 a2 -> compute_rel a1 a2 lhs) args1 args2)
      else report_error no_pos "Two rank_dec have different number of args"
    | _ -> report_error no_pos "Unexpected formula")
  | _ -> report_error no_pos "Unexpected formula"













