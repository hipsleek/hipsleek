open Gen
open Globals
open Ipure
open Cpure

(* module FPERM = *)
(* struct *)
  type iperm = Ipure.exp option
  type cperm = Cpure.spec_var option
  type cperm_var = Cpure.spec_var
  let cperm_typ = Float
  let empty_iperm = None
  let empty_perm = None
  let full_iperm = Some (Ipure.FConst (1.0, no_pos))
  (*LDK: a specvar to indicate FULL permission*)
  let full_perm_name = ("Anon_"^"full_perm")
  let perm_name = ("perm_")
  let full_perm = Some (Cpure.SpecVar (cperm_typ, full_perm_name, Unprimed))
  let fv_iperm = Ipure.afv
  let get_iperm perm =
    match perm with
      | None -> []
      | Some f -> [f]
  let apply_one_iperm = Ipure.e_apply_one
  let full_perm_var = (Cpure.SpecVar (cperm_typ, full_perm_name, Unprimed))
(*LDK: a constraint to indicate FULL permission = 1.0*)
  let full_perm_constraint = Mcpure.OnePF (Cpure.BForm (((Cpure.Eq (
      (Cpure.Var (full_perm_var,no_pos)),
      (Cpure.FConst (1.0,no_pos)),
      no_pos
  )), None),None))
  let mkFullPerm_pure  f : Cpure.formula = 
    Cpure.BForm (((Cpure.Eq (
        (Cpure.Var (f,no_pos)),
        (Cpure.Var (full_perm_var,no_pos)),
        no_pos
    )),None), None)
  let mkFullPerm_pure_from_ident id : Cpure.formula = 
    let var = (Cpure.SpecVar (cperm_typ, id, Unprimed)) in
    mkFullPerm_pure var
(*create fractional permission invariant 0<f<=1*)
  let mkPermInv (f:Cpure.spec_var) : Cpure.formula =
    let upper = 
      Cpure.BForm (((Cpure.Lte (
          (Cpure.Var (f,no_pos)),
          (Cpure.FConst (1.0,no_pos)),
          no_pos
      )), None),None) in
    let lower =  Cpure.BForm (((Cpure.Gt (
        (Cpure.Var (f,no_pos)),
        (Cpure.FConst (0.0,no_pos)),
        no_pos
    )), None),None) in
    let inv = 
      (Cpure.And (lower,upper,no_pos)) in
    inv
  let mkPermWrite (f:Cpure.spec_var) : Cpure.formula =
    Cpure.BForm (((Cpure.Eq (
        (Cpure.Var (f,no_pos)),
        (Cpure.FConst (1.0,no_pos)),
        no_pos
    )),None),None)
  let float_out_iperm perm pos = 
    match perm with
      | None -> (None, [])
      | Some f -> match f with
            | Ipure.Var _ -> (Some f,[])
		    | _ ->
                let nn_perm = ((perm_name^(string_of_int pos.start_pos.Lexing.pos_lnum)^(fresh_trailer ())),Unprimed) in
			    let nv_perm = Ipure.Var (nn_perm,pos) in
                let npf_perm = Ipure.BForm ((Ipure.Eq (nv_perm,f,pos), None), None) in (*TO CHECK: slicing for permissions*)
                (Some nv_perm,[(nn_perm,npf_perm)])
  let float_out_mix_max_iperm perm pos =
    match perm with
      | None -> (None, None)
      | Some f -> 
	      match f with
		    | Ipure.Null _
		    | Ipure.IConst _
		    | Ipure.Var _ -> (Some f, None)
		    | _ ->
		        let new_name_perm = fresh_var_name "ptr" pos.start_pos.Lexing.pos_lnum in
		        let nv_perm = Ipure.Var((new_name_perm, Unprimed), pos) in
			    (Some nv_perm, Some (Ipure.float_out_pure_min_max (Ipure.BForm ((Ipure.Eq (nv_perm, f, pos), None), None))))
  let fv_cperm perm =
    match perm with
      | None -> []
      | Some f -> [f]

  let get_cperm perm =
    match perm with
      | None -> []
      | Some f -> [f]
  let subst_var_perm ((fr, t) as s) perm =
    map_opt (Cpure.subst_var s) perm
  let fresh_cperm_var = Cpure.fresh_spec_var
  let mkEq_cperm v1 v2 pos =
    Cpure.mkEq_b (Cpure.mkVar v1 pos) ( Cpure.mkVar v2 pos) pos
(* end;; *)
