open Gen
open Globals
open Ipure
open Cpure

(* module CPERM = *)
(* struct *)
  type iperm = Ipure.exp option
  type cperm = Cpure.spec_var option
  type cperm_var = Cpure.spec_var
  let cperm_typ = Int
  let empty_iperm = None
  let empty_perm = None
  let full_iperm = Some (Ipure.IConst (1, no_pos))
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
  (*LDK: a constraint to indicate FULL permission = 0*)
  let full_perm_constraint = 
    (* let _ =   print_string ("fperm.ml: cperm = " ^ string_of_bool !Globals.allow_cperm   *)
    (*                         ^ " fperm =" ^ string_of_bool !Globals.allow_fperm *)
    (*                         ^ "\n") in *)
Mcpure.OnePF (Cpure.BForm (((Cpure.Eq (
      (Cpure.Var (full_perm_var,no_pos)),
      (Cpure.IConst (0,no_pos)),
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
(*create counting permission invariant c >=-1*)
  let mkPermInv (f:Cpure.spec_var) : Cpure.formula =
    let p_f = Cpure.mkGte (Cpure.Var (f,no_pos)) (Cpure.IConst (-1,no_pos)) no_pos in
    let b_f = (p_f,None) in
    Cpure.BForm (b_f,None)
  let mkPermWrite (f:Cpure.spec_var) : Cpure.formula =
    Cpure.BForm (((Cpure.Eq (
        (Cpure.Var (f,no_pos)),
        (Cpure.IConst (0,no_pos)),
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
