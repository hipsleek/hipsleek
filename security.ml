module CP = Cpure
module CF = Cformula

open Gen

let modified_variables e =
  let rec local_modified_and_declared_vars = function
    | Cast.Label {
        Cast.exp_label_type = _;
        Cast.exp_label_path_id = _;
        Cast.exp_label_exp = e } ->
        local_modified_and_declared_vars e
    | Cast.Assign {
        Cast.exp_assign_lhs = v;
        Cast.exp_assign_rhs = _;
        Cast.exp_assign_pos = _ } ->
        [v], []
    | Cast.Cond {
        Cast.exp_cond_type = _;
        Cast.exp_cond_condition = _;
        Cast.exp_cond_then_arm = e1;
        Cast.exp_cond_else_arm = e2;
        Cast.exp_cond_path_id = _;
        Cast.exp_cond_pos = _ } ->
        let mod_e1, local_e1 = local_modified_and_declared_vars e1 in
        let mod_e2, local_e2 = local_modified_and_declared_vars e2 in
        mod_e1 @ mod_e2, local_e1 @ local_e2
    | Cast.Seq {
        Cast.exp_seq_type = _;
        Cast.exp_seq_exp1 = e1;
        Cast.exp_seq_exp2 = e2;
        Cast.exp_seq_pos = _ } ->
        let mod_e1, local_e1 = local_modified_and_declared_vars e1 in
        let mod_e2, local_e2 = local_modified_and_declared_vars e2 in
        mod_e1 @ mod_e2, local_e1 @ local_e2
    | Cast.Block {
        Cast.exp_block_type = _;
        Cast.exp_block_body = e;
        Cast.exp_block_local_vars = local_v;
        Cast.exp_block_pos } ->
        let mod_e, local_e = local_modified_and_declared_vars e in
        mod_e, local_e @ List.map snd local_v
    | _ -> [], []
  in
  let modified, local = local_modified_and_declared_vars e in
  BList.difference_eq (=) modified local

let update_security_formula_for ?(add_label=false) var new_lbl formula =
  let spec_var = CP.sec_spec_var @@ CP.mk_primed_spec_var var in

  let update_sec_p_form = function
    | CP.Security (sec_f, loc) as spf -> begin match sec_f with
        | CP.VarBound (v, lbl) ->
            if CP.eq_spec_var spec_var v then
              CP.mk_security v (if not add_label then new_lbl else CP.lub lbl new_lbl) loc
            else
              spf
      end
    | pf -> pf
  in

  let rec update_sec_form = function
    | CP.BForm ((pf, l1), l2) -> CP.BForm ((update_sec_p_form pf, l1), l2)
    | CP.And (f1, f2, pos) -> CP.And (update_sec_form f1, update_sec_form f2, pos)
    | CP.AndList fs -> CP.AndList (List.map (fun (lbl, f) -> (lbl, update_sec_form f)) fs)
    | CP.Or (f1, f2, lbl, pos) -> CP.Or (update_sec_form f1, update_sec_form f2, lbl, pos)
    | CP.Not (f, lbl, pos) -> CP.Not (update_sec_form f, lbl, pos)
    | CP.Forall (v, f, lbl, pos) -> CP.Forall (v, update_sec_form f, lbl, pos)
    | CP.Exists (v, f, lbl, pos) -> CP.Exists (v, update_sec_form f, lbl, pos)
    | CP.SecurityForm (lbl, f, pos) -> CP.SecurityForm (lbl, update_sec_form f, pos)
  in

  CF.transform_pure update_sec_form formula

let is_security_spec_var v = BatString.starts_with (CP.name_of_spec_var v) "sec_"

let is_security_p_formula = function
  | CP.Security _ -> true
  | _ -> false

let is_security_formula = function
  | CP.BForm ((pf, _), _) -> is_security_p_formula pf
  | _ -> false

let extract_security_formulas f =
  let formulas = CP.split_conjunctions f in
  let security_formulas, other_formulas = List.partition is_security_formula formulas in
  security_formulas, CP.join_conjunctions other_formulas
