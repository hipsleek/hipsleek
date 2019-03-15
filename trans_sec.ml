#include "xdebug.cppo"
open Gen
open VarGen

let filter_not f xs = List.filter (fun x -> not (f x)) xs

let is_sec_spec_var (Cpure.SpecVar (_, id, _)) = BatString.starts_with id "sec_"

let extract_spec_var_name (Cpure.SpecVar (_, id, _)) =
  try
    BatString.slice ~first:4 ~last:(BatString.rfind id "_") id
  with
  | _ -> report_error no_pos ("Unexpected spec var name for sec formula: " ^ id)

let spec_var_add_prime prime spec_var = Cpure.sp_add_prime spec_var prime

let extract_sec_var_id (Cpure.SpecVar (_, id, _)) =
  try
    BatString.slice ~first:(BatString.rfind id "_" + 1) ~last:(String.length id) id
    |> int_of_string
  with
  | _ -> report_error no_pos ("Unexpected spec var name for sec formula: " ^ id)

let rec norm_quant_sec_form f =
  let open Cpure in
  match f with
    | BForm _ -> f
    | And (f1, f2, loc) -> mkAnd (norm_quant_sec_form f1) (norm_quant_sec_form f2) loc
    | AndList _ ->  f
    | Or (f1, f2, flbl, loc) -> mkOr (norm_quant_sec_form f1) (norm_quant_sec_form f2) flbl loc
    | Not (f, lbl, loc) -> mkNot (norm_quant_sec_form f) lbl loc
    | Forall (v, f, lbl, loc) -> if is_sec_spec_var v then (norm_quant_sec_form f) else mkForall [v] (norm_quant_sec_form f) lbl loc
    | Exists (v, f, lbl, loc) -> if is_sec_spec_var v then (norm_quant_sec_form f) else mkExists [v] (norm_quant_sec_form f) lbl loc
    | SecurityForm _ -> f

let norm_disj_sec_form : Cpure.formula -> Cpure.formula list list =
  fun f ->
  let open Cpure in
  let df  = split_disjunctions f in
  let cdf = List.map split_conjunctions df in
  y_binfo_hp (add_str "cdf: " (pr_list (pr_list !Cpure.print_formula))) cdf;
  let rec helper_conj cf df : (formula list) list =
    match df with
    | [] -> []
    | f::rf ->
      match f with
      | Or (f1, f2, flbl, loc) ->
        let nf = List.filter (fun x -> x <> f) cf in
        [f1::nf; f2::nf]
      | _ ->
        let res_f = helper_conj cf rf in
        List.map (fun x -> f::x) res_f
  in
  let rec helper_disj cdf : (formula list) list =
    match cdf with
    | [] -> []
    | df::rdf -> (helper_conj df df)@(helper_disj rdf)
  in
  let rec fix x =
    let cdf = helper_disj x in
    if x = cdf then x else fix cdf
  in
  fix cdf

let rev_translate_sec_from_infer f =
  let fold_right f acc xs = List.fold_right f xs acc in
  let is_translated_sec_formula f =
    Cpure.fv f
    |> List.exists is_sec_spec_var
  in
  let is_valid_translated_sec_p_formula f =
    let open Cpure in
    match f with
      | Gte (IConst (i, _), Var (SpecVar (_, id, _), _), _)
      | Gte (Var (SpecVar (_, id, _), _), IConst (i, _), _) ->
          (i = 0 || i = 1) && BatString.starts_with id "sec_"
      | Eq (Var (SpecVar (_, id, _), _), IConst (i, _), _) ->
          (i = 0 || i = 1) && BatString.starts_with id "sec_"
      | Lte (IConst (i, _), Var (SpecVar (_, id, _), _), _)
      | Lte (Var (SpecVar (_, id, _), _), IConst (i, _), _) ->
          (i = 0 || i = 1) && BatString.starts_with id "sec_"
      | Lt (Var (SpecVar (_, id1, _), _), Var (SpecVar (_, id2, _), _), _)
      | Lte (Var (SpecVar (_, id1, _), _), Var (SpecVar (_, id2, _), _), _)
      | Eq (Var (SpecVar (_, id1, _), _), Var (SpecVar (_, id2, _), _), _) ->
          BatString.starts_with id1 "sec_" && BatString.starts_with id2 "sec_"
      | LexVar _ -> true
      | _ ->
          let () = y_binfo_hp (add_str "Not valid translated p formula: " !Cpure.print_p_formula) f in
          false
  in
  let rec is_valid_translated_sec_formula f =
    let open Cpure in
    match f with
      | BForm ((pf, bf_ann), flbl) -> is_valid_translated_sec_p_formula pf
      | And (f1, f2, loc) -> is_valid_translated_sec_formula f1 && is_valid_translated_sec_formula f2
      | AndList formulas ->  List.for_all (fun (_, f) -> is_valid_translated_sec_formula f) formulas
      | Or (f1, f2, flbl, loc) -> is_valid_translated_sec_formula f1 && is_valid_translated_sec_formula f2
      | Not (f, lbl, loc) -> is_valid_translated_sec_formula f
      | Forall (v, f, lbl, loc) -> is_valid_translated_sec_formula f
      | Exists (v, f', lbl, loc) ->
          let () = y_binfo_hp (add_str "unnormalised: " !print_formula) f in
          let norm = norm_quant_sec_form f in
          let () = y_binfo_hp (add_str "normalised: " !print_formula) norm in
          let res = is_valid_translated_sec_formula norm in
          let () = y_binfo_hp (add_str "exists valid? " string_of_bool) res in
          res
      | SecurityForm (lbl, f, loc) -> is_valid_translated_sec_formula f
  in
  let create_security_formula formulas =
    let open Cpure in
    List.map
      (function
        | Gte (IConst (i, pos1), Var (v, pos2), pos3) ->
            mkLte (mkVar v pos2) (mkIConst i pos1) pos3
        | Gte (Var (v, pos1), IConst (i, pos2), pos3) ->
            mkLte (mkIConst i pos2) (mkVar v pos1) pos3
        | Eq (Var (v1, pos1), Var (v2, pos2), pos3)
        | Lt (Var (v1, pos1), Var (v2, pos2), pos3) ->
            mkLte (mkVar v1 pos1) (mkVar v2 pos2) pos3
        | f -> f)
      formulas
    |> List.filter
        (fun f -> match f with
          | Eq _ -> true
          | Lte (Var (SpecVar (_, id1, _), _), Var (SpecVar (_, id2, _), _), _) -> true
          | Lte (Var (SpecVar (_, id, _), _), IConst (i, _), _) -> true
          | _ -> false)
    |> BatList.group
        (fun f1 f2 ->
          match f1, f2 with
            | Eq (Var (v1, _), IConst (i1, _), _), Eq (Var (v2, _), IConst (i2, _), _) ->
                compare (extract_spec_var_name v1) (extract_spec_var_name v2)
            | Lte (Var (v1, _), IConst (i1, _), _), Lte (Var (v2, _), IConst (i2, _), _) ->
                compare (extract_spec_var_name v1) (extract_spec_var_name v2)
            | Lte (Var (v1, _), Var (v2, _), _), Lte (Var (v3, _), Var (v4, _), _) ->
                let v1_name = extract_spec_var_name v1 in
                let v2_name = extract_spec_var_name v2 in
                let v3_name = extract_spec_var_name v3 in
                let v4_name = extract_spec_var_name v4 in
                if v1_name = v3_name then
                  compare v2_name v4_name
                else
                  compare v1_name v3_name
            | _, _ -> compare f1 f2
        )
    |> fold_right
        (fun f_list acc ->
          (* let () = y_binfo_hp (add_str "f list" (pr_list !Cpure.print_p_formula)) f_list in *)
          match List.hd f_list with
            | Eq (Var v1, IConst (i1, _), _) ->
                let id_val_pairs =
                  List.map
                    (function
                      | Eq (Var (v1, _), IConst (i, _), _) -> (extract_sec_var_id v1, i)
                      | f -> report_error no_pos (__LOC__ ^ "Unexpected formula when creating security formula: " ^ !Cpure.print_p_formula f))
                    f_list in
                let label =
                  BatList.init (Security.representation_tuple_length !Security.current_lattice) ((+) 1)
                  |> fold_right
                      (fun i acc ->
                        match BatList.find_opt (fun (id, v) -> id = i) id_val_pairs with
                        | Some (id, v) -> v :: acc
                        | None -> 1 :: acc
                      )
                      []
                  |> Security.representation_to_label !Security.current_lattice
                  |> Cpure.sec_label in
                let spec_var =
                  match List.hd f_list with
                  | Eq (Var (v1, _), IConst (i, _), _) ->
                    extract_spec_var_name v1
                    |> Cpure.mk_spec_var
                    |> spec_var_add_prime (Cpure.primed_of_spec_var v1)
                  | f -> report_error no_pos (__LOC__ ^ "Unexpected formula when creating security formula: " ^ !Cpure.print_p_formula f) in
                Cpure.mk_sec_bform spec_var label no_pos :: acc
            | Lte (Var v1, IConst (i, _), _) ->
                let id_val_pairs =
                  List.map
                    (function
                      | Lte (Var (v1, _), IConst (i, _), _) -> (extract_sec_var_id v1, i)
                      | f -> report_error no_pos (__LOC__ ^ "Unexpected formula when creating security formula: " ^ !Cpure.print_p_formula f))
                    f_list in
                let label =
                  BatList.init (Security.representation_tuple_length !Security.current_lattice) ((+) 1)
                  |> fold_right
                      (fun i acc ->
                        match BatList.find_opt (fun (id, v) -> id = i) id_val_pairs with
                        | Some (id, v) -> v :: acc
                        | None -> 1 :: acc
                      )
                      []
                  |> Security.representation_to_label !Security.current_lattice
                  |> Cpure.sec_label in
                let spec_var =
                  match List.hd f_list with
                  | Lte (Var (v1, _), IConst (i, _), _) ->
                    extract_spec_var_name v1
                    |> Cpure.mk_spec_var
                    |> spec_var_add_prime (Cpure.primed_of_spec_var v1)
                  | f -> report_error no_pos (__LOC__ ^ "Unexpected formula when creating security formula: " ^ !Cpure.print_p_formula f) in
                Cpure.mk_sec_bform spec_var label no_pos :: acc
            | Lte (Var (v1, _), Var (v2, _), _) ->
                let v1_var =
                  extract_spec_var_name v1
                  |> Cpure.mk_spec_var
                  |> spec_var_add_prime (Cpure.primed_of_spec_var v1) in
                let v2_var =
                  extract_spec_var_name v2
                  |> Cpure.mk_spec_var
                  |> spec_var_add_prime (Cpure.primed_of_spec_var v2)in
                Cpure.mk_sec_bform v1_var (Cpure.sec_var v2_var) no_pos :: acc
            | f -> report_error no_pos (__LOC__ ^ "Unexpected formula when creating security formula: " ^ !Cpure.print_p_formula f)
        )
        []
  in
  (* let () = y_binfo_hp (add_str "f: " !Cpure.print_formula) f in *)
  (* let f = norm_quant_sec_form f in
  let disjunctions_of_conjunctions = norm_disj_sec_form f in *)
  let disjunctions = Cpure.split_disjunctions f in
  let disjunctions_of_conjunctions = List.map Cpure.split_conjunctions disjunctions in
  y_binfo_hp (add_str "disjunctions_of_conjunctions: " (pr_list (pr_list !Cpure.print_formula))) disjunctions_of_conjunctions;
  let res =
    List.map (List.partition is_translated_sec_formula) disjunctions_of_conjunctions
    |> fold_right
        (fun (sec_formulas, other_formulas) acc ->
          y_binfo_hp (add_str "sec forms: " (pr_list !Cpure.print_formula)) sec_formulas;
          if List.for_all is_valid_translated_sec_formula sec_formulas then
            let p_formulas =
              List.map
                (function
                  | Cpure.BForm ((pf, _), _) -> pf
                  | f -> report_error no_pos (__LOC__ ^ "Unexpected formula when extracting: " ^ !Cpure.print_formula f))
                sec_formulas in
            let rev_trans_sec_formula = create_security_formula p_formulas in
            (rev_trans_sec_formula @ other_formulas) :: acc
          else
            (Cpure.mkFalse no_pos :: other_formulas) :: acc
        )
        []
    |> List.map Cpure.join_conjunctions
    |> filter_not Cpure.isConstTrue
    |> Cpure.join_disjunctions in
  let () = y_binfo_hp (add_str "reverse translated" !Cpure.print_formula) res in
  res
