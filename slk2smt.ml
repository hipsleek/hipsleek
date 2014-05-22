open Globals
open Sleekcommons


let cmds = ref ([] : command list)

let process_data_def ddef =
  let s1 = ("(declare-sort " ^ ddef.I.data_name ^ " 0)\n") in
  let s2 = List.fold_left (fun s1 ((typ,id),_,_,_) ->
      s1 ^ ("(declare-fun " ^ id ^ " () (Field " ^ ddef.I.data_name ^ " " ^ (Globals.string_of_typ typ) ^ "))\n")) s1 ddef.I.data_fields in
  s2

let rec process_pure_formula pf =
  match pf with
    | Ipure.BForm ((pf, _), _) -> (
          match pf with
            | Ipure.Eq (e1, e2, _) ->
                  let s1 = match e1 with
                    | Ipure.Var _ -> "?" ^ Iprinter.string_of_formula_exp e1
                    | _ -> Iprinter.string_of_formula_exp e1
                  in
                  let s2 = match e2 with
                    | Ipure.Var _ -> "?" ^ Iprinter.string_of_formula_exp e2
                    | _ -> Iprinter.string_of_formula_exp e2
                  in
                  let s1 = if (s1 = "null") then "nil" else s1 in
                  let s2 = if (s2 = "null") then "nil" else s2 in
                  "(= " ^ s1 ^ " " ^ s2 ^ ")\n"
            | _ -> "later (base)\n"
      )
    | _ -> ""

let rec process_h_formula hf =
  match hf with
    | Iformula.Star _ -> " (ssep )"
    | Iformula.Conj _ -> " (conj )"
    | Iformula.ConjStar _ -> " (conj )"
    | Iformula.ConjConj _ -> " (conj )"
    | Iformula.HeapNode _ -> " (heapnode )"
    | Iformula.HeapNode2 _ -> " (heapnode2 )"
    | Iformula.HRel _ -> " (hrel )"
    | Iformula.Phase p -> " (phase )"
    | _ -> " (later )"

let rec process_formula f =
  match f with
    | Iformula.Base fb ->
          process_pure_formula fb.Iformula.formula_base_pure
    | Iformula.Exists fe ->
          let fes1 = "(exists " in
          let fes2 = "(" ^ (List.fold_left (fun s (id, p) -> s ^ "(?" ^ id ^ " )") "" fe.Iformula.formula_exists_qvars)  ^ ")" in
          let fes3 = process_h_formula fe.Iformula.formula_exists_heap in
          let fes4 =  " (tobool" ^ fes3 ^  ")\n" in
          fes1 ^ fes2 ^ fes4
    | _ -> ""

let rec process_struct_formula sf =
  match sf with
    | Iformula.EList sfl ->
          "(or\n" ^ (List.fold_left (fun s (_,sf) -> s ^ (process_struct_formula sf)) "" sfl) ^ ")"
    | Iformula.EBase sbf ->
          process_formula sbf.Iformula.formula_struc_base
    | _ -> ""

let process_pred_def pdef =
  let s1 = ("(declare-fun " ^ pdef.I.view_name ^ " ((?self )" ^ (List.fold_left (fun s v -> s ^ "(?" ^ v ^ " )") "" pdef.I.view_vars) ^ ")\n") in
  let s2 = s1 ^ "Space (tospace " in
  let s3 = s2 ^ (process_struct_formula pdef.I.view_formula) ^ "))" in
  let _ = print_endline (Iprinter.string_of_struc_formula pdef.I.view_formula) in
  let _ = List.iter (fun tid -> print_endline (Iprinter.string_of_typed_var tid)) pdef.I.view_typed_vars in
  s3

let process_cmd cmd =
  match cmd with
    | DataDef ddef -> process_data_def ddef
    | PredDef pdef -> process_pred_def pdef
    | _ -> ""

let trans_smt iprog cprog cmds =
  let s = List.fold_left (fun s cmd -> s ^ (process_cmd cmd)) "" cmds in
  let _ = print_endline s in
  true
