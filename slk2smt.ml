open Globals
open Sleekcommons

let tbl_datadef : (string, string list) Hashtbl.t = Hashtbl.create 1

let cmds = ref ([] : command list)

let find_typ spl name =
  let (_, sv_info) = List.find (fun (id,sv_info) -> id = name) spl in
  string_of_typ sv_info.Typeinfer.sv_info_kind


let rec process_exp e =
  match e with
    | Ipure.Var _ -> "?" ^ Iprinter.string_of_formula_exp e
    | _ ->
          let s = Iprinter.string_of_formula_exp e in
          if s = "null" then "nil" else s

let rec process_p_formula pf =
  match pf with
    | Ipure.Frm _ ->
          "frm"
    | Ipure.BConst _ ->
          ""
    | Ipure.BVar _ ->
          "bvar"
    | Ipure.SubAnn _ ->
          "subann"
    | Ipure.Lt _ ->
          "lt"
    | Ipure. Lte _ ->
          "lte"
    | Ipure.Gt _ ->
          "gt"
    | Ipure.Gte _ ->
          "gte"
    | Ipure.Neq _ ->
          "neq"
    | Ipure.EqMax _ ->
          "eqmax"
    | Ipure.EqMin _ ->
          "eqmin"
    | Ipure.LexVar _ ->
          "lexvar"
    | Ipure.BagIn _ ->
          "bagin"
    | Ipure.BagNotIn _ ->
          "bagnotin"
    | Ipure.BagSub _ ->
          "bagsub"
    | Ipure.BagMin _ ->
          "bagmin"
    | Ipure.BagMax _ ->
          "bagmax"
    | Ipure.VarPerm _ ->
          "varperm"
    | Ipure.ListIn _ ->
          "listin"
    | Ipure.ListNotIn _ ->
          "listnotin"
    | Ipure.ListAllN _ ->
          "listalln"
    | Ipure.ListPerm _ ->
          "listperm"
    | Ipure.Eq (e1, e2, _) ->
          "(= " ^ (process_exp e1) ^ " " ^ (process_exp e2) ^ ")\n"
    | Ipure.XPure _ ->
          "(xpure)"
    | Ipure.RelForm (id, el, _) ->
          "(" ^ id ^ ")"

let rec process_pure_formula pf =
  match pf with
    | Ipure.BForm ((pf, _), _) ->
          process_p_formula pf
    | _ -> ""

let rec process_h_formula hf =
  match hf with
    | Iformula.Phase p ->
          process_h_formula p.Iformula.h_formula_phase_rw
    | Iformula.Conj _ -> "(conj )"
    | Iformula.ConjStar _ -> "(conjstar )"
    | Iformula.ConjConj _ -> "(conjconj )"
    | Iformula.Star s ->
          "(ssep " ^ (process_h_formula s.Iformula.h_formula_star_h1) ^ " " ^ (process_h_formula s.Iformula.h_formula_star_h2) ^ ")"
    | Iformula.StarMinus _ -> "(starminus )"
    | Iformula.HeapNode hn ->
          let heap_name = hn.Iformula.h_formula_heap_name in
          let (id,_) = hn.Iformula.h_formula_heap_node in
          let s =
            try
              let stl = Hashtbl.find tbl_datadef heap_name in
              let args =
                if (List.length stl > 1) then
                  "(sref " ^ (List.fold_left (fun s (id, exp) -> s ^ "(ref " ^ id ^ " "  ^ (process_exp exp) ^ ") ") "" (List.combine stl hn.Iformula.h_formula_heap_arguments)) ^ ")"
                else
                  (List.fold_left (fun s (id, exp) -> s ^ " (ref " ^ id ^ " "  ^ (process_exp exp) ^ ")") "" (List.combine stl hn.Iformula.h_formula_heap_arguments))
              in "(pto ?" ^ id ^ args  ^ ")"
            with Not_found -> "(" ^ heap_name ^ " ?" ^ id ^ (List.fold_left (fun s exp -> s ^ " " ^ (process_exp exp)) "" hn.Iformula.h_formula_heap_arguments) ^ ")"
          in s
    | Iformula.HeapNode2 hn2 ->
          let heap_name = hn2.Iformula.h_formula_heap2_name in
          let (id,_) = hn2.Iformula.h_formula_heap2_node in
          let s =
            try
              let stl = Hashtbl.find tbl_datadef heap_name in
              let args =
                if (List.length stl > 1) then
                  "(sref " ^ (List.fold_left (fun s (id, exp) -> s ^ "(ref " ^ id ^ " "  ^ (process_exp exp) ^ ") ") "" hn2.Iformula.h_formula_heap2_arguments) ^ ")"
                else
                  (List.fold_left (fun s (id, exp) -> s ^ " (ref " ^ id ^ " " ^ (process_exp exp) ^ ")") "" hn2.Iformula.h_formula_heap2_arguments)
              in "(pto ?" ^ id ^ args  ^ ")"
            with Not_found -> "(" ^ heap_name ^ " ?" ^ id ^ (List.fold_left (fun s (_,exp) -> s ^ " " ^ (process_exp exp)) "" hn2.Iformula.h_formula_heap2_arguments) ^ ")"
          in s
    | Iformula.ThreadNode _ -> "(threadnode )"
    | Iformula.HRel _ -> "(hrel )"
    | Iformula.HTrue -> "(htrue )"
    | Iformula.HFalse -> "(hfalse )"
    | Iformula.HEmp -> ""

let rec process_formula f spl =
  match f with
    | Iformula.Base fb ->
          let fbs1 = process_h_formula fb.Iformula.formula_base_heap in
          let fbs2 = process_pure_formula fb.Iformula.formula_base_pure in
          fbs1 ^ fbs2
    | Iformula.Exists fe ->
          let fes1 = "(exists " in
          let fes2 = "(" ^ (List.fold_left (fun s (id, p) -> s ^ "(?" ^ id ^ " " ^ (find_typ spl id)  ^ ")") "" fe.Iformula.formula_exists_qvars)  ^ ")" in
          let fes3 = process_h_formula fe.Iformula.formula_exists_heap in
          let fes4 =  " (tobool " ^ fes3 ^  ")\n" in
          fes1 ^ fes2 ^ fes4
    | Iformula.Or _ -> "(for )\n"

let rec process_struct_formula sf spl =
  match sf with
    | Iformula.ECase _ -> "(ecase )\n"
    | Iformula.EBase sbf ->
          process_formula sbf.Iformula.formula_struc_base spl
    | Iformula.EAssume _ -> "(eassume )\n"
    | Iformula.EInfer _ -> "(einfer )\n"
    | Iformula.EList sfl ->
          "(or\n" ^ (List.fold_left (fun s (_,sf) -> s ^ (process_struct_formula sf spl)) "" sfl) ^ ")"

let process_pred_name pred_name =
  "\n(declare-fun " ^ pred_name

let process_pred_vars pred_vars pred_formula spl =
  let find_typ spl name =
    let (_, sv_info) = List.find (fun (id,sv_info) -> id = name) spl in
    string_of_typ sv_info.Typeinfer.sv_info_kind
  in
  let s1 = " ((?self " ^ (find_typ spl "self") ^ ")" in
  let s2 = (List.fold_left (fun s v -> s ^ " (?" ^ v ^ " " ^ (find_typ spl v) ^ ")") "" pred_vars) ^ ")\n" in
  s1 ^ s2

let process_pred_def pdef iprog =
  let pred_name = pdef.I.view_name in
  let pred_vars = pdef.I.view_vars in
  let pred_formula = pdef.I.view_formula in
  let spl = Typeinfer.gather_type_info_struc_f iprog pred_formula [] in
  let s1 = process_pred_name pred_name in
  let s2 = process_pred_vars pred_vars pred_formula spl in
  let s3 = (process_struct_formula pred_formula spl) in
  s1 ^ s2 ^ "Space (tospace\n" ^ s3 ^ "))\n"

let process_data_name data_name =
  ("\n(declare-sort " ^ data_name ^ " 0)\n")

let process_data_fields data_name data_fields =
  List.fold_left (fun (s,st_list) ((typ,field_name),_,_,_) ->
      let st = string_of_typ typ in
      let field_name_list = st_list@[field_name] in
      let s = s ^ ("(declare-fun " ^ field_name ^ " () (Field " ^ data_name ^ " " ^ st ^ "))\n")
      in (s,field_name_list)
  ) ("",[]) data_fields

let process_data_def ddef =
  let data_name = ddef.I.data_name in
  let data_fields = ddef.I.data_fields in
  let s1 = process_data_name data_name in
  let (s2, field_name_list) = process_data_fields data_name data_fields in
  let _ = Hashtbl.add tbl_datadef data_name field_name_list in
  s1 ^ s2

let process_iante iante iprog =
  let s1 = "(assert (tobool\n" in
  let s2 = match iante with
    | MetaVar id -> "(?" ^ id ^ ")"
    | MetaForm f -> process_formula f []
    | MetaEForm ef -> process_struct_formula ef []
    | _ -> ""
  in
  let s3 = "\n))\n" in
  s1 ^ s2 ^ s3

let process_iconseq iconseq iprog =
  let s1 = "(assert (not (tobool\n" in
  let s2 = match iconseq with
    | MetaVar id -> "(?" ^ id ^ ")"
    | MetaForm f -> process_formula f []
    | MetaEForm ef -> process_struct_formula ef []
    | _ -> ""
  in
  let s3 = "\n)))\n" in
  s1 ^ s2 ^ s3

let process_entail (iante, iconseq, etype) iprog =
  let spl1 = match iante with
    | MetaForm f ->
          Typeinfer.gather_type_info_formula iprog f [] true
    | _ -> []
  in
  let spl2 = match iconseq with
    | MetaForm f ->
          Typeinfer.gather_type_info_formula iprog f [] true
    | _ -> []
  in
  let spl = spl1@spl2 in
  let s0 = List.fold_left (fun s0 (id,sv_info) ->
      s0 ^ "(declare-fun " ^ id ^ " () " ^ (string_of_typ sv_info.Typeinfer.sv_info_kind) ^ ")\n"
  ) "" spl in
  let s1 = process_iante iante iprog in
  let s2 = process_iconseq iconseq iprog in
  "\n" ^ s0 ^ "\n" ^ s1 ^ "\n" ^ s2 ^ "\n(check-sat)"

let process_cmd cmd iprog =
  match cmd with
    | DataDef ddef -> process_data_def ddef
    | PredDef pdef -> process_pred_def pdef iprog
    | EntailCheck eche -> process_entail eche iprog
    | _ -> ";other command\n"

let trans_smt iprog cprog cmds =
  let s = List.fold_left (fun s cmd -> s ^ (process_cmd cmd iprog)) "" cmds in
  let _ = print_endline (s ^ "\n") in
  true
