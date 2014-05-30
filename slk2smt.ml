open Globals
open Sleekcommons
open Gen
open Cformula

let smt_number = ref (0:int)

let subst_pred_self = ref (true: bool)

let smt_self =  ("in": string)
let pred_pre_fix_var =  ref ("?": string)

let reset_smt_number () =
  smt_number :=0

let fresh_number () =
  smt_number := !smt_number + 1;
  !smt_number

let tbl_datadef : (string, string list) Hashtbl.t = Hashtbl.create 1

let smt_cmds = ref ([] : command list)

let smt_ent_cmds = ref ([] : (meta_formula * meta_formula * entail_type * Cformula.formula * Cformula.struc_formula ) list)

let find_typ spl name =
  let (_, sv_info) = List.find (fun (id,sv_info) -> id = name) spl in
  string_of_typ sv_info.Typeinfer.sv_info_kind


let rec process_exp pre_fix_var e =
  match e with
    | Ipure.Var _ -> pre_fix_var ^ Iprinter.string_of_formula_exp e
    | _ ->
          let s = Iprinter.string_of_formula_exp e in
          if s = "null" then "nil" else s

let rec process_p_formula pre_fix_var pf =
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
          "(= " ^ (process_exp pre_fix_var e1) ^ " " ^ (process_exp pre_fix_var e2) ^ ")\n"
    | Ipure.XPure _ ->
          "(xpure)"
    | Ipure.RelForm (id, el, _) ->
          "(" ^ id ^ ")"

let rec process_pure_formula pre_fix_var pf =
  match pf with
    | Ipure.BForm ((pf, _), _) ->
          process_p_formula pre_fix_var pf
    | _ -> ""

let rec process_h_formula pre_fix_var hf all_view_names pred_abs_num=
  let recf hf1 n =  process_h_formula pre_fix_var hf1 all_view_names n in
  let recf_e = process_exp pre_fix_var in
  match hf with
    | Iformula.Phase p ->
          recf p.Iformula.h_formula_phase_rw pred_abs_num
    | Iformula.Conj _ -> "(conj )",pred_abs_num
    | Iformula.ConjStar _ -> "(conjstar )",pred_abs_num
    | Iformula.ConjConj _ -> "(conjconj )",pred_abs_num
    | Iformula.Star s ->
          let nhf1,n1 = recf s.Iformula.h_formula_star_h1 pred_abs_num in
          let nhf2,n2 = recf s.Iformula.h_formula_star_h2 n1 in
          "(ssep " ^ (nhf1) ^ " " ^ (nhf2) ^ ")", n2
    | Iformula.StarMinus _ -> "(starminus )",pred_abs_num
    | Iformula.HeapNode hn ->
          let (id,_) = hn.Iformula.h_formula_heap_node in
          let heap_name = hn.Iformula.h_formula_heap_name in
          let s_vnode, n_pred_abs_num = if Gen.BList.mem_eq (fun s1 s2 -> String.compare s1 s2 = 0)  heap_name all_view_names then
            "index alpha" ^ (string_of_int  pred_abs_num) ^ " ",  pred_abs_num+1 else "", pred_abs_num in
          let _ = Debug.ninfo_hprint (add_str "HeapNode" pr_id) (heap_name ^ s_vnode) no_pos in
           let s =
            try
              let stl = Hashtbl.find tbl_datadef heap_name in
              let args =
                if (List.length stl > 1) then
                  "(sref " ^ (List.fold_left (fun s (id, exp) -> s ^ "(ref " ^ id ^ " "  ^ (recf_e exp) ^ ") ") "" (List.combine stl hn.Iformula.h_formula_heap_arguments)) ^ ")"
                else
                  (List.fold_left (fun s (id, exp) -> s ^ " (ref " ^ id ^ " "  ^ (recf_e exp) ^ ")") "" (List.combine stl hn.Iformula.h_formula_heap_arguments))
              in "(pto " ^ pre_fix_var  ^ id ^ args  ^ ")"
            with Not_found -> "(" ^ heap_name ^ " " ^ pre_fix_var ^ id ^ (List.fold_left (fun s exp -> s ^ " " ^ (recf_e exp)) "" hn.Iformula.h_formula_heap_arguments) ^ ")"
          in ("(" ^ s_vnode ^ s ^ ")"),n_pred_abs_num
    | Iformula.HeapNode2 hn2 -> "HeapNode2",pred_abs_num
          (* let heap_name = hn2.Iformula.h_formula_heap2_name in *)
          (* let _ = Debug.ninfo_hprint (add_str "HeapNode2" pr_id) heap_name no_pos in *)
          (* let (id,_) = hn2.Iformula.h_formula_heap2_node in *)
          (* let s = *)
          (*   try *)
          (*     let stl = Hashtbl.find tbl_datadef heap_name in *)
          (*     let args = *)
          (*       if (List.length stl > 1) then *)
          (*         "(sref " ^ (List.fold_left (fun s (id, exp) -> s ^ "(ref " ^ id ^ " "  ^ (recf_e exp) ^ ") ") "" hn2.Iformula.h_formula_heap2_arguments) ^ ")" *)
          (*       else *)
          (*         (List.fold_left (fun s (id, exp) -> s ^ " (ref " ^ id ^ " " ^ (recf_e exp) ^ ")") "" hn2.Iformula.h_formula_heap2_arguments) *)
          (*     in "(pto " ^ pre_fix_var ^ id ^ args  ^ ")" *)
          (*   with Not_found -> "(" ^ heap_name ^ " " ^ pre_fix_var ^ id ^ (List.fold_left (fun s (_,exp) -> s ^ " " ^ (recf_e exp)) "" hn2.Iformula.h_formula_heap2_arguments) ^ ")" *)
          (* in s *)
    | Iformula.ThreadNode _ -> "(threadnode )",pred_abs_num
    | Iformula.HRel _ -> "(hrel )",pred_abs_num
    | Iformula.HTrue -> "(htrue )",pred_abs_num
    | Iformula.HFalse -> "(hfalse )",pred_abs_num
    | Iformula.HEmp -> "",pred_abs_num

let rec process_formula pre_fix_var f spl all_view_names start_pred_abs_num=
  match f with
    | Iformula.Base fb ->
          let fbs1,n2 = process_h_formula pre_fix_var fb.Iformula.formula_base_heap all_view_names start_pred_abs_num in
          let fbs2 = process_pure_formula pre_fix_var fb.Iformula.formula_base_pure in
          fbs1 ^ fbs2,n2
    | Iformula.Exists fe ->
          let fes1 = "(exists " in
          let fes2 = "(" ^ (List.fold_left (fun s (id, p) ->
              s ^ "(" ^ pre_fix_var ^ id ^ " " ^ (find_typ spl id)  ^ ")") "" fe.Iformula.formula_exists_qvars)  ^ ")" in
          let fes3,n2 = process_h_formula pre_fix_var fe.Iformula.formula_exists_heap all_view_names start_pred_abs_num in
          let fes4 =  " (tobool " ^ fes3 ^  ")\n" in
          fes1 ^ fes2 ^ fes4,n2
    | Iformula.Or _ -> "(for )\n",start_pred_abs_num

let rec process_struct_formula pre_fix_var sf spl all_view_names start_pred_abs_num=
  match sf with
    | Iformula.ECase _ -> "(ecase )\n",start_pred_abs_num
    | Iformula.EBase sbf ->
          process_formula pre_fix_var sbf.Iformula.formula_struc_base spl all_view_names start_pred_abs_num
    | Iformula.EAssume _ -> "(eassume )\n",start_pred_abs_num
    | Iformula.EInfer _ -> "(einfer )\n",start_pred_abs_num
    | Iformula.EList sfl ->
          let s,n2 = List.fold_left (fun (s,n) (_,sf) ->
              let s_struc,n1 =  process_struct_formula pre_fix_var sf spl all_view_names n in
              s ^ (s_struc), n1
          ) ("",start_pred_abs_num) sfl in
          "(or\n" ^ (s) ^ ")", n2

let process_pred_name pred_name =
  "\n(declare-fun " ^ pred_name

let find_typ spl name =
  let (_, sv_info) = List.find (fun (id,sv_info) -> id = name) spl in
  sv_info.Typeinfer.sv_info_kind


let process_pred_vars pre_fix_var self_sv self_typ pred_vars pred_formula spl =
  let find_typ spl name =
    let (_, sv_info) = List.find (fun (id,sv_info) -> id = name) spl in
    string_of_typ sv_info.Typeinfer.sv_info_kind
  in
  let s1 = " ((" ^ pre_fix_var  ^ self_sv ^ " " ^ ( string_of_typ self_typ) ^ ")" in
  let s2 = (List.fold_left (fun s v -> s ^ " (" ^ pre_fix_var ^ v ^ " " ^ (find_typ spl v) ^ ")") "" pred_vars) ^ ")\n" in
  s1 ^ s2

let process_pred_def subst_self pdef iprog =
  let pred_name = pdef.I.view_name in
  let pred_vars = pdef.I.view_vars in
  let spl = Typeinfer.gather_type_info_struc_f iprog pdef.I.view_formula [] in
  let self_typ = find_typ spl self in
  let pred_formula, self_sv = if subst_self then
    let sst = [((self, Unprimed),(smt_self, Unprimed))] in
    (Iformula.subst_struc sst pdef.I.view_formula, smt_self)
  else (pdef.I.view_formula, self)
  in
  let _ = Debug.ninfo_hprint (add_str "pred_formula" Iprinter.string_of_struc_formula) pred_formula no_pos in
  let s1 = process_pred_name pred_name in
  let s2 = process_pred_vars !pred_pre_fix_var self_sv self_typ pred_vars pred_formula spl in
  let s3,_ = (process_struct_formula !pred_pre_fix_var pred_formula spl [] 0) in
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

let process_iante iante iprog all_view_names start_pred_abs_num=
  let s1 = "(assert (tobool\n" in
  let s2, n2 = match iante with
    | MetaVar id -> "(?" ^ id ^ ")",start_pred_abs_num
    | MetaForm f ->
          let spl = Typeinfer.gather_type_info_formula iprog f [] true in
          process_formula "" f spl all_view_names start_pred_abs_num
    | MetaEForm ef ->
          let spl = Typeinfer.gather_type_info_struc_f iprog ef [] in
          process_struct_formula "" ef spl all_view_names start_pred_abs_num
    | _ -> "",start_pred_abs_num
  in
  let s3 = "\n))\n" in
  (s1 ^ s2 ^ s3,n2)

let process_iconseq iconseq iprog all_view_names start_pred_abs_num =
  let s1 = "(assert (not (tobool\n" in
  let s2,n2 = match iconseq with
    | MetaVar id -> "(?" ^ id ^ ")",start_pred_abs_num
    | MetaForm f ->
          let spl = Typeinfer.gather_type_info_formula iprog f [] true in
          process_formula "" f spl all_view_names start_pred_abs_num
    | MetaEForm ef ->
          let spl = Typeinfer.gather_type_info_struc_f iprog ef [] in
          process_struct_formula "" ef spl all_view_names start_pred_abs_num
    | _ -> "",start_pred_abs_num
  in
  let s3 = "\n)))\n" in
  s1 ^ s2 ^ s3,n2

let process_entail (iante, iconseq, etype) iprog cprog =
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
  let all_view_names = List.map (fun vdecl -> vdecl.Cast.view_name) cprog.Cast.prog_view_decls in
  let s1,n1 = process_iante iante iprog all_view_names 0 in
  let s2,_ = process_iconseq iconseq iprog all_view_names n1 in
  "\n" ^ s0 ^ "\n" ^ s1 ^ "\n" ^ s2 ^ "\n(check-sat)"

let process_entail_new cprog iprog start_pred_abs_num (iante, iconseq, etype, cante,cconse) =
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
  (* declare abstraction for predicate instance *)
  let all_vnodes = (Cformula.get_views cante)@(Cformula.get_views_struc cconse) in
  let  s_pred_abs,num_vnodes  = List.fold_left (fun ( s, n) _ ->
      (s ^ ("(declare-fun alpha" ^ (string_of_int n) ^ "()  SetLoc)\n" ), n+1)
  ) ( "",start_pred_abs_num) all_vnodes in
  let all_view_names = List.map (fun vdecl -> vdecl.Cast.view_name) cprog.Cast.prog_view_decls in
  let s1, n1 = process_iante iante iprog all_view_names start_pred_abs_num in
  let s2,_ = process_iconseq iconseq iprog all_view_names n1 in
  "\n" ^ s0 ^ "\n" ^ s_pred_abs  ^ "\n"  ^ s1 ^ "\n" ^ s2 ^ "\n(check-sat)"

let process_cmd cmd iprog cprog=
  match cmd with
    | DataDef ddef -> process_data_def ddef
    | PredDef pdef -> process_pred_def (!subst_pred_self) pdef iprog
    | EntailCheck eche -> process_entail eche iprog cprog
    | _ -> ";other command\n"

let save_smt file_name s=
   let org_out_chnl = open_out file_name in
   try
     print_string ("\nSaving " ^ file_name ^ "\n"); flush stdout;
       let _ = Printf.fprintf  org_out_chnl "%s" s in
       let _ = close_out org_out_chnl in
       ()
   with
       End_of_file -> exit 0

let trans_smt slk_fname iprog cprog cmds =
  let _ = reset_smt_number () in
  let ent_cmds, other_cmds = List.partition (fun cmd -> match cmd with
    | EntailCheck _ -> true
    | _ -> false
  ) cmds in
  let ent_cmds = !smt_ent_cmds in
  let logic_header = "(set-logic QF_SLRD)\n" in
  (*declaration*)
  let decl_s0 = List.fold_left (fun s cmd -> s ^ (process_cmd cmd iprog cprog)) "" other_cmds in
  let decl_s = logic_header ^ decl_s0 in
  (*each ent check -> one file*)
  let str_ents = List.map (fun cmd -> decl_s ^ "\n" ^(process_entail_new cprog iprog 0 cmd)) ent_cmds in
  let norm_slk_fname =  Globals.norm_file_name slk_fname in
  let _ = List.iter (fun s ->
      let n= fresh_number () in
      save_smt (norm_slk_fname ^ "-" ^ (string_of_int n) ^ ".smt") s
      (* print_endline (s ^ "\n") *)
  ) str_ents in
  let _ = smt_cmds := [] in
  let _ = smt_ent_cmds := [] in
  true
