#include "xdebug.cppo"
open VarGen
open Globals
open Sleekcommons
open Gen
open Cformula

let smt_number = ref (0:int)

let subst_pred_self = ref (true: bool)

let smt_self =  ("in": string)
let pred_pre_fix_var =  ref ("?": string)

let smt_string_of_primed p =
  match p with
  | Primed -> "prm"
  | Unprimed -> ""

let string_of_sv (id,p) = id ^ (smt_string_of_primed p)

let reset_smt_number () =
  smt_number :=0

let fresh_number () =
  smt_number := !smt_number + 1;
  !smt_number

let smt_string_of_typ x=
  match x with
  | Int -> "Int"
  | TVar _ -> "Int"
  | _ -> string_of_typ x

let tbl_datadef : (string, string list) Hashtbl.t = Hashtbl.create 1

let smt_cmds = ref ([] : command list)

let smt_ent_cmds = ref ([]: 
                          (meta_formula list * meta_formula * entail_type * Cformula.formula * Cformula.struc_formula * bool) list)

let find_typ spl name =
  let (_, sv_info) = List.find (fun (id,sv_info) -> id = name) spl in
  smt_string_of_typ sv_info.Typeinfer.sv_info_kind


let rec process_exp pre_fix_var e =
  match e with
  | Ipure.Var ((id,p),_) -> pre_fix_var ^ (string_of_sv (id,p))
  (* Iprinter.string_of_formula_exp e *)
  | Ipure.Null _ ->
    "nil"
  | Ipure.Add (e1, e2, _) ->
    "(+ " ^ (process_exp pre_fix_var e1) ^ " " ^ (process_exp pre_fix_var e2)  ^  ")"
  | Ipure.Subtract (e1, e2, _) ->
    "(- " ^ (process_exp pre_fix_var e1) ^ " " ^ (process_exp pre_fix_var e2)  ^  ")"
  | Ipure.Mult (e1, e2, _) ->
    "(* " ^ (process_exp pre_fix_var e1) ^ " " ^ (process_exp pre_fix_var e2)  ^  ")"
  | _ ->
    let s = Iprinter.string_of_formula_exp e in
    s
(* if s = "null" then "nil" else s *)

let rec process_p_formula pre_fix_var pf =
  match pf with
  | Ipure.Frm _ ->
    ";frm"
  | Ipure.BConst _ ->
    ""
  | Ipure.BVar _ -> ""
  (* "bvar" *)
  | Ipure.SubAnn _ ->
    ";(subann)"
  | Ipure.Lt (e1, e2, _) ->
    "(< " ^ (process_exp pre_fix_var e1) ^ " " ^ (process_exp pre_fix_var e2) ^ ")\n"
  | Ipure. Lte (e1, e2, _) ->
    "(<= " ^ (process_exp pre_fix_var e1) ^ " " ^ (process_exp pre_fix_var e2) ^ ")\n"
  | Ipure.Gt (e1, e2, _) ->
    "(> " ^ (process_exp pre_fix_var e1) ^ " " ^ (process_exp pre_fix_var e2) ^ ")\n"
  | Ipure.Gte (e1, e2, _) ->
    "(>= " ^ (process_exp pre_fix_var e1) ^ " " ^ (process_exp pre_fix_var e2) ^ ")\n"
  | Ipure.Neq (e1, e2, _) ->
    "(distinct " ^ (process_exp pre_fix_var e1) ^ " " ^ (process_exp pre_fix_var e2) ^ ")\n"
  | Ipure.EqMax _ ->
    ";eqmax"
  | Ipure.EqMin _ ->
    ";eqmin"
  | Ipure.LexVar _ ->
    ";lexvar"
  | Ipure.BagIn _ ->
    ";bagin"
  | Ipure.BagNotIn _ ->
    ";bagnotin"
  | Ipure.BagSub _ ->
    ";bagsub"
  | Ipure.BagMin _ ->
    ";bagmin"
  | Ipure.BagMax _ ->
    ";bagmax"
  (* | Ipure.VarPerm _ -> *)
  (*       ";varperm"     *)
  | Ipure.ListIn _ ->
    ";listin"
  | Ipure.ListNotIn _ ->
    ";listnotin"
  | Ipure.ListAllN _ ->
    ";listalln"
  | Ipure.ListPerm _ ->
    ";listperm"
  | Ipure.Eq (e1, e2, _) ->
    "(= " ^ (process_exp pre_fix_var e1) ^ " " ^ (process_exp pre_fix_var e2) ^ ")\n"
  | Ipure.XPure _ ->
    ";(xpure)"
  | Ipure.RelForm (id, el, _) ->
    "(" ^ id ^ ")"
  | Ipure.ImmRel _ ->
    ";immrel"

let rec process_pure_formula pre_fix_var pf =
  let recf = process_pure_formula pre_fix_var in
  match pf with
  | Ipure.BForm ((pf, _), _) ->
    process_p_formula pre_fix_var pf
  | Ipure.And (p1,p2,_) -> let s1 = recf p1 in
    let s2 = recf p2 in
    ("and ("^ s1 ^ " " ^ s2 ^ ")" )
  | _ -> (* "other" *) ""

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
    let (n,p) = hn.Iformula.h_formula_heap_node in
    let id = string_of_sv (n,p) in
    let heap_name = hn.Iformula.h_formula_heap_name in
    let s_vnode, n_pred_abs_num = (* if Gen.BList.mem_eq (fun s1 s2 -> String.compare s1 s2 = 0)  heap_name all_view_names then *)
      (* "index alpha" ^ (string_of_int  pred_abs_num) ^ " ",  pred_abs_num+1 else *) "", pred_abs_num in
    let () = Debug.ninfo_hprint (add_str "HeapNode" pr_id) (heap_name ^ s_vnode) no_pos in
    let s =
      try
        let stl = Hashtbl.find tbl_datadef heap_name in
        let args =
          if (List.length stl > 1) then
            "(sref " ^ (List.fold_left (fun s (id, exp) -> s ^ "(ref " ^ id ^ " "  ^ (recf_e exp) ^ ") ") "" (List.combine stl hn.Iformula.h_formula_heap_arguments)) ^ ")"
          else
            (List.fold_left (fun s (id, exp) -> s ^ " (ref " ^ id ^ " "  ^ (recf_e exp) ^ ")") "" (List.combine stl hn.Iformula.h_formula_heap_arguments))
        in "(pto " ^ pre_fix_var  ^ id ^ " " ^ args  ^ ")"
      with Not_found -> "(" ^ heap_name ^ " " ^ pre_fix_var ^ id ^ (List.fold_left (fun s exp -> s ^ " " ^ (recf_e exp)) "" hn.Iformula.h_formula_heap_arguments) ^ ")"
    in (  s_vnode ^ s ),n_pred_abs_num
  | Iformula.HeapNode2 hn2 -> "HeapNode2",pred_abs_num
  (* let heap_name = hn2.Iformula.h_formula_heap2_name in *)
  (* let () = Debug.ninfo_hprint (add_str "HeapNode2" pr_id) heap_name no_pos in *)
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
  | Iformula.HEmp -> "emp",pred_abs_num
  | Iformula.HVar _ -> "HVar!!",pred_abs_num

let rec process_formula pre_fix_var f spl all_view_names start_pred_abs_num=
  match f with
  | Iformula.Base fb ->
    let hfs = Iformula.get_heaps fb.Iformula.formula_base_heap in
    (* let hfs1 = if String.compare pre_fix_var "" =0 then (hfs@[Iformula.HEmp]) *)
    (* else if List.length hfs = 1 then (hfs@[Iformula.HEmp]) else hfs in *)
    let hfs1 = hfs in
    let sep_s_start,sep_s_end  = if List.length hfs1 > 1 then "(ssep", ")" else "","" in
    let fbs1,n2 =List.fold_left (fun (s,n) hf ->
        let s1,n1 = process_h_formula pre_fix_var hf  all_view_names n in
        (s ^ s1 ^ "\n", n1)
      ) ("", start_pred_abs_num) (hfs1) in
    let s_heap = if hfs1 = [] || fb.Iformula.formula_base_heap = Iformula.HEmp then
        "" else  "(tobool " ^ sep_s_start ^" \n" ^ fbs1 ^ sep_s_end ^" )" in
    (* let fbs1,n2 = process_h_formula pre_fix_var fb.Iformula.formula_base_heap all_view_names start_pred_abs_num in *)
    let ps = Ipure.list_of_conjs fb.Iformula.formula_base_pure in
    let fbs2 = List.fold_left (fun s p -> s^ (process_pure_formula pre_fix_var p)) "" ps in
    let s_start_and,s_end_and =
      if (( hfs1 != [] && fb.Iformula.formula_base_heap != Iformula.HEmp
          )
          && List.length ps >= 1) || List.length ps >= 2 then
        "(and \n", "\n)" else "",""
    in
    s_start_and ^ fbs2 ^ s_heap ^ s_end_and,n2
  | Iformula.Exists fe ->
    let quan,bare = Iformula.split_quantifiers f in
    let fes1 = "exists " in
    let fes2 = "(" ^ (List.fold_left (fun s (id, p) ->
        s ^ "(" ^ pre_fix_var ^ (string_of_sv (id,p)) ^ " " ^ (find_typ spl id)  ^ ")") "" fe.Iformula.formula_exists_qvars)  ^ ")" in
    (* let fes3,n2 = process_h_formula pre_fix_var fe.Iformula.formula_exists_heap all_view_names start_pred_abs_num in *)
    (* let fes4 = " (tobool " ^ fes3 ^ ")" in *)
    let fes5,n2 = process_formula pre_fix_var bare spl all_view_names start_pred_abs_num in
    (* "(" ^ fes1 ^ fes2 ^ fes4 ^ ")" ^ fes5 ^ "\n",n2 *)
    "(" ^ fes1 ^ fes2 ^ fes5 ^ ")",n2
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
  "\n(define-fun " ^ pred_name

let find_typ spl name =
  let (_, sv_info) = List.find (fun (id,sv_info) -> id = name) spl in
  sv_info.Typeinfer.sv_info_kind


let process_pred_vars pre_fix_var self_sv self_typ pred_vars pred_formula spl =
  let find_typ spl name =
    let (_, sv_info) = List.find (fun (id,sv_info) -> id = name) spl in
    smt_string_of_typ sv_info.Typeinfer.sv_info_kind
  in
  let s1 = " ((" ^ pre_fix_var  ^ self_sv ^ " " ^ ( smt_string_of_typ self_typ) ^ ")" in
  let s2 = (List.fold_left (fun s v -> s ^ " (" ^ pre_fix_var ^ v ^ " " ^ (find_typ spl v) ^ ")") "" pred_vars) ^ ")\n" in
  s1 ^ s2

let process_pred_def subst_self pdef iprog =
  let pred_name = pdef.I.view_name in
  let pred_vars = pdef.I.view_vars in
  let spl = x_add Typeinfer.gather_type_info_struc_f iprog pdef.I.view_formula [] in
  let self_typ = find_typ spl self in
  let pred_formula, self_sv = if subst_self then
      let sst = [((self, Unprimed),(smt_self, Unprimed))] in
      (Iformula.subst_struc sst pdef.I.view_formula, smt_self)
    else (pdef.I.view_formula, self)
  in
  let () = Debug.ninfo_hprint (add_str "pred_formula" Iprinter.string_of_struc_formula) pred_formula no_pos in
  let s1 = process_pred_name pred_name in
  let s2 = process_pred_vars !pred_pre_fix_var self_sv self_typ pred_vars pred_formula spl in
  let s3,_ = (process_struct_formula !pred_pre_fix_var pred_formula spl [] 0) in
  s1 ^ s2 ^ "Space (tospace\n" ^ s3 ^ "))\n"

let process_data_name data_name =
  ("\n(declare-sort " ^ data_name ^ " 0)\n")

let process_data_fields data_name data_fields =
  List.fold_left (fun (s,st_list) ((typ,field_name),_,_,_) ->
      let st = smt_string_of_typ typ in
      let field_name_list = st_list@[field_name] in
      let s = s ^ ("(declare-fun " ^ field_name ^ " () (Field " ^ data_name ^ " " ^ st ^ "))\n")
      in (s,field_name_list)
    ) ("",[]) data_fields

let process_data_def ddef =
  let data_name = ddef.I.data_name in
  let data_fields = ddef.I.data_fields in
  let s1 = process_data_name data_name in
  let (s2, field_name_list) = process_data_fields data_name data_fields in
  let () = Hashtbl.add tbl_datadef data_name field_name_list in
  s1 ^ s2

let process_iante iante iprog all_view_names start_pred_abs_num=
  let s1 = "(assert \n" in
  let s2, n2 = match iante with
    | MetaVar id -> "(?" ^ id ^ ")",start_pred_abs_num
    | MetaForm f ->
      let spl = x_add Typeinfer.gather_type_info_formula iprog f [] true in
      process_formula "" f spl all_view_names start_pred_abs_num
    | MetaEForm ef ->
      let spl = x_add Typeinfer.gather_type_info_struc_f iprog ef [] in
      process_struct_formula "" ef spl all_view_names start_pred_abs_num
    | _ -> "",start_pred_abs_num
  in
  let s3 = "\n)\n" in
  (s1 ^ s2 ^ s3,n2)

let process_iconseq iconseq iprog all_view_names start_pred_abs_num =
  let s1 = "(assert (not \n" in
  let s2,n2 = match iconseq with
    | MetaVar id -> "(?" ^ id ^ ")",start_pred_abs_num
    | MetaForm f ->
      let spl = x_add Typeinfer.gather_type_info_formula iprog f [] true in
      process_formula "" f spl all_view_names start_pred_abs_num
    | MetaEForm ef ->
      let spl = x_add Typeinfer.gather_type_info_struc_f iprog ef [] in
      process_struct_formula "" ef spl all_view_names start_pred_abs_num
    | _ -> "",start_pred_abs_num
  in
  let s3 = "\n))\n" in
  s1 ^ s2 ^ s3,n2

let process_entail (iante, iconseq, etype) iprog cprog =
  let spl1 = match iante with
    | MetaForm f ->
      x_add Typeinfer.gather_type_info_formula iprog f [] true
    | _ -> []
  in
  let spl2 = match iconseq with
    | MetaForm f ->
      x_add Typeinfer.gather_type_info_formula iprog f [] true
    | _ -> []
  in
  let spl = spl1@spl2 in
  let s0 = List.fold_left (fun s0 (id,sv_info) ->
      s0 ^ "(declare-fun " ^ id ^ " () " ^ (smt_string_of_typ sv_info.Typeinfer.sv_info_kind) ^ ")\n"
    ) "" spl in
  let all_view_names = List.map (fun vdecl -> vdecl.Cast.view_name) cprog.Cast.prog_view_decls in
  let s1,n1 = process_iante iante iprog all_view_names 0 in
  let s2,_ = process_iconseq iconseq iprog all_view_names n1 in
  "\n" ^ s0 ^ "\n" ^ s1 ^ "\n" ^ s2 ^ "\n(check-sat)"

let process_entail_new cprog iprog start_pred_abs_num 
    (iantes, iconseq, etype, cante, cconseq, res) header data_decl =
  let iante = List.hd iantes in
  let spl1 = match iante with
    | MetaForm f ->
      x_add Typeinfer.gather_type_info_formula iprog f [] true
    | _ -> []
  in
  let spl2 = match iconseq with
    | MetaForm f ->
      x_add Typeinfer.gather_type_info_formula iprog f [] true
    | _ -> []
  in
  (* let spl = spl1@spl2 in *)
  let all_svl0 = CP.remove_dups_svl ((Cformula.fv cante)@(Cformula.struc_fv cconseq)) in
  let data_name =
    let used_data = List.fold_left (fun r sv ->
        let t = Cpure.type_of_spec_var sv in
        match t with
        | Named id -> r@[id]
        | _ -> r
      ) [] all_svl0 in
    List.hd (used_data@(List.map (fun d -> d.Cast.data_name) cprog.Cast.prog_data_decls)) in
  let all_svl = List.fold_left (fun r ((Cpure.SpecVar (t, id, p)) as sv) ->
      match t with
      | Bool -> r
      | TVar _ -> r@[(Cpure.SpecVar (Named data_name, id, p))]
      | _ -> r@[sv]
    )  [] all_svl0 in
  (* let all_svl = List.filter (fun sv -> let t = CP.type_of_spec_var sv in *)
  (* match t with *)
  (*   | Bool -> false *)
  (*   | _ -> true *)
  (* ) all_svl0 in *)
  (* let s0 = List.fold_left (fun s0 (id,sv_info) -> *)
  (*     s0 ^ "(declare-fun " ^ id ^ " () " ^ (string_of_typ sv_info.Typeinfer.sv_info_kind) ^ ")\n" *)
  (* ) "" spl in *)
  let status = "(set-info :status " ^ (if res then "unsat" else "sat") ^ ")\n" in 
  let s0 = List.fold_left (fun s0 (CP.SpecVar (t,id,p)) ->
      s0 ^ "(declare-fun " ^ (string_of_sv (id,p)) ^ " () " ^ (smt_string_of_typ t) ^ ")\n"
    ) "" all_svl in
  (* declare abstraction for predicate instance *)
  (* let all_vnodes = (Cformula.get_views cante)@(Cformula.get_views_struc cconse) in *)
  let all_vnodes = [] in
  let  s_pred_abs, num_vnodes  = List.fold_left (fun ( s, n) _ ->
      (s ^ ("(declare-fun alpha" ^ (string_of_int n) ^ "()  SetLoc)\n" ), n+1)
    ) ( "", start_pred_abs_num) all_vnodes in
  let all_view_names = List.map (fun vdecl -> vdecl.Cast.view_name) cprog.Cast.prog_view_decls in
  let s1, n1 = process_iante iante iprog all_view_names start_pred_abs_num in
  let s2= if Cformula.isAnyConstFalse_struc cconseq then "" else
      let s2,_ = process_iconseq iconseq iprog all_view_names n1 in
      s2
  in
  header ^ status ^ "\n" ^ data_decl ^ "\n" ^ 
  s0 ^ "\n" ^ s_pred_abs  ^ "\n"  ^ s1 ^ "\n" ^ s2 ^ "\n(check-sat)"

let process_cmd cmd iprog cprog=
  match cmd with
  | DataDef ddef -> process_data_def ddef
  | PredDef pdef -> process_pred_def (!subst_pred_self) pdef iprog
  | EntailCheck (a,q,c) -> begin
      match a with
      | [x] ->
        process_entail (x,q,c) iprog cprog
      | _ -> "\n" (*";other entailcheck command\n"*)
    end
  | _ -> "\n" (*";other command\n"*)

let save_smt file_name s=
  let org_out_chnl = open_out file_name in
  try
    print_string ("\nSaving " ^ file_name ^ "\n"); flush stdout;
    let () = Printf.fprintf  org_out_chnl "%s" s in
    let () = close_out org_out_chnl in
    ()
  with
    End_of_file -> exit 0

let trans_smt slk_fname iprog cprog cmds =
  let () = reset_smt_number () in
  let ent_cmds, other_cmds = List.partition (fun cmd -> match cmd with
      | EntailCheck _ -> true
      | _ -> false
    ) cmds in
  let ent_cmds = !smt_ent_cmds in
  let logic_header = 
    "(set-logic QF_S)\n" ^ 
    "(set-info :source |" ^
    "  Sleek solver\n" ^
    "  http://loris-7.ddns.comp.nus.edu.sg/~project/s2/beta/\n" ^  
    "|)\n\n" ^ 
    "(set-info :smt-lib-version 2.0)\n" ^
    "(set-info :category \"crafted\")\n" 
  in
  (*declaration*)
  let decl_s0 = List.fold_left (fun s cmd -> s ^ (process_cmd cmd iprog cprog)) "" other_cmds in
  (* let decl_s = logic_header ^ decl_s0 in *)
  (*each ent check -> one file*)
  let str_ents = List.map (fun cmd -> (process_entail_new cprog iprog 0 cmd logic_header decl_s0)) ent_cmds in
  let norm_slk_fname =  Globals.norm_file_name slk_fname in
  let () = List.iter (fun s ->
      let n= fresh_number () in
      save_smt (norm_slk_fname ^ "-" ^ (string_of_int n) ^ ".smt2") s
      (* print_endline (s ^ "\n") *)
    ) str_ents in
  let () = smt_cmds := [] in
  let () = smt_ent_cmds := [] in
  (* let () = Slk2smt1.tmp () in *)
  true
