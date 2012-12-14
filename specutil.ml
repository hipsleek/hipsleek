open Globals
module DD = Debug
open Gen
open Exc.GTable
open Cformula
open Cpure
open Cprinter

module CP = Cpure
module MCP = Mcpure
module CF = Cformula
module TP = Tpdispatcher
module IF = Iformula
module I = Iast
module C = Cast

type pure_dom = {
  para_names : spec_var list;
  (* TODO *)
(*  inductive_def : ...;*)
}
  

let syscall cmd =
  let ic, oc = Unix.open_process cmd in
  let buf = Buffer.create 16 in
  (try
     while true do
       Buffer.add_channel buf ic 1
     done
   with End_of_file -> ());
  let _ = Unix.close_process (ic, oc) in
  (Buffer.contents buf)

let print_spec spec file_name =
  let output_spec = file_name ^ ".spec" in
  let oc = open_out output_spec in
  Printf.fprintf oc "%s" spec;
  flush oc;
  close_out oc;;

let get_file_name full_file_name =
  try
    let pos = String.index full_file_name '.' in
    String.sub full_file_name 0 pos
  with _ -> report_error no_pos "Input file has a wrong format name"

let get_proc_name full_proc_name =
  try
    let pos = String.index full_proc_name '$' in
    String.sub full_proc_name 0 pos
  with _ -> report_error no_pos "Proc name has wrong format"

let rec string_of_elems elems string_of sep = match elems with 
  | [] -> ""
  | h::[] -> string_of h 
  | h::t -> (string_of h) ^ sep ^ (string_of_elems t string_of sep)

let rec create_alias_tbl svl keep_vars aset = match svl with
  | [] -> []
  | [hd] -> 
    [hd::(List.filter (fun x -> not(List.mem x keep_vars)) (CP.EMapSV.find_equiv_all hd aset))]
  | hd::tl ->
    let tmp = create_alias_tbl [hd] keep_vars aset in
    let tl = List.filter (fun x -> not(List.mem x (List.hd tmp))) tl in
    tmp@(create_alias_tbl tl keep_vars aset)

(* Supposed fml to be Base _ *)
let filter_var_heap keep_vars fml =
  let _,pure,_,_,_ = CF.split_components fml in
  let als = MCP.ptr_equations_without_null pure in
(*  DD.info_hprint (add_str "ALS: " (pr_list (pr_pair !print_sv !print_sv))) als no_pos;*)
  let aset = CP.EMapSV.build_eset als in
  let alias_tbl = create_alias_tbl (keep_vars@CP.fv (MCP.pure_of_mix pure)) keep_vars aset in
  let subst_lst = 
    List.concat (List.map (fun vars -> if vars = [] then [] else 
      let hd = List.hd vars in 
      List.map (fun v -> (v,hd)) (List.tl vars)) alias_tbl) in
(*  DD.info_hprint (add_str "SUBS: " (pr_list (pr_pair !print_sv !print_sv))) subst_lst no_pos;*)
  let fml = CF.subst subst_lst fml in
  let heap,pure,_,_,_ = CF.split_components fml in
  let pure = CP.remove_redundant_constraints (MCP.pure_of_mix pure) in
(*  CF.normalize_combine_heap (CF.formula_of_pure_formula pure no_pos) heap*)
  (heap, pure)

let infer_shape input file_name view_node keep_vars proc_name = 
  domain_name := view_node;
  let fmls_orig = Parse_shape.parse_shape input in
  let keep_vars = keep_vars @ ["NULL"] in
  Debug.tinfo_hprint (add_str "Keep vars: " (pr_list (fun x -> x))) keep_vars no_pos;
  let keep_vars = List.map (fun s -> SpecVar (Named "GenNode", s, Unprimed)) keep_vars in
  let fmls = List.map (fun f -> filter_var_heap keep_vars f) fmls_orig in
(*  Debug.info_hprint (add_str "Inferred shape (original) " (pr_list !CF.print_formula)) fmls_orig no_pos;*)
(*  Debug.info_hprint (add_str "Inferred shape (filtered) " (pr_list !CF.print_formula)) fmls no_pos;*)
(*  print_newline ()*)
  let print_fun = fun (h,p) -> (!print_h_formula_for_spec h) ^ " &" ^ (!CP.print_formula p) in
  let pre = print_fun (List.hd fmls) in
  let post = string_of_elems (List.tl fmls) print_fun " ||" in
  let spec = proc_name ^ "\nrequires" ^ pre ^ "\nensures" ^ post ^ ";\n" in
  print_spec spec file_name;;

let get_shape_from_file view_node keep_vars proc_name = 
  let file_name = get_file_name Sys.argv.(1) in
  let input_c = file_name ^ ".c" in
(*  let _ = syscall ". ./../../predator/src/register-paths.sh" in*)
  let input_shape = file_name ^ ".shape" in
  let _ = syscall ("rm -f " ^ input_shape) in
  let _ = syscall ("gcc -fplugin=libsl.so -DPREDATOR " ^ input_c) in
  let input_str = syscall ("cat " ^ input_shape) in
  infer_shape input_str file_name view_node keep_vars proc_name

(*let get_cmd_from_file =*)
(*  let input_cmd = (get_file_name Sys.argv.(1)) ^ ".cmd" in*)
(*  let input_str = syscall ("cat " ^ input_cmd) in*)
(*  let res = Parse_cmd.parse_cmd input_str in*)
(*(*  print_endline ("SPEC" ^ ((pr_pair (fun x -> x) Cprinter.string_of_struc_formula) res));*)*)
(*  res*)

let get_spec_from_file prog = 
  let input_spec = (get_file_name Sys.argv.(1)) ^ ".spec" in
  let input_str = syscall ("cat " ^ input_spec) in
  let res = Parser.parse_spec input_str in
(*  print_endline ("SPEC" ^ (Iprinter.string_of_struc_formula res));*)
(*  let id,command = get_cmd_from_file in*)
  let id, command = !(IF.cmd) in
  let cmd = match command with
    | (true,_,Some view_node) -> 
      let proc = List.filter (fun x -> x.I.proc_name=id) prog.I.prog_proc_decls in
      let keep_vars = 
        if List.length proc != 1 then report_error no_pos ("Error in get_spec_from_file " ^ input_spec)
        else 
          List.map (fun x -> x.I.param_name) (List.hd proc).I.proc_args
      in
      let _ = get_shape_from_file view_node keep_vars id in
      IF.mkETrue top_flow no_pos
    | (false,Some cmd,_) -> cmd
    | _ -> report_error no_pos "No command"
  in
  let res = List.map (fun (id1,spec) -> 
    if id1=id then (id1,IF.merge_cmd cmd spec) else (id1,spec)) res in
  res

let rec size_of_heap (fml:CF.h_formula) : CP.exp = match fml with
  | Star {h_formula_star_h1 = h1;
    h_formula_star_h2 = h2;
    h_formula_star_pos = pos} -> 
    let res1 = size_of_heap h1 in
    let res2 = size_of_heap h2 in
    Add (res1,res2,no_pos)
  | Conj {h_formula_conj_h1 = h1;
    h_formula_conj_h2 = h2;
    h_formula_conj_pos = pos} ->
    let res1 = size_of_heap h1 in
    let res2 = size_of_heap h2 in
    Add (res1,res2,no_pos)
  | Phase _ -> report_error no_pos "size_of_heap: Do not expect Phase"
  | DataNode _ -> IConst (1,no_pos)
  | ViewNode vn -> 
    let v = List.hd (List.rev vn.h_formula_view_arguments) in
    Var (v,no_pos)
  | Hole _ -> report_error no_pos "size_of_heap: Do not expect Hole"
  | HRel _ -> report_error no_pos "size_of_heap: Do not expect HRel"
  | HTrue
  | HFalse
  | HEmp -> IConst (0,no_pos)
  

let size_of_fml (fml:CF.formula) (lhs_para:CP.spec_var): CF.formula = match fml with
  | CF.Or _ -> report_error no_pos "size_of_fml: Do not expect Or formula"
  | CF.Base b -> 
    let pure = mkEqExp (Var (lhs_para,no_pos)) (size_of_heap b.formula_base_heap) no_pos in
    let mix = MCP.mix_of_pure (CP.mkAnd (MCP.pure_of_mix b.formula_base_pure) pure no_pos) in
    CF.Base {b with formula_base_pure = mix}
  | CF.Exists e -> 
    let pure = mkEqExp (Var (lhs_para,no_pos)) (size_of_heap e.formula_exists_heap) no_pos in
    let mix = MCP.mix_of_pure (CP.mkAnd (MCP.pure_of_mix e.formula_exists_pure) pure no_pos) in
    CF.Exists {e with formula_exists_pure = mix}

let rec size_of (fml:CF.struc_formula) (lhs_para:CP.spec_var): CF.struc_formula =
  match fml with
  | ECase b -> 
    let res = List.map (fun (p,c) -> (p,size_of c lhs_para)) b.formula_case_branches in
    ECase {b with formula_case_branches = res}
  | EBase b -> 
    let rbase = size_of_fml b.formula_struc_base lhs_para in
    let rcont = (match b.formula_struc_continuation with
      | None -> None
      | Some f -> Some(size_of f lhs_para)) in
    EBase {b with 
      formula_struc_base = rbase;
      formula_struc_continuation = rcont}
  | EAssume(svl,f,fl,t) -> 
    EAssume(svl,size_of_fml f lhs_para,fl,t)
  | EInfer b ->
    EInfer {b with formula_inf_continuation = size_of b.formula_inf_continuation lhs_para}
  | EList b -> 
    let r = List.map (fun (l,e) -> (l,size_of e lhs_para)) b in
    EList r
  | EOr b -> 
    let r1 = size_of b.formula_struc_or_f1 lhs_para in
    let r2 = size_of b.formula_struc_or_f2 lhs_para in
    EOr {b with formula_struc_or_f1 = r1;
                formula_struc_or_f2 = r2}

let gen_struc_fml (orig_fml:CF.struc_formula) (abs_dom:pure_dom) sub_pair: CF.struc_formula =
  let updated_fml = CF.tran_spec orig_fml sub_pair in
  let new_fml = size_of (fst updated_fml) (List.hd abs_dom.para_names) in
  new_fml

(* TODO: abs_dom *)
(* Primitive case: size(). See more in gen_pred.txt *)
let gen_pred_def (orig_def:C.view_decl) (abs_dom:pure_dom): C.view_decl =
  let new_view_name = fresh_old_name orig_def.C.view_name in
  let new_view_vars = orig_def.C.view_vars @ abs_dom.para_names in
  let sub_pair = ((orig_def.C.view_name,orig_def.C.view_vars),(new_view_name,new_view_vars)) in
  let new_def = {orig_def with
    C.view_name = new_view_name;
    C.view_vars = new_view_vars;
    C.view_formula = gen_struc_fml orig_def.C.view_formula abs_dom sub_pair;
    (* TODO: compute inv *)
    C.view_user_inv = orig_def.C.view_user_inv;
  }
  in
  new_def

let test prog =
  let orig_def = List.hd prog.C.prog_view_decls in
  let _ = pr_view_decl orig_def in
  let _ = print_endline "\n\n" in
  let abs_dom = {para_names = [SpecVar (Int, "n", Unprimed)]} in
  let new_def = gen_pred_def orig_def abs_dom in
  pr_view_decl new_def






