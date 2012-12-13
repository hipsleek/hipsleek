open Globals
module DD = Debug
open Gen
open Exc.GTable
open Cformula
open Cpure

module CP = Cpure
module MCP = Mcpure
module CF = Cformula
module TP = Tpdispatcher
module IF = Iformula
module I = Iast

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

let gen_pred_def abs_dom orig_def =
  orig_def






