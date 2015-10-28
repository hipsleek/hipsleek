#include "xdebug.cppo"
open VarGen
open Globals
open Others
(* open Gen *)
open Gen.Basic

module CF = Cformula
module CP = Cpure
module I = Iast
module IP = Iprinter


let init_proc_name = "main"
let violation_proc_name = "__VERIFIER_error"
let prefix_node = "A"

let get_fst ls=
  match ls with
    | x::rest -> x, rest
    | [] -> failwith "List is empty"

let save_witness file_name s=
  try
    (try Unix.mkdir "logs" 0o750 with _ -> ());
      let fname = "logs/" ^ file_name in
      let org_out_chnl = open_out fname in
      print_string_quiet ("\nSaving " ^ fname ^ "\n"); flush stdout;
      let () = Printf.fprintf  org_out_chnl "%s" s in
      let () = close_out org_out_chnl in
      ()
  with
    End_of_file -> exit 0

let mk_entry_node id=
  "<node id=\""^ id ^ "\">\n" ^
      "<data key=\"entry\">true</data>\n" ^
      "</node>\n"

let mk_sink_node id=
  "<node id=\""^ id ^ "\">\n" ^
      "<data key=\"sink\">true</data>\n" ^
      "</node>\n"

let mk_violation_node id=
  "<node id=\""^ id ^ "\">\n" ^
      "<data key=\"violation\">true</data>\n" ^
      "</node>\n"

let mk_node id=
  "<node id=\""^ id ^ "\"/>\n"

let mk_edge sid tid str_code start_line=
  "<edge source=\""^ sid ^ "\" target=\"" ^ tid ^ "\">\n" ^
      "<data key=\"sourcecode\">" ^ str_code ^ "</data>\n" ^
      "<data key=\"startline\">" ^ start_line ^ "</data>\n" ^
      "</edge>\n"

let mk_edge_func_call sid tid str_code start_line proc_name=
  "<edge source=\""^ sid ^ "\" target=\"" ^ tid ^ "\">\n" ^
      "<data key=\"sourcecode\">" ^ str_code ^ "</data>\n" ^
      "<data key=\"startline\">" ^ start_line ^ "</data>\n" ^
      "<data key=\"enterFunction\">" ^ proc_name ^ "</data>\n" ^
      "</edge>\n"

let mk_edge_return sid tid str_code start_line proc_name=
  "<edge source=\""^ sid ^ "\" target=\"" ^ tid ^ "\">\n" ^
      "<data key=\"sourcecode\">" ^ str_code ^ "</data>\n" ^
      "<data key=\"startline\">" ^ start_line ^ "</data>\n" ^
      "<data key=\"returnFromFunction\">" ^ proc_name ^ "</data>\n" ^
      "</edge>\n"

let mk_edge_control sid tid str_code start_line is_then=
  "<edge source=\""^ sid ^ "\" target=\"" ^ tid ^ "\">\n" ^
      "<data key=\"sourcecode\">" ^ str_code ^ "</data>\n" ^
      "<data key=\"startline\">" ^ start_line ^ "</data>\n" ^
      "<data key=\"control\">condition-" ^ (string_of_bool is_then)  ^ "</data>\n" ^
      "</edge>\n"

let gen_witness_header () =
  "<?xml version=\"1.0\" encoding=\"UTF-8\" standalone=\"no\"?>\n" ^
"<graphml xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\" xmlns=\"http://graphml.graphdrawing.org/xmlns\">\n" ^
"<key attr.name=\"assumption\" attr.type=\"string\" for=\"edge\" id=\"assumption\"/>\n" ^
"<key attr.name=\"sourcecode\" attr.type=\"string\" for=\"edge\" id=\"sourcecode\"/>\n" ^
"<key attr.name=\"sourcecodeLanguage\" attr.type=\"string\" for=\"graph\" id=\"sourcecodelang\"/>\n" ^
"<key attr.name=\"control\" attr.type=\"string\" for=\"edge\" id=\"control\"/>\n" ^
"<key attr.name=\"startline\" attr.type=\"int\" for=\"edge\" id=\"startline\"/>\n" ^
"<key attr.name=\"originFileName\" attr.type=\"string\" for=\"edge\" id=\"originfile\">\n" ^
"<default>path.c</default>\n" ^
"</key>\n" ^
"<key attr.name=\"nodeType\" attr.type=\"string\" for=\"node\" id=\"nodetype\">\n" ^
"<default>path</default>\n" ^
"</key>\n" ^
"<key attr.name=\"isFrontierNode\" attr.type=\"boolean\" for=\"node\" id=\"frontier\">\n" ^
"<default>false</default>\n" ^
"</key>\n" ^
"<key attr.name=\"isViolationNode\" attr.type=\"boolean\" for=\"node\" id=\"violation\">\n" ^
"<default>false</default>\n" ^
"</key>\n" ^
"<key attr.name=\"isEntryNode\" attr.type=\"boolean\" for=\"node\" id=\"entry\">\n" ^
"<default>false</default>\n" ^
"</key>\n" ^
"<key attr.name=\"isSinkNode\" attr.type=\"boolean\" for=\"node\" id=\"sink\">\n" ^
"<default>false</default>\n" ^
"</key>\n" ^
"<key attr.name=\"enterFunction\" attr.type=\"string\" for=\"edge\" id=\"enterFunction\"/>\n" ^
"<key attr.name=\"returnFromFunction\" attr.type=\"string\" for=\"edge\" id=\"returnFrom\"/>\n" ^
"<graph edgedefault=\"directed\"><data key=\"sourcecodelang\">C</data>\n"

let get_witness_conclude ()=
  "</graph>\n" ^
  "</graphml>"

let id_to_string inter intra=
  prefix_node ^ (string_of_int inter) ^ (string_of_int intra)

let enter_fnc_id_to_string inter=
  prefix_node ^ (string_of_int inter) 

let rec witness_search_loop iprog cprog call_stk inter_id intra_id e prev_n_id procn path_ctls res_str=
  let recf_no_change e1 = witness_search_loop iprog cprog call_stk inter_id intra_id e1 prev_n_id procn path_ctls res_str in
  match e with
    | I.Block {I.exp_block_body = bb} -> recf_no_change bb
    | I.Cond {I.exp_cond_condition = cond;
      I.exp_cond_then_arm = tb;
      I.exp_cond_else_arm=eb;
      I.exp_cond_pos = p
      } ->
          let () = x_binfo_hp (add_str "witness" (pr_id)) "cond" no_pos in
          (* retrieve the fst path ctrs: 1 -> then_arm; 2 -> else_arm *)
          let ctl, rest_ctls = get_fst path_ctls in
          let n_node_id = (id_to_string inter_id intra_id) in
          let ctl_node = mk_node n_node_id in
          let str_code_pure = !I.print_exp cond in
          let str_code = if ctl == 1 then "[" ^ str_code_pure ^ "]" else
            "[(!" ^ str_code_pure ^ ")]"
          in
          let str_line = line_number_of_pos p in
          let edge_ctl = mk_edge_control prev_n_id n_node_id str_code str_line (ctl == 1) in
          let n_intra_id = intra_id + 1 in
          let n_res_str = res_str ^ ctl_node ^ edge_ctl in
          if ctl == 1 then
            witness_search_loop iprog cprog call_stk inter_id n_intra_id tb n_node_id procn rest_ctls n_res_str
          else
            witness_search_loop iprog cprog call_stk inter_id n_intra_id eb  n_node_id procn rest_ctls n_res_str
    | I.Raise _ -> false, call_stk, inter_id, intra_id , prev_n_id , path_ctls, res_str
    | I.Return {
          exp_return_val = e_opt;
          exp_return_pos = p;
      } ->
          let () = x_binfo_hp (add_str "witness" (pr_id)) "return" no_pos in
          let str_code = "return " ^ ( match e_opt with
            | None -> ""
            | Some e1 -> (IP.string_of_exp e1)
          ) ^ ";" in
          let str_line = line_number_of_pos p in
          let n_node_id = (id_to_string inter_id intra_id) in
          let node = mk_node n_node_id in
          let edge = mk_edge_return prev_n_id n_node_id str_code str_line procn in
          let n_intra_id = intra_id+1 in
          false, call_stk, inter_id, n_intra_id , n_node_id , path_ctls, (res_str ^ node ^ edge)
    | Label (_, e1) ->
          let () = x_binfo_hp (add_str "witness" (pr_id)) "Label" no_pos in
          recf_no_change e1
    | I.CallRecv _ ->
          let () = x_binfo_hp (add_str "witness" (pr_id)) "CallRecv" no_pos in
          false, call_stk, inter_id, intra_id , prev_n_id , path_ctls, res_str
    | I.CallNRecv { 
          exp_call_nrecv_method = pname ;
          exp_call_nrecv_arguments = eargs;
          exp_call_nrecv_path_id = path_id;
          exp_call_nrecv_pos =p } -> begin
          let fnc_call = pname ^ "(" ^ (String.concat "," (List.map !I.print_exp eargs) )^ ")" in
          let () = x_binfo_hp (add_str "witness: CallNRecv" (pr_id)) fnc_call no_pos in
          let str_code = fnc_call^";" in
          let str_line = line_number_of_pos p in
          if string_eq pname violation_proc_name then
            (*mk violation node*)
            let n_node_id = (id_to_string inter_id intra_id) in
            let violation_node = mk_violation_node n_node_id in
            (*mkedge prev violation*)
            let edge = mk_edge prev_n_id n_node_id str_code str_line in
            true, call_stk,inter_id, intra_id+1, n_node_id, path_ctls,res_str^violation_node^edge
          else if call_stk=[] then
            false, [], inter_id,intra_id, prev_n_id, path_ctls,res_str
          else
            let (stk_pname, ctls), rest_stk = get_fst call_stk in
            if not (string_eq stk_pname pname) then
              failwith "not a valid error trace (CallNRecv 1)"
            else
              let proc = I.look_up_proc_def_raw iprog.I.prog_proc_decls pname in
              match proc.I.proc_body with
                | Some e ->
                      let n_node_id = enter_fnc_id_to_string inter_id in
                      let node = mk_node n_node_id in
                      let edge = mk_edge_func_call prev_n_id n_node_id str_code str_line pname in
                      let n_inter_id = inter_id+1 in
                      witness_search_loop iprog cprog rest_stk n_inter_id 0 e n_node_id pname ctls (res_str^node^edge)
                | _ -> failwith "not a valid error trace (CallNRecv 2)"
      end
    | I.Seq {I.exp_seq_exp1 = e1; I.exp_seq_exp2 = e2} ->
          let () = x_binfo_hp (add_str "witness" (pr_id)) "seq" no_pos in
          let is_found, rest_call_stk, intra_id1, inter_id1, last_n_id, ctls1,res_str1 = recf_no_change e1 in
          if is_found then
            is_found, rest_call_stk, intra_id1, inter_id1, last_n_id, ctls1,res_str1
          else
            witness_search_loop iprog cprog rest_call_stk inter_id1 intra_id1 e2 last_n_id procn ctls1 res_str1
    | I.While {exp_while_body = wb} -> failwith "not handled yet"
    | I.Assign {exp_assign_op =op;
      exp_assign_lhs =e1;
      exp_assign_rhs = e2;
      exp_assign_pos = p} ->
          let () = x_binfo_hp (add_str "witness" (pr_id)) "Assgin" no_pos in
          let str_code = (IP.string_of_exp e1) ^ (IP.string_of_assign_op op) ^ (IP.string_of_exp e2) ^";" in
          let str_line = line_number_of_pos p in
          let n_node_id = (id_to_string inter_id intra_id) in
          let node = mk_node n_node_id in
          let edge = mk_edge prev_n_id n_node_id str_code str_line in
          let n_intra_id = intra_id+1 in
          false, call_stk, inter_id, n_intra_id , n_node_id , path_ctls, (res_str ^ node ^ edge)
    | I.Binary _ ->
          let () = x_binfo_hp (add_str "witness" (pr_id)) "Binary" no_pos in
          false, call_stk, inter_id, intra_id , prev_n_id , path_ctls, res_str
    | I.VarDecl _ ->
          let () = x_binfo_hp (add_str "witness" (pr_id)) "VarDecl" no_pos in
          false, call_stk, inter_id, intra_id , prev_n_id , path_ctls, res_str
    | _ -> false, call_stk, inter_id, intra_id , prev_n_id , path_ctls, res_str

(*TOFIX:
  orig
   int n=3;
<====
  cil
   int n;
   int tmp;
   tmp = 3;
   n = tmp;
 *)
let remove_tmp_local_vars iprog=
  iprog

let witness_search iprog0 cprog src_fname call_stk=
  let old_xml_flag = !xml_flag in
  let () = xml_flag := true in
  (*preprocess iprog*)
  let iprog = remove_tmp_local_vars iprog0 in
  (* body *)
  let (init_pname, init_ctls),rest_call_stk = get_fst call_stk in
  let init_proc = I.look_up_proc_def_raw iprog.I.prog_proc_decls init_pname in
  let res =
    match init_proc.I.proc_body with
      | Some e ->
            let entry_id = enter_fnc_id_to_string 0 in
            let entry_node = mk_entry_node entry_id in
            let is_found, rest_call_stk, _, _,_,_, body_str=
              witness_search_loop iprog cprog rest_call_stk 
                  1 0 e entry_id init_pname init_ctls entry_node
            in
            if not is_found || rest_call_stk != [] then
              print_string_quiet "\nnot a valid error trace\n"
            else
              (* header *)
              let witness_header = gen_witness_header () in
              let norm_src_fname =  Globals.norm_file_name src_fname in
              let str_conclude = get_witness_conclude () in
              let s = witness_header^body_str^str_conclude in
              let () = save_witness (norm_src_fname  ^ ".graphml") s in
              ()
      | None -> ()
  in
  let () = xml_flag := old_xml_flag in
  res
