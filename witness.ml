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


let witness_from_orig = ref true

let init_proc_name = "main"
let violation_proc_name = "__VERIFIER_error"
let nondet_int_name = "__VERIFIER_nondet_int"
let prefix_node = "A"

let inter_num = ref (0:int)

let get_inter_id () =
  let n = !inter_num in
  let () = inter_num := !inter_num + 1 in
  n

let seq_num = ref (0:int)

let get_seq_id () =
  let n = !seq_num in
  let () = seq_num := !seq_num + 1 in
  n

let string_of_call_stk s=
  String.concat ";" (List.map (fun (fname, ids) -> fname ^ ":"^ (String.concat "," (List.map string_of_int ids))) s)

(*get the first met*)
let rec get_fst_met pname ls res=
  match ls with
    | ((pname1,_) as x)::rest -> if string_eq pname pname1 then x, rest@res
      else get_fst_met pname rest (res@[x])
    | [] -> failwith "List is empty"

let rec get_fst ls=
  match ls with
    | x::rest -> x, rest
    | [] -> failwith "List is empty"

let is_tmp_var str=
   try
     let fst_three = String.sub str 0 3 in
     if string_eq fst_three "tmp" then
       true
     else false
   with Invalid_argument _ -> false

let is_tmp_var str=
  Debug.no_1 "is_tmp_var" pr_id string_of_bool
      (fun _ -> is_tmp_var str) str

let get_source_if str=
  try
   let r = Str.regexp "if" in
   let idx = Str.search_forward r str 0 in
   if idx >= 0 then
     try
       let idx1 = String.index str '(' in
       if idx1 >=0 then
         let idx2 = String.rindex str ')' in
         if idx2>idx1 then
           true, String.trim(String.sub str (idx1+1) (idx2-idx1-1))
         else false,str
       else false,str
     with Not_found -> false,str
   else false,str
  with Not_found -> false,str

let get_source str=
  (* let _,str = get_source_if str in *)
  String.trim str

let start_line_of_pos p=p.start_pos.Lexing.pos_lnum

let parse_src src_lines fname=
  let chn = open_in fname in
  let quitloop = ref false in
  (* start from 1 instead of 0 *)
  let idx = ref 1 in
  while not !quitloop do
    try
      let line = input_line chn in
      let line1 = String.trim line in
      let line2 = get_source line1 in
      let () = Array.set src_lines !idx line2 in
      (* let ()= print_endline (line2^"\n") in *)
      flush stdout;
      idx := !idx + 1;
    with End_of_file -> begin
      quitloop := true;
    end;
  done;
  let () = close_in chn in
  (* src_lines *)
  ()

let xml_norm str=
  let l_and = Str.regexp "&" in
  let str1 = Str.global_replace l_and "&amp;" str in
  let lt = Str.regexp "<" in
  let str2 = Str.global_replace lt "&lt;" str1 in
  let gt = Str.regexp ">" in
  let str3 = Str.global_replace gt "&gt;" str2 in
  str3

let save_witness file_name s=
  try
    (try Unix.mkdir "logs" 0o750 with _ -> ());
      let fname = "logs/" ^ file_name in
      let org_out_chnl = open_out fname in
      print_string_quiet ("\nSaving " ^ fname ^ "\n"); flush stdout;
      let () = Printf.fprintf  org_out_chnl "%s" s in
      let () = close_out org_out_chnl in
      fname
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

let is_fun_call e=
  match e with
    | I.CallNRecv {exp_call_nrecv_method = pname;} ->
          if not ( string_eq pname violation_proc_name || string_eq pname nondet_int_name) then Some pname
          else None
    | _ -> None

(*
last_cond_lno: cil does split
  if a && b then ==> if a then if b then
  - the first then --> print orig in the witness
  - supress the rest
var_decls: set of var decl:
  int n = 4 ==> int n; n=4;
  - the first stmt (declarion) --> print orig in the witness (int n = 4;)
  - supress the second in witness
*)
let rec witness_search_loop iprog cprog orig_src_lines call_stk
      inter_id intra_id
      last_cond_lno var_decls
      e prev_n_id procn path_ctls res_str=
  (**********************)
  let recf_no_change e1 = witness_search_loop iprog cprog orig_src_lines call_stk
    inter_id intra_id last_cond_lno var_decls e1 prev_n_id procn path_ctls res_str in
  let recf call_stk inter_id intra_id last_cond_lno1 var_decls1 e0 prev_n_id procn path_ctls res_str=
    witness_search_loop iprog cprog orig_src_lines call_stk
        inter_id intra_id last_cond_lno1 var_decls1 e0 prev_n_id procn path_ctls res_str
  in
  let func_call call_stk pname e =
    if call_stk=[] then
      false, [], inter_id,intra_id, last_cond_lno, var_decls,false, prev_n_id, path_ctls,res_str
    else
      let (stk_pname, ctls), rest_stk = get_fst_met pname call_stk [] in
      if not (string_eq stk_pname pname) then
        failwith "not a valid error trace (CallNRecv 1)"
      else
        let proc = I.look_up_proc_def_raw iprog.I.prog_proc_decls pname in
        match proc.I.proc_body with
          | Some proc_body -> begin
              (* let str_code0 =  if not !witness_from_orig then *)
              (*   (!I.print_exp e) *)
              (* else *)
              (*   let str = Array.get orig_src_lines (start_line_of_pos (I.pos_of_exp e)) in *)
              (*   let r = Str.regexp pname in *)
              (*   let idx1 = Str.search_forward r str 0 in *)
              (*   let idx2 = String.rindex str ')' in *)
              (*   String.trim(String.sub str (idx1) (idx2-idx1+1)) *)
              (* in *)
              let str_code2a = (!I.print_exp e) in
              (* let () = x_binfo_hp (add_str "call" (!I.print_exp )) e no_pos in *)
              (* let () = x_binfo_hp (add_str "call (src 0)" (pr_id )) str_code0 no_pos in *)
              let str_code =
                try
                  let idx = String.index str_code2a ':' in
                  let str_code2 = String.sub str_code2a (idx+1) ((String.length str_code2a) - idx -1) in
                  let str_code1 = Str.global_replace (Str.regexp "(int)") "" str_code2 in
                  (* let () = x_binfo_hp (add_str "call (src 1)" (pr_id )) str_code1 no_pos in *)
                  (* if (Str.search_forward (Str.regexp str_code1) str_code0 0) >=0 then *)
                  (*   str_code1 else str_code0 *)
                  str_code1
                with _ -> str_code2a
              in
               let () = x_tinfo_hp (add_str "call (final)" (pr_id )) str_code no_pos in
              let str_line = line_number_of_pos (I.pos_of_exp e) in
              let n_node_id = enter_fnc_id_to_string inter_id in
              let node = mk_node n_node_id in
              let edge = mk_edge_func_call prev_n_id n_node_id str_code str_line pname in
              let n_inter_id = get_inter_id () in
              recf rest_stk n_inter_id 0 (start_line_of_pos proc.I.proc_loc)
                  [] proc_body n_node_id pname ctls (res_str^node^edge)
            end
          | _ -> failwith "not a valid error trace (CallNRecv at Assign)"
  in
  (**********************)
  match e with
    | I.Block {I.exp_block_body = bb} -> recf_no_change bb
    | I.Cond {I.exp_cond_condition = cond;
      I.exp_cond_then_arm = tb;
      I.exp_cond_else_arm=eb;
      I.exp_cond_pos = p
      } ->
          let () = x_binfo_hp (add_str "COND" (string_of_int)) inter_id no_pos in
          (* retrieve the fst path ctrs: 1 -> then_arm; 2 -> else_arm *)
          let ctl, rest_ctls = get_fst path_ctls in
          let src_line = start_line_of_pos p in
          let () = x_binfo_hp (add_str "last_cond_lno" string_of_int) last_cond_lno no_pos in
          let () = x_binfo_hp (add_str "src_line" string_of_int) src_line no_pos in
          let n_intra_id, n_node_id,  n_res_str =
            if !witness_from_orig && src_line = last_cond_lno then
            (* case if if (a && b) is split into if a { if b}*)
              intra_id, prev_n_id ,res_str
            else
              let n_node_id = (id_to_string inter_id intra_id) in
              let ctl_node = mk_node n_node_id in
              (* let str_code_pure = !I.print_exp cond in *)
              let str_code_pure = if not !witness_from_orig then
                !I.print_exp cond
              else
                let str = Array.get orig_src_lines src_line in
                let _ ,str = get_source_if str in
                xml_norm str
              in
              let () = x_binfo_hp (add_str "COND" (pr_pair string_of_int pr_id)) (src_line, str_code_pure) no_pos in
              let str_code = if ctl == 1 then "[" ^ str_code_pure ^ "]" else
                "[!(" ^ str_code_pure ^ ")]"
              in
              let str_line = line_number_of_pos p in
              let edge_ctl = mk_edge_control prev_n_id n_node_id str_code str_line (ctl == 1) in
              let n_intra_id = intra_id + 1 in
              let n_res_str = res_str ^ ctl_node ^ edge_ctl in
              n_intra_id, n_node_id,  n_res_str
          in
            if ctl == 1 then
              recf call_stk inter_id n_intra_id src_line var_decls tb n_node_id procn rest_ctls n_res_str
            else
              recf call_stk inter_id n_intra_id src_line var_decls eb n_node_id procn rest_ctls n_res_str
    | I.Raise _ -> false, call_stk, inter_id, intra_id, last_cond_lno, var_decls,false, prev_n_id , path_ctls, res_str
    | I.Return {
          exp_return_val = e_opt;
          exp_return_pos = p;
      } ->
          let () = x_binfo_hp (add_str "RETURN" (string_of_int)) inter_id no_pos in
          let src_line = line_number_of_pos p in
          let str_code =  if not !witness_from_orig then
            "return " ^ ( match e_opt with
              | None -> ""
              | Some e1 -> (IP.string_of_exp e1)
            ) ^ ";"
          else
            let str = Array.get orig_src_lines (start_line_of_pos p) in
            let () = x_binfo_hp (add_str "RETURN" (pr_id)) str no_pos in
            let r = Str.regexp "return" in
            let idx1 = Str.search_forward r str 0 in
            let idx2 = String.rindex str ';' in
            String.trim(String.sub str (idx1) (idx2-idx1+1))
          in
          let n_node_id = (id_to_string inter_id intra_id) in
          let node = mk_node n_node_id in
          let edge = mk_edge_return prev_n_id n_node_id str_code src_line procn in
          let n_intra_id = intra_id+1 in
          false, call_stk, inter_id, n_intra_id , last_cond_lno, var_decls, true, n_node_id , path_ctls, (res_str ^ node ^ edge)
    | Label (_, e1) ->
          let () = x_binfo_hp (add_str "Label" (pr_id)) "" no_pos in
          recf_no_change e1
    | I.CallRecv _ ->
          let () = x_binfo_hp (add_str "CallRecv" (pr_id)) "" no_pos in
          false, call_stk, inter_id, intra_id, last_cond_lno, var_decls, false, prev_n_id , path_ctls, res_str
    | I.CallNRecv { 
          exp_call_nrecv_method = pname ;
          exp_call_nrecv_arguments = eargs;
          exp_call_nrecv_path_id = path_id;
          exp_call_nrecv_pos =p } -> begin
          let fnc_call = pname ^ "(" ^ (String.concat "," (List.map !I.print_exp eargs) )^ ")" in
          let () = x_binfo_hp (add_str ("CallNRecv " ^fnc_call^ "inter_id" ) (string_of_int)) inter_id no_pos in
          let proc = I.look_up_proc_def_raw iprog.I.prog_proc_decls pname in
          let str_code = fnc_call^";" in
          let str_line = line_number_of_pos p in
          if string_eq pname violation_proc_name then
            (*mk violation node*)
            let n_node_id = (id_to_string inter_id intra_id) in
            let violation_node = mk_violation_node n_node_id in
            (*mkedge prev violation*)
            let edge = mk_edge prev_n_id n_node_id str_code str_line in
            true, call_stk,inter_id, intra_id+1, last_cond_lno, var_decls, false, n_node_id, path_ctls,res_str^violation_node^edge
          else if call_stk=[] then
            false, [], inter_id,intra_id, last_cond_lno, var_decls,false, prev_n_id, path_ctls,res_str
          else
            let (stk_pname, ctls), rest_stk = get_fst_met pname call_stk [] in
            if not (string_eq stk_pname pname) then
              let () = print_endline  "WARN: not a valid error trace (CallNRecv 1)" in
              true, call_stk, inter_id, intra_id, last_cond_lno, var_decls,false, prev_n_id , path_ctls, (res_str)
            else
              match proc.I.proc_body with
                | Some e -> begin
                      let n_node_id = enter_fnc_id_to_string inter_id in
                      let node = mk_node n_node_id in
                      let edge = mk_edge_func_call prev_n_id n_node_id str_code str_line pname in
                      let n_inter_id = get_inter_id () in
                      let ((is_found, rest_call_stk, inter_id1, intra_id1,last_cond_lno1, var_decls1, is_returning, last_n_id, ctls1,res_str1) as res) =
                        recf rest_stk n_inter_id 0 (start_line_of_pos proc.I.proc_loc)
                          [] e n_node_id pname ctls (res_str^node^edge) in
                      if is_found then res
                      else (is_found, rest_call_stk, inter_id, intra_id+1,last_cond_lno, var_decls, false, last_n_id, path_ctls,res_str1)
end
                | _ -> failwith "not a valid error trace (CallNRecv 2)"
      end
    | I.Seq {I.exp_seq_exp1 = e1; I.exp_seq_exp2 = e2} ->
          let seq_id = get_seq_id () in
          let () = x_binfo_hp (add_str "=========START" string_of_int) seq_id no_pos in
          let () = x_binfo_hp (add_str "SEQ - inter_id " string_of_int) inter_id no_pos in
          let is_found, rest_call_stk, inter_id1, intra_id1,last_cond_lno1, var_decls1, is_returning, last_n_id, ctls1,res_str1 = recf_no_change e1 in
          if is_found || is_returning then
            let () = x_binfo_hp (add_str "----(found, returning)" (pr_pair string_of_bool string_of_bool)) (is_found,is_returning) no_pos in
            is_found, rest_call_stk,  inter_id1, intra_id1, last_cond_lno1,var_decls1, is_returning, last_n_id, ctls1,res_str1
          else
            let () = x_binfo_hp (add_str "----" pr_id) "NOT FOUND" no_pos in
            let () = x_tinfo_hp (add_str "inter_id" (string_of_int)) inter_id no_pos in
            let res=
              recf rest_call_stk inter_id (intra_id1) last_cond_lno1 var_decls1 e2 last_n_id procn ctls1 res_str1
            in
            let () = x_binfo_hp (add_str "=========END" string_of_int) seq_id no_pos in
            res
    | I.While {exp_while_body = wb} -> failwith "not handled yet"
    | I.Assign {exp_assign_op =op;
      exp_assign_lhs =e1;
      exp_assign_rhs = e2;
      exp_assign_pos = p} -> begin
        (**********************)
        let assign_helper call_stk prev_n_id res_str=
          let () = x_binfo_hp (add_str ("Assgin" ^ (string_of_int inter_id) ) (!I.print_exp)) e no_pos in
          let new_node_edge str_code=
            let str_line = line_number_of_pos p in
            let n_node_id = (id_to_string inter_id intra_id) in
            let node = mk_node n_node_id in
            let edge = mk_edge prev_n_id n_node_id str_code str_line in
            let n_intra_id = intra_id+1 in
             n_node_id, node, edge, n_intra_id
          in
          let lhs = (IP.string_of_exp e1) in
          let rhs = (IP.string_of_exp e2) in
          let line_no = (start_line_of_pos p) in
          let n_intra_id, n_node_id, n_res_str=
            if not !witness_from_orig then
              let str_code =  lhs ^ (IP.string_of_assign_op op) ^ rhs ^";" in
              let n_node_id, node, edge, n_intra_id = new_node_edge str_code in
              (n_intra_id, n_node_id, res_str^ node ^ edge)
            else if ( not (is_tmp_var lhs) && not(is_tmp_var rhs)) &&
              List.for_all (fun id -> id != line_no) var_decls then
              let str_code = Array.get orig_src_lines line_no in
              let n_node_id, node, edge, n_intra_id = new_node_edge str_code in
              (n_intra_id, n_node_id, res_str^ node ^ edge)
            else
              (intra_id, prev_n_id, res_str)
          in
          false, call_stk, inter_id, n_intra_id, last_cond_lno, var_decls,false, n_node_id , path_ctls, (n_res_str)
        in
        (**********************)
        match is_fun_call e2 with
          | None -> assign_helper call_stk prev_n_id res_str
          | Some pname -> begin
              let () = x_binfo_hp (add_str ("Call at RHS of Assign -> inter_id" ^ (string_of_int inter_id) ) (!I.print_exp)) e2 no_pos in
              (* if call_stk=[] then *)
              (*   false, [], inter_id,intra_id, last_cond_lno, var_decls,false, prev_n_id, path_ctls,res_str *)
              (* else *)
              (*   let (stk_pname, ctls), rest_stk = get_fst call_stk in *)
              (*   if not (string_eq stk_pname pname) then *)
              (*     failwith "not a valid error trace (CallNRecv 1)" *)
              (*   else *)
              (*     let proc = I.look_up_proc_def_raw iprog.I.prog_proc_decls pname in *)
              (*     match proc.I.proc_body with *)
              (*       | Some proc_body -> begin *)
              (*           let str_code = (!I.print_exp e2) in *)
              (*           let str_line = line_number_of_pos (I.pos_of_exp e2) in *)
              (*           let n_node_id = enter_fnc_id_to_string inter_id in *)
              (*           let node = mk_node n_node_id in *)
              (*           let edge = mk_edge_func_call prev_n_id n_node_id str_code str_line pname in *)
              (*           let n_inter_id = get_inter_id () in *)
              (*           let ((is_found, rest_call_stk, inter_id1, intra_id1,last_cond_lno1, var_decls1, is_returning, last_n_id, ctls1,res_str1) as res) = *)
              (*             recf rest_stk n_inter_id 0 (start_line_of_pos proc.I.proc_loc) *)
              (*                 [] proc_body n_node_id pname ctls (res_str^node^edge) in *)
              (*           if is_found then res *)
              (*           else assign_helper rest_stk last_n_id res_str1 *)
              (*         end *)
              (*       | _ -> failwith "not a valid error trace (CallNRecv at Assign)" *)
              let ((is_found, rest_call_stk, inter_id1, intra_id1,last_cond_lno1, var_decls1, is_returning, last_n_id, ctls1,res_str1) as res) =  func_call call_stk pname e2 in
              if is_found then res
              else assign_helper rest_call_stk last_n_id res_str1
            end
      end
    | I.Binary _ ->
          let () = x_binfo_hp (add_str "Binary" (pr_id)) "" no_pos in
          false, call_stk, inter_id, intra_id,last_cond_lno, var_decls,false, prev_n_id , path_ctls, res_str
    | I.VarDecl {I.exp_var_decl_decls = vars;
      exp_var_decl_pos = p;
      } -> begin
          let () = x_binfo_hp (add_str ("VarDecl " ^ (string_of_int inter_id)) (!I.print_exp)) e no_pos in
          let is_tmp_var = if not !witness_from_orig then false
          else match vars with
            | [(id,_,_)] -> begin
               is_tmp_var id
              end
            | _ -> false
          in
          if is_tmp_var then
            false, call_stk, inter_id, intra_id,last_cond_lno,var_decls,false, prev_n_id , path_ctls, res_str
          else
             let str_line = line_number_of_pos p in
             let last_lno = (start_line_of_pos p) in
             let str_code = if not !witness_from_orig then
               !I.print_exp e ^ ";"
             else Array.get orig_src_lines last_lno in
             let n_node_id = (id_to_string inter_id intra_id) in
             let node = mk_node n_node_id in
             let edge = mk_edge prev_n_id n_node_id str_code str_line in
             let n_intra_id = intra_id+1 in
             false, call_stk, inter_id, n_intra_id, last_cond_lno,(var_decls@[last_lno]), false, n_node_id , path_ctls, (res_str ^ node ^ edge)
      end
    | _ ->
          let () = x_binfo_hp (add_str "Not Handled " (!I.print_exp)) e no_pos in
          false, call_stk, inter_id, intra_id,last_cond_lno, var_decls, false, prev_n_id , path_ctls, res_str

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
  let () = print_string_quiet ("call_stk: " ^ (string_of_call_stk call_stk)) in
  let old_xml_flag = !xml_flag in
  let () = xml_flag := true in
  let src_lines = Array.create 100 ("") in
  let () = if !witness_from_orig then
    parse_src src_lines src_fname
  else ()
  in
  (*preprocess iprog*)
  let iprog = remove_tmp_local_vars iprog0 in
  (* body *)
  let (init_pname, init_ctls),rest_call_stk = get_fst call_stk in
  let init_proc = I.look_up_proc_def_raw iprog.I.prog_proc_decls init_pname in
  let res =
    match init_proc.I.proc_body with
      | Some e ->
            let inter_id = get_inter_id () in
            let entry_id = enter_fnc_id_to_string inter_id in
            let entry_node = mk_entry_node entry_id in
            let is_found, rest_call_stk, _, _,_,_,_,_,_, body_str=
              witness_search_loop iprog cprog src_lines rest_call_stk 
                  1 inter_id (start_line_of_pos init_proc.I.proc_loc) [] e entry_id init_pname init_ctls entry_node
            in
            let () = print_string_quiet ("call_stk (final): " ^ (string_of_call_stk rest_call_stk)) in
            if not is_found || rest_call_stk != [] then
              let () = print_string_quiet "\nnot a valid error trace\n" in
              ""
            else
              (* header *)
              let witness_header = gen_witness_header () in
              let norm_src_fname =  Globals.norm_file_name src_fname in
              let str_conclude = get_witness_conclude () in
              let s = witness_header^body_str^str_conclude in
              let fname = save_witness (norm_src_fname  ^ ".graphml") s in
              fname
      | None -> ""
  in
  let () = xml_flag := old_xml_flag in
  res
