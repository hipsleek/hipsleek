open Gen.Basic
open Globals

module H = Hashtbl
module Err = Error
module CP = Cpure
module CF = Cformula
module MCP = Mcpure
module CEQ = Checkeq
module CAU = Cautility
let usage_msg = Sys.argv.(0) ^ " [options] <source files>"

(* let source_files = ref ([] : string list) *)

let set_source_file arg = 
  source_files := arg :: !source_files 

let process_cmd_line () = Arg.parse Scriptarguments.compare_arguments set_source_file usage_msg
module M = Lexer.Make(Token.Token)

let process_cp_file file_name =
 let _ = Debug.ninfo_pprint  ("File to compare: " ^ file_name ^ "\n" ) no_pos in
  let org_in_chnl = open_in file_name in 
  try
    let cp_prog  = Parser.parse_compare file_name (Stream.of_channel org_in_chnl) in
    close_in org_in_chnl;
    cp_prog
  with
      End_of_file -> exit 0
    | M.Loc.Exc_located (l,t)->
      (print_string ((Camlp4.PreCast.Loc.to_string l)^"\n --error: "^(Printexc.to_string t)^"\n at:"^(Printexc.get_backtrace ()));
       raise t)

let parse_file_full file_name =  (*prelude.ss*)
  let org_in_chnl = open_in file_name in
  try
    let _ = Gen.Profiling.push_time "Parsing" in
    Globals.input_file_name:= file_name;
    let prog = Parser.parse_hip file_name (Stream.of_channel org_in_chnl) in
    close_in org_in_chnl;
    let _ = Gen.Profiling.pop_time "Parsing" in
    prog
  with
      End_of_file -> exit 0
    | M.Loc.Exc_located (l,t)->
      (print_string ((Camlp4.PreCast.Loc.to_string l)^"\n --error: "^(Printexc.to_string t)^"\n at:"^(Printexc.get_backtrace ()));
       raise t)

(* Process all intermediate primitives which receive after parsing *)
let rec process_intermediate_prims prims_list =
  match prims_list with
  | [] -> []
  | hd::tl ->
        let iprims = Globalvars.trans_global_to_param hd in
        let iprims = Iast.label_procs_prog iprims false in
                iprims :: (process_intermediate_prims tl)

(* Parse all prelude files declared by user.*)
let process_primitives (file_list: string list) : Iast.prog_decl list =
  Debug.ninfo_pprint (" processing primitives \"" ^(pr_list pr_id file_list)) no_pos;
  flush stdout;
  let new_names = List.map (fun c-> (Gen.get_path Sys.executable_name) ^ (String.sub c 1 ((String.length c) - 2))) file_list in
  if (Sys.file_exists "./prelude.ss") then [parse_file_full "./prelude.ss"]
  else List.map parse_file_full new_names

let process_primitives (file_list: string list) : Iast.prog_decl list =
  let pr1 = pr_list (fun x -> x) in
  let pr2 = pr_list (fun x -> (pr_list Iprinter.string_of_rel_decl) x.Iast.prog_rel_decls)  in
  Debug.no_1 "process_primitives" pr1 pr2 process_primitives file_list

(* Process prelude pragma *)
let rec process_header_with_pragma hlist plist =
  match plist with
  | [] -> hlist
  | hd::tl ->
        let new_hlist = if (hd = "NoImplicitPrelude") then [] else hlist in
            process_header_with_pragma new_hlist tl

let process_sources_full sources =
  let source1 = List.hd sources in
  let source2 = List.hd (List.tl sources) in
  let cp_iprog2 = process_cp_file source2 in
  let cp_iprog1 = process_cp_file source1 in (*add here*)
  let iprog1 = cp_iprog1.Iast.cp_hprog in
  let iprog2 = cp_iprog2.Iast.cp_hprog in
  (* let cp_iprog1 = { cp_iprog1 with *)
  (*   Iast.cp_hprog = {cp_iprog1.Iast.cp_hprog with *)
  (*     Iast.prog_data_decls = iprog1.Iast.prog_data_decls @ iprog2.Iast.prog_data_decls; *)
  (*     Iast.prog_logical_var_decls = iprog1.Iast.prog_logical_var_decls @ iprog2.Iast.prog_logical_var_decls; *)
  (*     Iast.prog_global_var_decls = iprog1.Iast.prog_global_var_decls @ iprog2.Iast.prog_global_var_decls; *)
  (*     Iast.prog_enum_decls = iprog1.Iast.prog_enum_decls @ iprog2.Iast.prog_enum_decls; *)
  (*     Iast.prog_view_decls = iprog1.Iast.prog_view_decls @ iprog2.Iast.prog_view_decls; *)
  (*     Iast.prog_func_decls = iprog1.Iast.prog_func_decls @ iprog2.Iast.prog_func_decls; *)
  (*     Iast.prog_rel_decls = iprog1.Iast.prog_rel_decls @ iprog2.Iast.prog_rel_decls; *)
  (*     Iast.prog_hp_decls = iprog1.Iast.prog_hp_decls @ iprog2.Iast.prog_hp_decls; *)
  (*     Iast.prog_hp_ids = iprog1.Iast.prog_hp_ids @ iprog2.Iast.prog_hp_ids; *)
  (*     Iast.prog_rel_ids = iprog1.Iast.prog_rel_ids @ iprog2.Iast.prog_rel_ids; *)
  (*     Iast.prog_axiom_decls = iprog1.Iast.prog_axiom_decls @ iprog2.Iast.prog_axiom_decls; *)
  (*     Iast.prog_hopred_decls = iprog1.Iast.prog_hopred_decls @ iprog2.Iast.prog_hopred_decls *)
  (*   } *)
  (* } *)
  (* in *)
  let convert cp_iprog =
    let prog = cp_iprog.Iast.cp_hprog in
    let cpprocs = cp_iprog.Iast.cp_cpproc_decls in
    let header_files = Gen.BList.remove_dups_eq (=) !Globals.header_file_list in (*prelude.ss*)
    let new_h_files = process_header_with_pragma header_files !Globals.pragma_list in
    let prims_list = process_primitives new_h_files in (*list of primitives in header files*)
    let iprims_list = process_intermediate_prims prims_list in
    let iprims = Iast.append_iprims_list_head iprims_list in
    let intermediate_prog = Globalvars.trans_global_to_param prog in
    let intermediate_prog=IastUtil.pre_process_of_iprog iprims intermediate_prog in
    let intermediate_prog = Iast.label_procs_prog intermediate_prog true in
    let cp_prog = Astsimp.trans_cpprog intermediate_prog cpprocs (*iprims*) in
    cp_prog
  in
  (convert cp_iprog1, convert cp_iprog2)
  

let process_two_source_files sources_files =
  let (cp_prog1, cp_prog2) = process_sources_full !Globals.source_files in
  let test_procs1 = cp_prog1.Cast.cp_cpproc_decls in
  let test_procs2 = cp_prog2.Cast.cp_cpproc_decls in
  if (List.length test_procs1 == 0 || List.length test_procs2 == 0) then print_string "One file does not have any test-components\n" 
  else (
    (* print_string ("TEST PROC 1: " ^ test_proc1.Cast.cp_proc_name ^ "\n"); *)
    (* print_string ("TEST PROC 2: " ^ test_proc2.Cast.cp_proc_name ^ "\n"); *)
    let rec test_one_proc proc1 procs = 
      try (
	let proc2 = List.find (fun proc2 -> String.compare proc1.Cast.cp_proc_name proc2.Cast.cp_proc_name == 0) procs in
	CAU.cp_test_proc proc1 proc2
      )
      with | Not_found -> ()
    in
    List.iter (fun proc -> test_one_proc proc test_procs2) test_procs1
  )

let _ = 
  print_string "compare";
  try
    process_cmd_line ();
    Scriptarguments.check_option_consistency ();
    if List.length (!Globals.source_files) = 0 then
      print_string "Source file(s) not specified\n"
    else if List.length (!Globals.source_files) == 2 then (
      print_string "Start comparing two source files\n";
      let _ = Gen.Profiling.push_time "Overall" in
      let _ =  process_two_source_files !Globals.source_files in
      let _ = Gen.Profiling.pop_time "Overall" in
      ()
    )
    else print_string "Should given two source files\n"
  with _ as e -> begin
    print_string "caught\n"; Printexc.print_backtrace stdout;
    print_string ("\nException occurred: " ^ (Printexc.to_string e));
    print_string ("\nError(s) detected at main \n");
  end
