#include "xdebug.cppo"
open VarGen
open Gen.Basic
open Globals
open HipUtil
module C = Cast
module CP = Cpure
module CF = Cformula

module M = Lexer.Make(Token.Token)

let usage_msg = Sys.argv.(0) ^ " [options] <source files>"

let set_source_file arg =
  Globals.source_files := arg :: !Globals.source_files

let parse_file_full file_name (primitive: bool) =
  proc_files # push file_name;
  let org_in_chnl = open_in file_name in
  try
    Globals.input_file_name:= file_name;
    let parser_to_use = (
      if primitive then "default"
      else !Parser.parser_name
    ) in
    (* start parsing *)
    let (s,p) = Parser.parse_hip_with_option file_name (Stream.of_channel org_in_chnl) in
    let prog = (
      let _ = Scriptarguments.parse_arguments_with_string s in
      p
    ) in
    close_in org_in_chnl;
    let prog1 = if not primitive then
        let p = IastUtil.generate_free_fnc prog in
        p
      else prog
    in
    prog1
  with
    End_of_file -> exit 0
  | M.Loc.Exc_located (l,t)-> (
      raise t
    )

(* Parse all prelude files declared by user.*)
let process_primitives (file_list: string list) : Iast.prog_decl list =
  flush stdout;
  let new_names = List.map (fun c-> (Gen.get_path Sys.executable_name)
                                    ^ (String.sub c 1 ((String.length c) - 2)))
      file_list in
  if (Sys.file_exists "./prelude.ss") then
    [(parse_file_full "./prelude.ss" true)]
  else List.map (fun x -> parse_file_full x true) new_names

let process_primitives (file_list: string list) : Iast.prog_decl list =
  let pr1 = pr_list (fun x -> x) in
  let pr2 = pr_list (fun x -> (pr_list Iprinter.string_of_rel_decl) x.Iast.prog_rel_decls)  in
  Debug.no_1 "process_primitives" pr1 pr2 process_primitives file_list

(* Parse all include files declared by user.*)
let process_includes (file_list: string list) (curdir: string) : Iast.prog_decl list =
  Debug.info_zprint (lazy ((" processing includes \"" ^(pr_list pr_id file_list)))) no_pos;
  flush stdout;
  List.map  (fun x->
      if(Sys.file_exists (curdir^"/"^x)) then parse_file_full (curdir^"/"^x) true
      else
        let hip_dir = (Gen.get_path Sys.executable_name) ^x in
        parse_file_full hip_dir true (* WN is include file a primitive? *)
    )  file_list

let process_includes (file_list: string list) (curdir: string): Iast.prog_decl list =
  let pr1 = pr_list (fun x -> x) in
  let pr2 = pr_list (fun x -> (pr_list Iprinter.string_of_rel_decl) x.Iast.prog_rel_decls)  in
  Debug.no_1 "process_includes" pr1 pr2 (fun _ -> process_includes file_list curdir) file_list

(* Process all intermediate primitives which receive after parsing *)
let rec process_intermediate_prims prims_list =
  match prims_list with
  | [] -> []
  | hd::tl ->
    let iprims = x_add_1 Globalvars.trans_global_to_param hd in
    let iprims = Iast.label_procs_prog iprims false in
    iprims :: (process_intermediate_prims tl)

(* Process prelude pragma *)
let rec process_header_with_pragma hlist plist =
  match plist with
  | [] -> hlist
  | hd::tl ->
    let new_hlist = if (hd = "NoImplicitPrelude") then [] else hlist in
    process_header_with_pragma new_hlist tl

let process_include_files incl_files ref_file =
  if(List.length incl_files >0) then
    let header_files = Gen.BList.remove_dups_eq (=) incl_files in 
    let new_h_files = process_header_with_pragma header_files !Globals.pragma_list in
    try
      let (curdir,_)=BatString.rsplit ref_file "/" in
      (* let _= print_endline_quiet ("BachLe curdir: "^curdir) in    *)
      let prims_list = process_includes new_h_files curdir in
      prims_list
    with Not_found ->
      let prims_list = process_includes new_h_files "." in (*list of includes in header files*)
      prims_list
  else
    []

(***************end process preclude*********************)

let process_lib_file prog =
  let parse_one_lib (ddecls,vdecls) lib=
    let lib_prog = parse_file_full lib false in
    (*each template data of lib, find corres. data in progs, generate corres. view*)
    let tmpl_data_decls = List.filter (fun dd -> dd.Iast.data_is_template) lib_prog.Iast.prog_data_decls in
    let horm_views = Sa3.generate_horm_view tmpl_data_decls lib_prog.Iast.prog_view_decls prog.Iast.prog_data_decls in
    (ddecls@lib_prog.Iast.prog_data_decls),(vdecls@lib_prog.Iast.prog_view_decls@horm_views)
  in
  let ddecls,vdecls = List.fold_left parse_one_lib ([],[]) !Globals.lib_files in
  {prog with Iast.prog_data_decls = prog.Iast.prog_data_decls @ ddecls;
             Iast.prog_view_decls = prog.Iast.prog_view_decls @ vdecls;}


(* after scriptaguments are read *)
let hip_prologue () =
  Globals.is_hip_running := true;
  Globals.infer_const_obj # init

(* Process primitives list in prelude.ss.                   *)
let replace_with_user_include
    prim_lists prim_incls =
  let is_same_prim
      proc1 proc2 =
    match proc1.Iast.proc_body, proc2.Iast.proc_body with
    | None, None ->
      (proc1.Iast.proc_name = proc2.Iast.proc_name) 
    | _, _ ->
      false
  in
  let is_covered_by_user
      proc prim_incls =
    List.fold_left (fun r prog -> r || (List.fold_left (fun r1 proc1 ->
        r1 || (is_same_prim proc proc1)) false prog.Iast.prog_proc_decls)) false
      prim_incls
  in
  List.map (fun prog -> { prog with Iast.prog_proc_decls
                                    = List.filter (fun pc ->
                                        not (is_covered_by_user pc prim_incls))
                                        prog.Iast.prog_proc_decls}) prim_lists

(***************end process compare file*****************)

let saved_cprog = Cast.cprog (* ref None *)
let saved_prim_names = ref None

(*Working*)
let process_source_full source =
  let prog = parse_file_full source false in
  let () = Debug.ninfo_zprint
      (lazy (("       iprog:" ^ (Iprinter.string_of_program prog)))) no_pos in
  let prog = process_lib_file prog in
  (* Remove all duplicated declared prelude *)
  let header_files = match !Globals.prelude_file with
    | None -> ["\"prelude.ss\""]
    | Some s -> ["\""^s^"\""] in
  let new_h_files = process_header_with_pragma header_files !Globals.pragma_list in
  let prims_list = process_primitives new_h_files in (*list of primitives in header files*)
  let prims_incls = process_include_files prog.Iast.prog_include_decls source in
  let prims_list = replace_with_user_include prims_list prims_incls in
  if (!Tpdispatcher.tp_batch_mode) then Tpdispatcher.start_prover ();
  (* Global variables translating *)
  let iprims_list = process_intermediate_prims prims_list in
  let iprims = Iast.append_iprims_list_head iprims_list in
  let prim_names =
    (List.map (fun d -> d.Iast.data_name) iprims.Iast.prog_data_decls) @
    (List.map (fun v -> v.Iast.view_name) iprims.Iast.prog_view_decls) @
    ["__Exc"; "__Fail"; "__Error"; "__MayError";"__RET"]
  in
  let () = saved_prim_names := Some prim_names in
  let prog = Iast.append_iprims_list_head ([prog]@prims_incls) in
  let prog, _ = Hashtbl.fold
    (fun id _ (prog, acc) ->
      if List.exists (fun p -> String.compare p id == 0) acc then (prog, acc)
      else
        let prog = Parser.add_tnt_prim_proc prog id in
        (prog, acc @ [id]))
    Iast.tnt_prim_proc_tbl (prog, [])
  in
  let intermediate_prog = x_add_1 Globalvars.trans_global_to_param prog in
  let intermediate_prog = IastUtil.pre_process_of_iprog iprims intermediate_prog in
  let intermediate_prog = Iast.label_procs_prog intermediate_prog true in
  let search_for_locklevel proc =
    if (not !Globals.allow_locklevel) then
      let struc_fv = Iformula.struc_free_vars false proc.Iast.proc_static_specs in
      let b = List.exists (fun (id,_) -> (id = Globals.waitlevel_name)) struc_fv in
      if b then
        Globals.allow_locklevel := true
  in

  (*to improve: annotate field*)
  let () = Iast.annotate_field_pure_ext intermediate_prog in
  (*END: annotate field*)
  let cprog, tiprog = Astsimp.trans_prog intermediate_prog (*iprims*) in
  let () = saved_cprog := cprog in
  let () = Lemma.sort_list_lemma tiprog in
  let () = List.iter (fun x -> x_add Lemma.process_list_lemma_helper x tiprog cprog (fun a b -> b)) tiprog.Iast.prog_coercion_decls in
  (* ========= end - lemma process (normalize, translate, verify) ========= *)
  let c = cprog in
  let todo_unk = List.map (fun cadef ->
      let () = Smtsolver.add_axiom cadef.Cast.axiom_hypothesis Smtsolver.IMPLIES cadef.Cast.axiom_conclusion in
      Z3.add_axiom cadef.Cast.axiom_hypothesis Z3.IMPLIES cadef.Cast.axiom_conclusion
    ) (List.rev cprog.Cast.prog_axiom_decls) in
  (* print_string (Cprinter.string_of_program cprog); *)
  (try
     ignore (Typechecker.check_prog intermediate_prog cprog);
   with _ as e -> begin
       print_string_quiet ("\nException"^(Printexc.to_string e)^"Occurred!\n");
       print_string_quiet ("\nError1(s) detected at main "^"\n");
       let () = Log.process_proof_logging !Globals.source_files cprog prim_names in
       raise e
     end);

  (* Stopping the prover *)
  if (!Tpdispatcher.tp_batch_mode) then Tpdispatcher.stop_prover ();
  (* Get the total verification time *)
  let ptime4 = Unix.times () in
  let t4 = ptime4.Unix.tms_utime +. ptime4.Unix.tms_cutime
           +. ptime4.Unix.tms_stime +. ptime4.Unix.tms_cstime   in

  silenced_print print_string ("\nTotal verification time: "
                               ^ (string_of_float t4) ^ " second(s)\n")

let process_source_list source_files =
  match source_files with
  | [] -> []
  | file_name::_ ->
    let index = try String.rindex file_name '.' with _ -> 0 in
    let length = (String.length file_name) - index in
    let ext = String.lowercase(String.sub file_name index length) in
    if (ext = ".java") then
      let ss_file_name = file_name ^ ".ss" in
      [process_source_full ss_file_name]
    else
      let parser = !Parser.parser_name in
      let () = Parser.parser_name := parser in
      List.map process_source_full source_files

let main1 () =
  Arg.parse Scriptarguments.hip_arguments set_source_file usage_msg;
  Tpdispatcher.init_tp();
  hip_prologue ();
  let () = record_backtrace_quite () in
  if List.length (!Globals.source_files) = 0 then begin
    print_string "Source file(s) not specified\n"
  end;
  let todo_unk:unit list = process_source_list !Globals.source_files in
  ()

let finalize_bug () =
  let () = Log.last_cmd # dumping "finalize on hip" in
  let cprog = !saved_cprog in
  let () =
    (match !saved_prim_names with
     | Some(prim_names) ->
       let () = Log.process_proof_logging !Globals.source_files cprog prim_names in ()
     | None ->
       let () = Log.process_proof_logging !Globals.source_files cprog [] in ()
    ) in
  if (!Tpdispatcher.tp_batch_mode) then Tpdispatcher.stop_prover ()

let () =
  try
    main1 ()
  with _ as e ->
    begin
      finalize_bug ();
      print_string_quiet "caught\n";
      Printexc.print_backtrace stderr;
      print_string_quiet ("\nException occurred: " ^ (Printexc.to_string e));
      print_string_quiet ("\nError3(s) detected at main \n")
    end
