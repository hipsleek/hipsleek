#include "xdebug.cppo"
open VarGen
(* test - added to immutability branch *)
(******************************************)
(* command line processing                *)
(******************************************)
open Gen.Basic
open Globals
open HipUtil
module C = Cast
module CP = Cpure
module CF = Cformula

module M = Lexer.Make(Token.Token)

let to_java = ref false

let usage_msg = Sys.argv.(0) ^ " [options] <source files>"

let set_source_file arg = 
  Globals.source_files := arg :: !Globals.source_files

let process_cmd_line () =
    if not (Perm.allow_perm ()) then Perm.disable_para();
	Arg.parse Scriptarguments.hip_arguments set_source_file usage_msg;
	if !Globals.override_slc_ps then Globals.en_slc_ps:=false
	else ()

let print_version () =
  print_endline ("HIP: A Verifier for Heap Manipulating Programs");
  print_endline ("Version 1.0");
  print_endline ("THIS SOFTWARE IS PROVIDED AS-IS, WITHOUT ANY WARRANTIES.");
  print_endline ("IT IS FREE FOR NON-COMMERCIAL USE");
  print_endline ("Copyright @ PLS2 @ NUS")



(******************************************)
(* main function                          *)
(******************************************)


let parse_file_full file_name (primitive: bool) =
  proc_files # push file_name;
  let org_in_chnl = open_in file_name in
  try
    Globals.input_file_name:= file_name;
    (* choose parser to be used *)
    let parser_to_use = (
      if primitive || (!Parser.parser_name = "default") then
        (* always parse primitive files by default parser *)
        "default" 
      else if (!Parser.parser_name = "default") then
        (* default parser is indicated in command line parameter *)
        "default"
      else if (!Parser.parser_name = "cil") then
        (* cil parser is indicated in command line parameter *)
        "cil"
      else (
        (* no parser is indicated, decide to use which ones by file name extension  *)
        (* let index = try String.rindex file_name '.' with _ -> 0 in              *)
        (* let length = (String.length file_name) - index in                       *)
        (* let ext = String.lowercase(String.sub file_name index length) in        *)
        (* if (ext = ".c") || (ext = ".cc") || (ext = ".cpp") || (ext = ".h") then *)
        (*   "cil"                                                                 *)
        (* else if(ext = ".java") then "joust"                                     *)
        (* else "default"                                                          *)
          "default"
      )
    ) in
    (* start parsing *)
    if not primitive then
      if (not !Globals.web_compile_flag) then
      print_endline_quiet ("Parsing file \"" ^ file_name ^ "\" by " 
                     ^ parser_to_use ^ " parser...");
    let () = Gen.Profiling.push_time "Parsing" in
    let prog = (
      if parser_to_use = "cil" then
        let cil_prog = Cilparser.parse_hip file_name in
        cil_prog
      else if parser_to_use = "cil-i" then
        let cil_prog = Cilparser.parse_prep file_name in
        let stdlib_procs = Parser.create_tnt_stdlib_proc () in
        { cil_prog with Iast.prog_proc_decls = cil_prog.Iast.prog_proc_decls @ stdlib_procs; }
      else
        (* if parser_to_use = "joust" then                                                        *)
        (*   let ss_file_name = file_name ^ ".ss" in                                              *)
        (*   let result_str = Pretty_ss.print_out_str_from_files_new [file_name] ss_file_name in  *)
        (*   (* let () = print_endline_quiet "using jparser" in *)                                       *)
        (*   let input_channel = open_in ss_file_name in                                          *)
        (*   let parseresult = Parser.parse_hip ss_file_name (Stream.of_channel input_channel) in *)
        (*   close_in input_channel;                                                              *)
        (*   (*Sys.remove "tmp_java.ss";*)                                                        *)
        (*   parseresult                                                                          *)
        (* else                                                                                   *)
          (* Parser.parse_hip file_name (Stream.of_channel org_in_chnl) *)
        
        let (s,p) = Parser.parse_hip_with_option file_name (Stream.of_channel org_in_chnl) in
        let _ = Scriptarguments.parse_arguments_with_string s in
        p
    ) in
    close_in org_in_chnl;
    let () = Gen.Profiling.pop_time "Parsing" in
    let prog1 = if not primitive then
      let _ = Debug.ninfo_hprint (add_str "to add free" pr_id) "start\n" no_pos in
      let p = IastUtil.generate_free_fnc prog in
      let _ = Debug.ninfo_hprint (add_str "to add free" pr_id) "end\n" no_pos in
      p
    else prog
    in
    prog1
  with
      End_of_file -> exit 0
    | M.Loc.Exc_located (l,t)-> (
        print_string_quiet ((Camlp4.PreCast.Loc.to_string l)^"\n --error: "
                            ^(Printexc.to_string t)^"\n at:"^(get_backtrace_quiet ()));
        raise t
      )

(* Parse all prelude files declared by user.*)
let process_primitives (file_list: string list) : Iast.prog_decl list =
  if (not !Globals.web_compile_flag) then
  Debug.info_zprint (lazy ((" processing primitives \"" ^(pr_list pr_id file_list) ^ "\n"))) no_pos;
  flush stdout;
  let new_names = List.map (fun c-> (Gen.get_path Sys.executable_name) ^ (String.sub c 1 ((String.length c) - 2))) file_list in
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
        let iprims = Globalvars.trans_global_to_param hd in
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
      let prims_list = process_includes new_h_files curdir in (*list of includes in header files*)
	    prims_list
		with Not_found ->
			let prims_list = process_includes new_h_files "." in (*list of includes in header files*)
	    prims_list
	else
		[]		
		
(***************end process preclude*********************)

(**************vp: process compare file******************)
let parse_file_cp file_name = 
  let () = print_string ("File to compare: " ^ file_name ^ "\n" ) in
  let org_in_chnl = open_in file_name in 
  try
    let a  = Parser.parse_cpfile file_name (Stream.of_channel org_in_chnl) in
    close_in org_in_chnl;
    a
  with
      End_of_file -> exit 0
    | M.Loc.Exc_located (l,t)-> (
        print_string_quiet ((Camlp4.PreCast.Loc.to_string l)^"\n --error: "^(Printexc.to_string t)^"\n at:"^(Printexc.get_backtrace ()));
        raise t
      )

let process_validate prog =
  let file_to_cp = if(String.compare !Globals.validate_target "" != 0) then !Globals.validate_target else (
    "sa/hip/test/ll-append3.cp"
  )
  in
  let (hpdecls, proc_tcomps) = parse_file_cp file_to_cp in 
  let helper procs tcomps =
    let rec update_tcomp proc tcomps =
      let proc_name = proc.Iast.proc_name in
      match tcomps with
        |[] -> proc
        |(id, tcs)::y ->
             let () = Debug.ninfo_hprint (add_str "id" pr_id) id no_pos in
             let () = Debug.ninfo_hprint (add_str "proc_name" pr_id) proc_name no_pos in
             if(String.compare id proc_name == 0) then (
                 {proc with Iast.proc_test_comps = Some tcs}
             )
             else update_tcomp proc y
    in
    List.map (fun proc -> update_tcomp proc tcomps) procs
  in
  {prog with Iast.prog_hp_decls = prog.Iast.prog_hp_decls @ hpdecls;
  Iast.prog_proc_decls = helper prog.Iast.prog_proc_decls proc_tcomps;
  (*store this test for while loops*)
  Iast.prog_test_comps = proc_tcomps}

let process_lib_file prog =
  let parse_one_lib (ddecls,vdecls) lib=
    let lib_prog = parse_file_full lib false in
    (*each template data of lib, find corres. data in progs, generate corres. view*)
    let tmpl_data_decls = List.filter (fun dd -> dd.Iast.data_is_template) lib_prog.Iast.prog_data_decls in
    let horm_views = Sa.generate_horm_view tmpl_data_decls lib_prog.Iast.prog_view_decls prog.Iast.prog_data_decls in
    (ddecls@lib_prog.Iast.prog_data_decls),(vdecls@lib_prog.Iast.prog_view_decls@horm_views)
  in
  let ddecls,vdecls = List.fold_left parse_one_lib ([],[]) !Globals.lib_files in
  {prog with Iast.prog_data_decls = prog.Iast.prog_data_decls @ ddecls;
      Iast.prog_view_decls = prog.Iast.prog_view_decls @ vdecls;}

(* let rec replace_h_formula hformula fl cprog = (\* Long *\) *)
(*   Solver.unfold_heap_x (cprog, None) hformula [] (Cpure.SpecVar (Globals.Named "node", "H", Unprimed)) fl 1 no_pos *)
  (* match hformula with *)
    (* | Cformula.Star sh -> Cformula.Star { sh with *)
    (*       Cformula.h_formula_star_h1 = replace_h_formula sh.Cformula.h_formula_star_h1 iprog; *)
    (*       Cformula.h_formula_star_h2 = replace_h_formula sh.Cformula.h_formula_star_h2 iprog } *)
    (* | Cformula.StarMinus smh -> Cformula.StarMinus { smh with *)
    (*       Cformula.h_formula_starminus_h1 = replace_h_formula smh.Cformula.h_formula_starminus_h1 iprog; *)
    (*       Cformula.h_formula_starminus_h2 = replace_h_formula smh.Cformula.h_formula_starminus_h2 iprog } *)
    (* | Cformula.Conj ch -> Cformula.Conj { ch with *)
    (*       Cformula.h_formula_conj_h1 = replace_h_formula ch.Cformula.h_formula_conj_h1 iprog; *)
    (*       Cformula.h_formula_conj_h2 = replace_h_formula ch.Cformula.h_formula_conj_h2 iprog } *)
    (* | Cformula.ConjStar csh -> Cformula.ConjStar { csh with *)
    (*       Cformula.h_formula_conjstar_h1 = replace_h_formula csh.Cformula.h_formula_conjstar_h1 iprog; *)
    (*       Cformula.h_formula_conjstar_h2 = replace_h_formula csh.Cformula.h_formula_conjstar_h2 iprog } *)
    (* | Cformula.ConjConj cch -> Cformula.ConjConj { cch with *)
    (*       Cformula.h_formula_conjconj_h1 = replace_h_formula cch.Cformula.h_formula_conjconj_h1 iprog; *)
    (*       Cformula.h_formula_conjconj_h2 = replace_h_formula cch.Cformula.h_formula_conjconj_h2 iprog } *)
    (* | Cformula.Phase ph -> Cformula.Phase { ph with *)
    (*       Cformula.h_formula_phase_rd = replace_h_formula ph.Cformula.h_formula_phase_rd iprog; *)
    (*       Cformula.h_formula_phase_rw = replace_h_formula ph.Cformula.h_formula_phase_rw iprog } *)
    (* | Cformula.ViewNode vnh -> *)
    (*       (\* let rec helper vls = match vls with *\) *)
    (*       (\*   | v :: vl -> if v.Cast.view_name == vnh.Cformula.h_formula_view_name then v.Cast.view_formula else helper vl *\) *)
    (*       (\*   | [] -> raise (Failure "No view name") *\) *)
    (*       (\* in helper cprog.Cast.prog_view_decls *\) *)
    (* | _ -> raise (Failure "Impossible") *)

let rec replace_formula cformula cprog =
  match cformula with
    | Cformula.Base fb ->
          let hformula = fb.Cformula.formula_base_heap in
          let fl = fb.Cformula.formula_base_flow in
          let fv = Cformula.fv cformula in
          ( match fv with
            | [] -> cformula
            | hd::tl -> Solver.unfold_heap (cprog, None) hformula fv hd fl 1 no_pos )
          (* Cformula.Base { fb with *)
          (*  Cformula.formula_base_heap = replace_h_formula fb.Cformula.formula_base_heap fb.Cformula.formula_base_flow cprog } *)
    | Cformula.Or fo -> Cformula.Or { fo with
          Cformula.formula_or_f1 = replace_formula fo.Cformula.formula_or_f1 cprog;
          Cformula.formula_or_f2 = replace_formula fo.Cformula.formula_or_f2 cprog }
    | Cformula.Exists fe ->
          let hformula = fe.Cformula.formula_exists_heap in
          let fl = fe.Cformula.formula_exists_flow in
          let fv = Cformula.fv cformula in
          ( match fv with
            | [] -> cformula
            | hd::tl -> Solver.unfold_heap (cprog, None) hformula fv hd fl 1 no_pos )
          (* Cformula.Exists { fe with *)
          (* Cformula.formula_exists_heap = replace_h_formula fe.Cformula.formula_exists_heap fe.Cformula.formula_exists_flow cprog } *)

let rec replace_struc_formula cspec cprog =
  match cspec with
    | Cformula.EAssume ea -> Cformula.EAssume { ea with
          Cformula.formula_assume_simpl = replace_formula ea.Cformula.formula_assume_simpl cprog;
          Cformula.formula_assume_struc = replace_struc_formula ea.Cformula.formula_assume_struc cprog }
    | Cformula.EList el -> Cformula.EList (List.map (fun (spec, struc_for) -> (spec, replace_struc_formula struc_for cprog)) el)
    | Cformula.EInfer ei -> Cformula.EInfer { ei with
          Cformula.formula_inf_continuation = replace_struc_formula ei.Cformula.formula_inf_continuation cprog }
    | Cformula.EBase eb -> Cformula.EBase { eb with
          Cformula.formula_struc_base = replace_formula eb.Cformula.formula_struc_base cprog;
          Cformula.formula_struc_continuation = match eb.Cformula.formula_struc_continuation with
            | None -> None
            | Some sf -> Some (replace_struc_formula sf cprog) }
    | Cformula.ECase ec -> Cformula.ECase { ec with
           Cformula.formula_case_branches = List.map (fun (pure, struc_for) -> (pure, replace_struc_formula struc_for cprog)) ec.Cformula.formula_case_branches }

let print_spec cprog =
  let rec helper cproc_decls =
    match cproc_decls with
      | p :: pl -> (match p.Cast.proc_body with
          | None -> ""
          | Some _ ->
                let () = print_endline_quiet (Cprinter.string_of_struc_formula p.Cast.proc_static_specs) in
                (* let sf = p.Cast.proc_static_specs in *)
                (* let fvs = List.map (fun (t, id) -> Cpure.SpecVar(t, id, Unprimed)) p.Cast.proc_args in *)
                (* let new_sf = List.fold_left (fun sf fv ->  *)
                (*     Solver.unfold_struc_nth 10 (cprog, None) sf fv false 0 no_pos *)
                (*     ) sf fvs in *)
                ("Procedure " ^ p.Cast.proc_name ^ "\n") ^
                    (* Cprinter.string_of_struc_formula_for_spec new_sf *) (* (x_add Solver.unfold_struc_nth 1 (cprog, None) sf (List.hd (List.tl fv)) (\* (Cpure.SpecVar (Globals.Named "node", "x", Unprimed)) *\) false 1 no_pos) *)
                Cprinter.string_of_struc_formula_for_spec (replace_struc_formula p.Cast.proc_static_specs cprog)
        ) ^ (helper pl)
      | [] -> ""
  in
  print_endline (helper (Cast.list_of_procs cprog))

let reverify_with_hp_rel old_cprog iprog =
  (* let new_iviews = Astsimp.transform_hp_rels_to_iviews (Cast.collect_hp_rels old_cprog) in *)
  (* let cprog = Astsimp.trans_prog (Astsimp.plugin_inferred_iviews new_iviews iprog old_cprog) in *)
  let hp_defs, post_hps = Saout.collect_hp_defs old_cprog in
  let need_trans_hprels0, unk_hps = List.fold_left (fun (r_hp_defs, r_unk_hps) (hp_def) ->
      let (hp_kind, _,_,f) = Cformula.flatten_hp_rel_def hp_def in
        match hp_kind with
          |  Cpure.HPRelDefn (hp,r,args) -> begin
                 try
                   let todo_unk = x_add Cast.look_up_view_def_raw 33 old_cprog.Cast.prog_view_decls
                     (Cpure.name_of_spec_var hp)
                   in
                   (r_hp_defs, r_unk_hps)
                 with Not_found ->
                     (*at least one is node typ*)
                     if List.exists (fun sv -> Cpure.is_node_typ sv) (r::args) then
                       if (Cformula.is_unknown_f f) then
                         r_hp_defs, r_unk_hps@[hp]
                       else r_hp_defs@[hp_def], r_unk_hps
                     else r_hp_defs, r_unk_hps
             end
          | _ -> (r_hp_defs, r_unk_hps)
  ) ([],[]) hp_defs in
  (* let () = Debug.info_hprint (add_str "unk_hps " !Cpure.print_svl) unk_hps no_pos in *)
  let need_trans_hprels1 = (* List.map (fun def -> *)
  (*     let new_rhs = List.map (fun (f, og) -> *)
  (*         let nf, esvl= (Cformula.drop_hrel_f f unk_hps) in *)
  (*         let svl = List.fold_left (fun r eargs -> *)
  (*             match eargs with *)
  (*               | [] -> r *)
  (*               | e::_ -> r@(Cpure.afv e) *)
  (*         ) [] esvl in *)
  (*         let nf1 = Cformula.add_quantifiers (Cpure.remove_dups_svl svl) nf in *)
  (*         (nf1 , og) *)
  (*     ) def.Cformula.def_rhs in *)
  (*     {def with Cformula.def_rhs = new_rhs} *)
  (* ) *) need_trans_hprels0
  in
  let proc_name = "" in
  let n_cviews,chprels_decl = Saout.trans_hprel_2_cview iprog old_cprog proc_name need_trans_hprels1 in
  let cprog = Saout.trans_specs_hprel_2_cview iprog old_cprog proc_name unk_hps []
    [] [] need_trans_hprels1 chprels_decl in
  ignore (Typechecker.check_prog iprog cprog)

let hip_epilogue () = 
  (* ------------------ lemma dumping ------------------ *)
  if (!Globals.dump_lemmas) then 
    Lem_store.all_lemma # dump
  else ()
(* -------------------------------------------------------- *)
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
    List.fold_left (fun r prog -> r || (List.fold_left (fun r1 proc1 -> r1 || (is_same_prim proc proc1)) false prog.Iast.prog_proc_decls)) false prim_incls
  in
  List.map (fun prog -> { prog with Iast.prog_proc_decls = List.filter (fun pc -> not (is_covered_by_user pc prim_incls)) prog.Iast.prog_proc_decls}) prim_lists
;;
(* --------------------------------------------------------- *)

(***************end process compare file*****************)

let saved_cprog = ref None
let saved_prim_names = ref None

(*Working*)
let process_source_full source =
  if (not !Globals.web_compile_flag) then
  Debug.info_zprint (lazy (("Full processing file \"" ^ source ^ "\"\n"))) no_pos;
  flush stdout;
  let () = Gen.Profiling.push_time "Preprocessing" in
  let prog = parse_file_full source false in
  let () = Debug.ninfo_zprint (lazy (("       iprog:" ^ (Iprinter.string_of_program prog)))) no_pos in
  let () = Gen.Profiling.push_time "Process compare file" in
  let prog = if(!Globals.validate || !Globals.cp_prefile) then (
      process_validate prog
  )
  else prog
  in
  let prog = process_lib_file prog in
  let () = Gen.Profiling.pop_time "Process compare file" in
  (* Remove all duplicated declared prelude *)
  let header_files = match !Globals.prelude_file with
    | None -> ["\"prelude.ss\""]
    | Some s -> ["\""^s^"\""] in 
  (* let header_files = Gen.BList.remove_dups_eq (=) !Globals.header_file_list in (\*prelude.ss*\) *)
  (*let () = print_endline ("header_files"^((pr_list (fun x -> x)) header_files)) in*)
  let header_files = if (!Globals.allow_inf) then "\"prelude_inf.ss\""::header_files else header_files in
  let new_h_files = process_header_with_pragma header_files !Globals.pragma_list in
  let prims_list = process_primitives new_h_files in (*list of primitives in header files*)
  let () = Debug.ninfo_hprint (add_str "prims_list.proc_decl" (pr_list ((fun prog -> pr_list (fun proc -> match proc.Iast.proc_body with Some b -> Iprinter.string_of_proc_decl proc | None -> "None") prog.Iast.prog_proc_decls)))) prims_list no_pos in
  let prims_incls = process_include_files prog.Iast.prog_include_decls source in
  let () = Debug.ninfo_hprint (add_str "prims_incls.proc_decl" (pr_list ((fun prog -> pr_list (fun proc -> match proc.Iast.proc_body with Some b -> Iprinter.string_of_proc_decl proc | None -> "None") prog.Iast.prog_proc_decls)))) prims_incls no_pos in
  let prims_list = replace_with_user_include prims_list prims_incls in
  let () = Debug.ninfo_hprint (add_str "new_prims_lists.proc_decl" (pr_list ((fun prog -> pr_list (fun proc -> Iprinter.string_of_proc_decl proc) prog.Iast.prog_proc_decls)))) prims_list no_pos in
  if !to_java then begin
    print_string ("Converting to Java..."); flush stdout;
    let tmp = Filename.chop_extension (Filename.basename source) in
    let main_class = Gen.replace_minus_with_uscore tmp in
    let java_str = Java.convert_to_java prog main_class in
    let tmp2 = Gen.replace_minus_with_uscore (Filename.chop_extension source) in
    let jfile = open_out ("output/" ^ tmp2 ^ ".java") in
    output_string jfile java_str;
    close_out jfile;
    (* print_string (" done-1.\n"); flush stdout; *)
    exit 0
  end;
  (* Dump prog into ss file  *)
  if (!Scriptarguments.dump_ss) then (
    let dump_file = "logs/" ^ (Filename.basename source) ^ ".gen-ss" in
    let oc = open_out dump_file in
    Printf.fprintf  oc "%s\n" (Iprinter.string_of_program prog);
    close_out oc;
  );
  if (!Scriptarguments.parse_only) then
    let () = Gen.Profiling.pop_time "Preprocessing" in
    print_string (Iprinter.string_of_program prog)
  else
    if (!Tpdispatcher.tp_batch_mode) then Tpdispatcher.start_prover ();
    (* Global variables translating *)
    let () = Gen.Profiling.push_time "Translating global var" in
    (* let () = print_string ("Translating global variables to procedure parameters...\n"); flush stdout in *)
   
    (* Append all primitives in list into one only *)
		(* let () = print_endline_quiet ("process_source_full: before  process_intermediate_prims ") in *)
    let iprims_list = process_intermediate_prims prims_list in
		(* let () = print_endline_quiet ("process_source_full: after  process_intermediate_prims") in *)
    let iprims = Iast.append_iprims_list_head iprims_list in
    
    let prim_names = 
      (List.map (fun d -> d.Iast.data_name) iprims.Iast.prog_data_decls) @
      (List.map (fun v -> v.Iast.view_name) iprims.Iast.prog_view_decls) @
      ["__Exc"; "__Fail"; "__Error"; "__MayError";"__RET"]
    in
    let () = saved_prim_names := Some prim_names in
    (* let () = print_endline_quiet ("process_source_full: before Globalvars.trans_global_to_param") in *)
		(* let _=print_endline_quiet ("PROG: "^Iprinter.string_of_program prog) in *)
    let prog = Iast.append_iprims_list_head ([prog]@prims_incls) in
                
                (*let () = print_string (Iprinter.string_of_program prog^"haha") in*)
               
    let tnt_prim_proc_decls = Hashtbl.fold (fun id _ acc ->
      if List.exists (fun (p, _) -> String.compare p id == 0) acc then acc
      else 
        match (Parser.create_tnt_prim_proc id) with
        | None -> acc | Some pd -> acc @ [(id, pd)]) Iast.tnt_prim_proc_tbl [] in
    let tnt_prim_proc_decls = snd (List.split tnt_prim_proc_decls) in
    let prog = { prog with Iast.prog_proc_decls = prog.Iast.prog_proc_decls @ tnt_prim_proc_decls; } in
    let intermediate_prog = Globalvars.trans_global_to_param prog in
    
    (* let () = print_endline_quiet ("process_source_full: before pre_process_of_iprog" ^(Iprinter.string_of_program intermediate_prog)) in *)
    (* let () = print_endline_quiet ("== gvdecls 2 length = " ^ (string_of_int (List.length intermediate_prog.Iast.prog_global_var_decls))) in *)
    let intermediate_prog = IastUtil.pre_process_of_iprog iprims intermediate_prog in
   
    (* let _= print_string ("\n*After pre process iprog* "^ (Iprinter.string_of_program intermediate_prog)) in *)
    let intermediate_prog = Iast.label_procs_prog intermediate_prog true in
    (* let _= print_string ("\n*After label_procs_prog iprog* "^ (Iprinter.string_of_program intermediate_prog)) in *)
    
	(*let intermediate_prog_reverif = 
			if (!Globals.reverify_all_flag) then 
					Marshal.from_string (Marshal.to_string intermediate_prog [Marshal.Closures]) 0 
			else intermediate_prog in*)
    (* let () = print_endline_quiet ("process_source_full: before --pip") in *)
    let () = if (!Globals.print_input_all) then print_string (Iprinter.string_of_program intermediate_prog) 
		        else if(!Globals.print_input) then
							print_string (Iprinter.string_of_program_separate_prelude intermediate_prog iprims)
						else () in
    (* let () = print_endline_quiet ("process_source_full: after --pip") in *)
    let () = Gen.Profiling.pop_time "Translating global var" in
    (* Global variables translated *)
    (* let ptime1 = Unix.times () in
       let t1 = ptime1.Unix.tms_utime +. ptime1.Unix.tms_cutime in *)
    let () = Gen.Profiling.push_time "Translating to Core" in
(*    let () = print_string ("Translating to core language...\n"); flush stdout in *)
    (* let () = print_endline_quiet (Iprinter.string_of_program intermediate_prog) in *)
    (**************************************)
    (*Simple heuristic for ParaHIP website*)
    (*Heuristic: check if waitlevel and locklevels have been used for verification
      If not detect waitlevel or locklevel -> set allow_locklevel==faslse
      Note: this is used in ParaHIP website for demonstration only.
      We could use the run-time flag "--dis-locklevel" to disable the use of locklevels
      and waitlevel.
    *)
    let search_for_locklevel proc =
      if (not !Globals.allow_locklevel) then
        let struc_fv = Iformula.struc_free_vars false proc.Iast.proc_static_specs in
        let b = List.exists (fun (id,_) -> (id = Globals.waitlevel_name)) struc_fv in
        if b then
          Globals.allow_locklevel := true
    in
    let () = if !Globals.web_compile_flag then
          let todo_unk = List.map search_for_locklevel prog.Iast.prog_proc_decls in
          ()
    in
    (**************************************)
    (*to improve: annotate field*)
    let () = Iast.annotate_field_pure_ext intermediate_prog in
    (*END: annotate field*)
    (*used in lemma*)
    (* let () =  Debug.info_zprint (lazy  ("XXXX 1: ")) no_pos in *)
    (* let () = I.set_iprog intermediate_prog in *)
    (*let () = print_endline ("@@intermediate_prog\n"^Iprinter.string_of_program intermediate_prog) in*)
    let cprog, tiprog = Astsimp.trans_prog intermediate_prog (*iprims*) in
    let () = saved_cprog := Some cprog in
    (* let () = if !Globals.sa_pure then *)
    (*   let norm_views, extn_views = List.fold_left (fun (nviews, eviews) v -> *)
    (*       if v.Cast.view_kind = Cast.View_NORM then *)
    (*         (nviews@[v], eviews) *)
    (*       else if v.Cast.view_kind = Cast.View_EXTN then *)
    (*         (nviews, eviews@[v]) *)
    (*       else (nviews, eviews) *)
    (*   ) ([],[]) cprog.Cast.prog_view_decls in *)
    (*   Derive.expose_pure_extn tiprog cprog norm_views extn_views *)
    (* else cprog.Cast.prog_view_decls *)
    (* in *)
    (* ========= lemma process (normalize, translate, verify) ========= *)
    let () = List.iter (fun x -> Lemma.process_list_lemma_helper x tiprog cprog (fun a b -> b)) tiprog.Iast.prog_coercion_decls in
    (* ========= end - lemma process (normalize, translate, verify) ========= *)
    let c = cprog in
       let () = if !Globals.gen_coq_file 
         then 
           let () = print_endline "Generating Coq file ..."in
           let filename = (List.hd !Globals.source_files) in
           let i = (String.rindex filename '.') in
           let file = (String.sub filename 0  i) ^".v" in
           let j = (String.rindex filename '/') in
           let oc = open_out file in
           let moduletypename = (String.sub filename (j+1) (i-j)) in
           let imports = "Require Import ZArith.\n" in
           let moduletype = "\nModule Type M"^moduletypename^"\n" in
           let endmoduletype = "End M"^moduletypename^"\n" in
           let parameter_formula = "  Parameter formula : Type.\n" in
           let parameter_valid = "  Parameter valid : formula -> Prop.\n" in
           let ptto_list = List.map (fun dd ->
             if(List.length dd.C.data_fields > 0 
                && not(ExtString.String.starts_with dd.C.data_name "int_ptr")
                && not(ExtString.String.starts_with dd.C.data_name "barrier")) then
             let param_name = "  Parameter "^dd.C.data_name^" : Type.\n" in
             let param_null = "  Parameter null_"^dd.C.data_name^" : "
               ^dd.C.data_name^".\n" in 
             let param_ptto = "  Parameter ptto_"^dd.C.data_name
               ^" : "^dd.C.data_name^" -> " in
             let types_list = List.map (fun ((t,_),_) -> match t with
               | Int -> "Z"
               | Named i -> i
               | _ -> "Unknown"
             ) dd.C.data_fields in
             let param_types = String.concat " -> " types_list in
             let ptto = param_ptto^param_types^" -> formula.\n" in
             param_name^param_null^ptto
             else ""
           ) c.C.prog_data_decls in
           let parameter_ptto = String.concat "" ptto_list in
           let view_list = List.map (fun vd -> 
             if not(vd.C.view_is_prim) then
               let view_params = String.concat "" (List.map (fun sv ->
                 match (CP.type_of_spec_var sv) with
                   | Void -> "  Parameter A : Type.\n"
                   | _ -> ""
               ) vd.C.view_vars) in
               let view_params_arrow = String.concat " -> " (List.map (fun sv ->
                match (CP.type_of_spec_var sv) with
                  | Void -> "A"
                  | Int -> "Z"
                  | Named i -> i
                  | _ -> "Uknown"
               ) vd.C.view_vars) in
               let view_name = "  Parameter "^vd.C.view_name^" : "^
                 vd.C.view_data_name^" -> "^view_params_arrow^" -> formula.\n" in
               view_params^view_name
             else ""
           ) c.C.prog_view_decls in
           let parameter_views = String.concat "" view_list in
           let parameter_formulas = 
             "  Parameter star : formula -> formula -> formula.\n"^
             "  Parameter and : formula -> formula -> formula.\n"^
             "  Parameter imp : formula -> formula -> formula.\n"^
             "  Parameter not : formula -> formula.\n"^
             "  Parameter eq : node -> node -> formula.\n"^
               (if !Globals.allow_ramify then 
                   "  Parameter mwand : formula -> formula -> formula.\n"^
                   "  Parameter union : formula -> formula -> formula.\n"^
                   "  Parameter neq : Z -> Z -> formula.\n"
                else "") in
           let relation_list = List.map (fun rd ->
             if (ExtString.String.starts_with rd.C.rel_name "dom") ||
                (ExtString.String.starts_with rd.C.rel_name "update_array_") ||
                (ExtString.String.starts_with rd.C.rel_name "induce") ||
                (ExtString.String.starts_with rd.C.rel_name "amodr")
             then ""
             else
             let rel_params_arrow = String.concat " -> " (List.map (fun sv ->
                match (CP.type_of_spec_var sv) with
                  | Void -> "A"
                  | Int -> "Z"
                  | Named i -> i
                  | _ -> "Uknown"
             ) rd.C.rel_vars) in "  Parameter "^rd.C.rel_name^" : "^rel_params_arrow^
                             " -> formula.\n"
           ) c.C.prog_rel_decls in
           let parameter_relations = String.concat "" relation_list in
           let rec convert_cp_formula f = match f with
             | CP.BForm((pf,_),_) -> (match pf with 
                 | CP.Eq(e1,e2,_) -> "(eq "^(CP.exp_to_name_spec_var e1)
                     ^" "^(CP.exp_to_name_spec_var e2)^")"
                 | CP.Neq(e1,e2,_) ->"(neq "^(CP.exp_to_name_spec_var e1)
                     ^" "^(CP.exp_to_name_spec_var e2)^")"
                 | CP.RelForm(sv,elist,_) -> "("^(CP.name_of_spec_var sv)^" "^
                     (String.concat " " (List.map (fun e ->
                     CP.exp_to_name_spec_var e) elist))^")"
                 (*| CP.BConst(b,_) -> if b then "true" else "false"*)
                 | _ -> ""
             )
             | CP.And(f1,f2,_) -> "(and "^(convert_cp_formula f1) ^" "^
                 (convert_cp_formula f2)^")"
             | CP.Not(f,_,_) -> "(not "^(convert_cp_formula f)^")"
             | CP.Exists(_,f,_,_) -> convert_cp_formula f
             | _ -> "" in
           let axioms_list = List.map (fun axd -> 
             let var_list = CP.remove_dups_svl (List.filter (fun sv -> 
               (String.length (CP.name_of_spec_var sv)) < 3)
               ((CP.fv axd.C.axiom_hypothesis)@(CP.fv axd.C.axiom_conclusion)))
             in let var_list_string = String.concat " " (List.map 
                  (fun sv -> CP.name_of_spec_var sv) var_list) in
                let (_,exists_list) = CP.split_ex_quantifiers_rec axd.C.axiom_conclusion in
                let var_exlst = String.concat " " (List.map
                  (fun sv -> CP.name_of_spec_var sv) exists_list) in
              "  Axiom axiom_"^(string_of_int (Globals.fresh_int2()))
                ^" : forall "^var_list_string^","^
                (if (String.length var_exlst) > 0 
                 then " exists "^var_exlst^","
                 else "")^
                (if (CP.isConstTrue axd.C.axiom_hypothesis)
                then " valid "^(convert_cp_formula axd.C.axiom_conclusion)^".\n"
                else
                " valid (imp "^(convert_cp_formula axd.C.axiom_hypothesis)
                ^" "^(convert_cp_formula axd.C.axiom_conclusion)^").\n")
           ) (List.filter (fun a -> 
             if List.length (CP.fv a.C.axiom_hypothesis) > 0 then 
               if ExtString.String.starts_with (CP.name_of_spec_var
               (List.hd (CP.fv a.C.axiom_hypothesis))) "dom"
               then false
               else true
              else true)
                c.C.prog_axiom_decls) in
           let parameter_axioms = String.concat "" axioms_list in
           (*let () = Lem_store.all_lemma # dump in*)
           let rec convert_h_formula f = match f with
             | CF.Star({h_formula_star_h1 = h1;
                     h_formula_star_h2 = h2;}) -> "(star "^
                    (convert_h_formula h1)^" "^(convert_h_formula h2)^")"
             | CF.Conj({h_formula_conj_h1 = h1;
                     h_formula_conj_h2 = h2;}) -> "(union "^
                    (convert_h_formula h1)^" "^(convert_h_formula h2)^")"
             | CF.StarMinus({h_formula_starminus_h1 = h1;
                     h_formula_starminus_h2 = h2;}) -> "(mwand "^
                    (convert_h_formula h2)^" "^(convert_h_formula h1)^")"
             | CF.DataNode({h_formula_data_node = d;
                            h_formula_data_name = name;
                            h_formula_data_arguments = args}) -> "(ptto_"^name^" "^
                 (String.concat " " (List.map (fun sv -> CP.name_of_spec_var sv) (d::args)))
                 ^")"
             | CF.ViewNode({h_formula_view_node = v;
                            h_formula_view_name = name;
                            h_formula_view_arguments = args;}) -> "("^name^" "^
                 (String.concat " " (List.map (fun sv -> CP.name_of_spec_var sv) (v::args)))
                 ^")"
             | _ -> "" in
           let lemma_list = List.map (fun cd ->
             let h1, p1, _,_, _, _ = CF.split_components 
               (CF.elim_exists cd.C.coercion_head) in
             let h2, p2,_, _, _, _ = CF.split_components 
               (CF.elim_exists cd.C.coercion_body) in
             let var_list = CP.remove_dups_svl (List.filter (fun sv -> 
               (String.length (CP.name_of_spec_var sv)) < 3)
               ((CF.h_fv h1)@(CF.h_fv h2)@(CP.fv (Mcpure.pure_of_mix p1))
                @(CP.fv (Mcpure.pure_of_mix p2)))) in
             let var_list_string = String.concat " " (List.map 
                  (fun sv -> CP.name_of_spec_var sv) var_list) in
             "  Axiom lem_"^cd.C.coercion_name^" : forall "^
             var_list_string^", valid (imp "^"(and "^(convert_h_formula h1)^" "^
               (convert_cp_formula (Mcpure.pure_of_mix p1))^")"^" "^(convert_h_formula h2)
             ^").\n"
           ) (Lem_store.all_lemma # get_left_coercion) in
           let parameter_lemmas = String.concat "" lemma_list in
           Printf.fprintf oc "%s\n" (imports^moduletype^parameter_formula^
           parameter_valid^parameter_ptto^parameter_views^parameter_formulas^
           parameter_relations^parameter_axioms^parameter_lemmas^endmoduletype);
           close_out oc;
           print_endline ("Complete the proof in "^file);
         else () in 
		(* let cprog = Astsimp.trans_prog intermediate_prog (*iprims*) in *)
    (* let () = print_string ("Translating to core language...\n"); flush stdout in *)
    (*let cprog = Astsimp.trans_prog intermediate_prog (*iprims*) in*)
    (* Forward axioms and relations declarations to SMT solver module *)
    let todo_unk = List.map (fun crdef -> 
        let () = Smtsolver.add_relation crdef.Cast.rel_name crdef.Cast.rel_vars crdef.Cast.rel_formula in
        Z3.add_relation crdef.Cast.rel_name crdef.Cast.rel_vars crdef.Cast.rel_formula
    ) (List.rev cprog.Cast.prog_rel_decls) in
    let todo_unk = List.map (fun cadef ->
        let () = Smtsolver.add_axiom cadef.Cast.axiom_hypothesis Smtsolver.IMPLIES cadef.Cast.axiom_conclusion in
        Z3.add_axiom cadef.Cast.axiom_hypothesis Z3.IMPLIES cadef.Cast.axiom_conclusion
    ) (List.rev cprog.Cast.prog_axiom_decls) in
    (* let () = print_string (" done-2\n"); flush stdout in *)
    let () = if (!Globals.print_core_all) then print_string (Cprinter.string_of_program cprog)  
    else if(!Globals.print_core) then
      print_string (Cprinter.string_of_program_separate_prelude cprog iprims)
    else ()
    in
    let () = 
      if !Globals.verify_callees then begin
	    let tmp = Cast.procs_to_verify cprog !Globals.procs_verified in
	    Globals.procs_verified := tmp
      end in
    let () = Gen.Profiling.pop_time "Translating to Core" in
    (* let ptime2 = Unix.times () in
       let t2 = ptime2.Unix.tms_utime +. ptime2.Unix.tms_cutime in
       let () = print_string (" done in " ^ (string_of_float (t2 -. t1)) ^ " second(s)\n") in *)
    let _ =
      if !Scriptarguments.comp_pred then begin
	    let () = print_string ("Compiling predicates to Java..."); flush stdout in
	    let compile_one_view vdef = 
	      if (!Scriptarguments.pred_to_compile = ["all"] || List.mem vdef.Cast.view_name !Scriptarguments.pred_to_compile) then
	        let data_def, pbvars = Predcomp.gen_view cprog vdef in
	        let java_str = Java.java_of_data data_def pbvars in
	        let jfile = open_out (vdef.Cast.view_name ^ ".java") in
	        print_string ("\n\tWriting Java file " ^ vdef.Cast.view_name ^ ".java");
	        output_string jfile java_str;
	        close_out jfile
	      else
	        ()
	    in
	    ignore (List.map compile_one_view cprog.Cast.prog_view_decls);
	    print_string ("\nDone-3.\n"); flush stdout;
	    exit 0
      end 
    in
    let _ =
      if !Scriptarguments.rtc then begin
	    Rtc.compile_prog cprog source;
	    exit 0
      end
    in
    let () = Gen.Profiling.pop_time "Preprocessing" in

    (* An Hoa : initialize html *)
    let () = Prooftracer.initialize_html source in

    if (!Scriptarguments.typecheck_only) 
    then print_string (Cprinter.string_of_program cprog)
    else (try
      (* let () =  Debug.info_zprint (lazy  ("XXXX 5: ")) no_pos in *)
      (* let () = I.set_iprog intermediate_prog in *)
      ignore (Typechecker.check_prog intermediate_prog cprog);
    with _ as e -> begin
      print_string_quiet ("\nException"^(Printexc.to_string e)^"Occurred!\n");
      print_string_quiet ("\nError1(s) detected at main "^"\n");
      let () = Log.process_proof_logging !Globals.source_files cprog prim_names in
      raise e
    end);
	if (!Globals.reverify_all_flag || !Globals.reverify_flag)
	then
          let () =  Debug.info_pprint "re-verify\n" no_pos; in
	  reverify_with_hp_rel cprog intermediate_prog(*_reverif *)
	else ();
	
    (* Stopping the prover *)
    if (!Tpdispatcher.tp_batch_mode) then Tpdispatcher.stop_prover ();
    (* Get the total verification time *)
    let ptime4 = Unix.times () in
    let t4 = ptime4.Unix.tms_utime +. ptime4.Unix.tms_cutime +. ptime4.Unix.tms_stime +. ptime4.Unix.tms_cstime   in

    (* An Hoa : export the proof to html *)
    let () = if !Globals.print_proof then
    		begin 
    			print_string "\nExport proof to HTML file ... ";
    			Prooftracer.write_html_output ();
    			print_endline_quiet "done!" 
    		end
    in
    
    (* Proof Logging *)
    let () = Log.process_proof_logging !Globals.source_files cprog prim_names
    (*  if !Globals.proof_logging || !Globals.proof_logging_txt then  *)
      (* begin *)
      (*   let tstartlog = Gen.Profiling.get_time () in *)
      (*   let _= Log.proof_log_to_file () in *)
      (*   let with_option = if(!Globals.en_slc_ps) then "eps" else "no_eps" in *)
      (*   let fname = "logs/"^with_option^"_proof_log_" ^ (Globals.norm_file_name (List.hd !Globals.source_files)) ^".txt"  in *)
      (*   let fz3name= ("logs/"^with_option^"_z3_proof_log_"^ (Globals.norm_file_name (List.hd !Globals.source_files)) ^".txt") in *)
      (*   let _= if (!Globals.proof_logging_txt)  *)
      (*   then  *)
      (*     begin *)
      (*       Debug.info_zprint (lazy (("Logging "^fname^"\n"))) no_pos; *)
      (*       Debug.info_zprint (lazy (("Logging "^fz3name^"\n"))) no_pos; *)
      (*       Log.proof_log_to_text_file !Globals.source_files; *)
      (*       Log.z3_proofs_list_to_file !Globals.source_files *)
      (*     end *)
      (*   else try Sys.remove fname  *)
      (*     (\* ("logs/proof_log_" ^ (Globals.norm_file_name (List.hd !Globals.source_files))^".txt") *\) *)
      (*   with _ -> () *)
      (*   in *)
      (*   let tstoplog = Gen.Profiling.get_time () in *)
      (*   let _= Globals.proof_logging_time := !Globals.proof_logging_time +. (tstoplog -. tstartlog) in () *)
      (*   (\* let _=print_endline_quiet ("Time for logging: "^(string_of_float (!Globals.proof_logging_time))) in    () *\) *)
      (* end *)
    in
    (* let () = Log.process_sleek_logging () in *)
    (* print mapping table control path id and loc *)
    (*let () = print_endline_quiet (Cprinter.string_of_iast_label_table !Globals.iast_label_table) in*)
    hip_epilogue ();
    if (not !Globals.web_compile_flag) then 
      print_string_quiet ("\n"^(string_of_int (List.length !Globals.false_ctx_line_list))^" false contexts at: ("^
		(List.fold_left (fun a c-> a^" ("^(string_of_int c.VarGen.start_pos.Lexing.pos_lnum)^","^
		    ( string_of_int (c.VarGen.start_pos.Lexing.pos_cnum-c.VarGen.start_pos.Lexing.pos_bol))^") ") "" !Globals.false_ctx_line_list)^")\n")
    else ();
    Timelog.logtime # dump;
    silenced_print print_string ("\nTotal verification time: " 
	^ (string_of_float t4) ^ " second(s)\n"
	^ "\tTime spent in main process: " 
	^ (string_of_float (ptime4.Unix.tms_utime+.ptime4.Unix.tms_stime)) ^ " second(s)\n"
	^ "\tTime spent in child processes: " 
	^ (string_of_float (ptime4.Unix.tms_cutime +. ptime4.Unix.tms_cstime)) ^ " second(s)\n"
	^ if !Globals.allow_mem then "\nTotal Entailments : " 
	^ (string_of_int !Globals.total_entailments) ^ "\n" 
	^ "Ramification Entailments : "^ (string_of_int !Globals.ramification_entailments) ^"\n"
	^ "Noninter Entailments : "^ (string_of_int !Globals.noninter_entailments) ^"\n"
      else ""
	^ if !Globals.proof_logging || !Globals.proof_logging_txt then 
      "\tTime for logging: "^(string_of_float (!Globals.proof_logging_time))^" second(s)\n"
    else ""
	^ if(!Tpdispatcher.pure_tp = Others.Z3) then 
      "\tZ3 Prover Time: " ^ (string_of_float !Globals.z3_time) ^ " second(s)\n"
    else "\n"
	)
  
let process_source_list source_files =
  match source_files with
  | [] -> []
  | file_name::_ ->
    let index = try String.rindex file_name '.' with _ -> 0 in
    let length = (String.length file_name) - index in
    let ext = String.lowercase(String.sub file_name index length) in
    if (ext = ".java") then
      let ss_file_name = file_name ^ ".ss" in
      let () = Pretty_ss.print_out_str_from_files_new source_files ss_file_name in
      [process_source_full ss_file_name]
    else
      let parser = 
        if (ext = ".c") || (ext = ".cc") || (ext = ".cpp") || (ext = ".h") then
          "cil"
        else if (ext = ".i") then "cil-i"
        else (* "default" *) !Parser.parser_name
      in 
      let () = Parser.parser_name := parser in
      List.map process_source_full source_files

(*None Working: see process_source_full instead *)
let process_source_full_parse_only source =
  Debug.info_zprint (lazy (("Full processing file (parse only) \"" ^ source ^ "\"\n"))) no_pos;
  flush stdout;
  let prog = parse_file_full source false in
  (* Remove all duplicated declared prelude *)
  let header_files = match !Globals.prelude_file with
    | None -> ["\"prelude.ss\""]
    | Some s -> ["\""^s^"\""] in 
  (* let header_files = Gen.BList.remove_dups_eq (=) !Globals.header_file_list in (\*prelude.ss*\) *)
  let new_h_files = process_header_with_pragma header_files !Globals.pragma_list in
  let prims_list = process_primitives new_h_files in (*list of primitives in header files*)
	
  if !to_java then begin
    print_string ("Converting to Java..."); flush stdout;
    let tmp = Filename.chop_extension (Filename.basename source) in
    let main_class = Gen.replace_minus_with_uscore tmp in
    let java_str = Java.convert_to_java prog main_class in
    let tmp2 = Gen.replace_minus_with_uscore (Filename.chop_extension source) in
    let jfile = open_out ("output/" ^ tmp2 ^ ".java") in
    output_string jfile java_str;
    close_out jfile;
    (* print_string (" done-1.\n"); flush stdout; *)
    exit 0
  end;
  let () = Gen.Profiling.pop_time "Preprocessing" in
  (prog, prims_list)


let process_source_full_after_parser source (prog, prims_list) =
  Debug.info_zprint (lazy (("Full processing file (after parser) \"" ^ source ^ "\"\n"))) no_pos;
  flush stdout;
  if (!Tpdispatcher.tp_batch_mode) then Tpdispatcher.start_prover ();
  (* Global variables translating *)
  let () = Gen.Profiling.push_time "Translating global var" in
  (* let () = print_string ("Translating global variables to procedure parameters...\n"); flush stdout in *)
  (* Append all primitives in list into one only *)
  let iprims_list = process_intermediate_prims prims_list in
  let iprims = Iast.append_iprims_list_head iprims_list in
	(* let _= List.map (fun x-> print_endline_quiet ("Bachle: iprims "^x.Iast.proc_name)) iprims in *)
  (* let () = print_endline_quiet ("process_source_full: before Globalvars.trans_global_to_param") in *)
    (* let () = print_endline_quiet (Iprinter.string_of_program prog) in *)
  let intermediate_prog = Globalvars.trans_global_to_param prog in
  (* let () = print_endline_quiet ("process_source_full: before pre_process_of_iprog") in *)
    (* let () = print_endline_quiet (Iprinter.string_of_program intermediate_prog) in *)
  let intermediate_prog =IastUtil.pre_process_of_iprog iprims intermediate_prog in
    (* let () = print_endline_quiet ("process_source_full: before label_procs_prog") in *)
    (* let () = print_endline_quiet (Iprinter.string_of_program intermediate_prog) in *)
  let intermediate_prog = Iast.label_procs_prog intermediate_prog true in
  (* let () = print_endline_quiet ("process_source_full: before --pip") in *)
  let () = if (!Globals.print_input_all) then print_string (Iprinter.string_of_program intermediate_prog) 
	         else if(!Globals.print_input) then
							print_string (Iprinter.string_of_program_separate_prelude intermediate_prog iprims)
						else () in
  (* let () = print_endline_quiet ("process_source_full: after --pip") in *)
  let () = Gen.Profiling.pop_time "Translating global var" in
  (* Global variables translated *)
  (* let ptime1 = Unix.times () in
     let t1 = ptime1.Unix.tms_utime +. ptime1.Unix.tms_cutime in *)
  let () = Gen.Profiling.push_time "Translating to Core" in
  (* let () = print_string ("Translating to core language...\n"); flush stdout in *)

  (**************************************)
  (*Simple heuristic for ParaHIP website*)
  (*Heuristic: check if waitlevel and locklevels have been used for verification
    If not detect waitlevel or locklevel -> set allow_locklevel==faslse
    Note: this is used in ParaHIP website for demonstration only.
    We could use the run-time flag "--dis-locklevel" to disable the use of locklevels
    and waitlevel.
  *)
  let search_for_locklevel proc =
    if (not !Globals.allow_locklevel) then
      let struc_fv = Iformula.struc_free_vars false proc.Iast.proc_static_specs in
      let b = List.exists (fun (id,_) -> (id = Globals.waitlevel_name)) struc_fv in
      if b then
        Globals.allow_locklevel := true
  in
  let () = if !Globals.web_compile_flag then
        let todo_unk = List.map search_for_locklevel prog.Iast.prog_proc_decls in
        ()
  in
  (**************************************)
  (*annotate field*)
  let () = Iast.annotate_field_pure_ext intermediate_prog in
  (*used in lemma*)
  (* let () =  Debug.info_zprint (lazy  ("XXXX 2: ")) no_pos in *)
  (* let () = I.set_iprog intermediate_prog in *)
  let cprog,tiprog = Astsimp.trans_prog intermediate_prog (*iprims*) in
  let () = saved_cprog := Some cprog in
  (* let cprog = Astsimp.trans_prog intermediate_prog (*iprims*) in *)

  (* Forward axioms and relations declarations to SMT solver module *)
  let todo_unk = List.map (fun crdef -> 
      let () = Smtsolver.add_relation crdef.Cast.rel_name crdef.Cast.rel_vars crdef.Cast.rel_formula in
      Z3.add_relation crdef.Cast.rel_name crdef.Cast.rel_vars crdef.Cast.rel_formula
  )
    (List.rev cprog.Cast.prog_rel_decls) in

  let todo_unk = List.map (fun cadef ->
      let () = Smtsolver.add_axiom cadef.Cast.axiom_hypothesis Smtsolver.IMPLIES cadef.Cast.axiom_conclusion in
      Z3.add_axiom cadef.Cast.axiom_hypothesis Z3.IMPLIES cadef.Cast.axiom_conclusion
  ) (List.rev cprog.Cast.prog_axiom_decls) in
  (* let () = print_string (" done-2\n"); flush stdout in *)
  let () = if (!Globals.print_core_all) then print_string (Cprinter.string_of_program cprog)
  else if(!Globals.print_core) then
    print_string (Cprinter.string_of_program_separate_prelude cprog iprims)
  else ()
  in
  let _ =
    if !Globals.verify_callees then begin
      let tmp = Cast.procs_to_verify cprog !Globals.procs_verified in
      Globals.procs_verified := tmp
    end in
  let () = Gen.Profiling.pop_time "Translating to Core" in
  (* let ptime2 = Unix.times () in
     let t2 = ptime2.Unix.tms_utime +. ptime2.Unix.tms_cutime in
     let () = print_string (" done in " ^ (string_of_float (t2 -. t1)) ^ " second(s)\n") in *)
  let _ =
    if !Scriptarguments.comp_pred then begin
      let () = print_string ("Compiling predicates to Java..."); flush stdout in
      let compile_one_view vdef = 
	if (!Scriptarguments.pred_to_compile = ["all"] || List.mem vdef.Cast.view_name !Scriptarguments.pred_to_compile) then
	  let data_def, pbvars = Predcomp.gen_view cprog vdef in
	  let java_str = Java.java_of_data data_def pbvars in
	  let jfile = open_out (vdef.Cast.view_name ^ ".java") in
	  print_string ("\n\tWriting Java file " ^ vdef.Cast.view_name ^ ".java");
	  output_string jfile java_str;
	  close_out jfile
	else
	  ()
      in
      ignore (List.map compile_one_view cprog.Cast.prog_view_decls);
      print_string ("\nDone-3.\n"); flush stdout;
      exit 0
    end 
  in
  let _ =
    if !Scriptarguments.rtc then begin
      Rtc.compile_prog cprog source;
      exit 0
    end
  in
  let () = Gen.Profiling.pop_time "Preprocessing" in
  
  (* An Hoa : initialize html *)
  let () = Prooftracer.initialize_html source in
  
  if (!Scriptarguments.typecheck_only) 
  then print_string (Cprinter.string_of_program cprog)
  else (try
    (* let () =  Debug.info_zprint (lazy  ("XXXX 3: ")) no_pos in *)
    (* let () = I.set_iprog intermediate_prog in *)
    ignore (Typechecker.check_prog intermediate_prog cprog);
  with _ as e -> begin
    print_string ("\nException"^(Printexc.to_string e)^"Occurred!\n");
    print_string ("\nError2 (s) detected at main "^"\n");
    raise e
  end);
  (* Stopping the prover *)
  if (!Tpdispatcher.tp_batch_mode) then Tpdispatcher.stop_prover ();
  
  (* An Hoa : export the proof to html *)
  let () = if !Globals.print_proof then
    begin 
      print_string "\nExport proof to HTML file ... ";
      Prooftracer.write_html_output ();
      print_endline_quiet "done!" 
    end
  in
  
  (* print mapping table control path id and loc *)
  (*let () = print_endline_quiet (Cprinter.string_of_iast_label_table !Globals.iast_label_table) in*)
  let ptime4 = Unix.times () in
  let t4 = ptime4.Unix.tms_utime +. ptime4.Unix.tms_cutime +. ptime4.Unix.tms_stime +. ptime4.Unix.tms_cstime   in
  if (not !Globals.web_compile_flag) then 
    print_string_quiet ("\n"^(string_of_int (List.length !Globals.false_ctx_line_list))^" false contexts at: ("^
      (List.fold_left (fun a c-> a^" ("^(string_of_int c.VarGen.start_pos.Lexing.pos_lnum)^","^
	  ( string_of_int (c.VarGen.start_pos.Lexing.pos_cnum-c.VarGen.start_pos.Lexing.pos_bol))^") ") "" !Globals.false_ctx_line_list)^")\n")
  else ();
  silenced_print print_string ("\nTotal verification time: " 
  ^ (string_of_float t4) ^ " second(s)\n"
  ^ "\tTime spent in main process: " 
  ^ (string_of_float (ptime4.Unix.tms_utime+.ptime4.Unix.tms_stime)) ^ " second(s)\n"
  ^ "\tTime spent in child processes: " 
  ^ (string_of_float (ptime4.Unix.tms_cutime +. ptime4.Unix.tms_cstime)) ^ " second(s)\n")

let main1 () =
  (* Cprinter.fmt_set_margin 40; *)
  (* Cprinter.fmt_string "TEST1.................................."; *)
  (* Cprinter.fmt_cut (); *)
  (* Cprinter.fmt_string "TEST2...............................................................'''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''............"; *)
  (* Cprinter.fmt_cut (); *)
  (* Cprinter.fmt_string "TEST3....."; *)
  (* Cprinter.fmt_cut (); *)
  (* Cprinter.fmt_string "TEST3....."; *)
  (* Cprinter.fmt_cut (); *)
  (* Cprinter.fmt_string "TEST3....."; *)
  (* Cprinter.fmt_string "TEST3....."; *)
  (* Cprinter.fmt_string "TEST4..............................."; *)
  (* Cprinter.fmt_cut (); *)
  (* Cprinter.fmt_string "TEST5.................................."; *)
  (* Cprinter.fmt_cut (); *)
  (* Cprinter.fmt_string "TEST6.................................."; *)
  (* Cprinter.fmt_cut (); *)
  (* Cprinter.fmt_string "TEST7.................................."; *)
  (* Cprinter.fmt_cut (); *)
  process_cmd_line ();
  let () = Debug.read_main () in
  Scriptarguments.check_option_consistency ();
  if !Globals.print_version_flag then begin
	print_version ()
  end else
  (*let () = print_endline_quiet (string_of_bool (Printexc.backtrace_status())) in*)
    let () = record_backtrace_quite () in
  (*let () = print_endline_quiet (string_of_bool (Printexc.backtrace_status())) in *)

    if List.length (!Globals.source_files) = 0 then begin
      (* print_string (Sys.argv.(0) ^ " -help for usage information\n") *)
      (* Globals.procs_verified := ["f3"]; *)
      (* Globals.source_files := ["examples/test5.ss"] *)
        print_string "Source file(s) not specified\n"
    end;
    let () = Gen.Profiling.push_time "Overall" in
    let todo_unk:unit list = process_source_list !Globals.source_files in
    let () = Gen.Profiling.pop_time "Overall" in
    (*  Tpdispatcher.print_stats (); *)
    ()

(* let main1 () = *)
(*   Debug.loop_1_no "main1" (fun _ -> "?") (fun _ -> "?") main1 () *)

let pre_main () =
  process_cmd_line ();
  Tpdispatcher.init_tp();
  Scriptarguments.check_option_consistency ();
  if !Globals.print_version_flag then
	  let () = print_version ()
    in []
  else
    let () = record_backtrace_quite () in
    if List.length (!Globals.source_files) = 0 then
      print_string "Source file(s) not specified\n";
		List.map ( fun x-> let _= print_endline_quiet ("SOURCE: "^x) in process_source_full_parse_only x) !Globals.source_files

let loop_cmd parsed_content = 
  let todo_unk = List.map2 (fun s t -> process_source_full_after_parser s t) !Globals.source_files parsed_content in
  ()

let finalize_bug () =
  let () = Log.last_cmd # dumping "finalize on hip" in
  (match !saved_cprog,!saved_prim_names with
    | Some(cprog),Some(prim_names) ->
          let () = Log.process_proof_logging !Globals.source_files cprog prim_names in ()
    | Some(cprog),None ->
          let () = Log.process_proof_logging !Globals.source_files cprog [] in ()
    | _,_ ->
          let () = x_binfo_pp "WARNING : Logging not done on finalize" no_pos in ());
  if (!Tpdispatcher.tp_batch_mode) then Tpdispatcher.stop_prover ()

let old_main () = 
  try
    main1 ();
    (* let () =  *)
    (*   if !Global.enable_counters then *)
    (*     print_string (Gen.Profiling.string_of_counters ()) *)
    (*   else () in *)
    let () = Gen.Profiling.print_counters_info () in
    let () = Gen.Profiling.print_info () in
    ()
  with _ as e -> begin
    finalize_bug ();
    print_string_quiet "caught\n"; 
    Printexc.print_backtrace stderr;
    print_string_quiet ("\nException occurred: " ^ (Printexc.to_string e));
    print_string_quiet ("\nError3(s) detected at main \n");
    (* print result for svcomp 2015 *)
    (
    if !Globals.tnt_web_mode then
      print_web_mode ("\nError: " ^ (Printexc.to_string e))
    else if (!Globals.svcomp_compete_mode) then
      print_endline "UNKNOWN" (* UNKNOWN(5) *)
    )
  end

let () = 
  if not(!Globals.do_infer_inc) then
        (* let () = print_endline "I am executing old stuff?.." in *)
        old_main ()
  else
    (* this part seems to be for incremental inference *)
    let res = pre_main () in
    while true do
      try
        (* let () = print_endline "I am executing here.." in *)
        let () = print_string "# " in
        let s = Parse_cmd.parse_cmd (read_line ()) in
        match s with
          | (_,(false, None, None)) -> exit 0;
          | _ ->
          Iformula.cmd := s;
          loop_cmd res;
          (* let () =  *)
          (*   if !Global.enable_counters then *)
          (*     print_string (Gen.Profiling.string_of_counters ()) *)
          (*   else () in *)
          let () = Gen.Profiling.print_counters_info () in
          let () = Gen.Profiling.print_info () in
          ()
        with _ as e -> begin
          finalize_bug ();
          print_string_quiet "caught\n"; Printexc.print_backtrace stdout;
          print_string_quiet ("\nException occurred: " ^ (Printexc.to_string e));
          print_string_quiet ("\nError4(s) detected at main \n");
          (* print result for svcomp 2015 *)
          (
          if !Globals.tnt_web_mode then
            print_web_mode ("\nError: " ^ (Printexc.to_string e))
          else if (!Globals.svcomp_compete_mode) then
            print_endline "UNKNOWN" (* UNKNOWN(7) *)
          )
        end
    done;
    hip_epilogue ()


  
