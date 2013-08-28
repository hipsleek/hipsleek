(*
  Driver.


  loop
  . read command
  . switch <command>
    . data def
    . pred def
    . coercion
      call trans_data/trans_view/trans_coercion and update program
    . entailment check
      call trans_formula and heap_entail
  end loop
*)

open Globals
open Sleekcommons
open Sleekengine
open Gen.Basic
(* open Exc.ETABLE_NFLOW *)
open Exc.GTable

module H = Hashtbl
module I = Iast
module C = Cast
module CF = Cformula
module CP = Cpure
module IF = Iformula
module IP = Ipure
module AS = Astsimp

module XF = Xmlfront
module NF = Nativefront

let _ = Globals.sleek_flag := true

let usage_msg = Sys.argv.(0) ^ " [options] <source files>"

(* let source_files = ref ([] : string list) *)

let set_source_file arg = 
  Globals.source_files := arg :: !Globals.source_files 

let print_version () =
  print_endline ("SLEEK: A Separation Logic Entailment Checker");
  print_endline ("Version 1.0");
  print_endline ("THIS SOFTWARE IS PROVIDED AS-IS, WITHOUT ANY WARRANTIES.");
  print_endline ("IT IS CURRENTLY FREE FOR NON-COMMERCIAL USE");
  print_endline ("Copyright @ PLS2 @ NUS")

let process_cmd_line () = Arg.parse Scriptarguments.sleek_arguments set_source_file usage_msg

let inter = Scriptarguments.inter_hoa

let prompt = ref "SLEEK> "
let terminator = '.'
module M = Lexer.Make(Token.Token)

(*This is overriden by the below*)
(* let parse_file (parse) (source_file : string) = *)
(* 	(\* let _ = print_endline "parse_file 1" in *\) *)
(* 	try *)
(* 		let cmds = parse source_file in  *)
(* 		let _ = (List.map (fun c -> ( *)
(* 							match c with *)
(* 								 | DataDef ddef -> process_data_def ddef *)
(* 								 | PredDef pdef -> process_pred_def pdef *)
(*				                 | RelDef rdef -> process_rel_def rdef *)
(*								 | AxiomDef adef -> process_axiom_def adef (* An Hoa : Bug detected in MUTUALLY DEPENDENT relations! *) *)
                 (* | Infer (ivars, iante, iconseq) -> process_infer ivars iante iconseq *)
(* 								 | CaptureResidue lvar -> process_capture_residue lvar *)
(* 								 | LemmaDef ldef -> process_lemma ldef *)
(* 								 | PrintCmd pcmd ->  *)
(*                                      let _ = print_string " I am here \n" in (\*LDK*\) *)
(*                                      process_print_command pcmd *)
(* 								 | LetDef (lvar, lbody) -> put_var lvar lbody *)
(*                  | Time (b,s,_) -> if b then Gen.Profiling.push_time s else Gen.Profiling.pop_time s *)
(* 								 | EmptyCmd -> ())) cmds) in () *)
(* 	with *)
(* 	  | End_of_file -> *)
(* 		  print_string ("\n") *)
(*     | M.Loc.Exc_located (l,t)->  *)
(*       (print_string ((Camlp4.PreCast.Loc.to_string l)^"\n error: "^(Printexc.to_string t)^"\n at:"^(Printexc.get_backtrace ())); *)
(*       raise t) *)

let proc_gen_cmd cmd =
  match cmd with
    | DataDef ddef -> process_data_def ddef
    | PredDef pdef -> process_pred_def_4_iast pdef
    | BarrierCheck bdef -> (process_data_def (I.b_data_constr bdef.I.barrier_name bdef.I.barrier_shared_vars) 
                             ; process_barrier_def bdef)
    | FuncDef fdef -> process_func_def fdef
    | RelDef rdef -> process_rel_def rdef
    | HpDef hpdef -> process_hp_def hpdef
    | AxiomDef adef -> process_axiom_def adef
    | EntailCheck (iante, iconseq, etype) -> (process_entail_check iante iconseq etype;())
    | RelAssume (id, ilhs, iguard, irhs) -> process_rel_assume id ilhs iguard irhs
    | RelDefn (id, ilhs, irhs) -> process_rel_defn id ilhs irhs
    | ShapeInfer (pre_hps, post_hps) -> process_shape_infer pre_hps post_hps
    | ShapeDivide (pre_hps, post_hps) -> process_shape_divide pre_hps post_hps
    | ShapeConquer (ids, paths) -> process_shape_conquer ids paths
    | ShapePostObl (pre_hps, post_hps) -> process_shape_postObl pre_hps post_hps
    | ShapeInferProp (pre_hps, post_hps) -> process_shape_infer_prop pre_hps post_hps
    | ShapeSplitBase (pre_hps, post_hps) -> process_shape_split pre_hps post_hps
    | ShapeDeclDang (hp_names) -> process_decl_hpdang hp_names
    | ShapeDeclUnknown (hp_names) -> process_decl_hpunknown hp_names
    | ShapeElim (view_names) -> process_shape_elim_useless view_names
    | ShapeExtract (view_names) -> process_shape_extract view_names
    | ShapeSConseq (pre_hps, post_hps) -> process_shape_sconseq pre_hps post_hps
    | ShapeSAnte (pre_hps, post_hps) -> process_shape_sante pre_hps post_hps
    | EqCheck (lv, if1, if2) -> process_eq_check lv if1 if2
    | InferCmd (ivars, iante, iconseq,etype) -> (process_infer ivars iante iconseq etype;())
    | CaptureResidue lvar -> process_capture_residue lvar
    | LemmaDef ldef ->   process_list_lemma ldef
    | PrintCmd pcmd -> process_print_command pcmd
    | Simplify f -> process_simplify f
    | Slk_Hull f -> process_hull f
    | Slk_PairWise f -> process_pairwise f
    | CmpCmd pcmd -> process_cmp_command pcmd
    | LetDef (lvar, lbody) -> put_var lvar lbody
    | Time (b,s,_) -> if b then Gen.Profiling.push_time s else Gen.Profiling.pop_time s
    | EmptyCmd  -> ()

let parse_file (parse) (source_file : string) =
  let rec parse_first (cmds:command list) : (command list)  =
    try 
      parse source_file 
    with
      | End_of_file -> List.rev cmds
      | M.Loc.Exc_located (l,t)-> 
            (print_string ((Camlp4.PreCast.Loc.to_string l)^"\n error: "^(Printexc.to_string t)^"\n at:"^(Printexc.get_backtrace ()));
            raise t) in
  let parse_first (cmds:command list) : (command list)  =
    let pr = pr_list string_of_command in
    Debug.no_1 "parse_first" pr pr parse_first cmds in
  let proc_one_def c = 
    match c with
      | DataDef ddef -> process_data_def ddef
      | PredDef pdef -> process_pred_def_4_iast pdef
      | BarrierCheck bdef -> process_data_def (I.b_data_constr bdef.I.barrier_name bdef.I.barrier_shared_vars)
      | FuncDef fdef -> process_func_def fdef
      | RelDef rdef -> process_rel_def rdef
      | HpDef hpdef -> process_hp_def hpdef
      | AxiomDef adef -> process_axiom_def adef  (* An Hoa *)
            (* | Infer (ivars, iante, iconseq) -> process_infer ivars iante iconseq *)
      | LemmaDef _ | InferCmd _ | CaptureResidue _ | LetDef _ | EntailCheck _ | EqCheck _ | PrintCmd _ | CmpCmd _ 
      | RelAssume _ | RelDefn _ | ShapeInfer _ | ShapeDivide _ | ShapeConquer _ | ShapePostObl _ | ShapeInferProp _ | ShapeSplitBase _ | ShapeElim _ | ShapeExtract _ | ShapeDeclDang _ | ShapeDeclUnknown _
      | ShapeSConseq _ | ShapeSAnte _
      | Time _ | EmptyCmd | _ -> () 
  in
  let proc_one_def c =
    Debug.no_1 "proc_one_def" string_of_command pr_none proc_one_def c 
  in
  (* let proc_one_lemma c =  *)
  (*   match c with *)
  (*     | LemmaDef ldef -> process_list_lemma ldef *)
  (*     | DataDef _ | PredDef _ | BarrierCheck _ | FuncDef _ | RelDef _ | HpDef _ | AxiomDef _ (\* An Hoa *\) *)
  (*     | CaptureResidue _ | LetDef _ | EntailCheck _ | EqCheck _ | InferCmd _ | PrintCmd _  *)
  (*     | RelAssume _ | RelDefn _ | ShapeInfer _ | ShapeDivide _ | ShapeConquer _ | ShapePostObl _  *)
  (*     | ShapeInferProp _ | ShapeSplitBase _ | ShapeElim _ | ShapeExtract _ | ShapeDeclDang _ | ShapeDeclUnknown _ *)
  (*     | ShapeSConseq _ | ShapeSAnte _ *)
  (*     | CmpCmd _| Time _ | _ -> () in *)
  let proc_one_cmd c = 
    match c with
      | EntailCheck (iante, iconseq, etype) -> (process_entail_check iante iconseq etype; ())
            (* let pr_op () = process_entail_check_common iante iconseq in  *)
            (* Log.wrap_calculate_time pr_op !Globals.source_files ()               *)
      | RelAssume (id, ilhs, iguard, irhs) -> process_rel_assume id ilhs iguard irhs
      | RelDefn (id, ilhs, irhs) -> process_rel_defn id ilhs irhs
      | Simplify f -> process_simplify f
      | Slk_Hull f -> process_hull f
      | Slk_PairWise f -> process_pairwise f
      | ShapeInfer (pre_hps, post_hps) -> process_shape_infer pre_hps post_hps
      | ShapeDivide (pre_hps, post_hps) -> process_shape_divide pre_hps post_hps
      | ShapeConquer (ids, paths) -> process_shape_conquer ids paths
      | ShapePostObl (pre_hps, post_hps) -> process_shape_postObl pre_hps post_hps
      | ShapeInferProp (pre_hps, post_hps) -> process_shape_infer_prop pre_hps post_hps
      | ShapeSplitBase (pre_hps, post_hps) -> process_shape_split pre_hps post_hps
      | ShapeDeclDang (hp_names) -> process_decl_hpdang hp_names
      | ShapeDeclUnknown (hp_names) -> process_decl_hpunknown hp_names
      | ShapeElim (view_names) -> process_shape_elim_useless view_names
      | ShapeExtract (view_names) -> process_shape_extract view_names
      | ShapeSConseq (pre_hps, post_hps) -> process_shape_sconseq pre_hps post_hps
      | ShapeSAnte (pre_hps, post_hps) -> process_shape_sante pre_hps post_hps
      | EqCheck (lv, if1, if2) -> 
            (* let _ = print_endline ("proc_one_cmd: xxx_after parse \n") in *)
            process_eq_check lv if1 if2
      | InferCmd (ivars, iante, iconseq,etype) -> (process_infer ivars iante iconseq etype;())	
      | CaptureResidue lvar -> process_capture_residue lvar
      | PrintCmd pcmd -> process_print_command pcmd
      | CmpCmd ccmd -> process_cmp_command ccmd
      | LetDef (lvar, lbody) -> put_var lvar lbody
      | BarrierCheck bdef -> process_barrier_def bdef
      | Time (b,s,_) -> 
            if b then Gen.Profiling.push_time s 
            else Gen.Profiling.pop_time s
      | LemmaDef ldef -> process_list_lemma ldef
      | DataDef _ | PredDef _ | FuncDef _ | RelDef _ | HpDef _ | AxiomDef _ (* An Hoa *) (* | LemmaDef _ *) 
      | EmptyCmd -> () in
  let cmds = parse_first [] in
  List.iter proc_one_def cmds;
  (* An Hoa : Parsing is completed. If there is undefined type, report error.
   * Otherwise, we perform second round checking!
   *)
  let udefs = !Astsimp.undef_data_types in
  let _ = match udefs with
    | [] ->	perform_second_parsing_stage ()
    | _ -> let udn,udp = List.hd (List.rev udefs) in
      Error.report_error { Error.error_loc  = udp;
      Error.error_text = "Data type " ^ udn ^ " is undefined!" }
  in ();
  Debug.tinfo_pprint "sleek : after 2nd parsing" no_pos;
  convert_data_and_pred_to_cast ();
  Debug.tinfo_pprint "sleek : after convert_data_and_pred_to_cast" no_pos;
  (* List.iter proc_one_lemma cmds; *)
  (* Debug.tinfo_pprint "sleek : after proc one lemma" no_pos; *)
  (*identify universal variables*)
  let cviews = !cprog.C.prog_view_decls in
  let cviews = List.map (Cast.add_uni_vars_to_view !cprog (Lem_store.all_lemma # get_left_coercion) (*!cprog.C.prog_left_coercions*)) cviews in
  !cprog.C.prog_view_decls <- cviews;
  List.iter proc_one_cmd cmds 


let main () =
  let _ = Globals.is_sleek_running := true in
  let _ = Printexc.record_backtrace !Globals.trace_failure in
  let iprog = { I.prog_include_decls =[];
		            I.prog_data_decls = [iobj_def];
                I.prog_global_var_decls = [];
                I.prog_logical_var_decls = [];
                I.prog_enum_decls = [];
                I.prog_view_decls = [];
                I.prog_func_decls = [];
                I.prog_rel_decls = [];
                I.prog_rel_ids = [];
                I.prog_hp_decls = [];
			    I.prog_hp_ids = [];
                I.prog_axiom_decls = []; (* [4/10/2011] An Hoa *)
                I.prog_proc_decls = [];
                I.prog_coercion_decls = [];
                I.prog_hopred_decls = [];
				I.prog_barrier_decls = [];
              } in
  let _ = process_data_def (I.b_data_constr b_datan []) in
  let _ = I.inbuilt_build_exc_hierarchy () in (* for inbuilt control flows *)
  let _ = Iast.build_exc_hierarchy true iprog in
  let _ = exlist # compute_hierarchy  in  
  (* let _ = print_endline ("GenExcNum"^(Exc.string_of_exc_list (1))) in *)
  let quit = ref false in
  let parse x =
    match !Scriptarguments.fe with
      | Scriptarguments.NativeFE -> NF.parse_slk x
      | Scriptarguments.XmlFE -> XF.parse x in
  let parse x = Debug.no_1 "parse" pr_id string_of_command parse x in
  let buffer = Buffer.create 10240 in
  try
      if (!inter) then
        begin
            Debug.info_pprint "sleek : interactive" no_pos;
            while not (!quit) do
              if !inter then (* check for interactivity *)
                print_string !prompt;
                let input = read_line () in
                match input with
                  | "" -> ()
                  | _ -> 
                      try
                          let term_indx = String.index input terminator in
                          let s = String.sub input 0 (term_indx+1) in
                          Buffer.add_string buffer s;
                          let cts = Buffer.contents buffer in
                          if cts = "quit" || cts = "quit\n" then quit := true
                          else try
                                   let cmd = parse cts in
                                   proc_gen_cmd cmd;
                                   Buffer.clear buffer;
                                   if !inter then
                                     prompt := "SLEEK> "
                              with
                                | _ -> dummy_exception();
                                    print_string ("Error.\n");
                                    print_endline "Last SLEEK FAILURE:";
                                    Log.last_cmd # dumping "sleek_dump(interactive)";
                                    (*     sleek_command # dump; *)
                                    (* print_endline "Last PURE PROOF FAILURE:"; *)
                                    (* Log.last_proof_command # dump; *)
                                    Buffer.clear buffer;
                                    if !inter then prompt := "SLEEK> "
                      with 
                        | SLEEK_Exception
                        | Not_found -> dummy_exception();
                            Buffer.add_string buffer input;
                            Buffer.add_char buffer '\n';
                            if !inter then prompt := "- "
            done
        end
      else
        begin
      (* let _ = print_endline "Prior to parse_file" in *)
            Debug.tinfo_pprint "sleek : batch processing" no_pos;
            let _ = List.map (parse_file NF.list_parse) !Globals.source_files in ()
        end
  with
    | End_of_file -> 
        begin
            print_string ("\n")
        end
      (* | Not_found -> print_string ("Not found exception caught!\n") *)

(* let main () =  *)
(*   Debug.loop_1_no "main" (fun () -> "?") (fun () -> "?") main () *)
let sleek_proof_log_Z3 src_files =
  (* let _ = Log.process_proof_logging src_files in   *)
  if !Globals.proof_logging || !Globals.proof_logging_txt   then 
    begin
      (* let _=sleek_src_files := src_files in *)
      Debug.info_hprint (add_str "src_files" (pr_list pr_id)) src_files no_pos;
      let tstartlog = Gen.Profiling.get_time ()in	
      (* let _= Log.proof_log_to_file () in *)
      let with_option = if(!Globals.en_slc_ps) then "sleek_eps" else "sleek_no_eps" in
      let with_option_logtxt = if(!Globals.en_slc_ps) then "eps" else "no_eps" in
      let fname = "logs/"^with_option_logtxt^"_proof_log_" ^ (Globals.norm_file_name (List.hd src_files)) ^".txt"  in
      (* let fz3name= ("logs/"^with_option^(Globals.norm_file_name (List.hd src_files)) ^".z3")  in *)
      (* let fnamegt5 = "logs/greater_5sec_"^with_option_logtxt^"_proof_log_" ^ (Globals.norm_file_name (List.hd src_files)) ^".txt"  in *)
      let _= if (!Globals.proof_logging_txt) 
      then 
        begin
          (* Debug.info_pprint ("Logging "^fname^"\n") no_pos; *)
	  (* Debug.info_pprint ("Logging "^fz3name^"\n") no_pos; *)
	  (* Debug.info_pprint ("Logging "^fnamegt5^"\n") no_pos; *)
          Log.proof_log_to_text_file fname !Globals.source_files;
          Log.sleek_log_to_text_file2 !Globals.source_files;
	  (* Log.z3_proofs_list_to_file fz3name !Globals.source_files; *)
	  (* Log.proof_greater_5secs_to_file !Globals.source_files; *)
        end
      in
      let tstoplog = Gen.Profiling.get_time () in
      let _= Globals.proof_logging_time := !Globals.proof_logging_time +. (tstoplog -. tstartlog) 
        (* let _=print_endline ("Time for logging: "^(string_of_float (!Globals.proof_logging_time))) in	() *)
      in ()
    end
		
let _ =
  wrap_exists_implicit_explicit := false ;
  process_cmd_line ();
  let _ = Debug.read_main () in
  Scriptarguments.check_option_consistency ();
  if !Globals.print_version_flag then begin
    print_version ()
  end else (
    (* let _ = Printexc.record_backtrace !Globals.trace_failure in *)
    if (!Tpdispatcher.tp_batch_mode) then Tpdispatcher.start_prover ();
    Gen.Profiling.push_time "Overall";
    (* let _ = print_endline "before main" in *)
    main ();
    (* let _ = print_endline "after main" in *)
    Gen.Profiling.pop_time "Overall";
    if (!Tpdispatcher.tp_batch_mode) then Tpdispatcher.stop_prover ();
    (* Get the total proof time *)
    let _ = if not(!Globals.no_cache_formula) then
      begin
        let fp a = (string_of_float ((floor(100. *.a))/.100.)) in
        let calc_hit_percent c m = (100. *. ((float_of_int (c - m)) /. (float_of_int c))) in
        let string_of_hit_percent c m = (fp (calc_hit_percent c m))^"%" in
        let s_c = !Tpdispatcher.cache_sat_count in
        let s_m = !Tpdispatcher.cache_sat_miss in
        let i_c = !Tpdispatcher.cache_imply_count in
        let i_m = !Tpdispatcher.cache_imply_miss in
        if s_c>0 then
          begin
            print_endline_if !Globals.enable_count_stats ("\nSAT Count   : "^(string_of_int s_c)); 
            print_endline_if !Globals.enable_time_stats ("SAT % Hit   : "^(string_of_hit_percent s_c s_m))
          end;
        if i_c>0 then
          begin
            print_endline_if !Globals.enable_count_stats ("IMPLY Count : "^(string_of_int i_c)); 
            print_endline_if !Globals.enable_time_stats ("IMPLY % Hit : "^(string_of_hit_percent i_c i_m))
           end;
        if i_c+s_c>0 then 
          if !Globals.enable_time_stats 
          then (Gen.Profiling.print_info_task "cache overhead")
          else ()
        else ()
     end
          else ()
    in
    let _ = if !Globals.enable_time_stats then
      begin
        let ptime4 = Unix.times () in
        let t4 = ptime4.Unix.tms_utime +. ptime4.Unix.tms_cutime +. ptime4.Unix.tms_stime +. ptime4.Unix.tms_cstime in
        Timelog.logtime # dump;
        silenced_print print_string ("\nTotal verification time: " 
        ^ (string_of_float t4) ^ " second(s)\n"
        ^ "\tTime spent in main process: " 
        ^ (string_of_float (ptime4.Unix.tms_utime+.ptime4.Unix.tms_stime)) ^ " second(s)\n"
        ^ "\tTime spent in child processes: " 
        ^ (string_of_float (ptime4.Unix.tms_cutime +. ptime4.Unix.tms_cstime)) ^ " second(s)\n")
      end
    else ()
    in
    let _= sleek_proof_log_Z3 !Globals.source_files in
    let _ = 
      if (!Globals.profiling && not !inter) then 
        ( Gen.Profiling.print_info (); print_string (Gen.Profiling.string_of_counters ())) in
    print_string "\n"
  )
