(******************************************)
(* command line processing                *)
(******************************************)

let parse_only = ref false

let to_java = ref false

let comp_pred = ref false

let rtc = ref false

let pred_to_compile = ref ([] : string list)

let set_pred arg = 
  comp_pred := true;
  pred_to_compile := arg :: !pred_to_compile


let usage_msg = Sys.argv.(0) ^ " [options] <source files>"

let set_source_file arg = 
  Globals.source_files := arg :: !Globals.source_files

let set_proc_verified arg =
  let procs = Util.split_by "," arg in
	Globals.procs_verified := procs @ !Globals.procs_verified

let process_cmd_line () = Arg.parse [
	("--no-omega-simpl", Arg.Clear Globals.omega_simpl,
	"Do not use Omega to simplify the arithmetic constraints when using other solver");
	("--simpl-pure-part", Arg.Set Globals.simplify_pure,
	"Simplify the pure part of the formulas");
	("--combined-lemma-heuristic", Arg.Set Globals.lemma_heuristic,
	"Use the combined coerce&match + history heuristic for lemma application");
	("--move-exist-to-LHS", Arg.Set Globals.move_exist_to_LHS,
	"Move instantiation (containing existential vars) to the LHS at the end of the folding process");
	("--max-renaming", Arg.Set Globals.max_renaming,
	"Always rename the bound variables");
	("--no-anon-exist", Arg.Clear Globals.anon_exist,
	"Disallow anonymous variables in the precondition to be existential");
	("--LHS-wrap-exist", Arg.Set Globals.wrap_exist,
	"Existentially quantify the fresh vars in the residue after applying ENT-LHS-EX");
  ("-noee", Arg.Clear Tpdispatcher.elim_exists_flag,
   "No eleminate existential quantifiers before calling TP.");
  ("-nofilter", Arg.Clear Tpdispatcher.filtering_flag,
   "No assumption filtering.");
  ("-cp", Arg.String set_pred,
   "Compile specified predicate to Java.");
  ("-rtc", Arg.Set rtc,
   "Compile to Java with runtime checks.");
  ("-nopp", Arg.String Rtc.set_nopp,
   "-nopp caller:callee: do not check callee's pre/post in caller");
  ("-nofield", Arg.String Rtc.set_nofield,
   "-nofield proc: do not perform field check in proc");
  ("--verify-callees", Arg.Set Globals.verify_callees,
   "Verify callees of the specified procedures");
  ("--check-coercions", Arg.Set Globals.check_coercions,
   "Check coercion validity");
  ("-dd", Arg.Set Debug.devel_debug_on,
   "Turn on devel_debug");
  ("-gist", Arg.Set Globals.show_gist,
   "Show gist when implication fails");
  ("--hull-pre-inv", Arg.Set Globals.hull_pre_inv,
   "Hull precondition invariant at call sites");
  ("-inline", Arg.String Inliner.set_inlined,
   "Procedures to be inlined");
  (*("-java", Arg.Set to_java,
   "Convert source code to Java");*)
  ("--sat-timeout", Arg.Set_float Globals.sat_timeout,
   "Timeout for sat checking");
  ("--imply-timeout", Arg.Set_float Globals.imply_timeout,
   "Timeout for imply checking");
  ("--log-proof", Arg.String Prooftracer.set_proof_file,
   "Log (failed) proof to file");
  ("--trace-all", Arg.Set Globals.trace_all,
   "Trace all proof paths");
  ("--log-cvcl", Arg.String Cvclite.set_log_file,
   "Log all CVC Lite formula to specified log file");
  ("--log-omega", Arg.Set Omega.log_all_flag,
   "Log all formulae sent to Omega Calculator in file allinput.oc");
  ("--log-isabelle", Arg.Set Isabelle.log_all_flag,
   "Log all formulae sent to Isabelle in file allinput.thy");
  ("--log-coq", Arg.Set Coq.log_all_flag,
   "Log all formulae sent to Coq in file allinput.v");
  ("--log-mona", Arg.Set Mona.log_all_flag,
   "Log all formulae sent to Mona in file allinput.mona");
  ("--log-redlog", Arg.Set Redlog.is_log_all,
    "Log all formulae sent to Reduce/Redlog in file allinput.rl");
  ("--use-isabelle-bag", Arg.Set Isabelle.bag_flag,
   "Use the bag theory from Isabelle, instead of the set theory");
  ("--no-coercion", Arg.Clear Globals.use_coercion,
   "Turn off coercion mechanism");
  ("--no-exists-elim", Arg.Clear Globals.elim_exists,
   "Turn off existential quantifier elimination during type-checking");
  ("--no-diff", Arg.Set Solver.no_diff,
   "Drop disequalities generated from the separating conjunction");
  ("--no-set", Arg.Clear Globals.use_set,
   "Turn off set-of-states search");
  ("--unsat-elim", Arg.Set Globals.elim_unsat,
   "Turn on unsatisfiable formulae elimination during type-checking");
  ("-nxpure", Arg.Set_int Globals.n_xpure,
   "Number of unfolding using XPure");
  ("-p", Arg.String set_proc_verified, 
   "Procedure to be verified. If none specified, all are verified.");
  ("-parse", Arg.Set parse_only,
   "Parse only");
  ("-print", Arg.Set Globals.print_proc,
   "Print procedures being checked");
  ("--print-iparams", Arg.Set Globals.print_mvars,
   "Print input parameters of predicates");
  ("--print-x-inv", Arg.Set Globals.print_x_inv,
   "Print computed view invariants");
  ("-stop", Arg.Clear Globals.check_all,
   "Stop checking on erroneous procedure");
  ("--build-image", Arg.Symbol (["true"; "false"], Isabelle.building_image),
   "Build the image theory in Isabelle - default false");
   ("-tp", Arg.Symbol (["cvcl"; "omega"; "co"; "isabelle"; "coq"; "mona"; "om";
   "oi"; "set"; "cm"; "redlog"; "rm"; "prm" ], Tpdispatcher.set_tp),
   "Choose theorem prover:\n\tcvcl: CVC Lite\n\tomega: Omega Calculator (default)\n\tco: CVC Lite then Omega\n\tisabelle: Isabelle\n\tcoq: Coq\n\tmona: Mona\n\tom: Omega and Mona\n\toi: Omega and Isabelle\n\tset: Use MONA in set mode.\n\tcm: CVC Lite then MONA.");
  ("--use-field", Arg.Set Globals.use_field,
   "Use field construct instead of bind");
  ("--use-large-bind", Arg.Set Globals.large_bind,
   "Use large bind construct, where the bound variable may be changed in the body of bind");
  ("-v", Arg.Set Debug.debug_on, "Verbose");
  ("--pipe", Arg.Unit Tpdispatcher.Netprover.set_use_pipe, "use external prover via pipe");
  ("--dsocket", Arg.Unit (fun () -> Tpdispatcher.Netprover.set_use_socket "loris-7:8888"), "<host:port>: use external prover via loris-7:8888");
  ("--socket", Arg.String Tpdispatcher.Netprover.set_use_socket, "<host:port>: use external prover via socket");
  ("--prover", Arg.String Tpdispatcher.set_tp, "<p,q,..> comma-separated list of provers to try in parallel");
  ("--enable-sat-stat", Arg.Set Globals.enable_sat_statistics, "enable sat statistics");
  ("--epi", Arg.Set Globals.profiling, "enable profiling statistics");
  ("--sbc", Arg.Set Globals.enable_syn_base_case, "use only syntactic base case detection");
  ("--eci", Arg.Set Globals.enable_case_inference,"enable struct formula inference");
  ("--pcp", Arg.Set Globals.print_core,"print core representation");
  ("--pgbv", Arg.Set Globals.pass_global_by_value, "pass read global variables by value");
  ("--pip", Arg.Set Globals.print_input,"print input representation");
  ("--sqt", Arg.Set Globals.seq_to_try,"translate seq to try");
  ("--web", Arg.String (fun s -> (Tpdispatcher.Netprover.set_use_socket_for_web s); Tpdispatcher.webserver := true; Typechecker.webserver := true; Paralib1v2.webs := true; Paralib1.webs := true) , "<host:port>: use external web service via socket");
  ("-para", Arg.Int Typechecker.parallelize, "Use Paralib map_para instead of List.map in typecheker");
  ("--priority",Arg.String Tpdispatcher.Netprover.set_prio_list, "<proc_name1:prio1;proc_name2:prio2;...> To be used along with webserver");
  ("--decrprio",Arg.Set Tpdispatcher.decr_priority , "use a decreasing priority scheme");
  ("--redlog-int-relax", Arg.Set Redlog.integer_relax_mode, "use redlog real q.e to prove intefer formula  *experiment*");
  ("--redlog-ee", Arg.Set Redlog.is_ee, "enable Redlog existential quantifier elimination");
   ("--gui", Arg.Set Gui.enable_gui, "enable GUI")  
  (*("--iv", Arg.Set_int Globals.instantiation_variants,"instantiation variants (0-default)->existentials,implicit, explicit; 1-> implicit,explicit; 2-> explicit; 3-> existentials,implicit; 4-> implicit; 5-> existential,explicit;");*)
	] set_source_file usage_msg

(******************************************)
(* main function                          *)
(******************************************)

let parse_file_full file_name = 
  let org_in_chnl = open_in file_name in
  let input = Lexing.from_channel org_in_chnl in
    try
    (*let ptime1 = Unix.times () in
	  let t1 = ptime1.Unix.tms_utime +. ptime1.Unix.tms_cutime in
     *)
		print_string "Parsing...\n";
        let _ = Util.push_time "Parsing" in
		let prog = Iparser.program (Ilexer.tokenizer file_name) input in
		  close_in org_in_chnl;
         let _ = Util.pop_time "Parsing" in
    (*		  let ptime2 = Unix.times () in
		  let t2 = ptime2.Unix.tms_utime +. ptime2.Unix.tms_cutime in
			print_string ("done in " ^ (string_of_float (t2 -. t1)) ^ " second(s)\n"); *)
			prog 
    with
		End_of_file -> exit 0	  

let process_source_full source =
  print_string ("\nProcessing file \"" ^ source ^ "\"\n");
  let _ = Util.push_time "Preprocessing" in
  let prog = parse_file_full source in
    if !to_java then begin
      print_string ("Converting to Java...");
      let tmp = Filename.chop_extension (Filename.basename source) in
      let main_class = Util.replace_minus_with_uscore tmp in
      let java_str = Java.convert_to_java prog main_class in
      let tmp2 = Util.replace_minus_with_uscore (Filename.chop_extension source) in
      let jfile = open_out ("output/" ^ tmp2 ^ ".java") in
	output_string jfile java_str;
	close_out jfile;
	print_string (" done.\n");
	exit 0
    end;
    if (!parse_only) then 
      let _ = Util.pop_time "Preprocessing" in
	print_string (Iprinter.string_of_program prog)
    else 

      (* Global variables translating *)
      let _ = Util.push_time "Translating global var" in
      let _ = print_string ("Translating global variables to procedure parameters...\n"); flush stdout in
      let intermediate_prog = Globalvars.trans_global_to_param prog in
      let intermediate_prog = Iast.label_procs_prog intermediate_prog in
      let _ = if (!Globals.print_input) then print_string (Iprinter.string_of_program intermediate_prog) else () in
      let _ = Util.pop_time "Translating global var" in
	(* Global variables translated *)
	(* let ptime1 = Unix.times () in
	   let t1 = ptime1.Unix.tms_utime +. ptime1.Unix.tms_cutime in *)
      let _ = Util.push_time "Translating to Core" in
      let _ = print_string ("Translating to core language..."); flush stdout in
      let cprog = Astsimp.trans_prog intermediate_prog in
      let _ = print_string (" done\n"); flush stdout in
      let _ = if (!Globals.print_core) then print_string (Cprinter.string_of_program cprog) else () in
      let _ = 
	if !Globals.verify_callees then begin
	  let tmp = Cast.procs_to_verify cprog !Globals.procs_verified in
	    Globals.procs_verified := tmp
	end in
      let _ = Util.pop_time "Translating to Core" in
	(* let ptime2 = Unix.times () in
	   let t2 = ptime2.Unix.tms_utime +. ptime2.Unix.tms_cutime in
	   let _ = print_string (" done in " ^ (string_of_float (t2 -. t1)) ^ " second(s)\n") in *)
      let _ =
	if !comp_pred then begin
	  let _ = print_string ("Compiling predicates to Java...") in
	  let compile_one_view vdef = 
	    if (!pred_to_compile = ["all"] || List.mem vdef.Cast.view_name !pred_to_compile) then
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
	    print_string ("\nDone.\n");
	    exit 0
	end 
      in
      let _ =
	if !rtc then begin
	  Rtc.compile_prog cprog source;
	  exit 0
	end
      in
      let _ = Util.pop_time "Preprocessing" in
	if !Gui.enable_gui then begin
	  ignore (Gui.check_prog (Gui.get_win ()) cprog)
	end
	else 
	  ignore (Typechecker.check_prog cprog);

	(* i.e. stop Reduce/Redlog if it is running. *)
	let _ = Tpdispatcher.finalize () in

	let ptime4 = Unix.times () in
	let t4 = ptime4.Unix.tms_utime +. ptime4.Unix.tms_cutime +. ptime4.Unix.tms_stime +. ptime4.Unix.tms_cstime   in
	  print_string ("\n"^(string_of_int (List.length !Globals.false_ctx_line_list))^" false contexts at: ("^
			  (List.fold_left (fun a c-> a^" ("^(string_of_int c.Globals.start_pos.Lexing.pos_lnum)^","^
					     ( string_of_int (c.Globals.start_pos.Lexing.pos_cnum-c.Globals.start_pos.Lexing.pos_bol))^") ") "" !Globals.false_ctx_line_list)^")\n");
	  print_string ("\nTotal verification time: " 
			^ (string_of_float t4) ^ " second(s)\n"
			^ "\tTime spent in main process: " 
			^ (string_of_float (ptime4.Unix.tms_utime+.ptime4.Unix.tms_stime)) ^ " second(s)\n"
			^ "\tTime spent in child processes: " 
			^ (string_of_float (ptime4.Unix.tms_cutime +. ptime4.Unix.tms_cstime)) ^ " second(s)\n")



let main_gui () = 
  (* process_cmd_line (); *)
  let _ = GMain.init () in
  let _ = Tpdispatcher.prepare () in
    if List.length (!Globals.source_files) = 0 then begin
      (* print_string (Sys.argv.(0) ^ " -help for usage information\n") *)
      Globals.procs_verified := ["f3"];
      Globals.source_files := ["examples/test5.ss"]
    end;
    let _ = Gui.set_win (new Gui.mainwindow "HIP VIEWER" (List.hd !Globals.source_files)) in 
      Util.push_time "Overall";
      ignore (List.map process_source_full !Globals.source_files);
      Util.pop_time "Overall";
      (Gui.get_win ())#show ();
      GMain.Main.main ()



	  
let main1 () =
  (* process_cmd_line (); *)
  
  (* i.e. pre-start Reduce/Redlog if it will be used. *)
  let _ = Tpdispatcher.prepare () in
  
  if List.length (!Globals.source_files) = 0 then begin
	(* print_string (Sys.argv.(0) ^ " -help for usage information\n") *)
	Globals.procs_verified := ["f3"];
	Globals.source_files := ["examples/test5.ss"]
  end;
  let _ = Util.push_time "Overall" in
  let _ = List.map process_source_full !Globals.source_files in
  let _ = Util.pop_time "Overall" in
	(* Tpdispatcher.print_stats (); *)
	()
	  
let _ =  
  process_cmd_line ();
  if !Gui.enable_gui then main_gui () 
  else 
    main1 ();
  (*let rec check_aux (t1,t2,t3,t4) l = match l with
    | [] -> true
    | (p1,p2,p3,p4)::l1 -> if (p1<=t1 && p2<=t2&& p3<=t3&& p4<=t4) then check_aux (p1,p2,p3,p4) l1
    else false in
    let check_sorted l = match l with
    | a::b -> check_aux a b
    | [] -> true  in
    let _ = print_string ("stack height: "^(string_of_int (List.length !Util.profiling_stack))^"\n") in
    let _ = print_string ("get time length: "^(string_of_int (List.length !Util.time_list))^" "^
    (string_of_bool (check_sorted !Util.time_list))^"\n" ) in*)
  let _ = if (!Globals.profiling) then 
    let str_list = Hashtbl.fold (fun c1 (t,cnt,l) a-> (c1,t,cnt,l)::a) !Util.tasks [] in
    let str_list = List.sort (fun (c1,_,_,_)(c2,_,_,_)-> String.compare c1 c2) str_list in
    let (_,ot,_,_) = List.find (fun (c1,_,_,_)-> (String.compare c1 "Overall")=0) str_list in
    let f a = (string_of_float ((floor(100. *.a))/.100.)) in
    let fp a = (string_of_float ((floor(10000. *.a))/.100.)) in
    let (cnt,str) = List.fold_left (fun (a1,a2) (c1,t,cnt,l)  -> 
				      let r = (a2^" \n("^c1^","^(f t)^","^(string_of_int cnt)^","^ (f (t/.(float_of_int cnt)))^",["^
						 (if (List.length l)>0 then 
						    let l = (List.sort compare l) in		
						      (List.fold_left (fun a c -> a^","^(f c)) (f (List.hd l)) (List.tl l) )
						  else "")^"],  "^(fp (t/.ot))^"%)") in
					((a1+1),r) 
				   ) (0,"") str_list in
      print_string ("\n profile results: there where " ^(string_of_int cnt)^" keys \n"^str^"\n" ) in
    if (!Globals.enable_sat_statistics) then 
      print_string ("\n there where: \n -> successful imply checks : "^(string_of_int !Globals.true_imply_count)^
		      "\n -> failed imply checks : "^(string_of_int !Globals.false_imply_count)^
		      "\n -> successful sat checks : "^(string_of_int !Globals.true_sat_count)
		   )
    else ()

  
open Monads
open Typeclass

(* module MonadE_B (S:SHOW_B) = struct *)
(*   module A=SHOW(S)  *)
(*   type 'a m = Success of 'a | Error of string *)
(*   let return a = Success a *)
(*   let bind er f =  match er with *)
(*     |	Success v -> f v *)
(*     |   Error s -> Error s *)
(*   let showE e = match e with *)
(*     | (Success v) -> "Value: " (\* ^(A.show v) *\) *)
(*     | (Error s) -> "Error: "^s *)
(* end *)

module type MonadErr_B_sig = sig
  type 'a m = Success of 'a | Error of string
  val return : 'a -> 'a m
  val bind : 'a m -> ('a -> 'b m) -> 'b m
end

module MonadErr_B = struct
  type 'a m = Success of 'a | Error of string
  let return a = Success a
  let bind er f = match er with
    | Success v -> f v
    | Error s -> Error s
end

module MonadErr (S:SHOW_sig) = struct
  include MonadErr_B
  let showE e = match e with
    | (Success v) -> "Value: "  ^(S.show v) 
    | (Error s) -> "Error: "^s
end

module MonadState_B  = struct
  module E=MonadErr_B
  type 'a m = (int -> ('a E.m * int)) 
  let return a =  (fun s -> ((E.return a),s) )
  let bind (m1) k = (fun s ->
		       let (e1,s1) = m1 s in
			 match e1 with
			   | (E.Success v) -> let m2 = k v in (m2 s1)
			   | (E.Error s) -> (E.Error s,s1)
  		    )
end


module MonadState_E (S:SHOW_sig) = struct
  include MonadState_B
  module EX=MonadErr(S) 
  let bind1 m k = bind m (fun _ -> k)
  let errorM m = fun s -> (E.Error m, s)

   let showM m = let (a,s) = m 0 in
    EX.showE a (*^"  ; "^" Count: " ^ (B.show s)	 *)   
  let tickS () : unit m = fun s -> (E.Success (),s+1)
end

    
(* module MonadM_B(S:SHOW_B)  = struct *)
(*   module E=MonadE_B(S) *)
(*   module B=SHOW(S)   *)
(*   type 'a m = (int -> ('a E.m * int))  *)
(*   let return a =  (fun s -> ((E.return a),s) ) *)
(*   let bind (m1) k = (fun s -> *)
(* 		       let (e1,s1) = m1 s in *)
(* 			 match e1 with *)
(* 			   | (E.Success v) -> let m2 = k v in (m2 s1) *)
(* 			   | (E.Error s) -> (E.Error s,s1) *)
(*   		    ) *)
(*   let bind1 m k = bind m (fun _ -> k) *)
(*   let errorM m = fun s -> (E.Error m, s) *)

(*    let showM m = let (a,s) = m 0 in *)
(*     E.showE a (\*^"  ; "^" Count: " ^ (B.show s)	 *\)    *)
(*   let tickS () : unit m = fun s -> (E.Success (),s+1) *)

(* end *)


module I_EV_SHOW_B = struct
  type s = int 				(* Evalue.a *)
  let shows = fun x s -> (string_of_int x) ^ s
end    

module I_SHOW_B = struct
  module M = MonadState_B
  type s = ENum of int | EFun of (s M.m -> s M.m)
  let shows x s = match x with
    | ENum i -> (string_of_int i) ^ s
    | EFun _ -> "<function>"^s
  let show (x:s) : string  = shows x ""
end

module I_SHOW_B2 = struct
  module M = MonadState_B
  type s = ENum of int | EFun of (s M.m -> s M.m)
  let shows x s = match x with
    | ENum i -> (string_of_int i) ^ s
    | EFun _ -> "<function>"^s
end

(* below exposes the Show s type *)
module I_SHOW_B3 = struct 
  include I_SHOW_B2
  include SHOW_E(I_SHOW_B2)
end

module Evalue =  struct
  (* module M=MonadM_B(I_EV_SHOW_B) *)
  module S=I_SHOW_B3
  (* module S=SHOW_E(I_SHOW_B2) *)
  module M=MonadState_E(SHOW(S))
 
  (* type s = ENum of int | EFun of (s  M.m -> s  M.m) *)
    
  (* let shows v s= match v with *)
  (*     ENum i -> (string_of_int i) ^ s *)
  (*   | EFun f -> "<function>" ^s *)
  (* let show (v) : string = shows v "" *)

    
  type environment = (string * (S.s  M.m)) list

  let rec lookup (n:string) (ev:environment) : S.s M.m =
    match ev with
	[] -> M.errorM ("unbound variable: "^n)
      |(e,v)::evs -> if n=e then v else (lookup n evs)

  let add (x:S.s) (y:S.s) : S.s M.m =
    match (x,y) with
  	((S.ENum i),(S.ENum j)) -> M.bind1 (M.tickS ()) (M.return (S.ENum (i+j)))
      |  _ -> M.errorM ("should be numbers: ")

  let apply (x:S.s) (y: S.s M.m) : S.s M.m =
    match x with
	(S.EFun k) -> M.bind1 (M.tickS ()) (k y)
      | _ -> M.errorM ("should be function: "^ S.show x)
	  
  type eTerm = EVar of string | ECon of int
	       | EAdd of eTerm * eTerm
	       | ELam of string * eTerm
	       |EApp of eTerm * eTerm
		   
  let rec interp (t:eTerm) (ev:environment) : S.s M.m =
    match t with
      | (EVar x) -> lookup x ev
      | (ECon i) -> M.return (S.ENum i)
      | (EAdd (u,v)) -> M.bind (interp u ev) (fun a -> (M.bind (interp v ev) (fun b -> (add a b))))
      | (ELam (x,v)) -> M.return (S.EFun (fun a -> interp v ((x,a)::ev)))
      | EApp (u,v) -> M.bind (interp u ev) (fun a -> (apply a (interp v ev)))

 
  let test (t:eTerm) : string = M.showM (interp t [])

   let _ = print_string ("\n" ^ (test (ECon 2)) ^"\n");print_string ("\n" ^ (test (EApp ((ECon 2),(ECon 2)))) ^"\n")
       
     
end




  
(* type evalue = ENum of int | EFun of (evalue  EValue_MonadM_B.m -> evalue  EValue_MonadM_B.m)  *)

(* type environment = (string * (evalue  EValue_MonadM_B.m)) list *)

(* type eTerm = EVar of string | ECon of int *)
(* | EAdd of eTerm * eTerm *)
(* | ELam of string * eTerm *)
(* |EApp of eTerm * eTerm *)
    



    

  




  
