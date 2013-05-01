open Globals 
open GlobProver
open Stat_global
open Gen.Basic
open Printf
open Cprinter

module CP = Cpure
module CF = Cformula

 
type proof_type =
	| IMPLY of (CP.formula * CP.formula)
	| SAT of CP.formula
	| SIMPLIFY of CP.formula

type proof_res =
	| BOOL of bool
	| FORMULA of CP.formula

type proof_log = {
	log_id : string; (* TODO: Should change to integer for performance *)
	log_other_properties : string list; (* TODO: Should change to integer for performance *)
	log_prover : string;
	log_type : proof_type option;
	log_time : float;
	log_cache : bool;
	log_res : proof_res;
}

(* type sleek_proving_kind = *)
(* 	| POST *)
(* 	| PRE *)
(* 	| BINDING *)
(*     | ASSERTION *)

type sleek_log_entry = {
    sleek_proving_id :int;
    sleek_proving_pos: loc;
    sleek_proving_classic_flag: bool;
    sleek_proving_avoid: bool;
    sleek_proving_caller: string;
    sleek_proving_hec: int;
    sleek_proving_kind : string;
(* sleek_proving_kind; *)
    sleek_proving_ante: CF.formula;
    sleek_proving_conseq: CF.formula;
    sleek_proving_c_heap: CF.h_formula;
    sleek_proving_evars: CP.spec_var list;
    sleek_proving_hprel_ass: CF.hprel list;
    sleek_proving_rel_ass: CP.infer_rel_type list;
    sleek_proving_res : CF.list_context;
}

(* let string_of_sleek_proving_kind t= *)
  (* match t with *)
  (*   | POST -> "POST" *)
  (*   | PRE -> "PRE" *)
  (*   | BINDING -> "BINDING" *)
  (*   | ASSERTION -> "ASSERTION" *)

let string_of_sleek_proving_kind () = Globals.proving_kind#string_of

let pr_sleek_log_entry e=
  fmt_open_box 1;
  (if (e.sleek_proving_avoid) then
   fmt_string ("HIDE! ")
  );
  fmt_string ("id: " ^ (string_of_int e.sleek_proving_id));
  fmt_string ("; caller: " ^ (e.sleek_proving_caller));
  fmt_string ("; line: " ^ (Globals.line_number_of_pos e.sleek_proving_pos)) ;
  fmt_string ("; classic: " ^ (string_of_bool e.sleek_proving_classic_flag)) ;
  fmt_string ("; kind: " ^ (e.sleek_proving_kind)) ;
  fmt_string ("; hec_num: " ^ (string_of_int e.sleek_proving_hec)) ;
  fmt_string ("; evars: " ^ (Cprinter.string_of_spec_var_list e.sleek_proving_evars)) ;
  fmt_string ("; c_heap:" ^ (Cprinter.string_of_h_formula e.sleek_proving_c_heap)) ;
  fmt_string "\n checkentail";
  fmt_string (Cprinter.string_of_formula e.sleek_proving_ante);
  fmt_string "\n |- ";
  fmt_string  (Cprinter.string_of_formula e.sleek_proving_conseq);
  fmt_string ". \n";
  (match e.sleek_proving_hprel_ass with
        | [] -> ()
        | _  -> let pr = pr_list_ln Cprinter.string_of_hprel_short in
                fmt_string ("hprel_ass: " ^ (pr e.sleek_proving_hprel_ass)^"\n")
  );
  (match e.sleek_proving_rel_ass with
        | [] -> ()
        | _  -> let pr = pr_list_ln CP.string_of_infer_rel in
                fmt_string ("pure rel_ass: " ^ (pr e.sleek_proving_rel_ass)^"\n")
  );
  fmt_string  ("res: " ^ (Cprinter.string_of_list_context_short e.sleek_proving_res));
  fmt_close()

let string_of_sleek_log_entry e= Cprinter.poly_string_of_pr pr_sleek_log_entry e

let sleek_counter= ref 0

let proof_log_tbl : (string, proof_log) Hashtbl.t = Hashtbl.create 700

let sleek_log_stk : sleek_log_entry  Gen.stack_filter 
      = new Gen.stack_filter
  string_of_sleek_log_entry (==) (fun e -> not(e.sleek_proving_avoid))

(* let sleek_proving_kind = ref (POST : sleek_proving_kind) *)
let sleek_proving_id = ref (0 : int)

(* let current_hprel_ass = ref ([] : CF.hprel list) *)
let current_infer_rel_stk : CP.infer_rel_type Gen.stack_pr = new Gen.stack_pr 
  CP.string_of_infer_rel (==)

let current_hprel_ass_stk : CF.hprel  Gen.stack_pr 
      = new Gen.stack_pr Cprinter.string_of_hprel_short (==) 


let get_sleek_proving_id ()=
  let r = !sleek_proving_id in
  let _ = Globals.add_count sleek_proving_id in
  r

let proof_log_list  = ref [] (*For printing to text file with the original oder of proof execution*)

let proof_gt5_log_list = ref [] (*Logging proofs require more than 5 secs to be proved*)

(* let update_sleek_proving_kind k= let _ = sleek_proving_kind:= k in () *)

(* TODO : add result into the log printing *)
(* wrong order number indicates recursive invocations *)
let add_new_sleek_logging_entry classic_flag caller avoid hec slk_no ante conseq 
      consumed_heap evars (result:CF.list_context) pos=
  if !Globals.sleek_logging_txt then
    let sleek_log_entry = {
        (* sleek_proving_id = get_sleek_proving_id (); *)
        sleek_proving_id = slk_no;
        sleek_proving_caller = caller;
        sleek_proving_avoid = avoid;
        sleek_proving_classic_flag = classic_flag;
        sleek_proving_hec = hec;
        sleek_proving_pos = pos;
        sleek_proving_kind = proving_kind # string_of;
(* !sleek_proving_kind; *)
        sleek_proving_ante = ante;
        sleek_proving_conseq = conseq;
        sleek_proving_hprel_ass = current_hprel_ass_stk # get_stk;
        sleek_proving_rel_ass = current_infer_rel_stk # get_stk;
        sleek_proving_c_heap = consumed_heap;
        sleek_proving_evars = evars;
        sleek_proving_res = result;
    }
    in
    let _ = sleek_log_stk # push sleek_log_entry in
    (if not(avoid) then 
      begin
        current_hprel_ass_stk # reset; 
        current_infer_rel_stk # reset
      end)
        ; ()
  else ()

let find_bool_proof_res pno =
	try 
		let log = Hashtbl.find proof_log_tbl pno in
		match log.log_res with
		| BOOL r -> r
		| _ -> report_error no_pos "Fatal error with Proof Logging: Unexpected result."
	with _ -> report_error no_pos "Fatal error with Proof Logging. Do remember to enable proof logging before using LOG."

let find_formula_proof_res pno =
	try 
		let log = Hashtbl.find proof_log_tbl pno in
		match log.log_res with
		| FORMULA r -> r
		| _ -> report_error no_pos "Fatal error with Proof Logging: Unexpected result."
	with _ -> report_error no_pos "Fatal error with Proof Logging. Do remember to enable proof logging before using LOG."	
			
let proof_log_to_file () = 
	let out_chn = 
		(try Unix.mkdir "logs" 0o750 with _ -> ());
		open_out ("logs/proof_log_" ^ (Globals.norm_file_name (List.hd !Globals.source_files))) in
	 output_value out_chn proof_log_tbl 
	
let file_to_proof_log () =
	try 
		let in_chn = open_in ("logs/proof_log_" ^ (Globals.norm_file_name (List.hd !Globals.source_files))) in
		let tbl = input_value in_chn in
		Hashtbl.iter (fun k log -> Hashtbl.add proof_log_tbl k log) tbl
	with _ -> report_error no_pos "File of proof logging cannot be opened."

(* let log_append_properties (ls: string ) = (\*For append more properties to log, currently not used*\) *)
(* 	try *)
(* 	 let tl= List.nth !proof_log_list ((List.length !proof_log_list) -1) in *)
(* 	 let tlog=Hashtbl.find proof_log_tbl tl in *)
(* 	 let _= tlog.log_other_properties <- tlog.log_other_properties @ [ls] in *)
(* 	 print_endline (ls) *)
(*   with _-> () *)
	
(*TO DO: check unique pno??*)
let add_proof_log (cache_status:bool) old_no pno tp ptype time res =
  if !Globals.proof_logging || !Globals.proof_logging_txt then
	(* let _= print_endline ("loging :"^pno^" "^proving_info () ^"\n"^trace_info ()) in *)
	let tstartlog = Gen.Profiling.get_time () in
	let plog = {
		log_id = pno;
		log_other_properties = [proving_info ()]@[trace_info ()];
		(* log_old_id = old_no; *)
		log_prover = tp;
		log_type = Some ptype;
		log_time = time;
		log_cache = cache_status;
		log_res = res; } in
	let _=Hashtbl.add proof_log_tbl pno plog in
	let _=try
	  let _= BatString.find (Sys.argv.(0)) "hip" in
	  if(!Globals.proof_logging_txt && ((proving_kind # string_of)<>"TRANS_PROC")) then
		begin 
		  proof_log_list := !proof_log_list @ [pno];
		end		
	with _->
		if(!Globals.proof_logging_txt) then
		  try
			let temp=(proving_kind # string_of) in
			let _ =
              if !Globals.log_filter
              then BatString.find temp "SLEEK_ENT"
              else 0 in
			begin 
			  proof_log_list := !proof_log_list @ [pno];
			end		 	
		  with _->()	
	in
	let tstoplog = Gen.Profiling.get_time () in
	let _= Globals.proof_logging_time := !Globals.proof_logging_time +. (tstoplog -. tstartlog) in ()
	                                                                                                   (* let _=print_endline ("log time: "^(string_of_float (tstoplog))^" and "^(string_of_float (tstartlog))) in ()	  *)
  else ()
					
let proof_log_to_text_file (src_files) =
  if !Globals.proof_logging_txt then
    let tstartlog = Gen.Profiling.get_time () in
    let oc = 
      (try Unix.mkdir "logs" 0o750 with _ -> ());
      let with_option = if !Globals.en_slc_ps then "eps" else "no_eps" in
      open_out ("logs/"^with_option^"_proof_log_" ^ (Globals.norm_file_name (List.hd src_files)) ^".txt") in
    let string_of_log_type lt =
      match lt with
	|IMPLY (ante, conseq) -> "Imply: ante:" ^(string_of_pure_formula ante) ^"\n\t     conseq: " ^(string_of_pure_formula conseq)
    	|SAT f-> "Sat: "^(string_of_pure_formula f) 
    	|SIMPLIFY f -> "Simplify: "^(string_of_pure_formula f)
    in
    let helper log=
      "\n--------------\n"^
	  List.fold_left (fun a c->a^c) "" log.log_other_properties^
	  (* "\nid: "^log.log_id^ *)
      "\nProver: "^
      (if log.log_cache then "CACHED" else log.log_prover)^
      "\nType: "^(match log.log_type with | Some x-> string_of_log_type x | None -> "????")^
      (* "\nTime: "^(string_of_float(log.log_time))^ *)
      "\nResult: "^(match log.log_res with
	    |BOOL b -> string_of_bool b
	    |FORMULA f -> string_of_pure_formula f)^"\n" in
    let _= List.map (fun ix->let log=Hashtbl.find proof_log_tbl ix in
    let _=fprintf oc "%s" (helper log) in ()) !proof_log_list in
    let tstoplog = Gen.Profiling.get_time () in
    let _= Globals.proof_logging_time := !Globals.proof_logging_time +. (tstoplog -. tstartlog) in 
    close_out oc;
  else ()	

let z3_proofs_list_to_file (src_files) =
	if !Globals.proof_logging_txt then
		let tstartlog = Gen.Profiling.get_time () in
		let oc = 
		(try Unix.mkdir "logs" 0o750 with _ -> ());
		(* let with_option= if(!Globals.do_slicing) then "slice" else "noslice" in *)
		let with_option = if(!Globals.en_slc_ps) then "eps" else "no_eps" in
		let with_option= with_option^"_"^if(!Globals.split_rhs_flag) then "rhs" else "norhs" in
    let with_option= with_option^"_"^if(not !Globals.elim_exists_ff) then "noee" else "ee" in
		open_out ("logs/"^with_option^"_"^(Globals.norm_file_name (List.hd src_files)) ^".z3") in
		let _= List.map (fun ix-> let _=fprintf oc "%s" ix in ()) !z3_proof_log_list in
		let tstoplog = Gen.Profiling.get_time () in
	  let _= Globals.proof_logging_time := !Globals.proof_logging_time +. (tstoplog -. tstartlog) in 
		close_out oc;
	else ()	

let proof_greater_5secs_to_file (src_files) =
	if !Globals.proof_logging_txt then
		let tstartlog = Gen.Profiling.get_time () in
		let oc = 
		(try Unix.mkdir "logs" 0o750 with _ -> ());
		(* let with_option= if(!Globals.do_slicing) then "slice" else "noslice" in *)
		let with_option = if(!Globals.en_slc_ps) then "eps" else "no_eps" in
		let with_option= with_option^"_"^if(!Globals.split_rhs_flag) then "rhs" else "norhs" in
    let with_option= with_option^"_"^if(not !Globals.elim_exists_ff) then "noee" else "ee" in
		open_out ("logs/greater_5sec_"^with_option^"_"^(Globals.norm_file_name (List.hd src_files)) ^".log5") in
		let _= List.map (fun ix-> let _=fprintf oc "%s" ix in ()) !proof_gt5_log_list in
		let tstoplog = Gen.Profiling.get_time () in
	  let _= Globals.proof_logging_time := !Globals.proof_logging_time +. (tstoplog -. tstartlog) in 
		close_out oc;
	else ()	

let wrap_calculate_time exec_func src_file args =
  (* if !Globals.proof_logging_txt then  *)
	  let _= sleek_counter := !sleek_counter +1 in
		let tstartlog = Gen.Profiling.get_time () in
    let _ = exec_func args in
		let tstoplog = Gen.Profiling.get_time () in 
		let period = (tstoplog -. tstartlog) in
	  if (period> 0.7) then
			proof_gt5_log_list :=  
			(!proof_gt5_log_list@[(Globals.norm_file_name (List.hd src_file))^"-check-entail-num-"^string_of_int !sleek_counter^"--Time--"^string_of_float (period)^"\n"])
  (* else exec_func args *)
	
(* let sleek_z3_proofs_list_to_file source_files =                                                    *)
(* 	if !Globals.proof_logging_txt then                                                               *)
(* 		let tstartlog = Gen.Profiling.get_time () in                                                   *)
(* 		let oc =                                                                                       *)
(* 		(try Unix.mkdir "logs" 0o750 with _ -> ());                                                    *)
(* 		let with_option= if(!Globals.do_slicing) then "sleek_slice" else "sleek_noslice" in            *)
(* 		(* let with_option= with_option^"_"^if(!Globals.split_rhs_flag) then "rhs" else "norhs" in *)  *)
(* 		open_out ("logs/"^with_option^(Globals.norm_file_name (List.hd source_files)) ^".z3") in       *)
(* 		let _= List.map (fun ix-> let _=fprintf oc "%s" ix in ()) !z3_proof_log_list in                *)
(* 		let tstoplog = Gen.Profiling.get_time () in                                                    *)
(* 	  let _= Globals.proof_logging_time := !Globals.proof_logging_time +. (tstoplog -. tstartlog) in *)
(* 		close_out oc;                                                                                  *)
(* 	else ()                                                                                          *)

let sleek_log_to_text_file (src_files) =
    (* let tstartlog = Gen.Profiling.get_time () in *)
    let oc =
      (try Unix.mkdir "logs" 0o750 with _ -> ());
      (* let with_option = if !Globals.en_slc_ps then "eps" else "no_eps" in *)
      open_out ("logs/sleek_log_" ^ (Globals.norm_file_name (List.hd src_files)) ^".txt")
    in
    let str = 
      if (!Globals.sleek_log_filter)
        then sleek_log_stk # string_of_reverse_log_filter 
        else sleek_log_stk # string_of_reverse_log
    in
    let _=fprintf oc "%s" str in
    (* let tstoplog = Gen.Profiling.get_time () in *)
    (* let _= Globals.proof_logging_time := !Globals.proof_logging_time +. (tstoplog -. tstartlog) in  *)
    close_out oc


let process_proof_logging ()=
  if !Globals.proof_logging || !Globals.proof_logging_txt || !Globals.sleek_logging_txt then 
      begin
        let tstartlog = Gen.Profiling.get_time () in
        let _= proof_log_to_file () in
        let with_option = if(!Globals.en_slc_ps) then "eps" else "no_eps" in
        let fname = "logs/"^with_option^"_proof_log_" ^ (Globals.norm_file_name (List.hd !Globals.source_files)) ^".txt"  in
        let fz3name= ("logs/"^with_option^"_z3_proof_log_"^ (Globals.norm_file_name (List.hd !Globals.source_files)) ^".txt") in
        let slfn = "logs/sleek_log_" ^ (Globals.norm_file_name (List.hd !Globals.source_files)) ^".txt" in
        let _= if (!Globals.proof_logging_txt) 
        then 
          begin
            Debug.info_pprint ("Logging "^fname^"\n") no_pos;
            Debug.info_pprint ("Logging "^fz3name^"\n") no_pos;
            proof_log_to_text_file !Globals.source_files;
            z3_proofs_list_to_file !Globals.source_files
          end
        else try Sys.remove fname 
          (* ("logs/proof_log_" ^ (Globals.norm_file_name (List.hd !Globals.source_files))^".txt") *)
        with _ -> ()
        in
        let _= if (!Globals.sleek_logging_txt) 
        then 
          begin
            Debug.info_pprint ("Logging "^slfn^"\n") no_pos;
            sleek_log_to_text_file !Globals.source_files;
          end
        else try Sys.remove slfn 
          (* ("logs/proof_log_" ^ (Globals.norm_file_name (List.hd !Globals.source_files))^".txt") *)
        with _ -> ()
        in
        let tstoplog = Gen.Profiling.get_time () in
        let _= Globals.proof_logging_time := !Globals.proof_logging_time +. (tstoplog -. tstartlog) in ()
        (* let _=print_endline ("Time for logging: "^(string_of_float (!Globals.proof_logging_time))) in    () *)
      end
  else ()




(* let add_sleek_log_entry e= *)
(*   if !Globals.sleek_logging_txt then *)
(*     sleek_log_stk # push e *)
(*   else () *)



(* let process_sleek_logging ()= *)
(*   if !Globals.sleek_logging_txt then *)
(*     (\* let _ = print_endline "" in *\) *)
(*     (\* let _ = print_endline "*************************************" in *\) *)
(*     (\* let _ = print_endline "*******sleek logging ********" in *\) *)
(*     (\* let _ = print_endline "*************************************" in *\) *)
(*     (\* let _ = print_endline (sleek_log_stk # string_of) in *\) *)
(*     (\* let _ = print_endline "*************************************" in () *\) *)
(*     let _ = sleek_log_to_text_file !Globals.source_files in *)
(*     () *)
(*   else *)
(*     () *)
