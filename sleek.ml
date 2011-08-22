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


let print_version () =
  print_string ("SLEEK: A Separation Logic Entailment Checker");
  print_string ("Prototype version.");
  (*  print_string ("Copyright (C) 2005-2007 by Nguyen Huu Hai, Singapore-MIT Alliance."); *)
  print_string ("THIS SOFTWARE IS PROVIDED AS-IS, WITHOUT ANY WARRANTIES.")

let prompt = ref "SLEEK> "
let terminator = '.'
module M = Lexer.Make(Token.Token)

let process_cmd_line () = Arg.parse Scriptarguments.sleek_arguments set_source_file usage_msg

let parse_file (parse) (source_file : string) =
	(* let _ = print_endline "parse_file 1" in *)
	try
		let cmds = parse source_file in 
		Sleekengine.process_cmds cmds
	with
	  | End_of_file ->
		  print_string ("\n")
    | M.Loc.Exc_located (l,t)-> 
      (print_string ((Camlp4.PreCast.Loc.to_string l)^"\n error: "^(Printexc.to_string t)^"\n at:"^(Printexc.get_backtrace ()));
      raise t)

let parse_file (parse) (source_file : string) =
	(* let _ = print_endline "parse_file 2" in *)
  let rec parse_first (cmds:command list) : (command list)  =
    try 
       parse source_file 
	with
	  | End_of_file -> List.rev cmds
      | M.Loc.Exc_located (l,t)-> 
            (print_string ((Camlp4.PreCast.Loc.to_string l)^"\n error: "^(Printexc.to_string t)^"\n at:"^(Printexc.get_backtrace ()));
            raise t) in
  let proc_one_def c = 
    match c with
	  | DataDef (ddef,_) -> process_data_def ddef
	  | PredDef (pdef,_) -> process_pred_def_4_iast pdef
      | RelDef (rdef,_) -> process_rel_def rdef
	  | LemmaDef _
	  | CaptureResidue _
	  | LetDef _
	  | EntailCheck _
	  | PrintCmd _ 
      | Time _
	  | EmptyCmd -> () in
  let proc_one_lemma c = 
    match c with
	  | LemmaDef (ldef,_) -> process_lemma ldef
	  | DataDef _
	  | PredDef _
      | RelDef _
	  | CaptureResidue _
	  | LetDef _
	  | EntailCheck _
	  | PrintCmd _ 
      | Time _
	  | EmptyCmd -> () in
  let proc_one_cmd c = 
    match c with
	  | EntailCheck (iante, iconseq,_) -> process_entail_check iante iconseq
	  | CaptureResidue (lvar,_) -> process_capture_residue lvar
	  | PrintCmd (pcmd,_) -> process_print_command pcmd
	  | LetDef (lvar, lbody,_) -> put_var lvar lbody
      | Time (b,s,_) -> 
            if b then Gen.Profiling.push_time s 
            else Gen.Profiling.pop_time s
	  | DataDef _
	  | PredDef _
      | RelDef _
	  | LemmaDef _
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
  convert_pred_to_cast ();
  List.iter proc_one_lemma cmds;
   List.iter proc_one_cmd cmds 


let main () =
  let _ = Sleekengine.main_init() in
  (* let _ = print_endline (Gen.ExcNumbering.string_of_exc_list (1)) in *)
  let quit = ref false in
  let parse x =
    match !Scriptarguments.fe with
      | Scriptarguments.NativeFE -> NF.parse x
      | Scriptarguments.XmlFE -> XF.parse x in
  (* let parse x = Gen.Debug.no_1 "parse" pr_id string_of_command parse x in *)
  let buffer = Buffer.create 10240 in
    try
        let inter =  !Scriptarguments.inter in
      if (inter) then 
        while not (!quit) do
          if inter then (* check for interactivity *)
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
                  (* let _ = print_endline ("xxx_after parse"^cts) in *)
                  (match cmd with
                     | DataDef (ddef,_) -> process_data_def ddef
                     | PredDef (pdef,_) -> process_pred_def pdef
                     | RelDef (rdef,_) -> process_rel_def rdef
                     | EntailCheck (iante, iconseq,_) -> process_entail_check iante iconseq
                     | CaptureResidue (lvar,_) -> process_capture_residue lvar
                     | LemmaDef (ldef,_) -> process_lemma ldef
                     | PrintCmd (pcmd,_) -> process_print_command pcmd
                     | LetDef (lvar, lbody,_) -> put_var lvar lbody
                     | Time (b,s,_) -> if b then Gen.Profiling.push_time s else Gen.Profiling.pop_time s
                     | EmptyCmd -> ());
                  Buffer.clear buffer;
                  if inter then
                      prompt := "SLEEK> "
                with
                  | _ -> dummy_exception();
                print_string ("Error.\n");
                Buffer.clear buffer;
                if inter then prompt := "SLEEK> "
              with
                | SLEEK_Exception
                | Not_found -> dummy_exception();
              Buffer.add_string buffer input;
              Buffer.add_char buffer '\n';
              if inter then prompt := "- "
        done
      else 
        let _ = List.map (parse_file NF.list_parse) !source_files in ()
    with
      | End_of_file -> print_string ("\n")

(* let main () =  *)
(*   Gen.Debug.loop_1_no "main" (fun () -> "?") (fun () -> "?") main () *)

let _ = 
  wrap_exists_implicit_explicit := false ;
  process_cmd_line ();
  if !Scriptarguments.print_version_flag then begin
	print_version ()
  end else
    (Tpdispatcher.start_prover ();
    Gen.Profiling.push_time "Overall";
    main ();
    Gen.Profiling.pop_time "Overall";
    let _ = 
      if (!Globals.profiling && not !Scriptarguments.inter) then 
        ( Gen.Profiling.print_info (); print_string (Gen.Profiling.string_of_counters ())) in
    Tpdispatcher.stop_prover ();
    print_string "\n")
