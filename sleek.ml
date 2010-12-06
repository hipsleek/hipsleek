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

let usage_msg = Sys.argv.(0) ^ " [options] <source files>"

let source_files = ref ([] : string list)

let set_source_file arg = 
  source_files := arg :: !source_files

let print_version () =
  print_string ("SLEEK: A Separation Logic Entailment Checker");
  print_string ("Prototype version.");
  (*  print_string ("Copyright (C) 2005-2007 by Nguyen Huu Hai, Singapore-MIT Alliance."); *)
  print_string ("THIS SOFTWARE IS PROVIDED AS-IS, WITHOUT ANY WARRANTIES.")

let process_cmd_line () = Arg.parse Scriptarguments.sleek_arguments set_source_file usage_msg

let inter = Scriptarguments.inter

let prompt = ref "SLEEK> "
let terminator = '.'

let parse_file (parse) (source_file : string) =
	try
		let cmd = parse source_file in 
		let _ = (List.map (fun c -> (
							match c with
								 | DataDef ddef -> process_data_def ddef
								 | PredDef pdef -> process_pred_def pdef
								 | EntailCheck (iante, iconseq) -> process_entail_check iante iconseq
								 | CaptureResidue lvar -> process_capture_residue lvar
								 | LemmaDef ldef -> process_lemma ldef
								 | PrintCmd pcmd -> process_print_command pcmd
								 | LetDef (lvar, lbody) -> put_var lvar lbody
                 | Time (b,s,_) -> if b then Util.push_time s else Util.pop_time s
								 | EmptyCmd -> ())) cmd) in ()
	with
	  | End_of_file ->
		  print_string ("\n")


let main () = 
  let iprog = { I.prog_data_decls = [iobj_def];
                I.prog_global_var_decls = [];
                I.prog_enum_decls = [];
                I.prog_view_decls = [];
                I.prog_proc_decls = [];
                I.prog_coercion_decls = [] } in
  let _ = Iast.build_exc_hierarchy true iprog in
  let _ = Util.c_h () in
  let quit = ref false in
  let parse =
    match !Scriptarguments.fe with
      | Scriptarguments.NativeFE -> NF.parse
      | Scriptarguments.XmlFE -> XF.parse in
  let buffer = Buffer.create 10240 in
    try
      if (!inter) then 
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
                  (match cmd with
                     | DataDef ddef -> process_data_def ddef
                     | PredDef pdef -> process_pred_def pdef
                     | EntailCheck (iante, iconseq) -> process_entail_check iante iconseq
                     | CaptureResidue lvar -> process_capture_residue lvar
                     | LemmaDef ldef -> process_lemma ldef
                     | PrintCmd pcmd -> process_print_command pcmd
                     | LetDef (lvar, lbody) -> put_var lvar lbody
                     | Time (b,s,_) -> if b then Util.push_time s else Util.pop_time s
                     | EmptyCmd -> ());
                  Buffer.clear buffer;
                  if !inter then
                      prompt := "SLEEK> "
                with
                  | _ -> dummy_exception();
                print_string ("Error.\n");
                Buffer.clear buffer;
                if !inter then prompt := "SLEEK> "
              with 
                | SLEEK_Exception
                | Not_found -> dummy_exception();
              Buffer.add_string buffer input;
              Buffer.add_char buffer '\n';
              if !inter then prompt := "- "
        done
      else 
        let _ = List.map (parse_file NF.list_parse) !source_files in ()
    with
      | End_of_file -> print_string ("\n")

let _ = 
  wrap_exists_implicit_explicit := false ;
  process_cmd_line ();
  if !Scriptarguments.print_version_flag then begin
	print_version ()
  end else
    (Tpdispatcher.start_prover ();
    Util.push_time "Overall";
    main ();
    Util.pop_time "Overall";
    let _ = 
      if (!Globals.profiling && not !inter) then 
        ( Util.print_profiling_info (); print_string (Util.string_of_counters ())) in
    Tpdispatcher.stop_prover ())