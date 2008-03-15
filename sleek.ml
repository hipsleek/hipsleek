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

type front_end =
  | XmlFE
  | NativeFE

let fe = ref NativeFE

let set_frontend fe_str = match fe_str with
  | "native" -> fe := NativeFE
  | "xml" -> fe := XmlFE
  | _ -> failwith ("Unsupported frontend: " ^ fe_str)

let inter = ref false

let usage_msg = Sys.argv.(0) ^ " [options] <source files>"

let source_files = ref ([] : string list)

let set_source_file arg = 
  source_files := arg :: !source_files

let print_version_flag = ref false

let print_version () =
  print_string ("SLEEK: A Separation Logic Entailment Checker");
  print_string ("Prototype version.");
  (*  print_string ("Copyright (C) 2005-2007 by Nguyen Huu Hai, Singapore-MIT Alliance."); *)
  print_string ("THIS SOFTWARE IS PROVIDED AS-IS, WITHOUT ANY WARRANTIES.")

let process_cmd_line () = Arg.parse [
  ("-fe", Arg.Symbol (["native"; "xml"], set_frontend),
   "Choose frontend:\n\tnative: Native (default)\n\txml: XML");
  ("-int", Arg.Set inter,
   "Run in interactive mode.");
  ("-tp", Arg.Symbol (["cvcl"; "omega"; "co"; "isabelle"; "mona"; "om"; "oi"], Tpdispatcher.set_tp),
   "Choose theorem prover:\n\tcvcl: CVC Lite\n\tomega: Omega Calculator (default)\n\tco: CVC Lite then Omega\n\tisabelle: Isabelle\n\tmona: Mona\n\tom: Omega and Mona\n\toi: Omega and Isabelle");
  ("-v", Arg.Set print_version_flag,
   "Print version information");
  ("-version", Arg.Set print_version_flag,
   "Print version information");
  ("-dd", Arg.Set Debug.devel_debug_on,
   "Turn on devel_debug");
] set_source_file usage_msg

let prompt = ref "SLEEK> "
let terminator = '.'

let main () = 
  let quit = ref false in
  let parse =
	match !fe with
	  | NativeFE -> NF.parse
	  | XmlFE -> XF.parse in
  let buffer = Buffer.create 10240 in
	try
	  while not (!quit) do
		if !inter then (* check for interactivity *)
		  print_string !prompt;
		let input = read_line () in
		  match input with
			| "" -> ()
			| _ -> 
				try
				  let term_indx = String.index input terminator in
				  let s = String.sub input 0 term_indx in
					Buffer.add_string buffer s;
					let cts = Buffer.contents buffer in
					  if cts = "quit" || cts = "quit\n" then quit := true
					  else try
						let cmd = parse cts in
						  (match cmd with
							 | DataDef ddef -> process_data_def ddef
							 | PredDef pdef -> process_pred_def pdef
							 | EntailCheck (iante, iconseq) -> process_entail_check iante iconseq
							 | LemmaDef ldef -> process_lemma ldef
							 | PrintCmd pcmd -> process_print_command pcmd
							 | LetDef (lvar, lbody) -> put_var lvar lbody
							 | EmptyCmd -> ());
						  Buffer.clear buffer;
						  if !inter then
							prompt := "SLEEK> "
					  with
						| _ -> 
							print_string ("Error.\n");
							Buffer.clear buffer;
							if !inter then
							  prompt := "SLEEK> "
				with 
				  | SLEEK_Exception
				  | Not_found ->
					  Buffer.add_string buffer input;
					  Buffer.add_char buffer '\n';
					  if !inter then
						prompt := "- "
	  done
	with
	  | End_of_file ->
		  print_string ("\n")

let _ = 
  process_cmd_line ();
  if !print_version_flag then begin
	print_version ()
  end else
	main ()
