(**
 * Zeta theorem prover
 * Version 2.0
 *
 * @author Vu An Hoa
 *)

open Tree
open GList
open Domain
open Printing

module StringPrinter = Printer(StringBasePrinter)
module TexPrinter = Printer(TexBasePrinter)

(* Program entry *)

let print_help_msg = ref false

let print_version = ref false

let usage = "zeta (source files)+"
	
let input_files = ref ([] : string list)

let add_source_file src =
	input_files := List.append !input_files [src]

let parse_file file_name = 
	let input_channel = open_in file_name in
	try
		(*print_endline ("Parsing " ^ file_name ^ " ...\n");*)
		let ctx = Parser.parse file_name (Stream.of_channel input_channel) in
		close_in input_channel;
		ctx
	with End_of_file -> print_endline "End_of_file"; exit 0

(**
 * Read a file content to a string
 *)
let string_of_file fname =
	let chn = open_in fname in
	let len = in_channel_length chn in
	let str = String.make len ' ' in
	let _ = really_input chn str 0 len in
		(close_in chn; str)

let process_theory th =
	let th = Logic.process_theory th in
	(*StringPrinter.*)TexPrinter.print_theory th

(**
 * Command line options as in Arg.parse
 *)
let cmd_line_arg_speclist = [
	(* ("-z3inp", Arg.Set Zexprf.Z3.print_z3_input, "Print Z3 input generated."); *)
	("-h", Arg.Set print_help_msg, "Print the help message.");
	("-v", Arg.Set print_version, "Print zeta version.")]
	
let main () =
	let _ = Arg.parse cmd_line_arg_speclist add_source_file usage in
	let _ = Z3.toggle_warning_messages false in
	let _ = print_endline ("Source files : {" ^ (String.concat ", " !input_files) ^ "}") in
	let th = List.map parse_file !input_files in
	(*let _ = print_endline (string_of_int (List.length ctx)) in*)
	let th = List.hd th in
	let output = process_theory th in
	(*let _ = print_endline ((* "Content:\n" ^ *) output) in*)
	(*let defs = List.map parse_file !input_files in
	let output = List.map process_definitions defs in
	let output = List.flatten output in*)
	let html_template = string_of_file "template.html" in
	let outrexp = Str.regexp_string "$OUTPUT_CONTENT$" in
	let output = Str.global_replace outrexp ((*String.concat ""*) output) html_template in
	let chn = open_out "zeta.html" in
		output_string chn output
	
let _ = main ()