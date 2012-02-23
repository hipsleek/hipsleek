(**
 * Program entry point for integer theorem prover.
 * @author Vu An Hoa
 *)

open Zlogic

let usage = "zeta (source files)+"
	
let input_files = ref ([] : string list)

let add_source_file src =
	input_files := List.append !input_files [src]

let parse_file file_name = 
	let input_channel = open_in file_name in
	try
		(*print_endline ("Parsing " ^ file_name ^ " ...\n");*)
		let defs = Zparser.parse file_name (Stream.of_channel input_channel) in
		close_in input_channel;
		defs
	with End_of_file -> exit 0
	
let string_of_file fname =
	let chn = open_in fname in
	let len = in_channel_length chn in
	let str = String.make len ' ' in
	let _ = really_input chn str 0 len in
		(close_in chn; str)

let main () =
	let _ = Arg.parse [] add_source_file usage in
	let _ = Z3.toggle_warning_messages false in
	let _ = print_endline ("Source files : {" ^ (String.concat ", " !input_files) ^ "}") in
	let defs = List.map parse_file !input_files in
	let output = List.map process_definitions defs in
	let output = List.flatten output in
	let html_template = string_of_file "template.html" in
	let outrexp = Str.regexp_string "$OUTPUT_CONTENT$" in
	let output = Str.global_replace outrexp (String.concat "" output) html_template in
	let chn = open_out "zeta.html" in
		output_string chn output
	
let _ = main ()