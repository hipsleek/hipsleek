open Globals
open Sleekcommons

module I = Iast
module IF = Iformula
module IP = Ipure

(*
let get_command (input : string) : (string * string) =
  let start_idx = ref 0 in
  let len = String.length input in
  let _ = 
	while (!start_idx < len) && ((String.get input !start_idx) = ' ') do
	  start_idx := !start_idx + 1
	done in
  let end_idx = ref !start_idx in
  let _ = 
	while (!end_idx < len) && ((String.get input !end_idx) != ' ') do
	  end_idx := !end_idx + 1
	done in
  let cmd = String.sub input !start_idx (!end_idx - !start_idx) in
  let dat = String.sub input !end_idx (len - !end_idx) in
	(cmd, dat)

let parse (input : string) : command =
  let cmd, dat = get_command input in
  let inlex = Lexing.from_string dat in
	match cmd with
	  | "data" ->
		  let ddef = Sparser.data_decl (Slexer.tokenizer "interactive") inlex in
			DataDef ddef
	  | "pred" ->
		  let pdef = Sparser.view_decl (Slexer.tokenizer "interactive") inlex in
			PredDef pdef
	  | "lemma" ->
		  let ldef = Sparser.coercion_decl (Slexer.tokenizer "interactive") inlex in
			LemmaDef ldef
	  | "checkentail" ->
		  let [a_str; c_str] = Util.split_by "|-" dat in
		  let a_lex = Lexing.from_string a_str in
		  let c_lex = Lexing.from_string c_str in
		  let a_f = Sparser.constr (Slexer.tokenizer "interactive") a_lex in
		  let c_f = Sparser.constr (Slexer.tokenizer "interactive") c_lex in
			EntailCheck (a_f, c_f)
	  | "print" ->
		  Print (Util.trim_str dat)
	  | _ -> failwith ("Unsupported command: " ^ cmd)
*)

let parse (input : string) : command =
  let inlex = Lexing.from_string input in
  let cmd = Sparser.command (Slexer.tokenizer "interactive") inlex in
	cmd
let list_parse (input_file) : command list =
  let org_in_chnl = open_in input_file in
  let inlex = Lexing.from_channel org_in_chnl in
  let cmd = Sparser.opt_command_list (Slexer.tokenizer "interactive") inlex in
	cmd