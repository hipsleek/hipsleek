#include "xdebug.cppo"
open VarGen
open Globals
open Sleekcommons

module I = Iast
module IF = Iformula
module IP = Ipure

(*
let get_command (input : string) : (string * string) =
  let start_idx = ref 0 in
  let len = String.length input in
  let () = 
	while (!start_idx < len) && ((String.get input !start_idx) = ' ') do
	  start_idx := !start_idx + 1
	done in
  let end_idx = ref !start_idx in
  let () = 
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
		  let [a_str; c_str] = Gen.split_by "|-" dat in
		  let a_lex = Lexing.from_string a_str in
		  let c_lex = Lexing.from_string c_str in
		  let a_f = Sparser.constr (Slexer.tokenizer "interactive") a_lex in
		  let c_f = Sparser.constr (Slexer.tokenizer "interactive") c_lex in
			EntailCheck (a_f, c_f)
	  | "print" ->
		  Print (Gen.trim_str dat)
	  | _ -> failwith ("Unsupported command: " ^ cmd)
*)

let parse_slk (input : string) : command =  Parser.parse_sleek_int "sleek string" input

(* let parse (input : string) : command =   *)
(*   Debug.loop_1_no "parse" (fun x -> x) (fun _ -> "?") parse input *)

let list_parse (input_file) : command list =
  let org_in_chnl = open_in input_file in
  Globals.input_file_name:= input_file;
  let cmd = Parser.parse_sleek input_file (Stream.of_channel org_in_chnl) in
  close_in org_in_chnl;
	cmd

(* let list_parse (input_file) : command list = *)
(*   Debug.loop_1_no "list_parse" (fun _ -> "?") (fun _ -> "?") list_parse input_file *)
