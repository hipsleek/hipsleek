open Hipsleek_common

(* Used as placeholder for pos since no file is parsed *)
let no_pos : VarGen.loc =
  let no_pos1 = { Lexing.pos_fname = "";
                  Lexing.pos_lnum = 0;
                  Lexing.pos_bol = 0; 
                  Lexing.pos_cnum = 0 } in
  {VarGen.start_pos = no_pos1; VarGen.mid_pos = no_pos1; VarGen.end_pos = no_pos1;}

let check_anon var_name f = 
  match var_name with 
  | "_" -> ("Anon" ^ Globals.fresh_trailer ())
  | "" -> raise (Invalid_argument (f ^ ": name is empty"))
  | _ -> var_name

(* Check whether is a variable primed by variable name *)
(* Might need error handling if var has len 0*)
let check_prime var_name =
  let len = String.length var_name in
  let last = String.get var_name (len - 1) in
  match last with
  | '\'' -> VarGen.Primed
  | _ -> VarGen.Unprimed

(* Returns the truncated variable if variable is primed*)
(* Might also need error handling if var has len 0*)
let truncate_var var_name primed = 
  match primed with 
  | VarGen.Primed -> String.sub var_name 0 ((String.length var_name) - 1)
  | VarGen.Unprimed -> var_name
