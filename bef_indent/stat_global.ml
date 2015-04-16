#include "xdebug.cppo"
open Globals
open VarGen
open Gen.Basic
open Cprinter

module CF=Cformula

let string_of_path_trace x = pr_list (pr_pair (fun x->match x with (a,b)->"c_id:"^(string_of_int a)^":"^b) (fun x -> "p_label: "^string_of_int x)) x
let return_exp_loc = ref ""
let wr_tr = ref 0
let wr_stk : string Stack.t = Stack.create ()
let print_wrap_num =ref false (*For debugging wrap_trace: wrap's scope*)

class es_trace =
object
  inherit [path_trace] store [] (string_of_path_trace)
     (* method string_of_string : string = match lc with *)
     (*   | None -> "None"                               *)
     (*   | Some l -> l                                  *)
end;;
	
let last_trace  = new es_trace

(*Functions for localizing the return exp being proved at POST*) 
let compare_control_path path_list id_strict =
	let eq_path_id pid1 pid2 = match pid1, pid2 with
    | Some (i1, s1), (i2,s2) -> i1 = i2
    | None , _-> false
  in
	List.find ( fun ex-> eq_path_id ex id_strict) path_list                                                                                

let string_of_loc_line_col (p : loc) = 
    Printf.sprintf "(Line:%d,Col:%d)"
    (* p.start_pos.Lexing.pos_fname  *)
    p.start_pos.Lexing.pos_lnum
	 (p.start_pos.Lexing.pos_cnum-p.start_pos.Lexing.pos_bol)
					 		
let loc_of_return_exp (pid: control_path_id): string=
  let eq_path_id pid1 pid2 = match pid1, pid2 with
    | Some _, None -> false
    | None, Some _ -> false
    | None, None -> true
    | Some (i1, s1), Some (i2, s2) -> i1 = i2
  in
  let find_loc pid =
    let _, _, _, loc = List.find (fun (id, _, _ , _) -> eq_path_id pid id) !iast_label_table in
    loc
  in
		let p=(find_loc pid) in
		let _=proving_loc #set p in
   (string_of_loc_line_col  p)

let log_return_exp_loc (pt : path_trace) =
	let ret_loc = ref "" in
	let _ =List.map (fun ((id_strict),_)-> 
			try
			let r=compare_control_path !Globals.return_exp_pid id_strict in
			ret_loc := loc_of_return_exp r
			with Not_found -> ()
			) pt
	in
	if(!ret_loc<>"") then
		"--Return exp at: " ^ !ret_loc
		else ""(*"not found?"*) 
(*End return exp localizing*)

(*Set the trace info *)
let wrap_trace (tr : path_trace) exec_function args =
	(* let _= if(!print_wrap_num) then                                    *)
	(* 	begin                                                             *)
	(*   wr_tr := !wr_tr+1;                                               *)
	(*   print_endline ("*wrap_trace "^string_of_int !wr_tr^"*");         *)
	(*   Stack.push ("*end_wrap_trace "^string_of_int !wr_tr^"*") wr_stk  *)
	(* 	end                                                               *)
	(* in                                                                 *)
	if(!Globals.proof_logging_txt) then
     let b = last_trace # is_avail in
     let m = last_trace # get in
	   let _= return_exp_loc := log_return_exp_loc tr in
     let () = last_trace # set tr in 
     let res = exec_function args in
     let _= if b then last_trace # set m 
     else last_trace # reset
     (* while (not (Stack.is_empty wr_stk)) do  *)
		 (*   print_endline (Stack.pop wr_stk)      *)
	   (* done                                    *)
     in 
     res
	else
		 let res = exec_function args in res	

let rec wrap_trace_helper (ctx: CF.context) exec args=
	match ctx with
	| CF.OCtx (c1,c2)-> let _= wrap_trace_helper c1 exec args in wrap_trace_helper c2 exec args
	| CF.Ctx es-> wrap_trace es.CF.es_path_label exec args
		
let trace_info () = 
  if(last_trace # is_avail) then
        (!return_exp_loc^"\nTrace::"^(last_trace # string_of)^"\n")
  else "..."				
(*End trace info*)
