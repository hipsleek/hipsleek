open Globals
open Gen.Basic
open Cprinter

module CF=Cformula

let string_of_path_trace x = pr_list (pr_pair (fun x->match x with (a,b)->"c_id:"^(string_of_int a)^":"^b) (fun x -> "p_label: "^string_of_int x)) x
let return_exp_loc = ref ""

class es_trace =
object
  inherit [path_trace] store [] (string_of_path_trace)
     (* method string_of_string : string = match lc with *)
     (*   | None -> "None"                               *)
     (*   | Some l -> l                                  *)
end;;
	
let last_trace  = new es_trace
		

let compare_control_path path_list id_strict =
	let eq_path_id pid1 pid2 = match pid1, pid2 with
    | Some (i1, s1), (i2,s2) -> (*let _= print_endline (string_of_int i1^"compared"^string_of_int i2) in*) i1 = i2
  in
	List.find ( fun ex-> eq_path_id ex id_strict) path_list

(* let find_return_exps_paths_list =                                                                                                *)
(* 	if(List.length !iast_label_table >0) then                                                                                      *)
(* 	List.fold_left ( fun a (id, str, _ , _) ->                                                                                     *)
(* 		let _= print_endline ("Xuan bach") in if((String.compare str "return") = 0) then  a @ [id] else a @ []) [] !iast_label_table *)
(* 	else                                                                                                                           *)
(* 		let _= print_endline ("DCMR") in []	                                                                                        *)
	 		
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
   (string_of_list_loc  [find_loc pid])

let log_return_exp_loc (pt : path_trace) =
	let ret_loc = ref "" in
	(* let _= print_endline ("gohere: "^string_of_path_trace pt) in *)
	let _ =List.map (fun ((id_strict),_)-> 
			try
			(* let _= print_endline ("why?: ") in *)
			let r=compare_control_path !Globals.return_exp_pid id_strict in
			(* find_return_exps_paths_list *)
			ret_loc := loc_of_return_exp r
			with Not_found -> ()
			) pt
	in
	if(!ret_loc<>"") then
		"Return exp at: " ^ !ret_loc
		else ""(*"not found?"*) 

(*Set the trace info *)
let wrap_trace (tr : path_trace) exec_function args =
  let b = last_trace # is_avail in
  let m = last_trace # get in
	let _= return_exp_loc := log_return_exp_loc tr in
  let _ = last_trace # set tr in
  let res = exec_function args in
  let _ = 
    if b then last_trace # set m 
    else last_trace # reset in
  res
	
let trace_info () = 
  if(last_trace # is_avail) then
        ("Trace::"^(last_trace # string_of)^"\n"^ !return_exp_loc)
  else "..."				