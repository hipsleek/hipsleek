let source_file = ref ""
let n_exec = ref 1
let num_vars_test = ref 0
let nums_of_check_sat = ref 0
let with_else = ref false
let min = ref 0
let off_set = ref 0

let use_boogie = ref false
let run_boogie = ref false

let use_frama_c = ref false

let set_number_exec si=
    n_exec :=  (int_of_string si)

let set_generate_with_else si=
	let _= with_else := true in
	  num_vars_test := (int_of_string si)
		
let set_do_generate_test num=
	  num_vars_test := (int_of_string num)	

let set_generate_if_range ()= 	
	let _ = min := (int_of_string Sys.argv.(2))
	and _= num_vars_test := (int_of_string Sys.argv.(3))
	and _= off_set := (int_of_string Sys.argv.(4))
	in ()

let set_generate_if_else_range ()=
	let _= set_generate_if_range () in
	 with_else := true 	 			