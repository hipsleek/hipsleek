let source_file = ref ""
let n_exec = ref 1
let num_vars_test = ref 0
let nums_of_check_sat = ref 0

let use_boogie = ref false
let run_boogie = ref false

let use_frama_c = ref false

let set_number_exec si=
    n_exec :=  (int_of_string si)

let set_do_generate_test num=
	  num_vars_test := (int_of_string num)	

	