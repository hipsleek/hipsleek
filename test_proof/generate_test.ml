open Printf

let vn = "x" (*define variable name*)
let bn = "b" (*define boolean variable name*)
let l_ints = ref [] 
let gen_var crt_num primed = vn^(string_of_int crt_num)^(if primed then if !Globals.use_boogie then "" else "'" else if !Globals.use_boogie then "o" else "")

let gen_prog_var crt_num = vn^(string_of_int crt_num)
let gen_prog_bool crt_num = bn^(string_of_int crt_num)
		
let gen_header_typed_var crt_num primed = 
	if !Globals.use_boogie then gen_var crt_num primed ^":int" else ("ref int "^ gen_var crt_num primed)
	
let gen_typed_var_list num_vars primed=  String.concat "," (List.map (fun c-> gen_header_typed_var c primed) !l_ints) 
	
			
let gen_requires num_vars=
		let conj = if !Globals.use_boogie then " && " else " & " in
		let gen_one_constr crt_num = gen_var crt_num false ^">2" in
		String.concat conj (List.map gen_one_constr !l_ints)
		
let helper_ensures num_vars=
		let conj = if !Globals.use_boogie then " && " else " & " in
		let add_num= if (num_vars mod 2 = 0 ) then "2" else "3" in
		let gen_one_constr crt_num = (gen_var crt_num true)^"= "^(gen_var crt_num false)^"+"^add_num in 
		(String.concat conj (List.map gen_one_constr !l_ints))^";"
		
let boogie_var_inits num_vars = 
	let inits = String.concat "" (List.map (fun c-> (gen_prog_var c)^":= "^(gen_var c false)^";\n") !l_ints) in
	let v_decl = String.concat "" (List.map (fun c-> "var "^(gen_prog_bool c)^":bool;\n") !l_ints) in
	v_decl^inits
		
let num_tabs k= 
	let i = ref 0 in
		let str = ref "" in
		let _= 
      		while !i < k; do
      			str := !str^"\t";
						i := !i+1
      		done;
    in	!str	
		
let incs_decs num_vars alg num=
	let eqs = if !Globals.use_boogie then ":= " else "= " in
	let gen_const c = (num_tabs num)^(gen_prog_var c)^eqs^(gen_prog_var c)^alg^"1;\n" in
	String.concat "" (List.map gen_const !l_ints)
		
let bool_inits num_vars=
		let decl = if !Globals.use_boogie then "" else "bool " in
		let eqs = if !Globals.use_boogie then ":= " else "= " in
		let gen_const c = "\t"^decl^(gen_prog_bool c)^eqs^(gen_prog_var c)^">4;\n" in
		String.concat "" (List.map gen_const !l_ints)

let helper_body3 num_vars=
	let gen_const c = "\t if ("^(gen_prog_bool c)^")\n\t{\n"^(incs_decs num_vars (if(c mod 2 = 0) then "+" else "-") 2) in
	(String.concat "" (List.map gen_const !l_ints)) ^ (String.concat "" (List.map (fun _ -> "\t}\n") !l_ints))
							
let construct_string num_vars =
  let declare_args = gen_typed_var_list num_vars false in	
  let declare_fun = "void spring ("^declare_args^")\n" in (*1*)
	let declare_requires = "requires "^gen_requires num_vars^"\n" in (*2*)
	let declare_ensures = "ensures "^helper_ensures num_vars^"\n{\n" in (*3*)
	let temp= incs_decs num_vars "+" 1 in
	let declare_body1= temp^temp in
	let declare_body2=bool_inits num_vars in
	let declare_body3 = helper_body3 num_vars in
	declare_fun^declare_requires^declare_ensures^declare_body1^declare_body2^declare_body3^"}" 
	
let boogie_string num_vars = 
  let part_header = "spring("^(gen_typed_var_list num_vars false) ^") returns ("^(gen_typed_var_list num_vars true)^")" in
  let proc_header = "procedure "^part_header^";" in
  let func_header = "implementation "^part_header in
  let specs =  "requires "^gen_requires num_vars^";\nensures "^helper_ensures num_vars in
  let func_body = 
		let temp= incs_decs num_vars "+" 1 in
		"{"^ (boogie_var_inits num_vars) ^temp^temp^(bool_inits num_vars)^(helper_body3 num_vars) in
	proc_header^specs^func_header^func_body^"}" 
	
let construct_string_1 num_vars = if !Globals.use_boogie then boogie_string num_vars else construct_string num_vars

let generate_test num_vars =	 
	if (num_vars >= 2) then (
		l_ints:= (let rec f l i = if i>=0 then f (i::l) (i-1) else l in f [] (num_vars-1));
		let _=print_endline (construct_string_1 num_vars) in
		let oc =
		(try Unix.mkdir "spring" 0o750 with _ -> ());
		let with_option= string_of_int num_vars in
		open_out ("spring/spring-"^with_option^".ss") in
		let _= fprintf oc "%s" (construct_string_1 num_vars) in
		close_out oc)
	else 
		print_endline ("Should provide a number >= 2")