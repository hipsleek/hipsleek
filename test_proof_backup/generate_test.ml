open Printf

let vn = "x" (*define variable name*)
let bn = "b" (*define boolean variable name*)
	
let helper1 num_vars=
	let i = ref 0 in
		let str = ref "" in
		let _= 
      		while !i < num_vars-1; do
      			str := !str^"ref int "^vn^(string_of_int !i)^",";
      			i := !i+1 
      		done;
      			str := !str^"ref int "^vn^(string_of_int !i)
    in	!str 

let helper2 num_vars=
	let i = ref 0 in
		let str = ref "" in
		let _= 
      		while !i < num_vars-1; do
      			str := !str^vn^(string_of_int !i)^">2 & ";
      			i := !i+1 
      		done;
        		str := !str^vn^(string_of_int !i)^">2"
    in	!str 

let helper_ensures num_vars=
	let i = ref 0 in
		let str = ref "" in
		let add_num= if (num_vars mod 2 = 0 ) then "2" else "3" in
		let vnt i = vn^(string_of_int i) in
		let _= 
      		while !i < num_vars-1; do
      			str := !str^(vnt !i)^"'"^"= "^(vnt !i)^"+"^add_num^" & ";
      			i := !i+1 
      		done;
        	str := !str^(vnt !i)^"'"^"= "^(vnt !i)^"+"^add_num^";";
    in	!str	

let num_tabs k= 
	let i = ref 0 in
		let str = ref "" in
		let _= 
      		while !i < k; do
      			str := !str^"\t";
						i := !i+1
      		done;
    in	!str	
		
let helper_body1 num_vars alg num add_num=
	let i = ref 0 in
		let str = ref "" in
		let _= 
      		while !i < num_vars; do
      			str := !str^(num_tabs num)^vn^(string_of_int !i)^"= "^vn^(string_of_int !i)^alg^add_num^";\n";
      			i := !i+1 
      		done;
    in	!str	

let helper_body2 num_vars=
	let i = ref 0 in
		let str = ref "" in
		let gt_num = "4" in
		let _= 
      		while !i < num_vars; do
      			str := !str^"\t"^"bool "^bn^(string_of_int !i)^"= "^vn^(string_of_int !i)^">"^gt_num^";\n";
      			i := !i+1 
      		done;
    in	!str	

let helper_body3 num_vars=
	let i = ref 0 in
	let j = ref 0 in
		let str = ref "" in
		let alg= ref "" in
		let _= 
      		while !i < num_vars; do
            str := !str^"\t"^"if ("^bn^(string_of_int !i)^")\n\t"^"{\n";
						if(!i mod 2 = 0) then alg := "+" else alg := "-";							
      			str := !str^(helper_body1 num_vars !alg 2 "1");
      			i := !i+1 
      		done;
					while !j < num_vars; do				
      			str := !str^"\t}\n";
					  j := !j+1 
						done;
    in	!str	

let helper_body_if_else num_vars=
  let i = ref 0 in
		let str = ref "" in
		let alg= ref "" in
		let _= 
      		while !i < num_vars; do
            str := !str^"\t"^"if ("^bn^(string_of_int !i)^")\n\t"^"{\n";
						if(!i mod 2 = 0) then alg := "+" else alg := "-";							
      			str := !str^(helper_body1 num_vars !alg 2 "1");
      			i := !i+1 
      		done;
					i := 0;
					while !i < num_vars; do				
      			str := !str^"\t}"^"else {\n";
						if(!i mod 2 = 0) then alg := "+" else alg := "-";							
      			str := !str^(helper_body1 num_vars !alg 2 "2");
					  str := !str^"\t"^"}\n";
      			i := !i+1 
					done;
    in	!str	
																																																																																																																																							
let construct_string num_vars =
  let declare_args = helper1 num_vars	in	
  let declare_fun = "void spring ("^declare_args^")\n" in (*1*)
	let declare_requires = "requires "^helper2 num_vars^"\n" in (*2*)
	let declare_ensures = "ensures "^helper_ensures num_vars^"\n{\n" in (*3*)
	let temp= helper_body1 num_vars "+" 1 "1" in
	let declare_body1= temp^temp in
	let declare_body2=helper_body2 num_vars in
	if(not !Globals.with_else) then
	  let declare_body3 = helper_body3 num_vars in 
		declare_fun^declare_requires^declare_ensures^declare_body1^declare_body2^declare_body3^"}" 
	else
		let declare_body3 = helper_body_if_else num_vars in 
	  declare_fun^declare_requires^declare_ensures^declare_body1^declare_body2^declare_body3^"}"  

let generate_test num_vars =	 
	if (num_vars >= 2) then
		(* let _=print_endline (construct_string num_vars) in *)
		let oc =
		(try Unix.mkdir "spring" 0o750 with _ -> ());
		let with_option= string_of_int num_vars in
		let with_else_op = if(!Globals.with_else) then "if-else" else "if" in 
		open_out ("spring/"^with_else_op^"/spring-"^with_else_op^"-"^with_option^".ss") in
		let _= fprintf oc "%s" (construct_string num_vars) in
		close_out oc
	else 
		print_endline ("Should provide a number >= 2")