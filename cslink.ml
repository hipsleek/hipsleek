open Printf
open StdLabels
open GdkKeysyms
open Cast
open Globals
open Lexing
open Cformula


let get_proc_range (proc:proc_decl) = (proc.proc_loc.start_pos.pos_cnum, proc.proc_loc.end_pos.pos_cnum);;

let is_added_primitives (name:string) = (name = "add___$int~int") ||(name = "minus___$int~int") ||(name = "mult___$int~int") ||(name = "div___$int~int") ||(name = "mod___$int~int") ||(name = "eq___$int~int") ||(name = "eq___$bool~bool") ||(name = "neq___$int~int") ||(name = "neq___$bool~bool") ||(name = "lt___$int~int") ||(name = "lte___$int~int") ||(name = "gt___$int~int") ||(name = "gte___$int~int") ||(name = "land___$bool~bool") ||(name = "lor___$bool~bool") ||(name = "not___$bool") ||(name = "eq___$__Exc~__Exc") ||(name = "neq___$__Exc~__Exc") ||(name = "is_null___$__Exc") ||(name = "is_not_null___$__Exc") ||(name = "eq___$Object~Object") ||(name = "neq___$Object~Object") ||(name = "is_null___$Object") ||(name = "is_not_null___$Object") ||(name = "eq___$String~String") ||(name = "neq___$String~String") ||(name = "is_null___$String") ||(name = "is_not_null___$String")
  (** return procedure according to the offset*)
let rec look_up_proc_loc (procs : proc_decl list) (offset:int) = match procs with
  | p :: rest ->
      let loc = p.proc_loc in
      let start_p = loc.start_pos in
      let end_p = loc.end_pos in
      (*prerr_endline(sprintf "proc name:%s" p.proc_name);*)
      if (offset >= start_p.pos_cnum && offset <= end_p.pos_cnum && not (is_added_primitives p.proc_name)) then
		p
      else
		look_up_proc_loc rest offset
  | [] -> raise Not_found

(*given a loc, check whether the offset is within the range*)
let in_range (pos:Globals.loc) (offset:int) = 
      let start_p = pos.start_pos in
      let end_p = pos.end_pos in
      if (offset >= start_p.pos_cnum && offset <= end_p.pos_cnum) then true
      else false
;;

let in_next_exp (exp:Cast.exp) (offset:int) = match exp with 
  | Java ({exp_java_code = code}) ->false
  | CheckRef _ -> false
  | Assert ({exp_assert_asserted_formula = f1o; 
			 exp_assert_assumed_formula = f2o; 
			 exp_assert_pos = l;
			 exp_assert_label =  lbl;}) -> 
	  if (in_range l.pos offset) 
		then true
	  else false
  | Assign ({exp_assign_lhs = id; exp_assign_rhs = e; exp_assign_pos = l}) -> 
	  if (in_range l.pos offset) 
		then true
	  else false
  | BConst ({exp_bconst_val = b; exp_bconst_pos = l}) -> 
          if (in_range l.pos offset) 
		then true
	  else false
  | Bind ({exp_bind_type = _; 
	   exp_bind_bound_var = (_, id); 
	   exp_bind_fields = idl;
	   exp_bind_body = e;
	   exp_bind_pos = l}) -> 
	   if (in_range l.pos offset) 
		then true
	  else false
  | Block ({exp_block_type = _;
	    exp_block_body = e;
	    exp_block_local_vars = _;
	    exp_block_pos = l}) -> 
	  if (in_range l.pos offset) 
		then true
	  else false
  | ICall ({exp_icall_type = _;
	   exp_icall_receiver = r;
	   exp_icall_method_name = id;
	   exp_icall_arguments = idl;
	   exp_icall_visible_names = _;
	   exp_icall_pos = l}) -> 
	   if (in_range l.pos offset) 
		then true
	  else false
  | Cast ({exp_cast_target_type = t;
		   exp_cast_body = e; exp_cast_pos = l}) ->
 	  if (in_range l.pos offset) 
		then true
	  else false

  | Cond ({exp_cond_type = _;
	   exp_cond_condition = id;
	   exp_cond_then_arm = e1;
	   exp_cond_else_arm = e2;
	   exp_cond_pos = l;
	   exp_cond_id = br_id}) -> 
	  if (in_range l.pos offset) 
		then true
	  else false
  | Debug ({exp_debug_flag = b; exp_debug_pos = l}) -> if (in_range l.pos offset) 
		then true
	  else false
  | Dprint _                   -> false
  | FConst ({exp_fconst_val = f; exp_fconst_pos = l}) -> if (in_range l.pos offset) 
		then true
	  else false
  | IConst ({exp_iconst_val = i; exp_iconst_pos = l}) -> if (in_range l.pos offset) 
		then true
	  else false
  | New ({exp_new_class_name = id;
	  exp_new_arguments = idl;
	  exp_new_pos = l}) -> 
	  if (in_range l.pos offset) 
		then true
	  else false
  | Null l -> if (in_range l.pos offset) 
		then true
	  else false
  | Print (i, l)-> if (in_range l.pos offset) 
		then true
	  else false
  | Sharp ({exp_sharp_flow_type = st;
	     exp_sharp_val = eo;
	     exp_sharp_pos = l}) ->
	  if (in_range l.pos offset) 
		then true
	  else false 
  | SCall ({exp_scall_type = _;
	   exp_scall_method_name = id;
	   exp_scall_arguments = idl;
	   exp_scall_visible_names = _;
	   exp_scall_pos = l;
	   exp_scall_id = scall_id}) -> 
	  if (in_range l.pos offset) 
		then true
	  else false
  | Seq ({exp_seq_type = _;
	  exp_seq_exp1 = e1;
	  exp_seq_exp2 = e2;
	  exp_seq_pos = l}) -> 
	  if (in_range l.pos offset) 
		then true
	  else false
  | This { exp_this_type = _;
				 exp_this_pos =l }->
	 if (in_range l.pos offset) 
		then true
	  else false
  | Var ({exp_var_type = _;
	  exp_var_name = id;
	  exp_var_pos = l}) -> if (in_range l.pos offset) 
		then true
	  else false
  | VarDecl ({exp_var_decl_type = t;
	      exp_var_decl_name = id;
	      exp_var_decl_pos = l}) -> 
	  if (in_range l.pos offset) 
		then true
	  else false
  | Unit l                     -> if (in_range l.pos offset) 
		then true
	  else false
  | While ({exp_while_condition = id;
	    exp_while_body = e;
	    exp_while_spec = fl;
	    exp_while_pos = l})  -> 
	  if (in_range l.pos offset) 
		then true
	  else false
  | Unfold ({exp_unfold_var = sv; exp_unfold_pos = l}) ->if (in_range l.pos offset) 
		then true
	  else false
  | Try { exp_try_type = _;
				exp_try_body = e;
				exp_catch_clause = exp_catch ;
				exp_try_pos = l } -> 
	if (in_range l.pos offset) 
		then true
	  else false
;;

let rec search_exp_list (exp:Cast.exp) (elist:Cast.exp list ref) (offset:int) = match exp with 
  | Java ({exp_java_code = code}) -> elist
  | CheckRef _ -> elist
  | Assert ({exp_assert_asserted_formula = f1o; 
			 exp_assert_assumed_formula = f2o; 
			 exp_assert_pos = l;
			 exp_assert_label =  lbl;}) -> 
	  if (in_range l.pos offset) 
		then begin elist := exp::!elist; elist end
	  else elist
  | Assign ({exp_assign_lhs = id; exp_assign_rhs = e; exp_assign_pos = l}) -> 
	  if (in_range l.pos offset) 
		then begin elist := exp::!elist; search_exp_list e elist offset end
	  else search_exp_list e elist offset
  | BConst ({exp_bconst_val = b; exp_bconst_pos = l}) -> 
          if (in_range l.pos offset) 
		then begin elist := exp::!elist; elist end
	  else elist
  | Bind ({exp_bind_type = _; 
	   exp_bind_bound_var = (_, id); 
	   exp_bind_fields = idl;
	   exp_bind_body = e;
	   exp_bind_pos = l}) -> 
	   if (in_range l.pos offset) 
		then begin elist := exp::!elist; search_exp_list e elist offset end
	  else search_exp_list e elist offset
  | Block ({exp_block_type = _;
	    exp_block_body = e;
	    exp_block_local_vars = _;
	    exp_block_pos = l}) -> 
	  if (in_range l.pos offset) 
		then begin elist := e::!elist; search_exp_list e elist offset end
	  else search_exp_list e elist offset
  | ICall ({exp_icall_type = _;
	   exp_icall_receiver = r;
	   exp_icall_method_name = id;
	   exp_icall_arguments = idl;
	   exp_icall_visible_names = _;
	   exp_icall_pos = l}) -> 
	   if (in_range l.pos offset) 
		then begin elist := exp::!elist; elist end
	  else elist
  | Cast ({exp_cast_target_type = t;
		   exp_cast_body = e; exp_cast_pos = l}) ->
 	   if (in_range l.pos offset) 
		then begin elist := exp::!elist;  search_exp_list e elist offset end
	  else search_exp_list e elist offset

  | Cond ({exp_cond_type = _;
	   exp_cond_condition = id;
	   exp_cond_then_arm = e1;
	   exp_cond_else_arm = e2;
	   exp_cond_pos = l;
	   exp_cond_id = br_id}) -> 
	   if (in_range l.pos offset) 
		then begin elist := exp::!elist; 
			if (in_next_exp e1 offset) then search_exp_list e1 elist offset
			else search_exp_list e2 elist offset end
	  else begin if (in_next_exp e1 offset) then search_exp_list e1 elist offset
			else search_exp_list e2 elist offset end
  | Debug ({exp_debug_flag = b; exp_debug_pos = l}) -> if (in_range l.pos offset) 
		then begin elist := exp::!elist; elist end
	  else elist
  | Dprint _                   -> elist
  | FConst ({exp_fconst_val = f; exp_fconst_pos = l}) -> if (in_range l.pos offset) 
		then begin elist := exp::!elist; elist end
	  else elist
  | IConst ({exp_iconst_val = i; exp_iconst_pos = l}) -> if (in_range l.pos offset) 
		then begin elist := exp::!elist; elist end
	  else elist
  | New ({exp_new_class_name = id;
	  exp_new_arguments = idl;
	  exp_new_pos = l}) -> 
	  if (in_range l.pos offset) 
		then begin elist := exp::!elist; elist end
	  else elist
  | Null l -> if (in_range l.pos offset) 
		then begin elist := exp::!elist; elist end
	  else elist
  | Print (i, l)-> if (in_range l.pos offset) 
		then begin elist := exp::!elist; elist end
	  else elist
  | Sharp ({exp_sharp_flow_type = st;
	     exp_sharp_val = eo;
	     exp_sharp_pos = l}) ->
	  if (in_range l.pos offset) 
		then begin elist := exp::!elist; elist end
	  else elist 
  | SCall ({exp_scall_type = _;
	   exp_scall_method_name = id;
	   exp_scall_arguments = idl;
	   exp_scall_visible_names = _;
	   exp_scall_pos = l;
	   exp_scall_id = scall_id}) -> 
	   if (in_range l.pos offset) 
		then begin elist := exp::!elist; elist end
	  else elist
  | Seq ({exp_seq_type = _;
	  exp_seq_exp1 = e1;
	  exp_seq_exp2 = e2;
	  exp_seq_pos = l}) -> 
	  if (in_range l.pos offset) 
		then begin elist := exp::!elist; 
			search_exp_list e1 elist offset;
			search_exp_list e2 elist offset end
	  else begin search_exp_list e1 elist offset;search_exp_list e2 elist offset end
  | This { exp_this_type = _;
				 exp_this_pos =l } -> 
	  if (in_range l.pos offset) 
		then begin elist := exp::!elist; elist end
	  else elist
  | Var ({exp_var_type = _;
	  exp_var_name = id;
	  exp_var_pos = l}) -> if (in_range l.pos offset) 
		then begin elist := exp::!elist; elist end
	  else elist
  | VarDecl ({exp_var_decl_type = t;
	      exp_var_decl_name = id;
	      exp_var_decl_pos = l}) -> 
	      if (in_range l.pos offset) 
		then begin elist := exp::!elist; elist end
	  else elist
  | Unit l                     -> if (in_range l.pos offset) 
		then begin elist := exp::!elist; elist end
	  else elist
  | While ({exp_while_condition = id;
	    exp_while_body = e;
	    exp_while_spec = fl;
	    exp_while_pos = l})  -> 
	    if (in_range l.pos offset) 
		then begin elist := exp::!elist; search_exp_list e elist offset end
	  else search_exp_list e elist offset
  | Unfold ({exp_unfold_var = sv; exp_unfold_pos = l}) -> if (in_range l.pos offset) 
		then begin elist := exp::!elist; elist end
	  else elist
  | Try { exp_try_type = _;
				exp_try_body = e;
				exp_catch_clause = exp_catch ;
				exp_try_pos = l } -> 
	if (in_range l.pos offset) 
		then begin elist := exp::!elist; 
			if (in_range exp_catch.exp_catch_pos.pos offset) then
				search_exp_list exp_catch.exp_catch_body elist offset
			else
				search_exp_list e elist offset
			end
	  else begin if (in_range exp_catch.exp_catch_pos.pos offset) then
				search_exp_list exp_catch.exp_catch_body elist offset
			else
				search_exp_list e elist offset
			end
;;

let search_exp_list2 (exp:Cast.exp) (elist:Cast.exp list ref) (equeue:Cast.exp list ref)(offset:int) = match exp with 
  | Java ({exp_java_code = code}) -> elist
  | CheckRef _ -> elist
  | Assert ({exp_assert_asserted_formula = f1o; 
			 exp_assert_assumed_formula = f2o; 
			 exp_assert_pos = l;
			 exp_assert_label =  lbl;}) -> 
	  if (in_range l.pos offset) 
		then begin elist := exp::!elist; elist end
	  else elist
  | Assign ({exp_assign_lhs = id; exp_assign_rhs = e; exp_assign_pos = l}) -> 
	  if (in_range l.pos offset) 
		then begin elist := exp::!elist; 
		equeue := !equeue@[e];elist end
	  else begin equeue := !equeue@[e];elist end
  | BConst ({exp_bconst_val = b; exp_bconst_pos = l}) -> 
          if (in_range l.pos offset) 
		then begin elist := exp::!elist; elist end
	  else elist
  | Bind ({exp_bind_type = _; 
	   exp_bind_bound_var = (_, id); 
	   exp_bind_fields = idl;
	   exp_bind_body = e;
	   exp_bind_pos = l}) -> 
	   if (in_range l.pos offset) 
		then elist := exp::!elist;
	   equeue := List.append !equeue [e];elist
  | Block ({exp_block_type = _;
	    exp_block_body = e;
	    exp_block_local_vars = _;
	    exp_block_pos = l}) -> 
	  if (in_range l.pos offset) 
		then elist := exp::!elist;
		equeue := List.append !equeue [e];elist
  | ICall ({exp_icall_type = _;
	   exp_icall_receiver = r;
	   exp_icall_method_name = id;
	   exp_icall_arguments = idl;
	   exp_icall_visible_names = _;
	   exp_icall_pos = l}) -> 
	   if (in_range l.pos offset) 
		then begin elist := exp::!elist; elist end
	  else elist
  | Cast ({exp_cast_target_type = t;
		   exp_cast_body = e; exp_cast_pos = l}) ->
 	   if (in_range l.pos offset) 
		then elist := exp::!elist; equeue := List.append !equeue [e];elist

  | Cond ({exp_cond_type = _;
	   exp_cond_condition = id;
	   exp_cond_then_arm = e1;
	   exp_cond_else_arm = e2;
	   exp_cond_pos = l;
	   exp_cond_id = br_id}) -> 
	   if (in_range l.pos offset) 
		then elist := exp::!elist; equeue := List.append !equeue [e1;e2];elist
  | Debug ({exp_debug_flag = b; exp_debug_pos = l}) -> if (in_range l.pos offset) 
		then begin elist := exp::!elist; elist end
	  else elist
  | Dprint _                   -> elist
  | FConst ({exp_fconst_val = f; exp_fconst_pos = l}) -> if (in_range l.pos offset) 
		then begin elist := exp::!elist; elist end
	  else elist
  | IConst ({exp_iconst_val = i; exp_iconst_pos = l}) -> if (in_range l.pos offset) 
		then begin elist := exp::!elist; elist end
	  else elist
  | New ({exp_new_class_name = id;
	  exp_new_arguments = idl;
	  exp_new_pos = l}) -> 
	  if (in_range l.pos offset) 
		then begin elist := exp::!elist; elist end
	  else elist
  | Null l -> if (in_range l.pos offset) 
		then begin elist := exp::!elist; elist end
	  else elist
  | Print (i, l)-> if (in_range l.pos offset) 
		then begin elist := exp::!elist; elist end
	  else elist
  | Sharp ({exp_sharp_flow_type = st;
	     exp_sharp_val = eo;
	     exp_sharp_pos = l}) ->
	  if (in_range l.pos offset) 
		then begin elist := exp::!elist; elist end
	  else elist 
  | SCall ({exp_scall_type = _;
	   exp_scall_method_name = id;
	   exp_scall_arguments = idl;
	   exp_scall_visible_names = _;
	   exp_scall_pos = l;
	   exp_scall_id = scall_id}) -> 
	   if (in_range l.pos offset) 
		then begin elist := exp::!elist; elist end
	  else elist
  | Seq ({exp_seq_type = _;
	  exp_seq_exp1 = e1;
	  exp_seq_exp2 = e2;
	  exp_seq_pos = l}) -> 
	  if (in_range l.pos offset) 
		then elist := exp::!elist;
			 equeue := List.append !equeue [e1;e2];elist
  | This { exp_this_type = _;
				 exp_this_pos =l } -> 
	  if (in_range l.pos offset) 
		then begin elist := exp::!elist; elist end
	  else elist
  | Var ({exp_var_type = _;
	  exp_var_name = id;
	  exp_var_pos = l}) -> if (in_range l.pos offset) 
		then begin elist := exp::!elist; elist end
	  else elist
  | VarDecl ({exp_var_decl_type = t;
	      exp_var_decl_name = id;
	      exp_var_decl_pos = l}) -> 
	      if (in_range l.pos offset) 
		then begin elist := exp::!elist; elist end
	  else elist
  | Unit l                     -> if (in_range l.pos offset) 
		then begin elist := exp::!elist; elist end
	  else elist
  | While ({exp_while_condition = id;
	    exp_while_body = e;
	    exp_while_spec = fl;
	    exp_while_pos = l})  -> 
	    if (in_range l.pos offset) 
		then elist := exp::!elist; equeue := List.append !equeue [e];elist
  | Unfold ({exp_unfold_var = sv; exp_unfold_pos = l}) -> if (in_range l.pos offset) 
		then begin elist := exp::!elist; elist end
	  else elist
  | Try { exp_try_type = _;
				exp_try_body = e;
				exp_catch_clause = exp_catch ;
				exp_try_pos = l } -> 
	if (in_range l.pos offset) 
		then begin elist := exp::!elist;  equeue := List.append !equeue [exp_catch.exp_catch_body;e];elist
			end
	  else begin equeue := List.append !equeue [exp_catch.exp_catch_body;e];elist
			end
;;

let set_elist (exp: Cast.exp) (elist: Cast.exp list ref) (offset: int) = 
    let equeue = ref([]:Cast.exp list) in
	equeue := !equeue @ [exp];
	while not (List.length !equeue = 0) do
		search_exp_list2 (List.hd !equeue) elist equeue offset;
		equeue := List.tl !equeue
	done;;
let highlight (st:GText.iter) (en:GText.iter) (tag:string) (buffer:GSourceView.source_buffer)= buffer#apply_tag_by_name tag st en
;;
let highlight_range (st:int) (en:int) (tag:string) (buffer:GSourceView.source_buffer)=
			let start_iter = buffer#get_iter (`OFFSET st) in
			let end_iter = buffer#get_iter (`OFFSET en) in
			highlight start_iter end_iter tag buffer
;;

let remove_highlight (tag_name: string)(buffer:GSourceView.source_buffer)= buffer#remove_tag_by_name tag_name buffer#start_iter buffer#end_iter
;;

let highlight_exp (l:Cast.core_loc) (buffer:GSourceView.source_buffer) =
	let color = ref("yellow_highlight") in
        remove_highlight "yellow_highlight" buffer;
        remove_highlight "red_highlight" buffer;
        remove_highlight "old_fail_highlight" buffer;
	
	(Hashtbl.iter (fun e (v_pre, v_exc, v_post, fail_trace) -> 
		List.iter (fun (trace,flag) -> 
			if (flag == true) then color := "red_highlight"
			else color := ("old_fail_highlight")) fail_trace) l.state); highlight_range (l.pos.Globals.start_pos.Lexing.pos_cnum) (l.pos.Globals.end_pos.Lexing.pos_cnum) !color buffer
;;

let check_id (label:string) (id:int)= 
   let str = String.sub label 1 (String.index label ' ') in
   let id_str = string_of_int id in
   String.compare str id_str
;;

let rec string_of_exp_label e (id:int) =match e with 
  | Java ({exp_java_code = code; exp_java_pos=l}) -> (code,l,"Java Expression")
  | CheckRef ({ exp_check_ref_pos = l}) -> ("",l,"CheckRef Expression")
  | Assert ({exp_assert_asserted_formula = f1o; 
			 exp_assert_assumed_formula = f2o; 
			 exp_assert_pos = l;
			 exp_assert_label =  lbl;}) -> 
	 ("label: "^(Cprinter3.string_of_label_map l.state id)^"\nassert location: "^(string_of_full_loc l.pos)^"\n",l, "Assert Expression") 
  | Assign ({exp_assign_lhs = eid; exp_assign_rhs = e; exp_assign_pos = l}) -> 
	("label: "^(Cprinter3.string_of_label_map l.state id)^"assign loc:"^(string_of_full_loc l.pos)^"\n",l,"Assignment Expression")
  | BConst ({exp_bconst_val = b; exp_bconst_pos = l}) -> 
	("label: "^(Cprinter3.string_of_label_map l.state id)^"\nbconst location: "^(string_of_full_loc l.pos)^"\n",l,"BConst Expression")
  | Bind ({exp_bind_type = _; 
	   exp_bind_bound_var = (_, bid); 
	   exp_bind_fields = idl;
	   exp_bind_body = e;
	   exp_bind_pos = l}) -> 
	   ("label: "^(Cprinter3.string_of_label_map l.state id)^"\nbind location: "^(string_of_full_loc l.pos)^"\n",l,"Bind Expression")
  | Block ({exp_block_type = _;
	    exp_block_body = e;
	    exp_block_local_vars = _;
	    exp_block_pos = l}) -> ("label: "^(Cprinter3.string_of_label_map l.state id)^"\nblock location: "^(string_of_full_loc l.pos)^"\n",l,"Block Expression")
  | ICall ({exp_icall_type = _;
	   exp_icall_receiver = r;
	   exp_icall_method_name = iid;
	   exp_icall_arguments = idl;
	   exp_icall_visible_names = _;
	   exp_icall_pos = l}) -> 
	   ("label: "^(Cprinter3.string_of_label_map l.state id)^"\nicall location: "^(string_of_full_loc l.pos)^"\n",l,"Icall Expression")
  | Cast ({exp_cast_target_type = t;
		   exp_cast_body = body;exp_cast_pos = l}) -> ("label: "^(Cprinter3.string_of_label_map l.state id)^"\ncast location: "^(string_of_full_loc l.pos)^"\n",l,"Cast Expression")
  | Cond ({exp_cond_type = _;
	   exp_cond_condition = cid;
	   exp_cond_then_arm = e1;
	   exp_cond_else_arm = e2;
	   exp_cond_pos = l;
	   exp_cond_id = br_id}) -> 
	   ("label: "^(Cprinter3.string_of_label_map l.state id)^"\ncond location: "^(string_of_full_loc l.pos)^"\n",l,"Condition Expression")
  | Debug ({exp_debug_flag = b; exp_debug_pos = l}) -> ("label: "^(Cprinter3.string_of_label_map l.state id)^"\ndebug location: "^(string_of_full_loc l.pos)^"\n",l,"Debug Expression")
  | Dprint ({exp_dprint_pos = l})                  -> ("dprint",l,"Dprint Expression")
  | FConst ({exp_fconst_val = f; exp_fconst_pos = l}) -> ("label: "^(Cprinter3.string_of_label_map l.state id)^"\nfconst location: "^(string_of_full_loc l.pos)^"\n",l,"FConst Expression")
  (*| FieldRead (_, (v, _), (f, _), _) -> v ^ "." ^ f*)
  (*| FieldWrite ((v, _), (f, _), r, _) -> v ^ "." ^ f ^ " = " ^ r*)
  | IConst ({exp_iconst_val = i; exp_iconst_pos = l}) -> ("label: "^(Cprinter3.string_of_label_map l.state id)^"\niconst location: "^(string_of_full_loc l.pos)^"\n",l,"IConst Expression")
  | New ({exp_new_class_name = nid;
	  exp_new_arguments = idl;
	  exp_new_pos = l}) -> 
	  ("label: "^(Cprinter3.string_of_label_map l.state id)^"\nnew location: "^(string_of_full_loc l.pos)^"\n",l,"New Expression")
  | Null l -> ("null",l,"Null Expression")
  | Print (i, l)-> ("label: "^(Cprinter3.string_of_label_map l.state id)^"\nprint location: "^(string_of_full_loc l.pos)^"\n",l,"Print Expression")
  | Sharp ({exp_sharp_flow_type = st;
	     exp_sharp_val = eo;
	     exp_sharp_pos = l}) ->("label: "^(Cprinter3.string_of_label_map l.state id)^"\nsharp location: "^(string_of_full_loc l.pos)^"\n" ,l,"Sharp Expression")
  | SCall ({exp_scall_type = _;
	   exp_scall_method_name = sid;
	   exp_scall_arguments = idl;
	   exp_scall_visible_names = _;
	   exp_scall_pos = l;
	   exp_scall_id = scall_id}) -> ("label: "^(Cprinter3.string_of_label_map l.state id)^"\nscall location: "^(string_of_full_loc l.pos)^"\n",l,"SCall Expression")
  | Seq ({exp_seq_type = _;
	  exp_seq_exp1 = e1;
	  exp_seq_exp2 = e2;
	  exp_seq_pos = l}) -> 
	  ("label: "^(Cprinter3.string_of_label_map l.state id)^"\nseq location: "^(string_of_full_loc l.pos)^"\n",l,"Seq Expression")
  | This ({exp_this_pos = l}) -> ("this", l,"This Expression")
  | Var ({exp_var_type = _;
	  exp_var_name = vid;
	  exp_var_pos = l}) -> ("label: "^(Cprinter3.string_of_label_map l.state id)^"\nvar location: "^(string_of_full_loc l.pos)^"\n",l,"Var Expression")
  | VarDecl ({exp_var_decl_type = t;
	      exp_var_decl_name = vdid;
	      exp_var_decl_pos = l}) -> 
	      ("label: "^(Cprinter3.string_of_label_map l.state id)^"\nvardecl location: "^(string_of_full_loc l.pos)^"\n",l,"VarDecl Expression")
  | Unit l                     -> ("unit",l,"Unit Expression")
  | While ({exp_while_condition = wid;
	    exp_while_body = e;
	    exp_while_spec = fl;
	    exp_while_pos = l})  -> 
	  ( "label: "^(Cprinter3.string_of_label_map l.state id)^"\nwhile location: "^(string_of_full_loc l.pos)^"\n",l,"While Expression")
  | Unfold ({exp_unfold_var = sv; exp_unfold_pos = l}) -> ("label: "^(Cprinter3.string_of_label_map l.state id)^"\nunfold location: "^(string_of_full_loc l.pos)^"\n",l,"Unfold Expression")
  |  Try { exp_try_type = _;
				exp_try_body = e;
				exp_catch_clause = exp_catch ;
				exp_try_pos = l } -> 
	("label: "^(Cprinter3.string_of_label_map l.state id)^"\ntry location: "^(string_of_full_loc l.pos)^"\n",l,"Try Expression")
;;

let highlight_loc (pos:Globals.loc) (buffer:GSourceView.source_buffer) (color:string)= 
	(*let f = search_poscond_struc id struc_formula in
	let pos = get_poscon_loc f in*)
	highlight_range (pos.Globals.start_pos.Lexing.pos_cnum) (pos.Globals.end_pos.Lexing.pos_cnum) color buffer
;;

let check_eassume_id (id:int) (f:Cformula.ext_formula) = (*prerr_endline (sprintf "id:%s" id ) ;*)
match f with
|EAssume (var,pos,(pre_id,str)) -> 
	if (id = pre_id) then 1 else 0
|_-> 0
;;

let rec check_pre_id_list (id:int) (f_list:Cformula.ext_formula list) = 
match f_list with
|ext_f::rest -> if (check_eassume_id id ext_f = 1) then 1 else check_pre_id_list id rest
|[] -> 0
;;

let rec check_pre_id (id:int) (f:Cformula.ext_formula) = (*prerr_endline (sprintf "id:%s" id ) ;*)
match f with
|EAssume (var,pos,(pre_id,str)) -> 
	if (id = pre_id) then 1 else 0
|ECase ec-> prerr_endline ("ECase") ;0
|EBase  {formula_ext_pos = loc; formula_ext_continuation = cont}->
	let num = 0(*(List.fold_left (fun a b -> (a+(check_pre_id id b buffer))) 0 cont*) in 
	let c = (List.fold_left (*(fun a b -> 0)*)cont 0 cont) in 
	check_pre_id_list id cont
;;



let rec search_poscond_struc (id:int) (struc_formula:Cformula.struc_formula) (buffer:GSourceView.source_buffer) = match struc_formula with
|f::rest -> if not(check_pre_id id f= 0) then f
	    else search_poscond_struc id rest buffer
|[]-> raise Not_found
;;


let get_poscon_loc (f:Cformula.ext_formula) = match f with
|EAssume (var,poscon,(id,str)) -> (match poscon with
				| Base {formula_base_pos  = pos} -> pos
				| Or {formula_or_pos = pos} -> pos
				| Exists {formula_exists_pos = pos} -> pos)
|ECase {formula_case_exists =ee;
	formula_case_branches  =  case_list ;formula_case_pos= pos} -> pos;
|EBase {
	formula_ext_implicit_inst = ii;
	formula_ext_explicit_inst = ei;
	formula_ext_exists = ee;
 	formula_ext_base = fb;
 	formula_ext_continuation = cont;
	formula_ext_pos = pos} -> pos;
;;

let rec lbl_list spec_list : string list  = List.concat (List.map (fun c-> match c with 
				| ECase e -> List.concat (List.map (fun (_,c)-> lbl_list c) e.formula_case_branches)
				| EBase e -> lbl_list e.formula_ext_continuation
				| EAssume (_,_,(i,s)) -> [(string_of_int i)^" "^s]) spec_list)
;;

let rec get_poscon (start_offset:int) (end_offset:int) (struc_formula:Cformula.struc_formula) : int=
match struc_formula with
|[]-> -1
|f::rest -> match f with
	|EAssume (var,poscon,(id,str)) -> id(*let poscon_loc = get_poscon_loc f in
		prerr_endline (sprintf "in eassume: start_offset:%i end:%i; its start: %i; its end:%i" start_offset end_offset poscon_loc.start_pos.pos_cnum poscon_loc.end_pos.pos_cnum);if (start_offset >= poscon_loc.start_pos.pos_cnum && end_offset <= poscon_loc.end_pos.pos_cnum) then
		id
		else begin get_poscon start_offset end_offset rest end*)
	|EBase {
	formula_ext_implicit_inst = ii;
	formula_ext_explicit_inst = ei;
	formula_ext_exists = ee;
 	formula_ext_base = fb;
 	formula_ext_continuation = cont;
	formula_ext_pos = pos} -> let poscon_loc = get_poscon_loc f in
		if (start_offset >= poscon_loc.start_pos.pos_cnum && end_offset <= poscon_loc.end_pos.pos_cnum) then
		 begin get_poscon start_offset end_offset cont end
		else begin get_poscon start_offset end_offset rest end
	|ECase {formula_case_exists =ee;
	formula_case_branches  =  case_list ;formula_case_pos= pos}->
		let poscon_loc = get_poscon_loc f in
		if (start_offset >= poscon_loc.start_pos.pos_cnum && end_offset <= poscon_loc.end_pos.pos_cnum) then
		 -1(*begin get_poscon start_offset end_offset (snd(case_list)) end*)
		else begin get_poscon start_offset end_offset rest end
;;

let rec get_poscon_id (start_offset:int) (end_offset:int) (procs:Cast.proc_decl list) : int =
match procs with
|[]-> -1
|s::rest -> let num = get_poscon start_offset end_offset s.proc_static_specs_with_pre in if (num == -1) then get_poscon_id start_offset end_offset rest
		else num
;;


let highlight_poscon (id:int) (struc_formula:Cformula.struc_formula) (buffer:GSourceView.source_buffer) (color:string)= 
	remove_highlight "light_blue_highlight" buffer;
	remove_highlight color buffer;
	List.iter (fun f -> let pos = get_poscon_loc f in
	highlight_range (pos.Globals.start_pos.Lexing.pos_cnum) (pos.Globals.end_pos.Lexing.pos_cnum) "light_blue_highlight" buffer) struc_formula;
	if not (id = -1) then begin 
	let f = search_poscond_struc id struc_formula buffer in
	let pos_w = get_poscon_loc f in
	let start_iter = buffer#get_iter (`OFFSET (pos_w.Globals.start_pos.Lexing.pos_cnum)) in	
	let end_iter = buffer#get_iter (`OFFSET (pos_w.Globals.end_pos.Lexing.pos_cnum)) in
	(*prerr_endline ("found");*)
	buffer#remove_tag_by_name "light_blue_highlight" start_iter end_iter;
	buffer#apply_tag_by_name color start_iter end_iter end
	
;;

let highlight_poscons (struc_formula:Cformula.struc_formula) (buffer:GSourceView.source_buffer) (label:Cast.label_map) =
let leng = Hashtbl.length label in
(*prerr_endline(sprintf "no:%i" leng);*)
(Hashtbl.iter (fun id (v_pre, v_exc, v_post, fail_trace) -> 
		(*(prerr_endline (sprintf "id:%s;" id));*)
		let id_int = (Int32.to_int (Int32.of_string (String.sub id 0 ((String.length id)-1)))) in
		 if (List.length fail_trace = 0) then (highlight_poscon (-1) struc_formula buffer "err_pre_highlight")
		 else (highlight_poscon id_int struc_formula buffer "red_highlight")) label)
;;
