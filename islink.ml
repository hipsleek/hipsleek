open Printf
open StdLabels
open GdkKeysyms
open Globals
open Lexing
open Cformula
open Iast


exception Wrong_type of string;;
type mutable_exp = { mutable exp: Iast.exp option}

let exp_stack = ref([]:Iast.exp list)
;;

let prev_exp_stack = ref([]:Iast.exp list);;

let cur_exp = {exp = None};;

let next = ref([]:int list) (*update parellel with exp_stack to keep track of the next exp we should go to*)
;;

let prev_range = ref(0,0)
;;

let exp_pop ()= exp_stack := List.rev !exp_stack; 
	let e = List.hd !exp_stack in
	exp_stack:=List.tl !exp_stack;exp_stack := List.rev !exp_stack;e
	(*else raise (Wrong_type "exp_pop")*)
;;

let exp_push (exp: Iast.exp)= exp_stack := List.append !exp_stack [exp]
;;

let exp_top() = List.nth !exp_stack ((List.length !exp_stack)-1)
;;

let prev_pop ()= prev_exp_stack := List.rev !prev_exp_stack; 
	let e = List.hd !prev_exp_stack in
	prev_exp_stack:=List.tl !prev_exp_stack;prev_exp_stack := List.rev !prev_exp_stack;e
	(*else raise (Wrong_type "exp_pop")*)
;;

let prev_push (exp: Iast.exp)= prev_exp_stack := List.append !prev_exp_stack [exp]
;;

let prev_top() = List.nth !prev_exp_stack ((List.length !prev_exp_stack)-1)
;;

let int_pop ()= next := List.rev !next;
	let e = List.hd !next in next:=List.tl !next;next := List.rev !next;e
;;

let int_push (e: int)= next := List.append !next [e]
;;

let int_top ()= List.nth !next ((List.length !next)-1)
;;

let rec look_up_proc_loc (procs : Iast.proc_decl list) (offset:int) = match procs with
  | p :: rest ->
      let loc = p.proc_loc in
      let start_p = loc.start_pos in
      let end_p = loc.end_pos in
      if (offset >= start_p.pos_cnum && offset <= end_p.pos_cnum (*&& not (is_added_primitives p.proc_name)*)) then
		p
      else
		look_up_proc_loc rest offset
  | [] -> raise Not_found

let get_proc_range (proc:proc_decl) = (proc.proc_loc.start_pos.pos_cnum, proc.proc_loc.end_pos.pos_cnum);;
  (** return procedure according to the offset*)

(*given a loc, check whether the offset is within the range*)
let in_range (pos:Globals.loc) (offset:int) = 
      let start_p = pos.start_pos in
      let end_p = pos.end_pos in
      if (offset >= start_p.pos_cnum && offset <= end_p.pos_cnum) then true
      else false
;;

let highlight (st:GText.iter) (en:GText.iter) (tag:string) (buffer:GSourceView.source_buffer)= buffer#apply_tag_by_name tag st en
;;
let highlight_range (st:int) (en:int) (tag:string) (buffer:GSourceView.source_buffer)=
			let start_iter = buffer#get_iter (`OFFSET st) in
			let end_iter = buffer#get_iter (`OFFSET en) in
			highlight start_iter end_iter tag buffer
;;

let remove_highlight (tag_name: string)(buffer:GSourceView.source_buffer)= buffer#remove_tag_by_name tag_name buffer#start_iter buffer#end_iter
;;

let rec init_exp_stack (exp: Iast.exp) = match exp with 
  | Unfold u ->  exp_push exp; int_push 0
  | Java ({exp_java_code = code}) ->  exp_push exp; int_push 0
  | Bind ({exp_bind_bound_var = v;
		   exp_bind_fields = vs;
		   exp_bind_body = e})      ->  (*exp_push exp; int_push 0;*) init_exp_stack e
  | Block ({exp_block_body = e})    ->  (*exp_push exp; int_push 0;*) init_exp_stack e
  | Break b ->  exp_push exp; int_push 0
  | Cast ({ exp_cast_target_type =typ;
				 exp_cast_body = e;
				 exp_cast_pos = l }) -> (*exp_push exp; int_push 0;*) init_exp_stack e
  | Continue b -> exp_push exp; int_push 0
(*  | Empty l                         -> ""*)
  | Unary ({exp_unary_op = o;
			exp_unary_exp = e;
			exp_unary_pos = l})     -> exp_push exp; int_push 0; init_exp_stack e
  | Binary ({exp_binary_op = o;
			 exp_binary_oper1 = e1;
			 exp_binary_oper2 = e2;
			 exp_binary_pos = l})   -> exp_push exp; int_push 1; init_exp_stack e1
  | CallNRecv ({exp_call_nrecv_method = id;
				exp_call_nrecv_arguments = el;
				exp_call_nrecv_id = nrecv_id;})
                                    -> exp_push exp; int_push ((List.length el)-1); if not(List.length el = 0) then init_exp_stack (List.hd el)
  | CallRecv ({exp_call_recv_receiver = recv;
			   exp_call_recv_method = id;
			   exp_call_recv_arguments = el;
			   exp_call_recv_id = recv_id;})
                                    -> exp_push exp; int_push ((List.length el)-1);if not(List.length el = 0) then init_exp_stack (List.hd el)
  | New ({exp_new_class_name = id;
		  exp_new_arguments = el})  -> exp_push exp; int_push ((List.length el)-1);if not(List.length el = 0) then init_exp_stack (List.hd el)
  | Var ({exp_var_name = v})        -> exp_push exp; int_push 0
  | Member ({exp_member_base = e;
			 exp_member_fields = idl})
                                    -> (*exp_push exp; int_push 0; *)init_exp_stack e
  | Assign ({exp_assign_op = op;
			 exp_assign_lhs = e1;
			 exp_assign_rhs = e2})  -> (*exp_push exp; int_push 1; exp_push exp;*) init_exp_stack e2; init_exp_stack e1
  | Cond ({exp_cond_condition = e1;
		   exp_cond_then_arm = e2;
		   exp_cond_else_arm = e3;
		   exp_cond_id = id;}) -> (*exp_push exp; int_push 0; *)init_exp_stack e3;init_exp_stack e2;init_exp_stack e1
  | While ({exp_while_condition = e1;
			exp_while_body = e2;
			exp_while_label = lb;
			exp_while_specs = li}) -> (*exp_push exp; int_push 1;*)init_exp_stack e2; init_exp_stack e1         
  | Return ({exp_return_val = v})  -> (match v with 
	  | None   -> exp_push exp; int_push 0
	  | Some e -> exp_push exp; int_push 0; init_exp_stack e) 
  | Seq ({exp_seq_exp1 = e1;
		  exp_seq_exp2 = e2})      -> (*exp_push exp; int_push 0;*)init_exp_stack e2; init_exp_stack e1
  | VarDecl ({exp_var_decl_type = t;
			  exp_var_decl_decls = l})
                                   -> exp_push exp; int_push 0
  | ConstDecl ({exp_const_decl_type = t;
				exp_const_decl_decls = l})
                                   -> exp_push exp; int_push 0
  | BoolLit ({exp_bool_lit_val = b})
                                   -> exp_push exp; int_push 0
  | IntLit ({exp_int_lit_val = i}) -> exp_push exp; int_push 0
  | FloatLit ({exp_float_lit_val = f})
                                   -> exp_push exp; int_push 0
  | Null l                         -> exp_push exp; int_push 0
  | Assert _                       -> exp_push exp; int_push 0
  | Dprint l                       -> exp_push exp; int_push 0
  | Debug ({exp_debug_flag = f})   -> exp_push exp; int_push 0
  | This _ -> exp_push exp; int_push 0
  | Raise ({exp_raise_type = tb;
			exp_raise_val = b;})
				-> exp_push exp; int_push 0
  | Try ({	exp_try_block = bl;
			exp_catch_clauses = cl;
			exp_finally_clause = fl;})
				-> exp_push exp; int_push 0; init_exp_stack bl
  |_-> exp_push exp
 
;;
let next_exp1 ():Iast.exp = 
  let e = exp_pop() in
  match cur_exp.exp with
  |Some ex ->
  prev_push ex;
  cur_exp.exp <- Some e;e
  |None -> cur_exp.exp <- Some e; e
;;

let prev_exp ():Iast.exp =
  let e = prev_pop() in
  match cur_exp.exp with
  |Some ex ->
  exp_push ex;cur_exp.exp <-Some e;e
  |None -> cur_exp.exp <-Some e;e
;;

let prev_same_range (l:Globals.loc) = 
	if (l.start_pos.pos_cnum = fst(!prev_range) && l.end_pos.pos_cnum = snd(!prev_range)) then 1
	else 0
;;

let rec move_to_exp (exp:Iast.exp) (buffer:GSourceView.source_buffer)= try(
   let pos = Iast.get_exp_pos exp in
	remove_highlight "yellow_highlight" buffer; Cslink.highlight_loc pos buffer "yellow_highlight"; pos.end_pos.pos_cnum
  )
  with Wrong_type (s) -> raise (Wrong_type "move_to_exp")
;;

let search_exp_list (exp:Iast.exp) (ilist:Iast.exp list ref) (iqueue:Iast.exp list ref)(offset:int) = 
match exp with 
  | Unfold u ->  ilist
  | Java ({exp_java_code = code}) ->  ilist
  | Bind ({exp_bind_bound_var = v;
		   exp_bind_fields = vs;
		   exp_bind_body = e;
		exp_bind_pos = l})      -> 
	  iqueue := !iqueue@[e];
	  if (in_range l offset) 
		then begin ilist := exp::!ilist; ilist end
	  else ilist
  | Block ({exp_block_body = e; exp_block_pos = l})    -> 
	iqueue := !iqueue@[e];
	if (in_range l offset) 
		then begin ilist := exp::!ilist; ilist end
	  else ilist
  | Break ({ exp_break_pos= l}) ->
	if (in_range l offset) 
		then begin ilist := exp::!ilist; ilist end
	  else ilist
  | Cast ({ exp_cast_target_type =typ;
				 exp_cast_body = e;
				 exp_cast_pos = l }) -> 
	iqueue := !iqueue@[e];
	if (in_range l offset) 
		then begin ilist := exp::!ilist; ilist end
	  else ilist
  | Continue ({exp_continue_pos = l}) -> 
	  if (in_range l offset) 
		then begin ilist := exp::!ilist; ilist end
	  else ilist
(*  | Empty l                         -> ""*)
  | Unary ({exp_unary_op = o;
			exp_unary_exp = e;
			exp_unary_pos = l})     -> 
	iqueue := !iqueue@[e];
	if (in_range l offset) 
		then begin ilist := exp::!ilist; ilist end
	  else ilist
  | Binary ({exp_binary_op = o;
			 exp_binary_oper1 = e1;
			 exp_binary_oper2 = e2;
			 exp_binary_pos = l})   -> 
	iqueue := !iqueue@[e1];
	iqueue := !iqueue@[e2];
	if (in_range l offset) 
		then begin ilist := exp::!ilist; ilist end
	  else ilist
  | CallNRecv ({exp_call_nrecv_method = id;
				exp_call_nrecv_arguments = el;
				exp_call_nrecv_id = nrecv_id;exp_call_nrecv_pos = l})
                                    -> 
	if (in_range l offset) 
		then begin ilist := exp::!ilist; ilist end
	  else ilist
  | CallRecv ({exp_call_recv_receiver = recv;
			   exp_call_recv_method = id;
			   exp_call_recv_arguments = el;
			   exp_call_recv_id = recv_id;exp_call_recv_pos = l})
                                    -> 
	if (in_range l offset) 
		then begin ilist := exp::!ilist; ilist end
	  else ilist
  | New ({exp_new_class_name = id;
		  exp_new_arguments = el; exp_new_pos = l})  -> 
	if (in_range l offset) 
		then begin ilist := exp::!ilist; ilist end
	  else ilist
(*  | Var ({exp_var_name = v})        -> 
	if (in_range l offset) 
		then begin ilist := exp::!ilist; ilist end
	  else ilist*)
  | Member ({exp_member_base = e;
			 exp_member_fields = idl; exp_member_pos = l})
	                                    -> 
	iqueue := !iqueue@[e];	
	if (in_range l offset) 
		then begin ilist := exp::!ilist; ilist end
	  else ilist
  | Assign ({exp_assign_op = op;
			 exp_assign_lhs = e1;
			 exp_assign_rhs = e2; exp_assign_pos = l})  -> 
	iqueue := !iqueue@[e1];	
	iqueue := !iqueue@[e2];	
	if (in_range l offset) 
		then begin ilist := exp::!ilist; ilist end
	  else ilist
  | Cond ({exp_cond_condition = e1;
		   exp_cond_then_arm = e2;
		   exp_cond_else_arm = e3;
		   exp_cond_id = id;exp_cond_pos = l}) -> 
	iqueue := !iqueue@[e1];	
	iqueue := !iqueue@[e2];	
	iqueue := !iqueue@[e3];
	if (in_range l offset) 
		then begin ilist := exp::!ilist; ilist end
	  else ilist
  | While ({exp_while_condition = e1;
			exp_while_body = e2;
			exp_while_label = lb;
			exp_while_specs = li; exp_while_pos = l}) ->
	iqueue := !iqueue@[e1];	
	iqueue := !iqueue@[e2];	
	if (in_range l offset) 
		then begin ilist := exp::!ilist; ilist end
	  else ilist
  | Return ({exp_return_val = v; exp_return_pos = l})  ->  
	if (in_range l offset) 
		then begin ilist := exp::!ilist; ilist end
	  else ilist
  | Seq ({exp_seq_exp1 = e1;
		  exp_seq_exp2 = e2})      -> 
	iqueue := !iqueue@[e1];	
	iqueue := !iqueue@[e2];	ilist
 (* | VarDecl ({exp_var_pos = l})->
	if (in_range l.pos offset) 
		then begin ilist := exp::!ilist; ilist end
	  else ilist
  | ConstDecl ({exp_const_decl_type = t;
				exp_const_decl_decls = cl; exp_const_decl_pos = l})                                  -> 
	if (in_range l.pos offset) 
		then begin ilist := exp::!ilist; ilist end
	  else ilist
  | BoolLit ({exp_bool_lit_val = b})
                                   -> exp_push exp; int_push 0
  | IntLit ({exp_int_lit_val = i}) -> exp_push exp; int_push 0
  | FloatLit ({exp_float_lit_val = f})
                                   -> exp_push exp; int_push 0
  | Null l                         -> exp_push exp; int_push 0
  | Assert _                       -> exp_push exp; int_push 0
  | Dprint l                       -> exp_push exp; int_push 0
  | Debug ({exp_debug_flag = f})   -> exp_push exp; int_push 0
  | This _ -> exp_push exp; int_push 0
  | Raise ({exp_raise_type = tb;
			exp_raise_val = b;})
				-> exp_push exp; int_push 0
  | Try ({	exp_try_block = bl;
			exp_catch_clauses = cl;
			exp_finally_clause = fl;})
				-> exp_push exp; int_push 0; init_exp_stack bl*)
  |_-> let l = Iast.get_exp_pos exp in 
	if (in_range l offset) 
		then begin ilist := exp::!ilist; ilist end
	  else ilist
;;

let set_elist (exp: Iast.exp) (ilist: Iast.exp list ref) (offset: int) = 
    let iqueue = ref([]:Iast.exp list) in
	iqueue := !iqueue @ [exp];
	while not (List.length !iqueue = 0) do
		search_exp_list (List.hd !iqueue) ilist iqueue offset;
		iqueue := List.tl !iqueue
	done;;
