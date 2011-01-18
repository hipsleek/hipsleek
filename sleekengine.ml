(*
  The frontend engine of SLEEK.
*)

open Globals
open Sleekcommons

module H = Hashtbl
module I = Iast
module C = Cast
module CF = Cformula
module CP = Cpure
module IF = Iformula
module IP = Ipure
module AS = Astsimp

module XF = Xmlfront
module NF = Nativefront

(*
  Global data structures. If we want to support push/pop commands,
  we'll need to make them into a stack of scopes.
*)
let iobj_def = { I.data_name = "Object";
				 I.data_fields = [];
				 I.data_parent_name = "";
				 I.data_invs = []; (* F.mkTrue no_pos; *)
				 I.data_methods = [] }

let iprog = { I.prog_data_decls = [iobj_def];
			  I.prog_global_var_decls = [];
			  I.prog_enum_decls = [];
			  I.prog_view_decls = [];
			  I.prog_proc_decls = [];
			  I.prog_coercion_decls = [];
     (*added Oct 16 2010*)
     (*store all the predicates that are defined by users*)
        I.prog_pure_pred_decl = [];
        I.prog_pure_lemma = []}

let cobj_def = { C.data_name = "Object";
				 C.data_fields = [];
				 C.data_parent_name = "";
				 C.data_invs = [];
				 C.data_methods = [] }

let cprog = { C.prog_data_decls = [];
			  C.prog_view_decls = [];
			  C.prog_proc_decls = [];
			  C.prog_left_coercions = [];
			  C.prog_right_coercions = [] }

let residues = ref (None : CF.list_context option)

let check_data_pred_name name : bool =
  try 
	let _ = I.look_up_data_def_raw iprog.I.prog_data_decls name in
	  false
  with
	| Not_found -> begin
		try
		  let _ = I.look_up_view_def_raw iprog.I.prog_view_decls name in
			false
		with
		  | Not_found -> begin
        (*modify Oct 16 2010*)
        try
          let _ = I.look_up_pure_pred_def_raw iprog.I.prog_pure_pred_decl name in
            false
        with
          |Not_found -> true
      end 
	  end

let process_data_def ddef =
  (*
    print_string (Iprinter.string_of_data_decl ddef);
    print_string ("\n"); 
  *)
  if check_data_pred_name ddef.I.data_name then
    let tmp = iprog.I.prog_data_decls in
      try
	      iprog.I.prog_data_decls <- ddef :: iprog.I.prog_data_decls;
	      let _ = Iast.build_exc_hierarchy true iprog in
	      let _ = Util.c_h () in
	      let cddef = AS.trans_data iprog ddef in
	      let _ = if !Globals.print_core then print_string (Cprinter.string_of_data_decl cddef ^"\n") else () in
	      cprog.C.prog_data_decls <- cddef :: cprog.C.prog_data_decls
      with
	    | _ -> dummy_exception() ; iprog.I.prog_data_decls <- tmp
      else begin
        dummy_exception() ;
	      print_string (ddef.I.data_name ^ " is already defined.\n")
      end

let rec check_one_case one_case name_and_number_list = 
  let rec get_number_from_list name name_and_number_list = 
    match name_and_number_list with
      |(name_in_list, number)::tail -> if name_in_list = name then number else (get_number_from_list name tail)
      |[] -> -1
  in
  let rec check_one_pure_or_rec_formual formula name_and_number_list =
    match formula with
      |Iast.Expand _ (*this case never happened*)
      |Iast.Pure _ -> true
      |Iast.PreFormula p -> 
          let number = get_number_from_list p.I.pred_name name_and_number_list in
            if number = -1 then
              false
            else 
              (number = (List.length p.I.argument_list))
  in 
  match one_case with
    |head::tail -> (check_one_pure_or_rec_formual head name_and_number_list ) & ( check_one_case tail name_and_number_list)
    | [] -> true

let rec check_pred_in_RHS formula_list name_and_number_list = 
  match formula_list with
  |(Iast.Case_in_rec head)::tail -> (check_one_case head.I.formula_element name_and_number_list) & (check_pred_in_RHS tail name_and_number_list)
  | [] -> true

let rec add_in_out_property_for_arg pred =
  let rec check_one_form form = 
    match form with
   | Iast.Expand _
   | Iast.PreFormula _ -> ""
   | Iast.Pure form -> 
       (*we must convert this form first and then simplify it. later, check and
        * get IN properties*) 
       (*in this, I skip 2 first steps *)
     match form with
      | Ipure.Lt ( e1, e2, loc) 
      | Ipure.Lte(e1, e2, loc) 
      | Ipure.Gt(e1, e2, loc)
      | Ipure.Gte (e1, e2, loc) 
      | Ipure.Eq ( e1, e2, loc) ->
          begin
          match e1, e2 with
            | Ipure.Var((id, _), _) , Ipure.IConst(i, _) -> id
            | Ipure.IConst(i, _), Ipure.Var((id, _), _) -> id 
            | _, _ -> ""
          end
      | _ -> ""
  in 
  let rec check_one_case one_case = 
    match one_case with
   | head::tail -> 
      let id = check_one_form head in
      if id = "" then
        check_one_case tail
      else 
        id :: (check_one_case tail) 
   | [] -> [] 
  in
  let rec check_in_case_list case_list =
   match case_list with
   | (Iast.Case_in_rec head)::tail -> (check_one_case head.I.formula_element):: (check_in_case_list tail)
   | [] -> []
  in
  let rec string_of_list_id id_list = 
    match id_list with
    |head::tail -> head ^ "::" ^ string_of_list_id tail
    |[]-> "\n"
  in 
  let rec string_of_list_of_list input_list =
    match input_list with
      |head::tail -> "abc: " ^ string_of_list_id head ^"\n" ^ string_of_list_of_list tail 
      |[] -> "\n" 
  in
  let rec common_list input_list = 
(*input_list is the list of list, this function returns the list of 
 * variables that exist in all of list in input_list*)
    let rec is_exists ele list_ele = 
      match list_ele with
        |head::tail -> 
            List.mem ele head & (is_exists ele tail)
        |[] -> true 
    in 
    let rec helper fi list_string =
      match fi with
        | head::tail -> 
            if is_exists head list_string then 
              head::(helper tail list_string)
            else 
              helper tail list_string
        |[] ->[]
    in
    match input_list with
      |head::tail -> helper head tail
      | [] -> []
  in
  let temp_list = check_in_case_list pred.I.pure_formula in
  let in_argument = common_list temp_list in
    (*the name of arguments that have IN properties*)
  let rec add_in_out_properties_to_list in_list pre = 
    match pre with
      | (id, typ) :: tail -> 
          if List.mem id in_list then
            (id, Iast.IN)::(add_in_out_properties_to_list in_list tail)
          else 
            (id, Iast.OUT) :: (add_in_out_properties_to_list in_list tail )
      | [] -> []
  in 
  let new_argument_list = add_in_out_properties_to_list in_argument pred.I.pure_vars in
    {
      Iast.predicate_name = pred.I.predicate_name ;
      Iast.pure_vars = new_argument_list;
      Iast.pure_inv = pred.I.pure_inv;
      Iast.pure_formula = pred.I.pure_formula
    }  

let rec normalize_pure_pred ppred = 
  let rec eliminate_dups l = 
    match l with
      |head::tail -> 
          begin 
            if List.mem head tail then
              eliminate_dups tail
            else 
              head::(eliminate_dups tail)
          end
      |[] -> []
  in
  let rec process_argument arg_list adding_form_list adding_ele = 
    match arg_list with
      | head::tail ->
         begin 
           match head with
             | Ipure.Null _
             | Ipure.Var _ 
             | Ipure.IConst _ 
             | Ipure.FConst _ -> 
                begin 
                  let temp_arg, form_list, new_adding_ele = process_argument tail adding_form_list adding_ele in
                    (head::temp_arg, form_list, new_adding_ele)
                end  
             | _ -> 
                 begin 
                   let id = "Anon" ^ fresh_trailer() in
                   let temp_ele_list = id::adding_ele in
                   let new_var = Ipure.Var((id, Unprimed), no_pos) in
                   let new_ele = I.Pure(Ipure.Eq(new_var, head, no_pos)) in
                   let temp_arg , form_list, new_adding_ele = process_argument tail adding_form_list temp_ele_list in
                     (new_var::temp_arg, new_ele::form_list, new_adding_ele)
                 end 
         end 
      |[] -> [], adding_form_list, adding_ele 
  in
  let rec normalize_pred_formula pred adding_ele = 
    let new_arg_list, adding_formula, output_adding_ele  = process_argument pred.I.argument_list [] adding_ele in
    I.PreFormula{ pred with I.argument_list = new_arg_list} :: adding_formula, output_adding_ele
  in
  let rec normalize_each_form form adding_ele = 
    match form with
      |Iast.Expand _ (*this case never happened*)
      |Iast.Pure _ -> [form], adding_ele
      |Iast.PreFormula p -> normalize_pred_formula p adding_ele
  in
  let rec normalize_in_each_case one_case adding_ele = 
    match one_case with
      |head::tail -> 
          begin 
            let new_form, new_list = normalize_each_form head adding_ele in
            let temp_new_list = (new_list@adding_ele) in
            let new_tail, new_list_from_tail = normalize_in_each_case tail temp_new_list in
              ((new_form)::(new_tail)), new_list_from_tail
          end
      | [] -> [], adding_ele 
  in
  let rec normalize_pure_formula pred =
    match pred with
      |(Iast.Case_in_rec head) :: tail -> 
          let new_formula_ele, adding_ele = normalize_in_each_case head.I.formula_element [] in
          let new_exists_list = head.I.exists_list@adding_ele in
          let new_exists_list = eliminate_dups new_exists_list in
          ((Iast.Case_in_rec (
            {
              Iast.exists_list = new_exists_list; 
              Iast.forall_list = head.I.forall_list;
              Iast.formula_element = List.flatten new_formula_ele;
            }
          ))::(normalize_pure_formula tail)) 
      |[] -> []
  in
  let pred_formula = ppred.I.pure_formula in
  let new_pred_formula = normalize_pure_formula pred_formula in
    {
      Iast.predicate_name = ppred.I.predicate_name;
      Iast.pure_vars = ppred.I.pure_vars;
      Iast.pure_inv = ppred.I.pure_inv ;
      Iast.pure_formula = new_pred_formula 
    }
(************************)
let rec check_valid_variables_in_RHS ppred = 
  let rec print_test name_and_number_list =
    match name_and_number_list with
      |head:: tail -> head^"  " ^ (print_test tail )
      |[] -> ""
  in 
  let rec get_id_of_argument_list arg_list = 
    match arg_list with
      | head::tail -> 
          begin 
            match head with
              | Ipure.Var((id, _), _) -> id::(get_id_of_argument_list tail)
              | _ -> get_id_of_argument_list tail 
          end 
      |[] -> [] 
  in
  let rec merge_2_list l1 l2 = 
    match l1 with
      |head::tail -> 
          begin 
            if List.mem head l2 then
              merge_2_list tail l2
            else 
              head :: (merge_2_list tail l2)
          end
      | [] -> l2
  in 
  let rec check_first_step one_pure arg_list = 
    match one_pure with
      |head::tail -> 
          begin 
            match head with
              | Iast.Pure p -> 
                  begin 
                    (merge_2_list arg_list (check_first_step tail arg_list))
                  end 
              | Iast.PreFormula p -> 
                  begin 
                    let id_of_arg_list = (get_id_of_argument_list p.I.argument_list) in
                    let temp = merge_2_list arg_list id_of_arg_list in
                    let new_temp = check_first_step tail temp in
                      new_temp
                  end
              
          end 
      |[] -> arg_list  
  in
  let rec check_expression e all_args = 
    match e with
      | Ipure.Null _ 
      | Ipure.IConst _ 
      | Ipure.FConst _ -> true
      | Ipure.Var ((id, _) , _) -> 
          begin 
            if List.mem id all_args then 
              true
            else 
              begin 
                let _ = print_string("error in var: " ^ id^  "\n" ^ id ^ " variable is not defined\n") in
                  false
              end 
          end 
      | Ipure.Add(e1, e2, _)
      | Ipure.Subtract(e1, e2, _ )
      | Ipure.Mult (e1, e2, _)
      | Ipure.Div(e1, e2, _) -> (check_expression e1 all_args) & ( check_expression e2 all_args)
      | _ -> true
  in 
  let check_b_formula form all_args = 
    match form with
      | Ipure.BConst _ -> true
      | Ipure.BVar ((id, _), _) -> List.mem id all_args
      | Ipure.Lt( e1, e2, _)
      | Ipure.Lte(e1, e2, _ ) 
      | Ipure.Gt(e1, e2, _)
      | Ipure.Gte(e1, e2, _)
      | Ipure.Eq(e1, e2, _) -> (check_expression e1 all_args ) & (check_expression e2 all_args) 
      | _ -> true 
  in 
  let rec check_arg_list arg all_args = 
    match arg with
      |head::tail ->
          begin 
            match head with
              | Ipure.Var((id, _), _) -> 
                  if not (List.mem id all_args) then
                    begin
                      let _ = print_string(id^" is not defined\n") in
                        false
                    end
                  else 
                    (check_arg_list tail all_args)
              | _ -> false
          end
      |[] -> true
  in 
  let check_one_pure_or_pred one_pure_or_pred all_args = 
    match one_pure_or_pred with
      | Iast.Pure form -> check_b_formula form all_args
      | Iast.PreFormula form -> check_arg_list form.I.argument_list all_args 
      | _ -> true
  in 
  let rec check_second_step one_pure all_args =
    match one_pure with
      | head::tail -> (check_one_pure_or_pred head all_args) & (check_second_step tail all_args) 
      | [] -> true 
  in 
  let check_in_each_pure_pred one_pure arg_list = 
    (*let all_args = check_first_step one_pure arg_list in*)
      (* all_args will contain all the ident of the arguments in LHS and all the
       * argument of predicate in RHS*)
    let result = check_second_step one_pure (*all_args*)arg_list in
      result 
  in 
  let rec check_in_pure_formula pure_form arg_list =
    match pure_form with
      |(Iast.Case_in_rec head):: tail -> (check_in_each_pure_pred head.I.formula_element (arg_list@head.I.exists_list))&(check_in_pure_formula tail arg_list)
      | [] -> true
  in
  let get_arg_in_LHS ppred = 
    let pure_vars = ppred.I.pure_vars in
    let arg_list, typ_list = List.split pure_vars in
      arg_list
  in 
  let arg_list = get_arg_in_LHS ppred in
  let result = check_in_pure_formula ppred.I.pure_formula arg_list in
    result  

let rec get_predicate_name pred_decl =
(*return a list of ( name_of_predicate, number_of_its_argument for checking*)
  match pred_decl with
    |head::tail -> (head.I.predicate_name, List.length head.I.pure_vars) ::(get_predicate_name tail)
    |[] -> []

let check_inv ppred = 
  let rec check_exp e arg_list = 
    match e with
      | Ipure.Null _ -> false
      | Ipure.Var((id, _), _) -> 
          if List.mem id arg_list then
            true
          else 
            begin 
              print_string("\n I donot know variable "^id^" in invariant\n");
              false
            end
      | Ipure.IConst _ 
      | Ipure.FConst _ -> true
      | Ipure.Add(e1, e2, _)
      | Ipure.Subtract(e1, e2, _) 
      | Ipure.Mult(e1, e2, _)
      | Ipure.Div(e1, e2, _) -> (check_exp e1 arg_list)&(check_exp e2 arg_list)
      | _ -> false
  in 
  let rec check_b_form form arg_list = 
    match form with
      | Ipure.BConst _ -> true
      | Ipure.BVar ((id, _), _) -> 
          if not (List.mem id arg_list ) then
            begin 
              print_string("\n I donot know variable "^id^" in invarant\n");
              false
            end
          else 
            true
      | Ipure.Lt(e1, e2, _)
      | Ipure.Lte(e1, e2, _ ) 
      | Ipure.Gt(e1, e2, _)
      | Ipure.Gte(e1, e2, _ )
      | Ipure.Eq(e1, e2, _)
      | Ipure.Neq(e1, e2, _) -> (check_exp e1 arg_list)&(check_exp e2 arg_list)
      | _ -> false
  in 
  let rec check_each_part part arg_list = 
    match part with
      | Iast.Pure p -> check_b_form p arg_list 
      | Iast.PreFormula _  -> 
          begin 
            print_string("please use pure formula in invariant\n");
            false  
          end
      | _ -> true(*this case is never happened in this step*)
  in
  let rec check_valid_inv inv arg_list = 
    match inv with 
      |head::tail ->( check_each_part head arg_list) & (check_valid_inv tail arg_list)
      |[] -> true
  in  
  let arg_list, _  = List.split ppred.I.pure_vars in
  let inv = ppred.I.pure_inv in
  let result = check_valid_inv inv arg_list in
    result 

let process_pure_pred_def ppdef =
  (*check if the predicate name exists or not*)
  if check_data_pred_name ppdef.I.predicate_name then
    (*let _ = print_string("\n congratulation this name is valid \n") in*)
    (*check in the RHS of the predicate declaration is declared*)
    let all_pure_pred_decl_name = (ppdef.I.predicate_name,List.length ppdef.I.pure_vars) :: (get_predicate_name iprog.I.prog_pure_pred_decl) in (*return a list of ( name_of_predicate, number_of_its_argument for checking*)
(*
     let test_string = print_test all_pure_pred_decl_name in
     let _ = print_string (test_string) in
 *)
    let is_used_valid_pred_in_RHS = check_pred_in_RHS ppdef.I.pure_formula all_pure_pred_decl_name in
       (*is_used_valid_pred_in_RHS return false if you use too much argument in
        * predication on the RHS*)
    if is_used_valid_pred_in_RHS then
  (*check the in out properties of the arguments in predicate*)
      let new_pure_pred_def = add_in_out_property_for_arg ppdef in
            (*normalize the predicate*)
      let new_pure_pred_def = normalize_pure_pred new_pure_pred_def in
      (*check the valid of variable in the RHS*)
      let is_valid_variables_in_RHS = check_valid_variables_in_RHS new_pure_pred_def in
      if is_valid_variables_in_RHS then
        begin 
          let is_valid_inv = check_inv new_pure_pred_def in
          if is_valid_inv then
            begin 
              iprog.I.prog_pure_pred_decl <- new_pure_pred_def::iprog.I.prog_pure_pred_decl;
              print_string(Iprinter.string_of_pure_pred_decl new_pure_pred_def);
            end
          else 
            print_string("look back to your inv\n")
        end
      else 
        print_string("Please check carefully\n")
    else 
     print_string("\n there are some problems with your predicate definition \nYou use much more or less than definition on the LHS\n")
  else 
    (*if this name is already is for some definition above*)
    print_string(ppdef.I.predicate_name ^ " is already defined \n")

let process_pred_def pdef = 
  if check_data_pred_name pdef.I.view_name then
    let tmp = iprog.I.prog_view_decls in
	  try
      let h = (self,Unprimed)::(res,Unprimed)::(List.map (fun c-> (c,Unprimed)) pdef.Iast.view_vars ) in
      let p = (self,Primed)::(res,Primed)::(List.map (fun c-> (c,Primed)) pdef.Iast.view_vars ) in
      let wf,_ = AS.case_normalize_struc_formula iprog h p pdef.Iast.view_formula false false [] in
        (*what is the meaning of this function???????
        * convert HeapNode2 -> HeapNode
        * step2: for example ll<n-1> -> ll<t> & t = n-1
        * step3: eliminate max min
        * step4: rename bound var
        * step5: convert anonym vars inside exists symbol*)
      let new_pdef = {pdef with Iast.view_formula = wf} in
      iprog.I.prog_view_decls <- ( new_pdef :: iprog.I.prog_view_decls);
		(*let tmp_views = order_views iprog.I.prog_view_decls in*)
		(*let _ = print_string ("\n------ "^(Iprinter.string_of_struc_formula "\t" pdef.Iast.view_formula)^"\n normalized:"^(Iprinter.string_of_struc_formula "\t" wf)^"\n") in*)
      let cpdef = AS.trans_view iprog new_pdef in
        (*convert iformula -> cformala*)
      let old_vdec = cprog.C.prog_view_decls in
      cprog.C.prog_view_decls <- (cpdef :: cprog.C.prog_view_decls);
(* added 07.04.2008	*)	
		(*ignore (print_string ("init: "^(Iprinter.string_of_struc_formula "" pdef.Iast.view_formula )^"\n normalized: "^
							 (Iprinter.string_of_struc_formula "" wf )^"\n translated: "^
							 (Cprinter.string_of_struc_formula cpdef.Cast.view_formula)
							 ^"\n"
							 )
				)*)
		(* used to do this for all preds, due to mutable fields formulas exploded, i see no reason to redo for all: 
		ignore (List.map (fun vdef -> AS.compute_view_x_formula cprog vdef !Globals.n_xpure) cprog.C.prog_view_decls);*)
      ignore (AS.compute_view_x_formula cprog cpdef !Globals.n_xpure);
      (*if doesnot set any option in command, Globals.n_xpure = 1
      * unfold 1 level and store it in cprog*)
      let n_cpdef = AS.view_case_inference cprog iprog.I.prog_view_decls cpdef in
      let _ = if !Globals.print_core then print_string (Cprinter.string_of_view_decl n_cpdef ^"\n") else () in
      cprog.C.prog_view_decls <- (n_cpdef :: old_vdec) 
      (*  print_string ("\npred def: "^(Cprinter.string_of_view_decl cpdef)^"\n")*)
(* added 07.04.2008	*)									  
	  with
		| _ ->  dummy_exception() ; iprog.I.prog_view_decls <- tmp
  else
	print_string (pdef.I.view_name ^ " is already defined.\n")

	
let rec meta_to_struc_formula (mf0 : meta_formula) quant fv_idents stab : CF.struc_formula = match mf0 with
  | MetaFormCF mf -> (Cformula.formula_to_struc_formula mf)
  | MetaForm mf -> 
      let h = List.map (fun c-> (c,Unprimed)) fv_idents in
      let p = List.map (fun c-> (c,Primed)) fv_idents in
      let wf,_ = AS.case_normalize_struc_formula iprog h p (Iformula.formula_to_struc_formula mf) false true [] in
      AS.trans_struc_formula iprog quant fv_idents wf stab false (*(Cpure.Prim Void) []*)
  | MetaVar mvar -> 
    begin
      try 
        let mf = get_var mvar in
        meta_to_struc_formula mf quant fv_idents stab
      with
        | Not_found ->
            dummy_exception() ;
            print_string (mvar ^ " is undefined.\n");
            raise SLEEK_Exception
    end
  | MetaCompose (vs, mf1, mf2) -> begin
      let cf1 = meta_to_struc_formula mf1 quant fv_idents stab in
      let cf2 = meta_to_struc_formula mf2 quant fv_idents stab in
      let svs = List.map (fun v -> AS.get_spec_var_stab v stab no_pos) vs in
      let res = Solver.compose_struc_formula cf1 cf2 svs no_pos in
        res
    end
  | MetaEForm b -> 
      let h = List.map (fun c-> (c,Unprimed)) fv_idents in
      let p = List.map (fun c-> (c,Primed)) fv_idents in
      let wf,_ = AS.case_normalize_struc_formula iprog h p b false true [] in
      let res = AS.trans_struc_formula iprog quant fv_idents wf stab false (*(Cpure.Prim Void) [] *) in
        res
	
let rec meta_to_formula (mf0 : meta_formula) quant fv_idents stab : CF.formula = 
  match mf0 with
  | MetaFormCF mf -> mf
  | MetaFormLCF mf -> (List.hd mf)
  | MetaForm mf ->
      let h = List.map (fun c-> (c,Unprimed)) fv_idents in
      let wf = AS.case_normalize_formula iprog h mf in
        (*wf has Iformula.formula type*)
      let _ = Astsimp.collect_type_info_formula iprog wf stab false in
        AS.trans_formula iprog quant fv_idents false wf stab false
  | MetaVar mvar -> 
      begin
        try 
          let mf = get_var mvar in
            meta_to_formula mf quant fv_idents stab
        with
          | Not_found ->
              dummy_exception() ;
              print_string (mvar ^ " is undefined.\n");
              raise SLEEK_Exception
      end
  | MetaCompose (vs, mf1, mf2) -> 
      begin
        let cf1 = meta_to_formula mf1 quant fv_idents stab in
        let cf2 = meta_to_formula mf2 quant fv_idents stab in
        let svs = List.map (fun v -> AS.get_spec_var_stab v stab no_pos) vs in
        let res = Cformula.compose_formula cf1 cf2 svs Cformula.Flow_combine no_pos in
          res
      end
  | MetaEForm _ -> report_error no_pos ("can not have structured formula in antecedent")
	  
let process_entail_check (iante0 : meta_formula) (iconseq0 : meta_formula) =
  try
    (*
    let string_iante0 = string_of_meta_formula iante0 in
    print_string(string_iante0);
    let string_iconseq0 = string_of_meta_formula iconseq0 in
    print_string(string_iconseq0);
     *)
    let _ = residues := None in
    let stab = H.create 103 in
    let ante = meta_to_formula iante0 false [] stab in
      (*ante has Cformula.formula type*)
   (* 
    let ante_str = Cprinter.string_of_formula ante in
	  let _ = print_string ("\nante of sleex: " ^ ante_str ^ "\n") in
   *) 
    let fvs = CF.fv ante in
    let fv_idents = List.map CP.name_of_spec_var fvs in
    let conseq = meta_to_struc_formula iconseq0 false fv_idents stab in
    (*let conseq = (Cformula.substitute_flow_in_struc_f !n_flow_int !top_flow_int conseq ) in*)
    let ectx = CF.empty_ctx (CF.mkTrueFlow ()) no_pos in
    let ctx = CF.build_context ectx ante no_pos in

    let ctx = List.hd (Cformula.change_flow_ctx  !top_flow_int !n_flow_int [ctx]) in
      (*let _ = print_string ("\n checking: "^(Cprinter.string_of_formula
       ante)^" |- "^(Cprinter.string_of_struc_formula conseq)^"\n") in	
      *)
    let _ = if !Globals.print_core then print_string ((Cprinter.string_of_formula ante)^" |- "^(Cprinter.string_of_struc_formula conseq)^"\n") else () in
      (*let _ = print_string("\n context before transform: " ^
        (Cprinter.string_of_context ctx) ^"\n") in
        *)
    let ctx = CF.transform_context (Solver.elim_unsat_es cprog (ref 1)) ctx in
    	(*let _ = print_string ("\n context after transform:
      "^(Cprinter.string_of_context ctx)^"\n") in*)
    let rs, _ = Solver.heap_entail_struc_init cprog false false false (CF.SuccCtx[ctx]) conseq no_pos None in
    (* 
    let _ = print_string("\n string of list contexts after using heap_entail_struc_init\n")in
    let _ = print_string(Cprinter.string_of_list_context rs ^"\n") in
     *)
    let rs = CF.transform_list_context (Solver.elim_ante_evars,(fun c->c)) rs in
      (*
      let _ = print_string("\n after transform_list_context: "^Cprinter.string_of_list_context rs ^"\n") in
       *)
    residues := Some rs;
    if CF.isFailCtx rs then begin 
      print_string ("Fail.\n");
      if !Globals.print_err_sleek  then           
        print_string (Cprinter.string_of_list_context rs); 
    end 
    else
      print_string ("Valid.\n")
  with
    | _ ->  Printexc.print_backtrace stdout;dummy_exception() ; (print_string "exception in entail check\n")	
	
let process_capture_residue (lvar : ident) = 
	let flist = match !residues with 
      | None -> (CF.mkTrue (CF.mkTrueFlow()) no_pos)
      | Some s -> CF.formula_of_list_context s in
		put_var lvar (Sleekcommons.MetaFormCF flist)

let process_lemma ldef =
  let ldef = Astsimp.case_normalize_coerc iprog ldef in
  let l2r, r2l = AS.trans_one_coercion iprog ldef in
	cprog.C.prog_left_coercions <- l2r @ cprog.C.prog_left_coercions;
	cprog.C.prog_right_coercions <- r2l @ cprog.C.prog_right_coercions

let process_print_command pcmd0 = match pcmd0 with
  | PVar pvar ->
	  let stab = H.create 103 in
	  let mf = try get_var pvar with Not_found->  Error.report_error {
                   Error.error_loc = no_pos;
                   Error.error_text = "couldn't find " ^ pvar;
                 }in
	  let pf = meta_to_struc_formula mf false [] stab in
		print_string ((Cprinter.string_of_struc_formula pf) ^ "\n")
  | PCmd pcmd -> 
	  if pcmd = "residue" then
      match !residues with
        | None -> print_string ": no residue \n"
        | Some s -> print_string ((Cprinter.string_of_formula 
              (CF.formula_of_list_context s))^"\n")
		else
			print_string ("unsupported print command: " ^ pcmd)

let normalize_entailpure p =
    let rec normalize_argument_list arg_list id_list adding_form_list =
      match arg_list with
      |head::tail -> 
          begin 
            match head with
             (* | Ipure.IConst(_, _) *)
              | Ipure.Var((_, _),_ ) -> 
                 begin
                    let tail_argument_list, tail_id_list, tail_adding_form_list = normalize_argument_list tail id_list adding_form_list in
                      head::tail_argument_list, tail_id_list, tail_adding_form_list
                 end 
              | _ ->  
                  begin 
                    let new_var = "Anon"^fresh_trailer() in
                    let new_exp = Ipure.Var((new_var, Unprimed), no_pos) in
                    let new_formula = Iast.Pure(Ipure.Eq(new_exp, head, no_pos)) in
                    let tail_argumet_list, tail_id_list, tail_adding_form_list = normalize_argument_list tail (new_var::id_list) (new_formula::adding_form_list) in 
                      new_exp::tail_argumet_list, tail_id_list, tail_adding_form_list
                  end
          end
      | [] -> [], id_list, adding_form_list 
    in
    let normalize_one_pure_or_rec one =
      match one with
      | Iast.PreFormula p -> 
          begin 
            let arg_list, id_list, adding_form_list = normalize_argument_list p.Iast.argument_list [] [] in
              Iast.PreFormula{
                Iast.pred_name = p.Iast.pred_name ;
                Iast.argument_list = arg_list ;
              }, id_list, adding_form_list 
          end
      | _ -> one, [], []
    in
    let rec normalize_pure_or_rec_list fo =
      match fo with 
      |head::tail -> 
          begin 
            let new_one_head, id_list_head, adding_form_list = normalize_one_pure_or_rec head in
            let new_one_tail, id_list_tail = normalize_pure_or_rec_list tail in
            let new_one_head = new_one_head::adding_form_list in
              new_one_head::new_one_tail, id_list_head@id_list_tail
          end
      |[] -> [], []
    in
    let normalize_one_case one_case =
      let new_form_ele, id_list = normalize_pure_or_rec_list one_case.Iast.formula_element in
        Iast.Case_in_rec ({
        Iast.forall_list = one_case.Iast.forall_list;
        Iast.exists_list = one_case.Iast.exists_list;
        Iast.formula_element =List.flatten new_form_ele ;
      }), id_list 
    in
    let rec normalize_case_in_rec_list case_in_rec_list = 
      match case_in_rec_list with
      |(Iast.Case_in_rec head)::tail -> 
          begin 
            let processed_tail, id_list = normalize_case_in_rec_list tail in
            let processed_head, id_list_head = normalize_one_case head in
              (processed_head::processed_tail), (id_list @ id_list_head)
          end
      |[] -> [],[]
    in
    let rec normalize_pure_or_rec_list_rhs fo =
      match fo with
      |head::tail -> 
          begin
            let new_one_head, id_list_head, adding_form_list = normalize_one_pure_or_rec head in
            let new_one_tail, id_list_tail, adding_form_list_tail = normalize_pure_or_rec_list_rhs tail in
              new_one_head :: new_one_tail, id_list_head @ id_list_tail, adding_form_list @ adding_form_list_tail 
          end
      | [] -> [], [], []
    in
    let rec normalize_one_case_rhs one_case =
      let new_form_ele, id_list, adding_form = normalize_pure_or_rec_list_rhs one_case.Iast.formula_element in 
        Iast.Case_in_rec({
        Iast.forall_list = one_case.Iast.forall_list;
        Iast.exists_list = one_case.Iast.exists_list;
        Iast.formula_element = new_form_ele; 
      }), id_list, adding_form
    in
    let rec normalize_rhs rhs =
      match rhs with
      |(Iast.Case_in_rec head)::tail -> 
         begin 
           let processed_tail, id_list, adding_formula = normalize_rhs tail in
           let processed_head, id_list_head, adding_formula_head = normalize_one_case_rhs head in
             (processed_head::processed_tail), (id_list@id_list_head), (adding_formula @ adding_formula_head)
         end 
      | [] -> [], [], [] 
                       (*the 3rd argument is used to add to left hand side*)
    in
    let rec adding_formula_one_case one_case adding_form =
      let new_formula_ele = one_case.Iast.formula_element@adding_form in
        Iast.Case_in_rec({
        Iast.forall_list = one_case.Iast.forall_list;
        Iast.exists_list = one_case.Iast.exists_list;
        Iast.formula_element = new_formula_ele;
      })
    in
    let rec adding_formula_to_lhs lhs adding_form =
      match lhs with
      |(Iast.Case_in_rec head)::tail ->
        begin 
          let new_head = adding_formula_one_case head adding_form in
          let new_tail = adding_formula_to_lhs tail adding_form in
            new_head::new_tail 
        end
      | [] -> []
    in
    let rhs, id_list_rhs, adding_form = normalize_rhs p.Iast.right_hand_side in
    (*let lhs, id_list_lhs = normalize_case_in_rec_list p.Iast.left_hand_side in
      *)
    let lhs, id_list_lhs, adding_form2 = normalize_rhs p.Iast.left_hand_side in
    let lhs = adding_formula_to_lhs lhs (adding_form @ adding_form2) in
    (*let lhs = adding_formula_to_lhs lhs adding_form in*)
    (*let lhs, id_list_lhs = normalize_case_in_rec_list p.Iast.left_hand_side in
    let rhs, id_list_rhs = normalize_case_in_rec_list p.Iast.right_hand_side in*)
    let new_existslist = (p.Iast.existslist @ id_list_lhs)@id_list_rhs in
      {
        Iast.foralllist = p.Iast.foralllist ;
        Iast.existslist = new_existslist;
        Iast.left_hand_side = lhs;
        Iast.right_hand_side = rhs;
      }
  (*end of normalize_entailpure*)

let check_valid_entail_pure pred name_and_number_of_predicate s =(*s is just a string to annouce to users*)
    (*let _ = print_string(string_of_name_and_number_list
     * name_and_number_of_predicate) in*)
    let left = check_pred_in_RHS pred.I.left_hand_side name_and_number_of_predicate in
    let right = check_pred_in_RHS pred.I.right_hand_side name_and_number_of_predicate in
    if not left then
      begin 
        let _ = print_string(s ^ " error in your LHS\n") in
        false 
      end 
    else
      begin 
        if not right then 
          begin 
            let _ = print_string(s ^ " error in you RHS\n") in
              false
          end
        else 
          true
      end
  
let process_entail_pure p = 
  let rec string_of_name_and_number_list name_number =
    match name_number with
      |(name, num)::tail -> "name: "^name^" number: "^ (string_of_int num) ^"\n"^(string_of_name_and_number_list tail)
      |[] -> "\n"
  in 
  let name_and_number_of_predicate = get_predicate_name iprog.I.prog_pure_pred_decl in
    (*name_and_number_of_predicate is a list of pair (name_of_predicate, the number of its
     * argument*)
  let valid_of_predicate = check_valid_entail_pure p name_and_number_of_predicate "CHECKENTAILPURE" in
  let print_result is_valid =
    if is_valid then
      print_string("RESULT: Valid\n")
    else 
      print_string("RESULT: I don't know\n")
  in
  (*let _ = print_string(string_of_bool valid_of_predicate) in*)
  if valid_of_predicate then 
      let normalized_entailpure = normalize_entailpure p in
      let _ = print_string("after normalize\n") in
      let _ = print_string(Iprinter.string_of_pure_derive normalized_entailpure) in
      let _ = print_string("\n") in
      (*let is_valid = Solver.checkentailpure iprog.I.prog_pure_pred_decl
       * iprog.I.prog_pure_lemma normalized_entailpure in *)
      let is_valid = Checkentailpure.checkentailpure iprog.I.prog_pure_pred_decl iprog.I.prog_pure_lemma normalized_entailpure in 

      let _= print_result is_valid in  
        (* print_string(Iprinter.string_of_pure_derive normalized_entailpure)*)
      ()

let get_var_name entailpure = 
  let rec get_var_exp exp var_list = 
    match exp with
      | Ipure.Var((id, _), _) ->
          begin
            if(List.mem id var_list) then
              var_list
            else 
              id::var_list
          end
      | Ipure.Add(e1, e2, _)
      | Ipure.Subtract(e1, e2, _)
      | Ipure.Mult(e1, e2, _) 
      | Ipure.Div(e1, e2, _) ->
          begin
            let var_e1 = get_var_exp e1 var_list in
            let var_e2 = get_var_exp e2 var_e1 in
              var_e2
          end
      | _ -> var_list
  in
  let get_var_pure b_form var_list =
    match b_form with
      | Ipure.BVar((id, _), _) ->
         begin
          if (List.mem id var_list) then
            var_list
          else
            id::var_list
         end 
      | Ipure.Lt(e1, e2, _)
      | Ipure.Lte(e1, e2, _)
      | Ipure.Gt(e1, e2, _) 
      | Ipure.Gte(e1, e2, _) 
      | Ipure.Eq(e1, e2, _)
      | Ipure.Neq(e1, e2, _) ->
          begin
            let var_e1 = get_var_exp e1 var_list in
            let var_e2 = get_var_exp e2 var_e1 in
              var_e2
          end
      | _ -> var_list
  in
  let rec get_var_from_arg p var_list =
    match p with
      | head::tail -> 
         begin
            let var_of_head = get_var_exp head var_list in
            let var_of_tail = get_var_from_arg tail var_of_head in
              var_of_tail
         end 
      | [] -> var_list
  in
  let rec get_var_pure_or_rec_formula form var_list =
    match form with
      |Iast.Pure b_form -> get_var_pure b_form var_list
      |Iast.PreFormula p -> get_var_from_arg p.Iast.argument_list var_list
      |Iast.Expand e -> get_var_name_case_in_rec e var_list
  and get_var_formula_element form_ele var_list =
    match form_ele with
      |head::tail ->
          begin
            let var_of_head = get_var_pure_or_rec_formula head var_list in
            let var_of_tail = get_var_formula_element tail var_of_head in
              var_of_tail
          end
      |[] -> var_list
  and get_var_one_case_in_rec one_case var_list = 
    get_var_formula_element one_case.Iast.formula_element var_list
  and get_var_name_case_in_rec one_side var_list =
    match one_side with
      |(Iast.Case_in_rec head)::tail -> 
          begin
            let var_of_head = get_var_one_case_in_rec head var_list in
            let var_of_tail = get_var_name_case_in_rec tail var_of_head in
              var_of_tail 
          end
      | [] -> var_list
  in
  let vars_of_LHS = get_var_name_case_in_rec entailpure.Iast.left_hand_side [] in
  let vars_of_RHS = get_var_name_case_in_rec entailpure.Iast.right_hand_side vars_of_LHS in 
    vars_of_RHS

let process_pure_lemma pldef =
  (*this part is used for some supporting functions for processing lemmas*)
  let rename_var_in_lemma lemma tbl =
    let rec rename_id_list id_list tbl result =
      match id_list with
        | head::tail -> 
            begin
              let new_head = Hashtbl.find tbl head in
              let new_tail = rename_id_list tail tbl (new_head::result) in
                new_tail
            end
        | [] -> result
    in
    let rec rename_exp e tbl = 
      match e with
        | Ipure.Var((id, p), l) ->
            begin
              let new_id = Hashtbl.find tbl id in
                Ipure.Var((new_id, p), l)
            end 
        | Ipure.Add(e1, e2, l) -> Ipure.Add(rename_exp e1 tbl, rename_exp e2 tbl, l)
        | Ipure.Subtract(e1, e2, l) -> Ipure.Subtract(rename_exp e1 tbl, rename_exp e2 tbl, l)
        | Ipure.Mult(e1, e2, l) -> Ipure.Mult(rename_exp e1 tbl, rename_exp e2 tbl, l)
        | Ipure.Div(e1, e2, l) -> Ipure.Div(rename_exp e1 tbl, rename_exp e2 tbl, l)
        | Ipure.Max(e1, e2, l) -> Ipure.Max(rename_exp e1 tbl, rename_exp e2 tbl, l)
        | Ipure.Min(e1, e2, l) -> Ipure.Min(rename_exp e1 tbl, rename_exp e2 tbl, l)
        | _ -> e
    in
    let rename_b_form b_form tbl =
      match b_form with
        | Ipure.BVar((id, p), l) -> 
            begin
              let new_id = Hashtbl.find tbl id in
               Ipure.BVar((new_id, p), l) 
            end
        | Ipure.Lt(e1, e2, l) -> Ipure.Lt(rename_exp e1 tbl, rename_exp e2 tbl, l)
        | Ipure.Lte(e1, e2, l) -> Ipure.Lte(rename_exp e1 tbl, rename_exp e2 tbl, l)
        | Ipure.Gte(e1, e2, l) -> Ipure.Gte(rename_exp e1 tbl, rename_exp e2 tbl, l)
        | Ipure.Gt(e1, e2, l) -> Ipure.Gt(rename_exp e1 tbl, rename_exp e2 tbl, l)
        | Ipure.Eq(e1, e2, l) -> Ipure.Eq(rename_exp e1 tbl, rename_exp e2 tbl, l)
        | Ipure.Neq(e1, e2, l) -> Ipure.Neq(rename_exp e1 tbl, rename_exp e2 tbl, l)
        | _ -> b_form
    in
    let rec rename_exp_list e_list tbl =
      match e_list with
        | head::tail ->
            begin
              let new_head = rename_exp head tbl in
                new_head :: (rename_exp_list tail tbl) 
            end
        | [] -> []
    in
    let rename_pred_form p tbl = 
      {
        Iast.pred_name = p.Iast.pred_name;
        Iast.argument_list = rename_exp_list p.Iast.argument_list tbl;
      }
    in
    let rec rename_one_pure_or_rec one tbl =
      match one with
        | Iast.Pure b_form -> Iast.Pure (rename_b_form b_form tbl)
        | Iast.PreFormula p -> Iast.PreFormula (rename_pred_form p tbl)
        | Iast.Expand e -> Iast.Expand (rename_case_in_rec_list e tbl)
    and rename_pure_or_rec_formula_list form_ele tbl =
      match form_ele with
        |head::tail ->
            begin
              let new_head = rename_one_pure_or_rec head tbl in
              let new_tail = rename_pure_or_rec_formula_list tail tbl in
                new_head::new_tail
            end
        | [] -> []
    and rename_one_case_in_rec one_case tbl =
      {
        Iast.forall_list = rename_id_list one_case.Iast.forall_list tbl [];
        Iast.exists_list = rename_id_list one_case.Iast.exists_list tbl [];
        Iast.formula_element = rename_pure_or_rec_formula_list one_case.Iast.formula_element tbl;
      }
    and rename_case_in_rec_list one_side tbl =
      match one_side with
        |(Iast.Case_in_rec head)::tail ->
           begin
            let new_head = rename_one_case_in_rec head tbl in
              (Iast.Case_in_rec new_head)::(rename_case_in_rec_list tail tbl)
           end 
        | [] -> [] 
    in
    let new_foralllist = rename_id_list lemma.Iast.foralllist tbl [] in
    let new_existslist = rename_id_list lemma.Iast.existslist tbl [] in
    let new_LHS = rename_case_in_rec_list lemma.Iast.left_hand_side tbl   in
    let new_RHS = rename_case_in_rec_list lemma.Iast.right_hand_side tbl  in
      {
        Iast.foralllist = new_foralllist;
        Iast.existslist = new_existslist;
        Iast.left_hand_side = new_LHS;
        Iast.right_hand_side = new_RHS;
      }
  in
  let rec string_of_id_list name_list = 
    match name_list with
      |head::tail -> head ^ " " ^ (string_of_id_list tail)
      |[] -> "\n" 
  in
  let rec generate_random_list number var_list = 
    match number with
      | 0 -> var_list
      | _ -> 
          begin
            let new_id = "Anon"^(fresh_trailer ()) in
              generate_random_list (number - 1) (new_id::var_list)
          end
  in
  let rec init_tbl tbl var_name random_name index =
    match index with
      | -1 -> tbl 
      | _ -> 
         begin
          let var = List.nth var_name index in
          let ran = List.nth random_name index in
          let _ = Hashtbl.add tbl var ran in
            init_tbl tbl var_name random_name (index -1)
         end 
  in
  let print_id_x_id_tbl tbl =
    let f x y = 
      print_string("id1: " ^ x ^ " -- " ^ y ^ "\n")
    in
      Hashtbl.iter f tbl
  in
    (*end of supporting functions
     * reading the following part to understand how to process lemmas*)
  let name_and_number_of_pred = get_predicate_name iprog.I.prog_pure_pred_decl in
  let valid_of_predicate = check_valid_entail_pure pldef name_and_number_of_pred "LEMMAS" in
  if valid_of_predicate then 
    let normalize_lemma = normalize_entailpure pldef in
    let _ = print_string("lemma after normalization:\n") in
    let _ = print_string(Iprinter.string_of_pure_derive normalize_lemma) in
    let _ = print_string("\n") in
    let var_name_list = get_var_name normalize_lemma in
    let _ = print_string("Vars in Lemma \n") in
    let temp = string_of_id_list var_name_list   in
    let _ = print_string(temp) in
    let random_name_list = generate_random_list (List.length var_name_list) [] in
    let tbl = Hashtbl.create (List.length var_name_list) in
    let tbl = init_tbl tbl var_name_list random_name_list ((List.length var_name_list)-1) in
    let _ = print_id_x_id_tbl tbl in
    let new_lemma = rename_var_in_lemma normalize_lemma tbl in
    let _ = print_string("lemma after rename:\n") in
    let _ = print_string(Iprinter.string_of_pure_derive new_lemma) in
    let _ = print_string("\n") in
    let is_valid = Purelemma.is_valid_lemma new_lemma iprog.Iast.prog_pure_pred_decl in
    let _ = print_string("Valid of lemma: " ^ string_of_bool is_valid ^"\n") in
    iprog.I.prog_pure_lemma <- new_lemma :: iprog.I.prog_pure_lemma
