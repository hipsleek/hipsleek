(* Translate an input program with pointer into an intermediate 
   input program without
   @param prog current program declaration
   @return new program declaration 

   STEP 1: eliminate pointer type (e.g. int* )
   - translate pointers into objects: int* p -> integer p;
     + Translate global variables first
     + For each proc, go forward, find (param + local) and replace.

   STEP 2: eliminate address-of operator (e.g. &x )
   - Translate local vars + params that are addressed of (&x) into object
     + Pass 1: find
     + Pass 2: convert

   NOTE:
    - For local variables, can reuse the variable names
      int x -> integer x;
    - For params, to be consistent with the specification, create a new variables pointing to the param.
      + For pass-by-ref variables, need to update to the param param = ptr_param.val before deleting ptr_param

*)
open Globals
open Iast
open Gen.Basic
open Iprinter

module P = Ipure
module F = Iformula
module Err = Error
module E = Env

let ptr_target : string = "val" 

(*roughly similar to Astsimp.trans_type*)
let rec trans_type (prog : prog_decl) (t : typ) (pos : loc) : typ =
  match t with
    | Named c ->
	      (try
            let _ = look_up_data_def_raw prog.prog_data_decls c
            in Named c
	      with
	        | Not_found ->
                  (try
		            let _ = look_up_enum_def_raw prog.prog_enum_decls c
		            in Int
		          with
		            | Not_found -> (* An Hoa : cannot find the type, just keep the name. *)
                        let _ = report_warning pos ("Type " ^ c ^ " is not yet defined!") in
						Named c (* Store this temporarily *)
				  ))
    | Array (et, r) -> Array (trans_type prog et pos, r) (* An Hoa *)
    | p -> p

let default_value (t :typ) pos : exp =
  match t with
    | Int -> 
        IntLit { exp_int_lit_val = 0; exp_int_lit_pos = pos; }
    | Bool ->
	    BoolLit {exp_bool_lit_val = true;  exp_bool_lit_pos = pos;}
    | Float ->
	    FloatLit {exp_float_lit_val = 0.0; exp_float_lit_pos = pos;}
    | (TVar _) ->
	      failwith
              "default_value: typevar in variable declaration should have been rejected"
    | NUM | UNK | Void | AnnT ->
	      failwith
              "default_value: void/NUM/UNK/AnnT in variable declaration should have been rejected by parser"
    | (BagT _) ->
	      failwith "default_value: bag can only be used for constraints"
    | List _ ->
          failwith "default_value: list can only be used for constraints"
    | RelT ->
          failwith "default_value: RelT can only be used for constraints"
    | Named c -> Null pos
    | Pointer ptr -> Null pos
	| Array (t, d) ->
       failwith "default_value: Array not supported"


let string_of_ident_list vs = (pr_list (fun id ->id) vs)

let is_pointer_typ (t:typ) : bool =
  match t with
    | Pointer _ -> true
    | _ -> false

let convert_typ (t:typ) : typ =
  match t with
    | Pointer t1 -> 
        (match t1 with
          | Int -> Named "integer"
          | _ -> t1 (*TO CHECK: need to generalize for float, bool, ...*)
        )
    | _ -> t

(**
  Replace int* -> integer and other translation (STEP 1)
  @param e: expression
  @param vars: list of identifiers that need to be translated
  @return e*vars: new expression * (new list of vars that need to
   be translate)
   Note: 
   - After case_normalize_program, no more name collision on variables
   - We are interested in declarations (to update list of vars) and
   unary operations (to translate): Var, VarDecl, ConstDecl, Unary
   
**)
let trans_exp_ptr_x (e:exp) (vars: ident list) : exp * (ident list) =
  let rec helper (e:exp) (vars: ident list) : exp * (ident list)=
    (*apply helper to a list of variables*)
    let func (es,vars) e =
      let new_e,new_vars = helper e vars in
      (es@[new_e]),new_vars
    in
    let helper_list (es: exp list) (vars: ident list) = 
      List.fold_left func ([],vars) es
    in
    match e with
      | Var v -> (e,vars)
      | VarDecl v ->
          (*translate*)
          let decls = List.map (fun (id,e0,pos) ->
              match e0 with
                | None -> (id,e0,pos)
                | Some e0 ->
                    let e1,_ = helper e0 vars in
                    (id,Some e1,pos)
          ) v.exp_var_decl_decls
          in
          let new_e = VarDecl {v with exp_var_decl_decls =decls} in
          if (is_pointer_typ v.exp_var_decl_type) then
            let t = convert_typ v.exp_var_decl_type in
            let new_vars = List.map (fun (id,_,_) -> id) decls in
            (new_e,vars@new_vars)
          else
            (new_e,vars)
      | ConstDecl c ->
          (*translate*)
          let decls = List.map (fun (id,e0,pos) -> 
              let e1,_ = helper e0 vars in
              (id,e1,pos)
          ) c.exp_const_decl_decls 
          in
          let new_e = ConstDecl {c with exp_const_decl_decls =decls} in
          if (is_pointer_typ c.exp_const_decl_type) then 
            let t = convert_typ c.exp_const_decl_type in
            let new_vars = List.map (fun (id,_,_) -> id) decls in
            (new_e,vars@new_vars)
          else
            (new_e,vars)
      | Unary u ->
          (*translate*)
           let e0 = u.exp_unary_exp in
          (match u.exp_unary_op with
            | OpVal ->
                (*value-of: *p --> p.val *)
                (match e0 with
                  | Var v ->
                      let id = v.exp_var_name in
                      if (List.mem id vars) then
                      (*p.val*)
                        let e1 = Member { exp_member_base = e0;
		                                  exp_member_fields = [ptr_target];
                                          exp_member_path_id = u.exp_unary_path_id;
                                          exp_member_pos = u.exp_unary_pos}
                        in
                        (e1,vars)
                      else
                        let e0,_ = helper u.exp_unary_exp vars in
                        let new_e =  Unary {u with exp_unary_exp = e0} in
                        (new_e,vars)
                  | _ -> Error.report_error 
                      {Err.error_loc = u.exp_unary_pos;
                       Err.error_text = "Expecting Var after OpVal unary operation (*p)"})
            | OpAddr ->
                (*address-off: &p --> p *)
                (match e0 with
                  | Var v ->
                      let id = v.exp_var_name in
                      if (List.mem id vars) then
                        (u.exp_unary_exp,vars)
                      else
                        let e0,_ = helper u.exp_unary_exp vars in
                        let new_e =  Unary {u with exp_unary_exp = e0} in
                        (new_e,vars)
                  | _ -> Error.report_error 
                      {Err.error_loc = u.exp_unary_pos;
                       Err.error_text = "Expecting Var after OpAddr unary operation (*p)"})
            | _ ->
                let e0,_ = helper u.exp_unary_exp vars in
                let new_e =  Unary {u with exp_unary_exp = e0} in
                (new_e,vars)
          )
	  | ArrayAt b ->
          let new_base,_ =  helper b.exp_arrayat_array_base vars in
          let new_index,_ = helper_list b.exp_arrayat_index vars in
          let new_e = ArrayAt {b with exp_arrayat_array_base = new_base;
			  exp_arrayat_index = new_index;}
          in (new_e,vars)
	  | ArrayAlloc a ->
          let es,_ = helper_list a.exp_aalloc_dimensions vars in
          let new_e = ArrayAlloc {a with exp_aalloc_dimensions = es;} in
          (new_e,vars)
      | Assert _ -> (e,vars) (*TO CHECK: need to translate vars in the assertion*)
      | Assign a ->
          let new_lhs,_ = helper a.exp_assign_lhs vars in
          let new_rhs,_ = helper a.exp_assign_rhs vars in
          let new_e = Assign {a with exp_assign_lhs = new_lhs;
              exp_assign_rhs = new_rhs}
          in (new_e,vars)
      | Binary b ->
          let e1,_ = helper b.exp_binary_oper1 vars in
          let e2,_ = helper b.exp_binary_oper2 vars in
          let new_e = Binary {b with exp_binary_oper1 = e1;
              exp_binary_oper2 = e2;}
          in (new_e,vars)
      | Bind b ->
          (*Assuming no pointer operations in exp_bind_bound_var*)
          let new_body,_ = helper b.exp_bind_body vars in 
          let new_e = Bind {b with exp_bind_body = new_body} in
          (new_e,vars) (*bind opens another scope*)
      | Block b ->
          (*Note: no more Block after case_normalize_program*)
          let _ = print_endline ("Block: " ^ (pr_list (fun (id,_,_) -> id) b.exp_block_local_vars)) in
          (*b.exp_block_local_vars is empty until IastUtil.float_var_decl*)
          let new_body,_ = helper b.exp_block_body vars in
          let new_e = Block {b with exp_block_body = new_body} in
          (new_e,vars) (* Block creates a new inner scope *)
      | BoolLit _ -> (e,vars)
      | Break _ -> (e,vars)
      | CallRecv c ->
          let new_args,_ = helper_list c.exp_call_recv_arguments vars in
          let new_rev, _ = helper c.exp_call_recv_receiver vars in
          let new_e = CallRecv {c with exp_call_recv_arguments = new_args;
              exp_call_recv_receiver = new_rev;}
          in (new_e,vars)
      | CallNRecv c ->
          let new_args,_ = helper_list c.exp_call_nrecv_arguments vars in
          let new_e = CallNRecv {c with exp_call_nrecv_arguments = new_args} in
          (new_e,vars)
      | Cast c ->
          let new_body,_ = helper c.exp_cast_body vars in
          let new_e = Cast {c with exp_cast_body = new_body} in
          (new_e,vars)
      | Cond c ->
          let cond_e,_ = helper c.exp_cond_condition vars in
          let then_e,_ = helper c.exp_cond_then_arm vars in
          let else_e,_ = helper c.exp_cond_else_arm vars in
          let new_e = Cond {c with exp_cond_condition = cond_e;
              exp_cond_then_arm = then_e;
              exp_cond_else_arm = else_e;} in
          (new_e,vars)
      | Finally f ->
          let body,_ = helper f.exp_finally_body vars in
          let new_e = Finally {f with exp_finally_body = body} in
          (new_e,vars)
      | Label ((pid,plbl),e0) ->
          let e1,_ = helper e0 vars in
          let new_e = Label ((pid,plbl),e1) in
          (new_e,vars)
      | Member m ->
          let base,_ = helper m.exp_member_base vars in
          (*TO CHECK: pointers of struct type ??? *)
          let new_e = Member {m with exp_member_base = base} in
          (new_e,vars)
      | New n ->
          (*TO CHECK: handle malloc() ??? *)
          let args = List.map (fun e0 -> fst (helper e0 vars)) n.exp_new_arguments in
          (*Assume int* ptr = new integer(...) --> do not need 
            to change exp_new_class_name*)
          let new_e = New {n with exp_new_arguments = args} in
          (new_e,vars)
      | Try t ->
          let try_e, vars1 = helper t.exp_try_block vars in
          (*vars in try_block are still in scopes of catch_clauses
          and finally clause*)
          let catch_es = List.map (fun e0 -> fst (helper e0 vars1)) t.exp_catch_clauses in
          let finally_es = List.map (fun e0 -> fst (helper e0 vars1)) t.exp_finally_clause in
          let new_e = Try {t with exp_try_block = try_e;
              exp_catch_clauses = catch_es;
              exp_finally_clause = finally_es}
          in
          (new_e,vars)
          (*Vars donot change because it is out-of-scope of Try*)

      | Raise r -> (*Assume no pointers*)
          (e,vars)
      | Catch _ -> (*assume no pointer*)
          (e,vars)
      | Return r ->
          (match r.exp_return_val with
            | None -> (e,vars)
            | Some e0 ->
                let e1, _ = helper e0 vars in
                let new_e = Return {r with exp_return_val = Some e1} in
                (new_e, vars)
          )
      | Seq s ->
          let e1,vars1 = helper s.exp_seq_exp1 vars in
          let e2,vars2 = helper s.exp_seq_exp2 vars1 in
          let new_e =  Seq {s with exp_seq_exp1 = e1;
                            exp_seq_exp2 = e2} 
          in
          (new_e,vars2)
      | This _ -> (*assume no pointer *)
          (e,vars)
      | While w ->
          let cond, _ = helper w.exp_while_condition vars in
          let body, _ = helper w.exp_while_body vars in
          (*TO CHECK: not sure what exp_while_wrappings is for? *)
          let wrap =
            (match w.exp_while_wrappings with
              | None -> None
              | Some e0 ->
                  let e1,_ = helper e0 vars in
                  Some e1
            )
          in
          let new_e = While {w with exp_while_condition = cond;
              exp_while_body = body;
              exp_while_wrappings = wrap}
          in
          (new_e,vars)
      | Debug _
      | Dprint _
      | Empty _
      | FloatLit _
      | IntLit _
      | Java _
      | Null _
      | Time _
      | Unfold _
      | Continue _ -> (e,vars)
  in helper e vars

(*STEP 1: Translate pointers: 
  int* p --> integer p 
  p:int* -> p
  *( p:int* ) -> p.val
  &( p:int* ) -> p
*)
let trans_exp_ptr (e:exp) (vars: ident list) : exp * (ident list) =
  let pr1 ls = pr_list (fun id -> id) ls in
  let pr_out = pr_pair string_of_exp pr1 in
  Debug.ho_2 "trans_exp_ptr" string_of_exp pr1 pr_out trans_exp_ptr_x e vars

(*
  Need typ information to delete x at the end.

  STEP2: translate address_of (&x) operators
  int x --> integer x = new integer(0); ...; delete(x);
  x:int --> x.val
  &(x:int) --> x

  At the end of each scope:
  1) look_up --> addr_vars
  intersect(E.visible_names,add_vars) --> those that need to be translated
  2) translate

  RULE of THUMP:
  scope1{scope2}
  addr_vars = find_add e(scope2);
  vars_to_delete(scope2) = (vars(scope2) \diff vars(scope1)) \intesect addr_vars
*)

let compute_vars_to_delete_x addr_vars outer_vars inner_vars : ident list =
  let new_vars = Gen.BList.difference_eq (=) inner_vars outer_vars in
  Gen.BList.intersect_eq (=) new_vars addr_vars

let compute_vars_to_delete addr_vars outer_vars inner_vars : ident list =
  let pr = string_of_ident_list in
  Debug.ho_3 "compute_vars_to_delete" 
      pr pr pr pr
      compute_vars_to_delete_x addr_vars outer_vars inner_vars

let trans_exp_addr (e:exp) : exp =
  let rec helper (e:exp) (vars: ident list) : (exp) =
    match e with
      | Var { exp_var_name = v; exp_var_pos = pos } ->
          (*translate: x -> x.val*)

            if (List.mem v vars) then
            (*x.val*)
              let e1 = Member { exp_member_base = e;
		                        exp_member_fields = [ptr_target];
                                exp_member_path_id = None;
                                exp_member_pos = pos}
              in (e1)
            else
              e
      | VarDecl v ->
          (*Add variables into current scope*)
          let org_t = v.exp_var_decl_type in
          let _ = List.map (fun (v,_,_) ->
              let alpha = E.alpha_name v in
              (E.add v (E.VarInfo{
                  E.var_name = v;
                  E.var_alpha = alpha;
                  E.var_type = UNK; }))
          ) v.exp_var_decl_decls in
          let decls = List.map (fun (id,e0,pos) -> 
              let e1 = match e0 with
                | None -> None
                | Some e0 -> Some (helper e0 vars) in
              (id,e1,pos) ) v.exp_var_decl_decls 
          in
          let names = List.map (fun (id,e0,loc) -> id) decls in
          (*List of variables to convert*)
          let vs = intersect names vars in
          if (vs=[]) then (e)
          else
            let decls1,decls2 = List.partition (fun (id,_,_) -> List.mem id vs) v.exp_var_decl_decls in
            let e1 = VarDecl {v with exp_var_decl_decls = decls2} in
            (*int x --> integer x = new integer(0)*)
            let new_t = convert_typ org_t in
            let func (id,eo,pos) =
              let nm = match new_t with
                | Named id -> id
                | _ -> Error.report_error 
                      {Err.error_loc = pos;
                       Err.error_text = "Expecting (Named ident) after convert_typ"}
              in
              (* (0) *)
              let args = match eo with
                | None -> [default_value org_t pos]
                | Some e0 -> [e0]
              in
              (*new integer(0)*)
              let e0 = New {exp_new_class_name = id;
                            exp_new_arguments = args;
                            exp_new_pos = pos;}
              in
              let decl = (id,Some e0,pos) in
              (*int x --> integer x = new integer(0)*)
              let e1 = VarDecl {exp_var_decl_type = new_t;
                                exp_var_decl_decls = [decl] ;
                                exp_var_decl_pos = pos;
                               }
              in e1
            in
            let es = List.map func decls1 in
            let new_e = List.fold_left (fun e1 e2 -> mkSeq e1 e2 v.exp_var_decl_pos) e1 es in
            (new_e)
      | ConstDecl c ->
          (*Add variables into current scope*)
          let org_t = c.exp_const_decl_type in
          let _ = List.map (fun (v,_,_) ->
              let alpha = E.alpha_name v in
              (E.add v (E.VarInfo{
                  E.var_name = v;
                  E.var_alpha = alpha;
                  E.var_type = UNK; }))
          ) c.exp_const_decl_decls in
          let decls = List.map (fun (id,e0,pos) -> 
              let e1 = helper e0 vars in
              (id,e1,pos) ) c.exp_const_decl_decls 
          in
          let names = List.map (fun (id,e0,loc) -> id) decls in
          (*List of variables to convert*)
          let vs = intersect names vars in
          if (vs=[]) then (e)
          else
            let decls1,decls2 = List.partition (fun (id,_,_) -> List.mem id vs) c.exp_const_decl_decls in
            let e1 = ConstDecl {c with exp_const_decl_decls = decls2} in
            (*int x --> integer x = new integer(0)*)
            let org_t = c.exp_const_decl_type in
            let new_t = convert_typ org_t in
            let func (id,eo,pos) =
              let nm = match new_t with
                | Named id -> id
                | _ -> Error.report_error 
                    {Err.error_loc = pos;
                     Err.error_text = "Expecting (Named ident) after convert_typ"}
              in
              (* (0) *)
              let args = [eo] in
              let e0 = New {exp_new_class_name = id;
                            exp_new_arguments = args;
                            exp_new_pos = pos;}
              in
              let decl = (id,e0,pos) in
              (*int x --> integer x = new integer(0)*)
              let e1 = ConstDecl {exp_const_decl_type = new_t;
                                exp_const_decl_decls = [decl] ;
                                exp_const_decl_pos = pos;
                               }
              in e1
            in
            let es = List.map func decls1 in
            let new_e = List.fold_left (fun e1 e2 -> mkSeq e1 e2 c.exp_const_decl_pos) e1 es in
            (new_e)
      | Unary u ->
          (*translate*)
          let e0 = u.exp_unary_exp in
          (match u.exp_unary_op with
            | OpVal ->
                (*value-of: *p --> p.val *)
                (*This may not happen because we have already 
                  convert *p -> p.val in trans_exp_ptr*)
                (match e0 with
                  | Var v ->
                      let id = v.exp_var_name in
                      if (List.mem id vars) then
                        (*p.val*)
                        let e1 = Member { exp_member_base = e0;
		                                  exp_member_fields = [ptr_target];
                                          exp_member_path_id = u.exp_unary_path_id;
                                          exp_member_pos = u.exp_unary_pos}
                        in
                        (e1)
                      else
                        let e0 = helper u.exp_unary_exp vars in
                        let new_e =  Unary {u with exp_unary_exp = e0} in
                        (new_e)
                  | _ -> Error.report_error 
                      {Err.error_loc = u.exp_unary_pos;
                       Err.error_text = "Expecting Var after OpVal unary operation (*p)"})
            | OpAddr ->
                (*address-off: &p --> p *)
                (match e0 with
                  | Var v ->
                      let id = v.exp_var_name in
                      if (List.mem id vars) then
                        (u.exp_unary_exp)
                      else
                        let e0 = helper u.exp_unary_exp vars in
                        let new_e =  Unary {u with exp_unary_exp = e0} in
                        (new_e)
                  | _ -> Error.report_error 
                      {Err.error_loc = u.exp_unary_pos;
                       Err.error_text = "Expecting Var after OpAddr unary operation (*p)"})
            | _ ->
                let e0 = helper u.exp_unary_exp vars in
                let new_e =  Unary {u with exp_unary_exp = e0} in
                (new_e)
          )
	  | ArrayAt b ->
          let new_base =  helper b.exp_arrayat_array_base vars in
          let new_index = List.map (fun e -> helper e vars) b.exp_arrayat_index in
          let new_e = ArrayAt {b with exp_arrayat_array_base = new_base;
			  exp_arrayat_index = new_index;}
          in (new_e)
	  | ArrayAlloc a ->
          let es = List.map (fun e -> helper e vars) a.exp_aalloc_dimensions in
          let new_e = ArrayAlloc {a with exp_aalloc_dimensions = es;} in
          (new_e)
      | Assert _ -> (e)
      | Assign a ->
          let new_lhs = helper a.exp_assign_lhs vars in
          let new_rhs = helper a.exp_assign_rhs vars in
          let new_e = Assign {a with exp_assign_lhs = new_lhs;
              exp_assign_rhs = new_rhs}
          in (new_e)
      | Binary b ->
          let e1 = helper b.exp_binary_oper1 vars in
          let e2 = helper b.exp_binary_oper2 vars in
          let new_e = Binary {b with exp_binary_oper1 = e1;
              exp_binary_oper2 = e2;}
          in (new_e)
      | Bind b ->
          (*scoping*)
          let _,outer_vars = List.split (E.visible_names ()) in
          let addr_vars = find_addr b.exp_bind_body in
          let _ = E.push_scope () in
          let _ = List.map (fun v -> 
              let alpha = E.alpha_name v in
              E.add v (E.VarInfo{
                  E.var_name = v;
                  E.var_alpha = alpha;
                  E.var_type = UNK;})) b.exp_bind_fields in
          (*Assuming no pointer operations in exp_bind_bound_var*)
          let new_body = helper b.exp_bind_body vars in
          (*scoping*)
          let _,inner_vars = List.split (E.visible_names ()) in
          let del_vars = compute_vars_to_delete addr_vars outer_vars inner_vars in
          let _ = E.pop_scope ()in
          let new_e = Bind {b with exp_bind_body = new_body} in
          (new_e)
      | Block b ->
          (*Note: no more Block after case_normalize_program*)
          let _ = print_endline ("Warning: unexpected Block: no more Block after case_normalize_program") in
          (*b.exp_block_local_vars is empty until IastUtil.float_var_decl*)
          let _ = E.push_scope () in
          let new_body = helper b.exp_block_body vars in
          let _ = E.pop_scope ()in
          let new_e = Block {b with exp_block_body = new_body} in
          (new_e) (* Block creates a new inner scope *)
      | BoolLit _ -> e
      | Break _ -> e
      | CallRecv c ->
          let new_args = List.map (fun e -> helper e vars) c.exp_call_recv_arguments in
          let new_rev = helper c.exp_call_recv_receiver vars in
          let new_e = CallRecv {c with exp_call_recv_arguments = new_args;
              exp_call_recv_receiver = new_rev;}
          in (new_e)
      | CallNRecv c ->
          let new_args = List.map (fun e -> helper e vars) c.exp_call_nrecv_arguments in
          let new_e = CallNRecv {c with exp_call_nrecv_arguments = new_args} in
          (new_e)
      | Cast c ->
          let new_body = helper c.exp_cast_body vars in
          let new_e = Cast {c with exp_cast_body = new_body} in
          (new_e)
      | Cond c ->
          (*scope ???*)
          let cond_e = helper c.exp_cond_condition vars in
          (*then branch*)
          let _ = E.push_scope () in
          let then_e = helper c.exp_cond_then_arm vars in
          let _ = E.pop_scope ()in
          (*else branch*)
          let _ = E.push_scope () in
          let else_e = helper c.exp_cond_else_arm vars in
          let _ = E.push_scope () in
          let new_e = Cond {c with 
              exp_cond_condition = cond_e;
              exp_cond_then_arm = then_e;
              exp_cond_else_arm = else_e;} in
          (new_e)
      | Finally f ->
          (*assume no pointers*)
          let body = helper f.exp_finally_body vars in
          let new_e = Finally {f with exp_finally_body = body} in
          (new_e)
      | Label ((pid,plbl),e0) ->
          let e1 = helper e0 vars in
          let new_e = Label ((pid,plbl),e1) in
          (new_e)
      | Member m ->
          let base = helper m.exp_member_base vars in
          (*TO CHECK: pointers of struct type ??? *)
          let new_e = Member {m with exp_member_base = base} in
          (new_e)
      | New n ->
          (*TO CHECK: handle malloc() ??? *)
          let args = List.map (fun e0 -> helper e0 vars) n.exp_new_arguments in
          (*Assume int* ptr = new integer(...) --> do not need 
            to change exp_new_class_name*)
          let new_e = New {n with exp_new_arguments = args} in
          (new_e)
      | Try t ->
          (*Assume no pointers*)
          (*Scoping*)
          let try_e = helper t.exp_try_block vars in
          (*vars in try_block are still in scopes of catch_clauses
          and finally clause*)
          let catch_es = List.map (fun e0 -> helper e0 vars) t.exp_catch_clauses in
          let finally_es = List.map (fun e0 -> helper e0 vars) t.exp_finally_clause in
          let new_e = Try {t with exp_try_block = try_e;
              exp_catch_clauses = catch_es;
              exp_finally_clause = finally_es}
          in
          (new_e)
          (*Vars donot change because it is out-of-scope of Try*)
      | Raise r -> (*Assume no pointers*)
          e
      | Catch _ -> (*assume no pointer*)
          (*scoping ??? *)
          e
      | Return r ->
          (match r.exp_return_val with
            | None -> (e)
            | Some e0 ->
                let e1 = helper e0 vars in
                let new_e = Return {r with exp_return_val = Some e1} in
                (new_e)
          )
      | Seq s ->
          let e1 = helper s.exp_seq_exp1 vars in
          let e2 = helper s.exp_seq_exp2 vars in
          let new_e =  Seq {s with exp_seq_exp1 = e1;
                            exp_seq_exp2 = e2} 
          in
          (new_e)

      | This _ -> (*assume no pointer *)
          e
      | While w ->
          let cond = helper w.exp_while_condition vars in
          let _ = E.push_scope () in
          let body = helper w.exp_while_body vars in
          let _ = E.pop_scope ()in
          (*TO CHECK: not sure what exp_while_wrappings is for? *)
          let wrap =
            (match w.exp_while_wrappings with
              | None -> None
              | Some e0 ->
                  let e1 = helper e0 vars in
                  Some e1
            )
          in
          let new_e = While {w with exp_while_condition = cond;
              exp_while_body = body;
              exp_while_wrappings = wrap}
          in
          (new_e)
      | Debug _
      | Dprint _
      | Empty _
      | FloatLit _
      | IntLit _
      | Java _
      | Null _
      | Time _
      | Unfold _
      | Continue _ -> e
  in 
  let _ = helper e [] in
  e

(*Find a list of variables with address_of &x*)
let find_addr (e:exp) : ident list =
  let rec helper e =
    match e with
      | Var v -> []
      | VarDecl v ->
          let vars = List.map (fun (id,e0,pos) ->
              match e0 with
                | None -> []
                | Some e0 -> helper e0
          ) v.exp_var_decl_decls
          in
          let vars = List.concat vars in
          vars
      | ConstDecl c ->
          let vars = List.map (fun (id,e0,pos) -> helper e0) c.exp_const_decl_decls in
          let vars = List.concat vars in
          vars
      | Unary u ->
          (*translate*)
          let _ = print_endline ("Unary operations" ^ (string_of_exp e)) in
          (match u.exp_unary_op with
            | OpAddr -> 
                let e0 = u.exp_unary_exp in
                (match e0 with
                  | Var v -> [v.exp_var_name] (*FOUND*)
                  | _ -> Error.report_error 
                      {Err.error_loc = u.exp_unary_pos;
                       Err.error_text = "Expecting Var after OpVal unary operation (*p)"}
                )
            | _ -> []
          )
	  | ArrayAt b ->
          let vars1 =  helper b.exp_arrayat_array_base in
          let vars2 = List.concat (List.map helper b.exp_arrayat_index) in
          (vars1@vars2)
	  | ArrayAlloc a ->
          let vars = List.concat (List.map helper a.exp_aalloc_dimensions) in
          vars
      | Assert _ -> []
      | Assign a ->
          let vs1 = helper a.exp_assign_lhs in
          let vs2 = helper a.exp_assign_rhs in
          (vs1@vs2)
      | Binary b ->
          let vs1 = helper b.exp_binary_oper1 in
          let vs2 = helper b.exp_binary_oper2 in
          (vs1@vs2)
      | Bind b ->
          let vs = helper b.exp_bind_body in 
          vs
      | Block b ->
          (*Note: no more Block after case_normalize_program*)
          let vs = helper b.exp_block_body in
          vs
      | BoolLit _ -> []
      | Break _ -> []
      | CallRecv c ->
          let vs1 = List.concat (List.map helper c.exp_call_recv_arguments) in
          let vs2 = helper c.exp_call_recv_receiver in
          (vs1@vs2)
      | CallNRecv c ->
          let vs = List.concat (List.map helper c.exp_call_nrecv_arguments) in
          vs
      | Cast c ->
          let vs = helper c.exp_cast_body in
          vs
      | Cond c ->
          let vs1 = helper c.exp_cond_condition in
          let vs2 = helper c.exp_cond_then_arm in
          let vs3 = helper c.exp_cond_else_arm in
          (vs1@vs2@vs3)
      | Finally f ->
          let vs = helper f.exp_finally_body in
          vs
      | Label ((pid,plbl),e0) ->
          let vs = helper e0 in
          vs
      | Member m ->
          let vs = helper m.exp_member_base in
          (*TO CHECK: pointers of struct type ??? *)
          vs
      | New n ->
          let vs = List.concat (List.map helper n.exp_new_arguments) in
          vs
      | Try t ->
          let vs1 = helper t.exp_try_block in
          (*vars in try_block are still in scopes of catch_clauses
            and finally clause*)
          let vs2 = List.concat (List.map helper t.exp_catch_clauses) in
          let vs3 = List.concat (List.map helper t.exp_finally_clause) in
          (vs1@vs2@vs3)
      | Raise r -> (*Assume no pointers*)
          []
      | Catch _ -> (*assume no pointer*)
          []
      | Return r ->
          (match r.exp_return_val with
            | None -> []
            | Some e0 ->
                let vs = helper e0 in
                vs
          )
      | Seq s ->
          let vs1 = helper s.exp_seq_exp1 in
          let vs2 = helper s.exp_seq_exp2 in
          (vs1@vs2)
      | This _ -> (*assume no pointer *)
          []
      | While w ->
          let vs1 = helper w.exp_while_condition in
          let vs2 = helper w.exp_while_body in
          (*TO CHECK: not sure what exp_while_wrappings is for? *)
          let vs3 =
            (match w.exp_while_wrappings with
              | None -> []
              | Some e0 ->
                  helper e0
            )
          in
          (vs1@vs2@vs3)
      | Debug _
      | Dprint _
      | Empty _
      | FloatLit _
      | IntLit _
      | Java _
      | Null _
      | Time _
      | Unfold _
      | Continue _ -> []
  in helper e
  

let trans_global_var_decl (decl:exp_var_decl) : exp_var_decl =
  let t = decl.exp_var_decl_type in
  let new_t = convert_typ t in
  {decl with exp_var_decl_type = new_t}

let trans_param (p:param) : param =
  let t = p.param_type in
  let new_t = convert_typ t in
  {p with param_type = new_t}

let trans_proc_decl prog (proc:proc_decl) : proc_decl =
  let ret_t = proc.proc_return in
  let new_ret_t = convert_typ ret_t in
  let params = proc.proc_args in
  let new_params = List.map trans_param params in
  (*List of params (typ*ident) that has been changed*)
  let func p = 
    let t = p.param_type in 
    (match t with
      | Pointer _ -> true
      | _ -> false)
  in
  (*params whose type has been changed*)
  let vars = List.filter func params in
  (*Keep track of names of changed params*)
  let vars = List.map (fun v -> v.param_name) vars in
  let new_body = match proc.proc_body with
    | None -> None
    | Some e -> 
        let e1,_ = trans_exp_ptr e vars in
        (*Similar to Astsimp.trans_proc*)
        let _ = E.push_scope () in
        let all_args = 
          if Gen.is_some proc.proc_data_decl then
            (let cdef = Gen.unsome proc.proc_data_decl in
             let this_arg ={
                 param_type = Named cdef.data_name;
                 param_name = this;
                 param_mod = NoMod;
                 param_loc = proc.proc_loc;} in 
             this_arg :: proc.proc_args)
          else proc.proc_args in
        let p2v (p : param) = {
            E.var_name = p.param_name;
            E.var_alpha = p.param_name;
            E.var_type = p.param_type; } in
        let vinfos = List.map p2v all_args in
        let _ = List.map (fun v -> E.add v.E.var_name (E.VarInfo v)) vinfos in
        (*vs contains variables that are taken adrress-of in e1*)
        let addr_vars = find_addr e1 in
        let _ = print_endline ("vs = " ^ (string_of_ident_list addr_vars)) in
        let e2 = trans_exp_addr e1 in
        let _,inner_vars = List.split (E.visible_names ()) in
        (*those that were converted and need to be deleted*)
        let vars = compute_vars_to_del addr_vars [] inner_vars in
        let _ = print_endline ("vars = " ^ (string_of_ident_list vars)) in
        let _ = E.pop_scope () in
        Some e2
  in
  {proc with proc_return  = new_ret_t;
      proc_args = new_params;
      proc_body = new_body}

let trans_pointers_x (prog : prog_decl) : prog_decl =
  let gvar_decls = prog.prog_global_var_decls in
  let new_gvar_decls = List.map trans_global_var_decl gvar_decls in
  let procs = prog.prog_proc_decls in
  let new_procs = List.map (trans_proc_decl prog) prog.prog_proc_decls in
  {prog with prog_global_var_decls = new_gvar_decls;
             prog_proc_decls = new_procs;}

let trans_pointers (prog : prog_decl) : prog_decl =
  (* let pr x = (pr_list string_of_global_var_decl) x.Iast.prog_global_var_decls in *)
  let pr x = (string_of_program x) in
  Debug.no_1 "trans_pointers" pr pr trans_pointers_x prog
