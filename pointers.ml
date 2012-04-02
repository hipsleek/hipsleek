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

   Release notes: currently, assume no pointers inside try..catch..finally blocks

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
let ptr_delete : string = "delete" 
let ptr_string : string = "ptr"

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

let string_of_subst (subst: (ident*ident) list) : string =
  pr_list (pr_pair pr_id pr_id) subst

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

let convert_prim_to_obj (t:typ) : typ =
  (match t with
    | Int -> Named "integer"
    | _ -> t (*TO CHECK: need to generalize for float, bool, ...*)
  )

let subst_var (v:ident) (subst:(ident*ident) list) : ident =
  let rec helper subst =
    match subst with
      | [] -> v
      | (fr,t)::xs ->
          if (fr=v) then t
          else helper xs
  in helper subst

(*Find a list of free variables accessed in expression e*)
(*ArrayAt, ArrayAlloc, Bind, Raise,catch -> access var
  VarDecl,ConstDecl -> bound var
*)

(*
  @param expression e
  @param list of bound variables bvars
  @return list of NEW bound variables bvars * list of free vars

  ASSUME: no name clashes among scopes
*)
and modifies (e:exp) (bvars:ident list) : (ident list) * (ident list) =
  let rec helper e bvars =
    match e with
      | Var v -> 
          let id = v.exp_var_name in
          if (List.mem id bvars) then
            (bvars,[]) (*access to variables*)
          else
            (bvars,[id])
      | VarDecl v ->
          let vars = List.map (fun (id,e0,pos) -> id) v.exp_var_decl_decls in
          let new_bvars = vars@bvars in
          (* let _ = print_endline ("new_bvars = " ^ (string_of_ident_list new_bvars)) in *)
          (new_bvars,[])
      | ConstDecl c ->
          let vars = List.map (fun (id,e0,pos) -> id) c.exp_const_decl_decls in
          let new_bvars = vars@bvars in
          (new_bvars,[])
      | Unary u ->
          let _,fvars = helper u.exp_unary_exp bvars in
          (bvars,fvars)
	  | ArrayAt b ->
          let _,fvars1 =  helper b.exp_arrayat_array_base bvars in
          let _,fvars_l = List.split (List.map (fun e -> helper e bvars) b.exp_arrayat_index) in
          let fvars2 = List.concat fvars_l in
          (bvars,fvars1@fvars2)
	  | ArrayAlloc a ->
          let _, fvars_l = List.split (List.map (fun e -> helper e bvars) a.exp_aalloc_dimensions) in
          let fvars = List.concat fvars_l in
          let a = a.exp_aalloc_etype_name in
          (bvars,a::fvars)
      | Assert _ -> (bvars,[])
      | Assign a ->
          let _,fvars1 = helper a.exp_assign_lhs bvars in
          let _,fvars2 = helper a.exp_assign_rhs bvars in
          (bvars,fvars1@fvars2)
      | Binary b ->
          let _,fvars1 = helper b.exp_binary_oper1 bvars in
          let _,fvars2 = helper b.exp_binary_oper2 bvars in
          (bvars,fvars1@fvars2)
      | Bind b ->
          let fvar = b.exp_bind_bound_var in
          let fvars1 = if (List.mem fvar bvars) then [] else [fvar] in
          let new_bvars = bvars@b.exp_bind_fields in
          let _,fvars = helper b.exp_bind_body new_bvars in
          (bvars,fvars1@fvars)
      | Block b ->
          (*Note: no more Block after case_normalize_program*)
          let bvars1,fvars = helper b.exp_block_body bvars in
          (bvars1,fvars)
      | BoolLit _ -> (bvars,[])
      | Break _ -> (bvars,[])
      | CallRecv c ->
          (*ignore exp_call_recv_method*)
          let _,fvars_l = List.split (List.map (fun e -> helper e bvars) c.exp_call_recv_arguments) in
          let fvars1 = List.concat fvars_l in
          let _,fvars2 = helper c.exp_call_recv_receiver bvars in
          (bvars,fvars1@fvars2)
      | CallNRecv c ->
          (*ignore exp_call_nrecv_method*)
          let _,fvars_l = List.split (List.map (fun e -> helper e bvars) c.exp_call_nrecv_arguments) in
          let fvars = List.concat fvars_l in
          (bvars,fvars)
      | Cast c ->
          let _,fvars = helper c.exp_cast_body bvars in
          (bvars,fvars)
      | Cond c ->
          let _,fvars1 = helper c.exp_cond_condition bvars in
          let _,fvars2 = helper c.exp_cond_then_arm bvars in
          let _,fvars3 = helper c.exp_cond_else_arm bvars in
          (bvars,fvars1@fvars2@fvars3)
      | Finally f ->
          let _,fvars = helper f.exp_finally_body bvars in
          (bvars,fvars)
      | Label ((pid,plbl),e0) ->
          let bvars1,fvars = helper e0 bvars in
          (bvars1,fvars)
      | Member m ->
          let _,fvars = helper m.exp_member_base bvars in
          (bvars,fvars)
      | New n ->
          let _,fvars_l = List.split (List.map (fun e -> helper e bvars) n.exp_new_arguments) in
          let fvars = List.concat fvars_l in
          (bvars,fvars)
      | Try t ->
          let bvars1,fvars1 = helper t.exp_try_block bvars in
          (*vars in try_block are still in scopes of catch_clauses
            and finally clause*)
          let _,fvars2_l = List.split (List.map (fun e -> helper e bvars1) t.exp_catch_clauses) in
          let _,fvars3_l = List.split (List.map (fun e -> helper e bvars1) t.exp_finally_clause) in
          let fvars2 = List.concat fvars2_l in
          let fvars3 = List.concat fvars3_l in
          (bvars1,fvars1@fvars2@fvars3)
      | Raise r -> (*Assume no pointers*)
          let _,fvars = match r.exp_raise_val with
            | None -> (bvars,[])
            | Some e ->
                helper e bvars
          in
          (bvars,fvars)
      | Catch c -> (*assume no pointer*)
          let fvars = match c.exp_catch_var with
            | None -> []
            | Some v ->
                if List.mem v bvars then [] else [v]
          in
          (bvars,fvars)
      | Return r ->
          let fvars = 
            (match r.exp_return_val with
              | None -> []
              | Some e0 ->
                  let _,vs = helper e0 bvars in
                  vs
            )
          in
          (bvars,fvars)
      | Seq s ->
          let bvars1,fvars1 = helper s.exp_seq_exp1 bvars in
          let bvars2,fvars2 = helper s.exp_seq_exp2 bvars1 in
          (bvars2,fvars1@fvars2)
      | This _ -> (*assume no pointer *)
          (bvars,[])
      | While w ->
          let _,fvars1 = helper w.exp_while_condition bvars in
          let _,fvars2 = helper w.exp_while_body bvars in
          (*TO CHECK: not sure what exp_while_wrappings is for? *)
          let fvars3 =
            (match w.exp_while_wrappings with
              | None -> []
              | Some e0 ->
                  let _,vs =  (helper e0 bvars) in
                  vs
            )
          in
          (bvars,fvars1@fvars2@fvars3)
      | Debug _
      | Dprint _
      | Empty _
      | FloatLit _
      | IntLit _
      | Java _
      | Null _
      | Time _
      | Unfold _
      | Continue _ -> (bvars,[])
  in helper e bvars

(*substitute variables [from,to] *)
let subst_exp_x (e:exp) (subst:(ident*ident) list): exp =
  let rec helper (e:exp) (subst: (ident*ident) list) : (exp) =
    match e with
      | Var v ->
          let id = subst_var v.exp_var_name subst  in
          let new_e = Var {v with exp_var_name = id} in
          (new_e)
      | VarDecl v ->
          let decls = List.map (fun (id,e0,pos) -> 
              let e1 = match e0 with
                | None -> None
                | Some e0 -> 
                    let e1 = helper e0 subst in
                    Some e1 in
              (id,e1,pos) ) v.exp_var_decl_decls 
          in
          let new_e = VarDecl {v with exp_var_decl_decls = decls} in
          (new_e)
      | ConstDecl c ->
          let decls = List.map (fun (id,e0,pos) -> 
              let e1 = helper e0 subst in
              (id,e1,pos) ) c.exp_const_decl_decls 
          in
          let new_e = ConstDecl {c with exp_const_decl_decls = decls} in
          (new_e)
      | Unary u ->
          (*translate*)
          let e0 = helper u.exp_unary_exp subst in
          let new_e = Unary {u with exp_unary_exp = e0} in
          (new_e)
	  | ArrayAt b ->
          let new_base =  helper b.exp_arrayat_array_base subst in
          let new_index = List.map (fun e -> helper e subst) b.exp_arrayat_index in
          let new_e = ArrayAt {b with exp_arrayat_array_base = new_base;
			  exp_arrayat_index = new_index;}
          in (new_e)
	  | ArrayAlloc a ->
          let es = List.map (fun e -> helper e subst) a.exp_aalloc_dimensions in
          let new_e = ArrayAlloc {a with exp_aalloc_dimensions = es;} in
          (new_e)
      | Assert _ -> (e) (*TO CHECK: need to rename formula after assert*)
      | Assign a ->
          let new_lhs = helper a.exp_assign_lhs subst in
          let new_rhs = helper a.exp_assign_rhs subst in
          let new_e = Assign {a with exp_assign_lhs = new_lhs;
              exp_assign_rhs = new_rhs}
          in (new_e)
      | Binary b ->
          let e1 = helper b.exp_binary_oper1 subst in
          let e2 = helper b.exp_binary_oper2 subst in
          let new_e = Binary {b with exp_binary_oper1 = e1;
              exp_binary_oper2 = e2;}
          in (new_e)
      | Bind b ->
          let bound_var = subst_var b.exp_bind_bound_var subst in
          let new_body = helper b.exp_bind_body subst in
          let new_e = Bind {b with exp_bind_bound_var = bound_var; 
              exp_bind_body = new_body} 
          in
          (new_e)
      | Block b ->
          let vars = List.map (fun (id,t,pos) -> 
              let new_id = subst_var id subst in
              (new_id,t,pos)) b.exp_block_local_vars in
          let new_body = helper b.exp_block_body subst in
          let new_e = Block {b with exp_block_local_vars = vars;
              exp_block_body = new_body} 
          in
          (new_e) (* Block creates a new inner scope *)
      | BoolLit _ -> e
      | Break _ -> e
      | CallRecv c ->
          let new_args = List.map (fun e -> helper e subst) c.exp_call_recv_arguments in
          let new_rev = helper c.exp_call_recv_receiver subst in
          let new_e = CallRecv {c with exp_call_recv_arguments = new_args;
              exp_call_recv_receiver = new_rev;}
          in (new_e)
      | CallNRecv c ->
          let new_args = List.map (fun e -> helper e subst) c.exp_call_nrecv_arguments in
          let new_e = CallNRecv {c with exp_call_nrecv_arguments = new_args} in
          (new_e)
      | Cast c ->
          let new_body = helper c.exp_cast_body subst in
          let new_e = Cast {c with exp_cast_body = new_body} in
          (new_e)
      | Cond c ->
          let cond_e = helper c.exp_cond_condition subst in
          let then_e = helper c.exp_cond_then_arm subst in
          let else_e = helper c.exp_cond_else_arm subst in
          let new_e = Cond {c with 
              exp_cond_condition = cond_e;
              exp_cond_then_arm = then_e;
              exp_cond_else_arm = else_e;} in
          (new_e)
      | Finally f ->
          (*assume no pointers*)
          let body = helper f.exp_finally_body subst in
          let new_e = Finally {f with exp_finally_body = body} in
          (new_e)
      | Label ((pid,plbl),e0) ->
          let e1 = helper e0 subst in
          let new_e = Label ((pid,plbl),e1) in
          (new_e)
      | Member m ->
          let base = helper m.exp_member_base subst in
          let new_e = Member {m with exp_member_base = base} in
          (new_e)
      | New n ->
          let args = List.map (fun e0 -> helper e0 subst) n.exp_new_arguments in
          let new_e = New {n with exp_new_arguments = args} in
          (new_e)
      | Try t ->
          let try_e = helper t.exp_try_block subst in
          let catch_es = List.map (fun e0 -> helper e0 subst) t.exp_catch_clauses in
          let finally_es = List.map (fun e0 -> helper e0 subst) t.exp_finally_clause in
          let new_e = Try {t with exp_try_block = try_e;
              exp_catch_clauses = catch_es;
              exp_finally_clause = finally_es}
          in
          (new_e)
      | Raise r ->
          (match r.exp_raise_val with
            | None -> e
            | Some e0 ->
                let e1 = helper e0 subst in
                let new_e = Raise {r with exp_raise_val = Some e1} in
                (new_e))
      | Catch c -> 
          (match c.exp_catch_var,c.exp_catch_flow_var with
            | None,None -> e
            | None, Some id0 ->
                let id1 =  subst_var id0 subst in
                let new_e = Catch {c with exp_catch_flow_var = Some id1} in
                (new_e)
            | Some id0, None ->
                let id1 = subst_var id0 subst in
                let new_e = Catch {c with exp_catch_var = Some id1} in
                (new_e)
            | Some e0,Some e1 ->
                let e01 = subst_var e0 subst in
                let e11 = subst_var e1 subst in
                let new_e = Catch {c with exp_catch_var = Some e11; exp_catch_flow_var = Some e01} in
                (new_e))
      | Return r ->
          (match r.exp_return_val with
            | None -> (e)
            | Some e0 ->
                let e1 = helper e0 subst in
                let new_e = Return {r with exp_return_val = Some e1} in
                (new_e)
          )
      | Seq s ->
          let e1 = helper s.exp_seq_exp1 subst in
          let e2 = helper s.exp_seq_exp2 subst in
          let new_e =  Seq {s with exp_seq_exp1 = e1;
                            exp_seq_exp2 = e2} 
          in
          (new_e)
      | This _ -> (*assume no pointer *)
          e
      | While w ->
          let cond = helper w.exp_while_condition subst in
          let body = helper w.exp_while_body subst in
          (*TO CHECK: not sure what exp_while_wrappings is for? *)
          let wrap =
            (match w.exp_while_wrappings with
              | None -> None
              | Some e0 ->
                  let e1 = helper e0 subst in
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
  in helper e subst

let subst_exp (e:exp) (subst:(ident*ident) list): exp =
  Debug.no_2 "subst_exp"
      string_of_exp string_of_subst string_of_exp
      subst_exp_x e subst

  

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
          if (is_pointer_typ v.exp_var_decl_type) then
            let t = convert_typ v.exp_var_decl_type in
            let new_e = VarDecl {v with exp_var_decl_type = t;
                exp_var_decl_decls =decls} 
            in
            let new_vars = List.map (fun (id,_,_) -> id) decls in
            (new_e,vars@new_vars)
          else
            let new_e = VarDecl {v with exp_var_decl_decls =decls} in
            (new_e,vars)
      | ConstDecl c ->
          (*translate*)
          let decls = List.map (fun (id,e0,pos) -> 
              let e1,_ = helper e0 vars in
              (id,e1,pos)
          ) c.exp_const_decl_decls 
          in
          if (is_pointer_typ c.exp_const_decl_type) then 
            let t = convert_typ c.exp_const_decl_type in
            let new_e = ConstDecl {c with exp_const_decl_type = t;
                exp_const_decl_decls =decls}
            in
            let new_vars = List.map (fun (id,_,_) -> id) decls in
            (new_e,vars@new_vars)
          else
            let new_e = ConstDecl {c with exp_const_decl_decls =decls} in
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
  Debug.no_2 "trans_exp_ptr" string_of_exp pr1 pr_out trans_exp_ptr_x e vars

let mkDelete (var:ident) pos =
  let arg = Var {exp_var_name =var; exp_var_pos = pos} in
  let args = [arg] in
  CallNRecv {
      exp_call_nrecv_method = ptr_delete;
      exp_call_nrecv_lock = None;
      exp_call_nrecv_arguments = args;
      exp_call_nrecv_path_id = None;
      exp_call_nrecv_pos = pos;}

(*
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
  Debug.no_3 "compute_vars_to_delete" 
      pr pr pr pr
      compute_vars_to_delete_x addr_vars outer_vars inner_vars

(*
  @trans_exp_addr
  Need typ information to delete x at the end.

  STEP2: translate address_of (&x) operators
  int x --> integer x = new integer(0); ...; delete(x);
  x:int --> x.val
  &(x:int) --> x

  At the end of each scope:
  1) look_up --> addr_vars
  intersect(E.visible_names,add_vars) --> those that need to be translated
  2) translate

*)
let rec trans_exp_addr (e:exp) (vars: ident list) : exp =
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
                | Some e0 -> 
                    let e1 = helper e0 vars in
                    Some e1 in
              (id,e1,pos) ) v.exp_var_decl_decls 
          in
          let names = List.map (fun (id,e0,loc) -> id) decls in
          (*List of variables to convert*)
          let vs = intersect names vars in
          if (vs=[]) then 
            let new_e = VarDecl {v with exp_var_decl_decls = decls} in
            new_e
          else
            let decls1,decls2 = List.partition (fun (id,_,_) -> List.mem id vs) decls in
            let e1 = if (decls2!=[]) then 
                  VarDecl {v with exp_var_decl_decls = decls2} 
                else (Empty v.exp_var_decl_pos)
            in
            (*int x --> integer x = new integer(0)*)
            let new_t = convert_prim_to_obj org_t in
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
              let e0 = New {exp_new_class_name = nm;
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
          if (vs=[]) then 
            let new_e = ConstDecl {c with exp_const_decl_decls = decls} in
            new_e
          else
            let decls1,decls2 = List.partition (fun (id,_,_) -> List.mem id vs) decls in
            let e1 = if (decls2!=[]) then 
                  ConstDecl {c with exp_const_decl_decls = decls2}
                else (Empty c.exp_const_decl_pos)
            in
            (*int x --> integer x = new integer(0)*)
            let org_t = c.exp_const_decl_type in
            let new_t = convert_prim_to_obj org_t in
            let func (id,eo,pos) =
              let nm = match new_t with
                | Named id -> id
                | _ -> Error.report_error
                    {Err.error_loc = pos;
                     Err.error_text = "Expecting (Named ident) after convert_typ"}
              in
              (* (0) *)
              let args = [eo] in
              let e0 = New {exp_new_class_name = nm;
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
          (*addr vars of the inner scope*)
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
          (**********************>>>***********************)
          (*scoping*)
          let _,inner_vars = List.split (E.visible_names ()) in
          let del_vars = compute_vars_to_delete addr_vars outer_vars inner_vars in
          let new_body2 = List.fold_left (fun e var ->
              let del_e = mkDelete var no_pos in
              mkSeq e del_e no_pos) new_body del_vars
          in
          (**********************<<<***********************)
          let _ = E.pop_scope ()in
          let new_e = Bind {b with exp_bind_body = new_body2} in
          (new_e)
      | Block b ->
          (*Note: no more Block after case_normalize_program*)
          let _ = print_endline ("Warning: unexpected Block: no more Block after case_normalize_program") in
          (*b.exp_block_local_vars is empty until IastUtil.float_var_decl*)
          let _,outer_vars = List.split (E.visible_names ()) in
          (*addr vars of the inner scope*)
          let addr_vars = find_addr b.exp_block_body in
          let _ = E.push_scope () in
          let new_body = helper b.exp_block_body vars in
          (********************>>>*************************)
          let _,inner_vars = List.split (E.visible_names ()) in
          let del_vars = compute_vars_to_delete addr_vars outer_vars inner_vars in
          let new_body = List.fold_left (fun e var ->
              let del_e = mkDelete var no_pos in
              mkSeq e del_e no_pos) new_body del_vars
          in
          (***********************<<<**********************)
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
          (*scoping*)
          let _,outer_vars = List.split (E.visible_names ()) in
          let cond_e = helper c.exp_cond_condition vars in
          (*then branch*)
          (*addr vars of then branch*)
          let then_addr_vars = find_addr c.exp_cond_then_arm in
          let _ = E.push_scope () in
          let then_e = helper c.exp_cond_then_arm vars in
          (******************>>>**************************)
          let _,then_inner_vars = List.split (E.visible_names ()) in
          let del_vars = compute_vars_to_delete then_addr_vars outer_vars then_inner_vars in
          let then_e = List.fold_left (fun e var ->
              let del_e = mkDelete var no_pos in
              mkSeq e del_e no_pos) then_e del_vars
          in
          (*******************<<<**************************)
          let _ = E.pop_scope ()in
          (*else branch*)
          let else_addr_vars = find_addr c.exp_cond_else_arm in
          let _ = E.push_scope () in
          let else_e = helper c.exp_cond_else_arm vars in
          (*******************>>>**************************)
          let _,else_inner_vars = List.split (E.visible_names ()) in
          let del_vars = compute_vars_to_delete else_addr_vars outer_vars else_inner_vars in
          let else_e = List.fold_left (fun e var ->
              let del_e = mkDelete var no_pos in
              mkSeq e del_e no_pos) else_e del_vars
          in
          (********************<<<*************************)
          let _ = E.pop_scope () in
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
          let _,outer_vars = List.split (E.visible_names ()) in
          (*cond*)
          let cond = helper w.exp_while_condition vars in
          (*body*)
          let addr_vars = find_addr w.exp_while_body in
          let _ = E.push_scope () in
          let body = helper w.exp_while_body vars in
          (**********************>>>***********************)
          (*scoping*)
          let _,inner_vars = List.split (E.visible_names ()) in
          let del_vars = compute_vars_to_delete addr_vars outer_vars inner_vars in
          let body = List.fold_left (fun e var ->
              let del_e = mkDelete var no_pos in
              mkSeq e del_e no_pos) body del_vars
          in
          (**********************<<<***********************)
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
  in helper e vars

(*Find a list of variables with address_of &x*)
and find_addr (e:exp) : ident list =
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

(*Add code for pass-by-val variables that are addressed of*)
let rec add_code_val e (x,ptrx) =
  (*for each arg in val_params1:
    integer ptrx = new integer(x);
    ...
    delete(ptrx);
  *)
  let pos = x.param_loc in
  let nm = match ptrx.param_type with
    | Named id -> id (*Name integer -> integer*)
    | _ -> Error.report_error
        {Err.error_loc = pos;
         Err.error_text = "Expecting (Named ident) of ptrx"}
  in
  let args = [Var {exp_var_name = x.param_name; exp_var_pos = pos}] in
  (*new integer(x)*)
  let e0 = New {exp_new_class_name = nm;
                exp_new_arguments = args;
                exp_new_pos = pos;}
  in
  let decl = (ptrx.param_name,Some e0,no_pos) in
  (*integer ptrx = new integer(x)*)
  let e1 = VarDecl {exp_var_decl_type = ptrx.param_type;
                    exp_var_decl_decls = [decl] ;
                    exp_var_decl_pos = pos;
                   }
  in
  let new_e = mkSeq e1 e pos in
  (*delete(ptrx);*)
  let e2 = mkDelete ptrx.param_name pos in
  let new_e1 = mkSeq new_e e2 pos in
  new_e1

(*Add code for pass-by-ref variables that are addressed of*)
let rec add_code_ref e (x,ptrx) =
  (*for each arg in ref_params1:
    integer ptrx = new integer(x);
    ...
    x = ptrx.val;
    delete(ptrx);
  *)
  let pos = x.param_loc in
  let nm = match ptrx.param_type with
    | Named id -> id (*Name integer -> integer*)
    | _ -> Error.report_error
        {Err.error_loc = pos;
         Err.error_text = "Expecting (Named ident) of ptrx"}
  in
  let arg = Var {exp_var_name = x.param_name; exp_var_pos = pos} in
  let ptr_arg = Var {exp_var_name = ptrx.param_name; exp_var_pos = pos} in
  let args = [arg] in
  (*new integer(x)*)
  let e0 = New {exp_new_class_name = nm;
                exp_new_arguments = args;
                exp_new_pos = pos;}
  in
  let decl = (ptrx.param_name,Some e0,no_pos) in
  (*integer ptrx = new integer(x)
    ...e
  *)
  let e1 = VarDecl {exp_var_decl_type = ptrx.param_type;
                    exp_var_decl_decls = [decl] ;
                    exp_var_decl_pos = pos;
                   }
  in
  let new_e = mkSeq e1 e pos in
  (*ptrx.val*)
  let mem = Member { exp_member_base = ptr_arg;
		            exp_member_fields = [ptr_target];
                    exp_member_path_id = None;
                    exp_member_pos = pos}
  in
  (*x = ptrx.val*)
  let a = {
      exp_assign_op = OpAssign;
	  exp_assign_lhs = arg;
	  exp_assign_rhs = mem;
	  exp_assign_path_id = None;
	  exp_assign_pos =pos;}
  in
  let e2 = Assign a in
  (*
    ...new_e
    x = ptrx.val
  *)
  let new_e1 = mkSeq new_e e2 pos in
  (*delete(ptrx);*)
  let e3 = mkDelete ptrx.param_name pos in
  let new_e2 = mkSeq new_e1 e3 pos in
  new_e2

(*similar to that in Astsimp.ml*)
let get_type_name_for_mingling (prog : prog_decl) (t : typ) : ident =
  match t with
    | Named c ->
	      (try let _ = look_up_enum_def_raw prog.prog_enum_decls c in "int"
	      with | Not_found -> c)
    |t -> string_of_typ t

(*similar to that in Astsimp.ml*)
let mingle_name_enum prog (m : ident) (targs : typ list) =
  let param_tnames =
    String.concat "~" (List.map (get_type_name_for_mingling prog) targs)
  in m ^ ("$" ^ param_tnames)

let trans_proc_decl_x prog (proc:proc_decl) : proc_decl =
  let ret_t = proc.proc_return in
  let new_ret_t = convert_typ ret_t in
  let params = proc.proc_args in
  let new_params = List.map trans_param params in
  let ptypes = List.map (fun p -> p.param_type) new_params in
  let new_mingled = mingle_name_enum prog proc.proc_name ptypes in
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
    | Some body -> 
        let body1,_ = trans_exp_ptr body vars in
        (*Similar to Astsimp.trans_proc*)
        let _ = E.clear () in
        let _ = E.push_scope () in
        (*Note: ordering of args is important*)
        let all_args = 
          if Gen.is_some proc.proc_data_decl then
            (let cdef = Gen.unsome proc.proc_data_decl in
             let this_arg ={
                 param_type = Named cdef.data_name;
                 param_name = this;
                 param_mod = NoMod;
                 param_loc = proc.proc_loc;} in 
             this_arg :: new_params)
          else new_params in
        let val_params,ref_params = List.partition (fun p -> (p.param_mod = NoMod)) all_args in
        (*addr_vars contains variables that are taken adrress-of in e1*)
        let addr_vars = find_addr body1 in
        (*List of pass-by-val/ref params that have been taken address-of*)
        let val_params1,_ = List.partition (fun p -> List.mem p.param_name addr_vars) val_params in
        let ref_params1,_ = List.partition (fun p -> List.mem p.param_name addr_vars) ref_params in
        (*
          for each arg in val_params1:
          integer ptr_arg = new integer(arg);
          sub(arg |-> ptr_arg)[e1]
          delete(ptr_arg);

          for each arg in ref_params1:
          integer ptr_arg = new integer(arg);
          sub(arg |-> ptr_arg)[e1]
          arg = ptr_arg.val;
          delete(ptr_arg);
        *)
        let val_ptrs = List.map (fun p ->
                                 let name = (ptr_string^"_"^ p.param_name) in
                                 let t = convert_prim_to_obj p.param_type in
                                 {p with param_type=t; param_name = name}) val_params1 
        in
        let ref_ptrs = List.map (fun p ->
                                 let name = (ptr_string^"_"^ p.param_name) in
                                 let t = convert_prim_to_obj p.param_type in
                                 {p with param_type=t; param_name = name}) ref_params1 
        in
        let val_subst = List.map2 (fun v ptr -> (v.param_name,ptr.param_name)) val_params1 val_ptrs in
        let ref_subst = List.map2 (fun v ptr -> (v.param_name,ptr.param_name)) ref_params1 ref_ptrs in
        let all_subst = val_subst@ref_subst in

        (* let _ = print_endline ("val_subst = " ^ (string_of_subst val_subst)) in *)
        (* let _ = print_endline ("ref_subst = " ^ (string_of_subst ref_subst)) in *)
        let body2 = if (all_subst!=[]) then
              subst_exp body1 all_subst 
            else
              body1
        in
        (* let _ = print_endline ("body2 (after all_subst) : \n" ^ (string_of_exp body2)) in *)

        let addr_vars = List.map (fun id ->
            subst_var id all_subst
        ) addr_vars 
        in

        let p2v (p : param) = {
            E.var_name = p.param_name;
            E.var_alpha = p.param_name;
            E.var_type = UNK; } (*Do not care about typ when translating*)
        in
        let vinfos = List.map p2v all_args in
        let _ = List.map (fun v -> E.add v.E.var_name (E.VarInfo v)) vinfos in
        let body3 = trans_exp_addr body2 addr_vars in
        let _,inner_vars = List.split (E.visible_names ()) in
        (*those that were converted and need to be deleted*)
        let vars = compute_vars_to_delete addr_vars [] inner_vars in
        (*body3;delete(..); .... *)
        let new_body = List.fold_left (fun e var ->
            let del_e = mkDelete var no_pos in
            mkSeq e del_e no_pos) body3 vars
        in
        (*Add code for pass-by-val variables that are addressed of*)
        let tmp_val = List.combine val_params1 val_ptrs in
        let new_body2 = 
          if (tmp_val!=[]) then
            List.fold_left (fun e (x,ptrx) -> add_code_val e (x,ptrx)) new_body tmp_val
          else
            new_body
        in
        (* let _ = print_endline ("new_body2: \n " ^ (string_of_exp new_body2)) in *)
        (* <<< Add code for pass-by-val variables that are addressed of*)
        (*Add code for pass-by-ref variables that are addressed of*)
        let tmp_ref = List.combine ref_params1 ref_ptrs in
        let new_body3 = 
          if (tmp_ref!=[]) then
          List.fold_left (fun e (x,ptrx) -> add_code_ref e (x,ptrx)) new_body2 tmp_ref
          else
            new_body2
        in
        (* let _ = print_endline ("new_body3: \n " ^ (string_of_exp new_body3)) in *)
        (* <<< Add code for pass-by-ref variables that are addressed of*)

        let _ = E.pop_scope () in
        let _ = E.clear () in
        (Some new_body3)
  in
  {proc with proc_return  = new_ret_t;
      proc_mingled_name = new_mingled;
      proc_args = new_params;
      proc_body = new_body}

let trans_proc_decl prog (proc:proc_decl) : proc_decl =
  Debug.no_1 "trans_proc_decl"
      string_of_proc_decl string_of_proc_decl
      (fun _ ->  trans_proc_decl_x prog proc) proc

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
