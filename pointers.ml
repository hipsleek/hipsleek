#include "xdebug.cppo"
open VarGen
(* Translate an input program with pointer into an intermediate 
   input program without
   @param prog current program declaration
   @return new program declaration 

   STEP 1 (trans_exp_ptr): eliminate pointer type (e.g. int* )
   - translate pointers into objects: int* p -> int_ptr p;
     + Translate global variables first
     + For each proc, go forward, find (param + local) and replace.

   STEP 2 (trans_exp_addr): eliminate address-of operator (e.g. &x )
   - Translate local vars + params that are addressed of (&x) into object
     + Pass 1: find
     + Pass 2: convert

   NOTE:
    - For local variables, can reuse the variable names
      int x -> int_ptr x;
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


(* Addressable variables *)
let h = Hashtbl.create 200

(*List of proc that has been translated*)
let procs = []

(*
  Auxiliary procs due to translation
  [int x;
  ...&x...
  inc(x);]

  ==TRANSLATE==>
  [int_ptr x;
  ...x...
  inc(x.val) ==> NOT CORRECT
  delete(x);]

  WE SHOULD HAVE
  [int_ptr x;
  ...x...
  ****aux_inc()****
  int v = x.val;
  inc(v);
  x.val =v;
  ****aux_inc()****
  delete(x);]
*)
(*can be duplicated. Deal later*)
let aux_procs : (proc_decl list) ref = ref []

let ptr_target : string = "val" 
let ptr_delete : string = "delete_ptr" 
let ptr_string : string = "ptr"
let aux_str : string = "aux"

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
  | NUM | UNK | Void | AnnT | FORM | Tup2 _ ->
    failwith
      "default_value: void/NUM/UNK/AnnT/FORM/Tup2 in variable declaration should have been rejected by parser"
  | (BagT _) ->
    failwith "default_value: bag can only be used for constraints"
  | List _ ->
    failwith "default_value: list can only be used for constraints"
  | RelT _ ->
    failwith "default_value: RelT can only be used for constraints"
  | Named _ (* | SLTyp *) -> Null pos
  | Pointer ptr -> Null pos
  | Array (t, d) ->
    failwith "default_value: Array not supported"
  | FuncT _ -> failwith "default_value: FuncT not supported"
  | UtT _ -> failwith "default_value: UtT not supported"
  | HpT | Tree_sh ->
    failwith "default_value: (HpT|Tree_sh) not supported"
  | INFInt -> Error.report_no_pattern ()
  | Bptyp ->
    failwith "default_value: Bptyp not supported"

(*similar to that in Astsimp.ml*)
let get_type_name_for_mingling (prog : prog_decl) (t : typ) : ident =
  match t with
  | Named c ->
    (try let todo_unk = look_up_enum_def_raw prog.prog_enum_decls c in "int"
     with | Not_found -> c)
  |t -> string_of_typ t

(*similar to that in Astsimp.ml*)
let mingle_name_enum prog (m : ident) (targs : typ list) =
  let param_tnames =
    String.concat "~" (List.map (get_type_name_for_mingling prog) targs)
  in m ^ ("$" ^ param_tnames)

let string_of_ident_list vs = (pr_list (fun id ->id) vs)

let string_of_subst (subst: (ident*ident) list) : string =
  pr_list (pr_pair pr_id pr_id) subst

let string_of_subst_primed (subst: ((ident*primed)*(ident * primed)) list) : string =
  let pr (id,pr) = id^(string_of_primed pr) in
  pr_list (pr_pair pr pr) subst


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

  WN : Can we improve this method to return a list
   of vars that have been modified as suggested by method name?
  --> (bound_var, free_vars, free_modified_vars)
*)

let modifies (e:exp) (bvars:ident list) prog : (ident list) * (ident list) * (ident list) =
  let rec accumulate (el:exp list) (bvars:ident list) : (ident list) * (ident list) * (ident list) =
    List.fold_right (fun (a,b,c) (aa,bb,cc) -> (a@aa,b@bb,c@cc)) (List.map (fun e -> helper e bvars) el) ([],[],[])
  and helper e bvars =
    match e with
    | Var v ->
      let id = v.exp_var_name in
      if (List.mem id bvars) then
        (bvars,[],[]) (*access to variables*)
      else
        (bvars,[id],[])
    | VarDecl v ->
      let vars = List.map (fun (id,e0,pos) -> id) v.exp_var_decl_decls in
      let new_bvars = vars@bvars in
      (* let () = print_endline ("new_bvars = " ^ (string_of_ident_list new_bvars)) in *)
      (new_bvars,[],[])
    | ConstDecl c ->
      let vars = List.map (fun (id,e0,pos) -> id) c.exp_const_decl_decls in
      let new_bvars = vars@bvars in
      (new_bvars,[],[])
    | Unary u ->
      let _,fvars,fw = helper u.exp_unary_exp bvars in
      let () = x_binfo_hp (add_str "Unary" string_of_exp) e no_pos in
      ( match u.exp_unary_op with
        | OpPreInc
        | OpPreDec
        | OpPostInc
        | OpPostDec -> if (is_var u.exp_unary_exp) then (bvars,fvars,fvars@fw) else (bvars,fvars,fw)
        | _ -> (bvars,fvars,fw) (* more *) )
    | ArrayAt b ->
      let _,fvars1,fw1 =  helper b.exp_arrayat_array_base bvars in
      (* let _,fvars2,fw2 = List.fold_right (fun (a,b,c) (aa,bs,cs) -> (a@as,b@bs,c@cs)) (List.map (fun e -> helper e bvars) b.exp_arrayat_index) ([],[],[]) in *)
      let _,fvars2,fw2 = accumulate b.exp_arrayat_index bvars in
      (* let fvars2 = List.concat fvars_l in *)
      (bvars,fvars1@fvars2,fw1@fw2)
    | ArrayAlloc a ->
      (* let _, fvars_l = List.split (List.map (fun e -> helper e bvars) a.exp_aalloc_dimensions) in *)
      (* let _,fvars2,fw2 = List.fold_right (fun (a,b,c) (aa,bs,cs) -> (a@as,b@bs,c@cs)) (List.map (fun e -> helper e bvars) a.exp_aalloc_dimensions) ([],[],[]) in *)
      let _,fvars2,fw2 = accumulate a.exp_aalloc_dimensions bvars in
      (* let fvars = List.concat fvars_l in *)
      let a = a.exp_aalloc_etype_name in
      (bvars,a::fvars2,fw2)
    | Assert _ -> (bvars,[],[])
    | Assign a ->
      let _,fvars1,fw1 = helper a.exp_assign_lhs bvars in
      let _,fvars2,fw2 = helper a.exp_assign_rhs bvars in
      let () = Debug.ninfo_hprint (add_str "modifies" (pr_list pr_id)) fvars1 no_pos in
      if (is_var a.exp_assign_lhs) then
        (bvars,fvars1@fvars2,fvars1@fw1@fw2)
      else (bvars,fvars1@fvars2,fw1@fw2)
    | Binary b ->
      let _,fvars1,fw1 = helper b.exp_binary_oper1 bvars in
      let _,fvars2,fw2 = helper b.exp_binary_oper2 bvars in
      (bvars,fvars1@fvars2,fw1@fw2)
    | Bind b ->
      let fvar = b.exp_bind_bound_var in
      let fvars1 = if (List.mem fvar bvars) then [] else [fvar] in
      let new_bvars = bvars@b.exp_bind_fields in
      let _,fvars,fw1 = helper b.exp_bind_body new_bvars in
      (bvars,fvars1@fvars,fw1)
    | Block b ->
      (*Note: no more Block after case_normalize_program*)
      let bvars1,fvars,fw = helper b.exp_block_body bvars in
      (bvars1,fvars,fw)
    | BoolLit _ -> (bvars,[],[])
    | Break _ -> (bvars,[],[])
    | CallRecv c ->
      (*ignore exp_call_recv_method*)
      (* let _,fvars1,fw1 = List.fold_right (fun (a,b,c) (aa,bs,cs) -> (a@as,b@bs,c@cs)) (List.map (fun e -> helper e bvars) c.exp_call_recv_arguments) ([],[],[]) in *)
      let _,fvars1,fw1 = accumulate c.exp_call_recv_arguments bvars in
      let () = Debug.ninfo_hprint (add_str "modifies(call)" string_of_exp) e no_pos in
      (* let _,fvars_l = List.split (List.map (fun e -> helper e bvars) c.exp_call_recv_arguments) in *)
      (* let fvars1 = List.concat fvars_l in *)
      let _,fvars2,fw2 = helper c.exp_call_recv_receiver bvars in
      (bvars,fvars1@fvars2,fw1@fw2)
    | CallNRecv c ->
      (*ignore exp_call_nrecv_method*)
      (* let _,fvars2,fw2 = List.fold_right (fun (a,b,c) (aa,bs,cs) -> (a@as,b@bs,c@cs)) (List.map (fun e -> helper e bvars) c.exp_call_nrecv_arguments) ([],[],[]) in *)
      let _,fvars,fw1 = accumulate c.exp_call_nrecv_arguments bvars in
      let proc = look_up_proc_def_raw prog.prog_proc_decls c.exp_call_nrecv_method in
      let args = 
        (*let () = x_binfo_hp (add_str "proc_args" (pr_list string_of_param))  proc.proc_args no_pos in
        let () = x_binfo_hp (add_str "call arguments" (pr_list string_of_exp))  c.exp_call_nrecv_arguments no_pos in*)
        List.combine proc.proc_args c.exp_call_nrecv_arguments in
      let fw2 = List.map (fun (_,arg) -> 
          match get_ident arg with
          | Some v -> v
          | None -> failwith "Impossible") (List.filter (fun (para,arg) ->
          (para.param_mod = RefMod) && (is_var arg)
        ) args) in
      let () = Debug.ninfo_hprint (add_str "modifies(Ncall)" string_of_exp) e no_pos in
      let () = Debug.ninfo_hprint (add_str "ref args" (pr_list pr_id)) fw2 no_pos in
      (* let _,fvars_l = List.split (List.map (fun e -> helper e bvars) c.exp_call_nrecv_arguments) in *)
      (* let fvars = List.concat fvars_l in *)
      (bvars,fvars,fw1@fw2)
    | Cast c ->
      let _,fvars,fw = helper c.exp_cast_body bvars in
      (bvars,fvars,fw)
    | Cond c ->
      let _,fvars1,fw1 = helper c.exp_cond_condition bvars in
      let _,fvars2,fw2 = helper c.exp_cond_then_arm bvars in
      let _,fvars3,fw3 = helper c.exp_cond_else_arm bvars in
      (bvars,fvars1@fvars2@fvars3,fw1@fw2@fw3)
    | Finally f ->
      let _,fvars,fw = helper f.exp_finally_body bvars in
      (bvars,fvars,fw)
    | Label ((pid,plbl),e0) ->
      let bvars1,fvars,fw = helper e0 bvars in
      (bvars1,fvars,fw)
    | Member m ->
      let _,fvars,fw = helper m.exp_member_base bvars in
      (bvars,fvars,fw)
    | New n ->
      let _,fvars,fw = accumulate n.exp_new_arguments bvars in
      (* let _,fvars_l = List.split (List.map (fun e -> helper e bvars) n.exp_new_arguments) in *)
      (* let fvars = List.concat fvars_l in *)
      (bvars,fvars,fw)
    | Try t ->
      let bvars1,fvars1,fw1 = helper t.exp_try_block bvars in
      (*vars in try_block are still in scopes of catch_clauses
        and finally clause*)
      let _,fvars2,fw2 = accumulate t.exp_catch_clauses bvars1 in
      let _,fvars3,fw3 = accumulate t.exp_finally_clause bvars1 in
      (* let _,fvars2_l = List.split (List.map (fun e -> helper e bvars1) t.exp_catch_clauses) in *)
      (* let _,fvars3_l = List.split (List.map (fun e -> helper e bvars1) t.exp_finally_clause) in *)
      (* let fvars2 = List.concat fvars2_l in *)
      (* let fvars3 = List.concat fvars3_l in *)
      (bvars1,fvars1@fvars2@fvars3,fw1@fw2@fw3)
    | Raise r -> (*Assume no pointers*)
      let _,fvars,fw = match r.exp_raise_val with
        | None -> (bvars,[],[])
        | Some e ->
          helper e bvars
      in
      (bvars,fvars,fw)
    | Catch c -> (*assume no pointer*)
      let fvars,fw = match c.exp_catch_var with
        | None -> ([],[])
        | Some v ->
          if List.mem v bvars then ([],[]) else ([v],[])
      in
      (bvars,fvars,fw)
    | Return r ->
      let fvars,fw =
        (match r.exp_return_val with
         | None -> ([],[])
         | Some e0 ->
           let _,vs,fw = helper e0 bvars in
           (vs,fw)
        )
      in
      (bvars,fvars,fw)
    | Seq s ->
      let bvars1,fvars1,fw1 = helper s.exp_seq_exp1 bvars in
      let bvars2,fvars2,fw2 = helper s.exp_seq_exp2 bvars1 in
      (bvars2,fvars1@fvars2,fw1@fw2)
    | This _ -> (*assume no pointer *)
      (bvars,[],[])
    | While w ->
      let _,fvars1,fw1 = helper w.exp_while_condition bvars in
      let _,fvars2,fw2 = helper w.exp_while_body bvars in
      (*TO CHECK: not sure what exp_while_wrappings is for? *)
      let fvars3,fw3 =
        (match w.exp_while_wrappings with
         | None -> ([],[])
         | Some (e0,id) -> (*TO CHECK: what is id ??? *)
           let _,vs,fw =  (helper e0 bvars) in
           vs,fw
        )
      in
      (bvars,fvars1@fvars2@fvars3,fw1@fw2@fw3)
    | Debug _
    | Dprint _
    | Empty _
    | FloatLit _
    | IntLit _
    | Java _
    | Null _
    | Time _
    | Unfold _
    | Barrier _ (*TO CHECK*)
    | Continue _ -> (bvars,[],[])
    | Par _ -> (bvars, [], []) (* TODO: Par *)
  in helper e bvars

let modifies (e:exp) (bvars:ident list) prog : (ident list) * (ident list) * (ident list) =
  let pr_ids = pr_list pr_id in
  let pr_exp = string_of_exp in
  Debug.no_2 "modifies" pr_exp pr_ids (pr_triple pr_ids pr_ids pr_ids)
    (fun _ _ -> modifies e bvars prog) e bvars

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
         | Some (e0,id) -> (*TO CHECK: what is id ?*)
           let e1 = helper e0 subst in
           Some (e1,id)
        )
      in
      let new_e = While {w with exp_while_condition = cond;
                                exp_while_body = body;
                                exp_while_wrappings = wrap}
      in
      (new_e)
    | Par _ -> e (* TODO: Par *) 
    | Debug _
    | Dprint _
    | Empty _
    | FloatLit _
    | IntLit _
    | Java _
    | Null _
    | Time _
    | Unfold _
    | Barrier _ (*TO CHECK*)
    | Continue _ -> e
  in helper e subst

let subst_exp (e:exp) (subst:(ident*ident) list): exp =
  Debug.no_2 "subst_exp"
    string_of_exp string_of_subst string_of_exp
    subst_exp_x e subst



(**
   Replace int* -> int_ptr and other translation (STEP 1)
   @param e: expression
   @param vars: list of identifiers that need to be translated
   @return e*vars: new expression * (new list of vars that need to
   be translate)
   Note: 
   - After case_normalize_program, no more name collision on variables
   - We are interested in declarations (to update list of vars) and
   unary operations (to translate): Var, VarDecl, ConstDecl, Unary

 **)
let trans_exp_ptr_x prog (e:exp) (vars: ident list) : exp * (ident list) =
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
         let e0,_ = helper u.exp_unary_exp vars in
         let new_e =  Unary {u with exp_unary_exp = e0} in
         (new_e,vars)
       (* (match e0 with *)
       (*   | Var v -> *)
       (*       let id = v.exp_var_name in *)
       (*       if (List.mem id vars) then *)
       (*         (u.exp_unary_exp,vars) *)
       (*       else *)
       (*         let e0,_ = helper u.exp_unary_exp vars in *)
       (*         let new_e =  Unary {u with exp_unary_exp = e0} in *)
       (*         (new_e,vars) *)
       (*   | _ -> Error.report_error  *)
       (*       {Err.error_loc = u.exp_unary_pos; *)
       (*        Err.error_text = "Expecting Var after OpAddr unary operation (\*p)"}) *)
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
      let () = print_endline_quiet ("Block: " ^ (pr_list (fun (id,_,_) -> id) b.exp_block_local_vars)) in
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
      (*Assume int* ptr = new int_ptr(...) --> do not need 
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
         | Some (e0,id) ->
           let e1,_ = helper e0 vars in
           Some (e1,id)
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
    | Barrier _ (*TO CHECK*)
    | Continue _ -> (e,vars)
    | Par _ -> (e, vars) (* TODO: Par *)
  in helper e vars

(*STEP 1: Translate pointers: 
  int* p --> int_ptr p 
  p:int* -> p
  *( p:int* ) -> p.val
  &( p:int* ) -> p
*)
let trans_exp_ptr prog (e:exp) (vars: ident list) : exp * (ident list) =
  let pr1 ls = pr_list (fun id -> id) ls in
  let pr_out = pr_pair string_of_exp pr1 in
  Debug.no_2 "trans_exp_ptr" 
    string_of_exp pr1 pr_out 
    (fun _ _ -> trans_exp_ptr_x prog e vars) e vars

(*
  Translate specifications in the presence of pointer translation
  specs: list of spec need to be transform
  flags: bitmap to decide which paramters to be translated
  new_params: list of new params to translate
  pos: 
*)
let rec trans_specs_x specs new_params flags pos =
  (*
    inc(ref int x,int y) ensures x'=x+y ==>
    inc(ref int_ptr x, int_ptr y)
    requires x::node<old_x> * y::node<old_y>
    ensures x'::node<new_x> & new_x = old_x + old_y

    subst: x-->old_x; y--> old_y; x' --> new_x
    pre-condition: impl_vars = {old_x}
    post-condition: exists_vars = {new_x}
  *)
  let tmp = List.combine new_params flags in
  let sst = List.fold_left (fun sst (param,flag) ->
      if (flag) then
        let nm = param.param_name in
        let unprimed_param = (nm,Unprimed) in
        let primed_param = (nm,Primed) in
        let old_param = (nm^"_old",Unprimed) in
        let new_param = (nm^"_new",Unprimed) in
        let sub1 = (unprimed_param,old_param) in
        let sub2 = (primed_param,new_param) in
        (sub1::(sub2::sst))
      else sst) [] tmp
  in
  (* let () = print_endline ("specs: " ^ (string_of_struc_formula specs)) in *)
  (* let () = print_endline ("sst: " ^ (string_of_subst_primed sst)) in *)
  (*list of addressable reference parameters*)
  let rvars = List.map (fun (param,flag) ->
      if (flag) then [(param.param_name, Unprimed)] else []
    ) tmp
  in
  let rvars = List.concat rvars in 
  (*NEED to maintain point-to information
    e.g. p::int_ptr(x) --> p=x
  *)
  let new_specs = Iformula.subst_pointer_struc sst specs rvars in
  (* let () = print_endline ("new_specs: " ^ (string_of_struc_formula new_specs)) in *)
  (*create h_formula to add to pre-condition*)
  (* inc(ref int_ptr x, int_ptr y) *)
  (*   requires [old_x,old_y] x::node<old_x> * y::node<old_y> *)
  let pre,impl_vars = List.fold_left (fun (h,impl_vars) (param,flag) ->
      if (flag) then
        let typ_name = name_of_typ param.param_type in
        let var = (param.param_name, Unprimed) in
        let old_var = (param.param_name^"_old",Unprimed) in
        let h_arg = Ipure.Var (old_var,no_pos) in
        let var_node = Iformula.mkHeapNode var typ_name [] (* TODO:HO *) 0 false SPLIT0 (Ipure.ConstAnn(Mutable)) false false false None [h_arg] [] None no_pos in
        let new_h = Iformula.mkStar h var_node no_pos in
        (new_h,old_var::impl_vars)
      else (h,impl_vars)
    ) (Iformula.HTrue,[]) tmp 
  in
  (*create h_formula to add to post-condition
    Consider only REF param
    inc(ref int_ptr x, int_ptr y)
    requires ...
    ensures (Ex: new_x) x'::int_ptr<new_x> * y::int_ptr<old_y> & new_x = old_x + old_y *)
  let post_h,post_p,ex_vars = List.fold_left (fun (h,p,ex_vars) (param,flag) ->
      if (flag) then
        let typ_name = match param.param_type with
          | Named t -> t
          | _ -> Error.report_error 
                   {Err.error_loc = pos;
                    Err.error_text = "Expecting Named t"}
        in
        let var_node,new_p,new_ex_vars = 
          if (param.param_mod = RefMod) then
            (*pass-by-ref*)
            (* x'::int_ptr<new_x> *)
            let var = (param.param_name, Primed) in (* PRIMED *)
            let new_var = (param.param_name^"_new",Unprimed) in
            let h_arg = Ipure.Var (new_var,no_pos) in
            let var_node = Iformula.mkHeapNode var typ_name [] (* TODO:HO *) 0 false SPLIT0 (Ipure.ConstAnn(Mutable)) false false false None [h_arg] [] None no_pos in
            let uvar = (param.param_name, Unprimed) in (* UNPRIMED *)
            let new_p = Ipure.mkEqVarExp var uvar pos in
            (var_node,new_p,new_var::ex_vars)
          else
            (*??? why consider pass-by-value parameters here ??? *)
            (* pass-by-value*)
            (* y::int_ptr<old_y> *)
            let typ_name = match param.param_type with
              | Named t -> t
              | _ -> Error.report_error 
                       {Err.error_loc = pos;
                        Err.error_text = "Expecting Named t"}
            in
            let var = (param.param_name, Unprimed) in
            (* let old_var = (param.param_name^"_old",Unprimed) in *)
            let new_var = (param.param_name^"_new",Unprimed) in
            (* let h_arg = Ipure.Var (old_var,no_pos) in *)
            let h_arg = Ipure.Var (new_var,no_pos) in
            let var_node = Iformula.mkHeapNode var typ_name [] (* TODO:HO *) 0 false SPLIT0 (Ipure.ConstAnn(Mutable)) false false false None [h_arg] [] None no_pos in
            (var_node, Ipure.mkTrue pos, new_var::ex_vars)
        in
        let new_h = Iformula.mkStar h var_node no_pos in
        let new_p1 = Ipure.mkAnd p new_p pos in
        (new_h,new_p1,new_ex_vars)
      else (h,p,ex_vars)
    ) (Iformula.HTrue,Ipure.mkTrue pos,[]) tmp
  in
  let post = Iformula.mkBase_wo_flow post_h post_p IvpermUtils.empty_vperm_sets [] pos in
  (* let () = print_endline ("pre = " ^ (string_of_h_formula pre)) in *)
  (* let () = print_endline ("post = " ^ (string_of_h_formula post)) in *)
  let new_specs2 = Iformula.add_h_formula_to_pre (pre,impl_vars) new_specs in
  let new_specs3 = Iformula.add_formula_to_post (post,ex_vars) new_specs2 in
  (* let () = print_endline ("new_specs3: " ^ (string_of_struc_formula new_specs3)) in *)
  new_specs3

and trans_specs specs (new_params:param list) flags pos =
  let pr = pr_list string_of_bool in
  Debug.no_3 "trans_specs"
    string_of_struc_formula string_of_param_list pr string_of_struc_formula
    (fun _ _ _ -> trans_specs_x specs new_params flags pos) specs new_params flags
(*****************************)
(***<<<<< trans_specs ********)
(*****************************)

(*
  Create a new auxiliary proc_decl for pointer translation
  proc : original proc_decl
  c : orignal exp_call_nrecv
  flags: bitmap to decide which paramters to be translated
  new_proc_name : name of the new auxiliary proc
*)
and create_aux_proc prog (proc:proc_decl) (c:exp_call_nrecv) (flags: bool list) (new_proc_name:ident) pos =
  (* let () = print_endline ("new_proc_name = " ^ new_proc_name ) in *)
  (*inc(ref int x,int y) --> inc(ref int_ptr x, int_ptr y)*)
  let params = proc.proc_args in
  let new_params = List.map2 (fun param flag ->
      if (flag) then
        let new_t = convert_prim_to_obj param.param_type in
        {param with param_type = new_t}
      else param) params flags
  in
  (******** translate specification >>> ****************)
  let new_static_specs = trans_specs proc.proc_static_specs new_params flags pos in
  let new_dynamic_specs = trans_specs proc.proc_dynamic_specs new_params flags pos in
  (********<<< translate specification ****************)
  let ptypes = List.map (fun p -> p.param_type) new_params in
  let new_mingled = mingle_name_enum prog new_proc_name ptypes in

  (* let tmp = List.combine new_params flags in *)
  (* let trans_tmp = List.map (fun (x,flag) ->  *)
  (*     if (flag) then *)
  (*       (\*x.val*\) *)
  (*       let var = Var { exp_var_name = x.param_name; exp_var_pos = pos;} in *)
  (*       let e1_mem = Member { exp_member_base = var; *)
  (*   	                      exp_member_fields = [ptr_target]; *)
  (*                             exp_member_path_id = None; *)
  (*                             exp_member_pos = pos} *)
  (*       in *)
  (*       let tmp_name = fresh_any_name aux_str in *)
  (*       let e1_decl = (tmp_name,Some e1_mem,no_pos) in *)
  (*       let t = revert_typ x.param_type in *)
  (*       (\*t tmp_name = x.val*\) *)
  (*       let e1 = VarDecl {exp_var_decl_type = t; *)
  (*                         exp_var_decl_decls = [e1_decl]; *)
  (*                         exp_var_decl_pos = pos; *)
  (*                        } *)
  (*       in *)
  (*       let e3_lhs = e1_mem in *)
  (*       let e3_rhs = Var { exp_var_name = tmp_name; exp_var_pos = pos} in *)
  (*       (\*x.val = tmp_name*\) *)
  (*       let e3 = Assign { exp_assign_op = OpAssign; *)
  (*   	                  exp_assign_lhs = e3_lhs; *)
  (*   	                  exp_assign_rhs = e3_rhs; *)
  (*   	                  exp_assign_path_id = None; *)
  (*   	                  exp_assign_pos = pos } *)
  (*       in *)
  (*       (tmp_name,Some (e1,e3)) *)
  (*     else *)
  (*       (x.param_name,None) *)
  (* ) tmp *)
  (* in *)
  (* let names, es = List.split trans_tmp in *)
  (* let vars = List.map (fun id -> Var {exp_var_name =id; exp_var_pos=pos}) names in *)
  (* let orig_call =  CallNRecv {c with exp_call_nrecv_arguments = vars} in *)
  (* (\* let () = print_endline ("### orig_call : " ^ (string_of_exp orig_call)) in *\) *)
  (* let new_body = List.fold_left (fun e2 eo -> *)
  (*     match eo with *)
  (*       | None -> e2 *)
  (*       | Some (e1,e3) -> *)
  (*           let e12 = mkSeq e1 e2 no_pos in *)
  (*           let e123 = mkSeq e12 e3 no_pos in *)
  (*           e123 *)
  (* ) orig_call es *)
  (* in *)
  (* let () = print_endline ("### new_body : " ^ (string_of_exp new_body)) in *)
  (* let new_body = match proc.proc_body with *)
  (*   | None -> None *)
  (*   | Some e -> *)
  (*       let new_e = trans_exp_addr *)
  (* in *)
  let new_proc = {proc with proc_name = new_proc_name;
                            proc_mingled_name = new_mingled;
                            proc_args = new_params;
                            proc_body = proc.proc_body;
                            proc_static_specs = new_static_specs;
                            proc_dynamic_specs = new_dynamic_specs;}
  in
  let rvars = Hashtbl.find h proc.proc_name in
  let () = Hashtbl.replace h new_proc_name rvars in (*their ref vars are comparable*)
  (*trans auxiliary variables*)
  let new_proc1 = trans_proc_decl prog new_proc true in
  let () = print_endline_quiet ("### new_proc1 : " ^ (string_of_proc_decl new_proc1)) in
  (* UPDATE TO GLOBAL VARIABLE *)
  let () = (aux_procs := new_proc1::!aux_procs) in
  new_proc
(*********************************)
(***<<<<< create_aux_proc ********)
(*********************************)


and mkDelete (var:ident) pos =
  let arg = Var {exp_var_name =var; exp_var_pos = pos} in
  let args = [arg] in
  CallNRecv {
    exp_call_nrecv_method = ptr_delete;
    exp_call_nrecv_lock = None;
    exp_call_nrecv_arguments = args;
    exp_call_nrecv_ho_arg = None;
    exp_call_nrecv_path_id = None;
    exp_call_nrecv_pos = pos;}

(*
  RULE of THUMP:
  scope1{scope2}
  addr_vars = find_add e(scope2);
  vars_to_delete(scope2) = (vars(scope2) \diff vars(scope1)) \intesect addr_vars
*)
and compute_vars_to_delete_x addr_vars outer_vars inner_vars : ident list =
  let new_vars = Gen.BList.difference_eq (=) inner_vars outer_vars in
  Gen.BList.intersect_eq (=) new_vars addr_vars

and compute_vars_to_delete addr_vars outer_vars inner_vars : ident list =
  let pr = string_of_ident_list in
  Debug.no_3 "compute_vars_to_delete" 
    pr pr pr pr
    compute_vars_to_delete_x addr_vars outer_vars inner_vars

(*
  @trans_exp_addr
  Need typ information to delete x at the end.

  STEP2: translate address_of (&x) operators
  int x --> int_ptr x = new int_ptr(0); ...; delete(x);
  x:int --> x.val
  &(x:int) --> x

  At the end of each scope:
  1) look_up --> addr_vars
  intersect(E.visible_names,add_vars) --> those that need to be translated
  2) translate

  vars: fordward a list of vars that has been taken address-off
*)
and trans_exp_addr prog (e:exp) (vars: ident list) : exp =
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
      (* let () = print_endline ("Vardecl : " ^ (string_of_exp e)) in *)
      (* let () = print_endline ("Vardecl : before E.add") in *)
      let org_t = v.exp_var_decl_type in
      let todo_unk = List.map (fun (v,_,_) ->
          let alpha = E.alpha_name v in
          (E.add v (E.VarInfo{
               E.var_name = v;
               E.var_alpha = alpha;
               E.var_type = UNK; }))
        ) v.exp_var_decl_decls in
      (* let () = print_endline ("Vardecl : after E.add") in *)
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
        (*int x --> int_ptr x = new int_ptr(0)*)
        (*int* ptr -> int_ptr_ptr = new int_ptr_ptr(..);*)
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
          (*new int_ptr(0)*)
          let e0 = New {exp_new_class_name = nm;
                        exp_new_arguments = args;
                        exp_new_pos = pos;}
          in
          let decl = (id,Some e0,pos) in
          (*int x --> int_ptr x = new int_ptr(0)*)
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
      (*let org_t = c.exp_const_decl_type in*)
      let todo_unk = List.map (fun (v,_,_) ->
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
        (*int x --> int_ptr x = new int_ptr(0)*)
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
          (*int x --> int_ptr x = new int_ptr(0)*)
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
      let () = E.push_scope () in
      let todo_unk = List.map (fun v ->
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
      let () = E.pop_scope ()in
      let new_e = Bind {b with exp_bind_body = new_body2} in
      (new_e)
    | Block b ->
      (*Note: no more Block after case_normalize_program*)
      let () = print_endline_quiet ("Warning: unexpected Block: no more Block after case_normalize_program") in
      (*b.exp_block_local_vars is empty until IastUtil.float_var_decl*)
      let _,outer_vars = List.split (E.visible_names ()) in
      (*addr vars of the inner scope*)
      let addr_vars = find_addr b.exp_block_body in
      let () = E.push_scope () in
      let new_body = helper b.exp_block_body vars in
      (********************>>>*************************)
      let _,inner_vars = List.split (E.visible_names ()) in
      let del_vars = compute_vars_to_delete addr_vars outer_vars inner_vars in
      let new_body = List.fold_left (fun e var ->
          let del_e = mkDelete var no_pos in
          mkSeq e del_e no_pos) new_body del_vars
      in
      (***********************<<<**********************)
      let () = E.pop_scope ()in
      let new_e = Block {b with exp_block_body = new_body} in
      (new_e) (* Block creates a new inner scope *)
    | BoolLit _ -> e
    | Break _ -> e
    | CallRecv c ->
      (*TODO: do the same as trans_arg_addr for CallNRecv*)
      let new_args = List.map (fun e -> helper e vars) c.exp_call_recv_arguments in
      let new_rev = helper c.exp_call_recv_receiver vars in
      let new_e = CallRecv {c with exp_call_recv_arguments = new_args;
                                   exp_call_recv_receiver = new_rev;}
      in (new_e)
    | CallNRecv c ->
      (*Do not need for Globals.join_name because join(id) is always
        passed by value*)
      (* match c.exp_call_nrecv_method with *)
      (*   | Globals.init_name *)
      (*   | Globals.finalize_name *)
      (*   | Globals.acquire_name *)
      (*   | Globals.release_name -> e (\*ignore*\) *)
      (*   | _ -> *)
      if (c.exp_call_nrecv_method=Globals.init_name ||
          c.exp_call_nrecv_method=Globals.finalize_name ||
          c.exp_call_nrecv_method=Globals.acquire_name ||
          c.exp_call_nrecv_method=Globals.release_name) 
      then
        e  (* ignore *)
      else
      if (c.exp_call_nrecv_method=Globals.fork_name) then
        (*Construct the async call from parameters of the fork procedure*)
        (*method name is the first arguments*)
        try
          let fn_exp = (List.hd c.exp_call_nrecv_arguments) in
          let fn = match fn_exp with
            | Var v ->
              v.exp_var_name
            | _ -> 
              Error.report_error {Error.error_loc = no_pos; Error.error_text = ("[Pointers.ml] expecting a method name as the first parameter of a fork")}
          in
          let args = List.tl c.exp_call_nrecv_arguments in
          let new_e = CallNRecv {
              exp_call_nrecv_lock = c.exp_call_nrecv_lock;
              exp_call_nrecv_method = fn;
              exp_call_nrecv_arguments = args;
              exp_call_nrecv_ho_arg = None;
              exp_call_nrecv_path_id = c.exp_call_nrecv_path_id;
              exp_call_nrecv_pos = c.exp_call_nrecv_pos} in
          (*trans_exp_addr that asyn call*)
          let new_e1 = helper new_e vars in
          (*then get back the fork call*)
          (* ================== *)
          match new_e1 with
          | CallNRecv e1 ->
            let fn1 = Var { exp_var_name = e1.exp_call_nrecv_method;
                            exp_var_pos = e1.exp_call_nrecv_pos} 
            in
            let new_fork_exp = CallNRecv {
                exp_call_nrecv_lock = c.exp_call_nrecv_lock;
                exp_call_nrecv_method = c.exp_call_nrecv_method; (*fork_name*)
                exp_call_nrecv_arguments = fn1::(e1.exp_call_nrecv_arguments);
                exp_call_nrecv_ho_arg = None;
                exp_call_nrecv_path_id = e1.exp_call_nrecv_path_id;
                exp_call_nrecv_pos = e1.exp_call_nrecv_pos} 
            in
            new_fork_exp
          | _ -> Error.report_error {Error.error_loc = no_pos; Error.error_text = ("expecting forked method to be a CallNRecv")}
        (* ================== *)
        with _ ->
          Error.report_error {Error.error_loc = no_pos; Error.error_text = ("[Pointers.ml] expecting fork has at least 1 argument: method name")}
      else
        (* trans_exp_addr *)
        (try
           let proc = look_up_proc_def_raw prog.prog_proc_decls c.exp_call_nrecv_method in
(*
              let pos = c.exp_call_nrecv_pos in
              let rvars = Hashtbl.find h proc.proc_name in
              let args  =c.exp_call_nrecv_arguments in*)
              (*
                If there are some parameters that are not addressable
                -> create auxiliary variables
              *)
           let trans_arg_addr arg param =
             match arg with
             | Var e0 -> 
               (*Maybe we only need to translate for primitive types*)
               (*If this argument var needs to be translate*)
               if (List.mem e0.exp_var_name vars)  
               && (param.param_mod = RefMod) then
                 (*addressable variable that are passed by reference*)
                 (true,arg) (*need to be processed*)
               else
                 (*normal variables or addressible variables that are
                   passed by value*)
                 let new_arg = helper arg vars in
                 (false,new_arg)
             | _ ->
               let new_arg = helper arg vars in
               (false,new_arg)
           in
           (* let () = print_endline ("c.args = " ^ (pr_list string_of_exp c.exp_call_nrecv_arguments)) in *)
           (* let () = print_endline ("proc.proc_name = " ^ proc.proc_name) in *)
           (* let () = print_endline ("proc.args = " ^ (string_of_param_list proc.proc_args)) in *)

           let flags,new_args = List.split (List.map2 (fun arg param -> trans_arg_addr arg param) c.exp_call_nrecv_arguments proc.proc_args) in
           (* if (List.exists (fun (b:bool) -> b) flags) then *)
           (*   (\*if there are some args to be processed*\) *)
           (*   let mk_aux_proc_name name (flags: bool list) : ident = *)
           (*     let rec helper (flags:bool list) :ident = *)
           (*       match flags with *)
           (*         | [] -> "" *)
           (*         | (x::xs) -> *)
           (*             (\*TO AVOIT proc_aux name clashes, if a variable needs  *)
           (*               to be convert -> mark its bit as 1 *)
           (*             otherwise, 0*\) *)
           (*             let str1 = if (x) then "_1" else "_0" in *)
           (*             let str2 = helper xs in *)
           (*             (str1^str2) *)
           (*     in *)
           (*     let bitmap = helper flags in *)
           (*     (name^"_"^aux_str^bitmap) *)
           (*   in *)
           (*   let new_proc_name = mk_aux_proc_name c.exp_call_nrecv_method flags in *)
           (*   let new_proc = *)
           (*     (\*look for new_proc_name in*\) *)
           (*     (\*TO PREVENT redundant same new_aux_proc*\) *)
           (*     (try *)
           (*          look_up_proc_def_raw !aux_procs new_proc_name;() *)
           (*      (\*if found, do nothing*\) *)
           (*      with | Not_found -> *)
           (*          (\*if not found -> create a new_proc*\) *)
           (*          (\********************************\) *)
           (*          (\*Creating a new aux_proc*\) *)
           (*          (\********************************\) *)
           (*          create_aux_proc prog proc c (\* params *\) flags new_proc_name pos;() *)
           (*     ) *)
           (*   in (\*after ensure that new_proc_name exists*\) *)
           (*   (\********************************\) *)
           (*   (\*Finish creating a new aux_proc*\) *)
           (*   (\********************************\) *)
           (*   (\*Call the new wrapper procedure instead of the old proc*\) *)
           (*   let new_e = CallNRecv { c with *)
           (*       exp_call_nrecv_method = new_proc_name; *)
           (*       exp_call_nrecv_arguments = new_args;} *)
           (*   in *)
           (*   (\* let () = print_endline ("### new_e : " ^ (string_of_exp new_e)) in *\) *)
           (*   new_e *)
           (* else *)
           (*   let new_e = CallNRecv {c with exp_call_nrecv_arguments = new_args} in *)
           (*   (new_e) *)
           CallNRecv {c with exp_call_nrecv_arguments = new_args}
         with Not_found ->
           Error.report_error 
             {Err.error_loc = c.exp_call_nrecv_pos;
              Err.error_text = "Procedure " ^ c.exp_call_nrecv_method ^ " not found!"})
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
      let () = E.push_scope () in
      let then_e = helper c.exp_cond_then_arm vars in
      (******************>>>**************************)
      let _,then_inner_vars = List.split (E.visible_names ()) in
      let del_vars = compute_vars_to_delete then_addr_vars outer_vars then_inner_vars in
      let then_e = List.fold_left (fun e var ->
          let del_e = mkDelete var no_pos in
          mkSeq e del_e no_pos) then_e del_vars
      in
      (*******************<<<**************************)
      let () = E.pop_scope ()in
      (*else branch*)
      let else_addr_vars = find_addr c.exp_cond_else_arm in
      let () = E.push_scope () in
      let else_e = helper c.exp_cond_else_arm vars in
      (*******************>>>**************************)
      let _,else_inner_vars = List.split (E.visible_names ()) in
      let del_vars = compute_vars_to_delete else_addr_vars outer_vars else_inner_vars in
      let else_e = List.fold_left (fun e var ->
          let del_e = mkDelete var no_pos in
          mkSeq e del_e no_pos) else_e del_vars
      in
      (********************<<<*************************)
      let () = E.pop_scope () in
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
      (*Assume int* ptr = new int_ptr(...) --> do not need 
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
      let all_addr_vars = Gen.BList.remove_dups_eq (=) (vars@addr_vars) in
      (* let () = print_endline ("While : addr" ^ (string_of_ident_list all_addr_vars))  in *)
      let () = E.push_scope () in
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
      let () = E.pop_scope ()in
      (*TO CHECK: not sure what exp_while_wrappings is for? *)
      let wrap =
        (match w.exp_while_wrappings with
         | None -> None
         | Some (e0,id) ->
           let e1 = helper e0 vars in
           Some (e1,id)
        )
      in
      (*NOTE: the translation for while loop specification
        requires type information -> delay the translation until we
        transform while loop into recursive call in Astsimp.trans_loop_proc*)
      let new_e = While {w with exp_while_condition = cond;
                                exp_while_body = body;
                                exp_while_addr_vars = all_addr_vars;
                                exp_while_wrappings = wrap}
      in
      (new_e)
    | Par _ -> e (* TODO: Par *)
    | Debug _
    | Dprint _
    | Empty _
    | FloatLit _
    | IntLit _
    | Java _
    | Null _
    | Time _
    | Unfold _
    | Barrier _ (*TO CHECK*)
    | Continue _ -> e
  in helper e vars

(*Find a list of variables with address_of &x*)
(*intra-procedural analysis*)
and find_addr (e:exp) : ident list =
  let rec helper e =
    match e with
    | Var v -> []
    | VarDecl v ->
      (* let () = print_endline ("VarDecl: " ^ (string_of_exp e)) in *)
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
         (* let () = print_endline ("Unary: " ^ (string_of_exp e)) in *)
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
         | Some (e0,_) ->
           helper e0
        )
      in
      (vs1@vs2@vs3)
    | Par _ -> [] (* TODO: Par *)
    | Debug _
    | Dprint _
    | Empty _
    | FloatLit _
    | IntLit _
    | Java _
    | Null _
    | Time _
    | Unfold _
    | Barrier _ (*TO CHECK*)
    | Continue _ -> []
  in helper e


and trans_global_var_decl (decl:exp_var_decl) : exp_var_decl =
  let t = decl.exp_var_decl_type in
  let new_t = convert_typ t in
  {decl with exp_var_decl_type = new_t}

and trans_param (p:param) : param =
  let t = p.param_type in
  let new_t = convert_typ t in
  {p with param_type = new_t}

(*Add code for pass-by-val variables that are addressed of*)
and add_code_val e (x,ptrx) =
  (*for each arg in val_params1:
    int_ptr ptrx = new int_ptr(x);
    ...
    delete(ptrx);
  *)
  let pos = x.param_loc in
  let nm = match ptrx.param_type with
    | Named id -> id (*Name int_ptr -> int_ptr*)
    | _ -> Error.report_error
             {Err.error_loc = pos;
              Err.error_text = "Expecting (Named ident) of ptrx"}
  in
  let args = [Var {exp_var_name = x.param_name; exp_var_pos = pos}] in
  (*new int_ptr(x)*)
  let e0 = New {exp_new_class_name = nm;
                exp_new_arguments = args;
                exp_new_pos = pos;}
  in
  let decl = (ptrx.param_name,Some e0,no_pos) in
  (*int_ptr ptrx = new int_ptr(x)*)
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
and add_code_ref e (x,ptrx) =
  (*for each arg in ref_params1:
    int_ptr ptrx = new int_ptr(x);
    ...
    x = ptrx.val;
    delete(ptrx);
  *)
  let pos = x.param_loc in
  let nm = match ptrx.param_type with
    | Named id -> id (*Name int_ptr -> int_ptr*)
    | _ -> Error.report_error
             {Err.error_loc = pos;
              Err.error_text = "Expecting (Named ident) of ptrx"}
  in
  let arg = Var {exp_var_name = x.param_name; exp_var_pos = pos} in
  let ptr_arg = Var {exp_var_name = ptrx.param_name; exp_var_pos = pos} in
  let args = [arg] in
  (*new int_ptr(x)*)
  let e0 = New {exp_new_class_name = nm;
                exp_new_arguments = args;
                exp_new_pos = pos;}
  in
  let decl = (ptrx.param_name,Some e0,no_pos) in
  (*int_ptr ptrx = new int_ptr(x)
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

(*
  @param proc: the procedure needs to be transformed
  @param is_aux: this proc is an auxiliary proc
*)
and trans_proc_decl_x prog (proc:proc_decl) (is_aux:bool) : proc_decl =
  (*update list of translated procs*)
  (* let procs = proc::procs in *)
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
  (match proc.proc_body with
   | None ->
     {proc with proc_return  = new_ret_t;
                proc_mingled_name = new_mingled;
                proc_args = new_params;}
   | Some body ->
     let body1,_ = trans_exp_ptr prog body vars in
     (* let () = print_endline ("### [" ^ proc.proc_name ^ "] body1 (after trans_exp_ptr): \n " ^ (string_of_exp body1)) in *)
     (*Similar to Astsimp.trans_proc*)
     (* let () = E.clear () in *)
     let () = E.push_scope () in
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
     (*addressable reference variables*)
     let rvars = Hashtbl.find h proc.proc_name in
     (*addr_vars contains variables that are taken adrress-of in e1*)
     let addr_vars = find_addr body1 in
     (* if ((rvars@addr_vars) =[]) then *)
     (*   (\*no addresable variables --> for perf efficency*\) *)
     (*   {proc with proc_return  = new_ret_t; *)
     (*       proc_mingled_name = new_mingled; *)
     (*       proc_args = new_params; *)
     (*       proc_body = (Some body1)} *)
     (* else *)
     let val_params,ref_params = List.partition (fun p -> (p.param_mod = NoMod)) all_args in
     (*addressable reference parameters of this procedure only*)
     let rrparams = List.filter (fun param -> List.mem param.param_name rvars) ref_params in
     let rrvars = List.map (fun param -> param.param_name) rrparams in

     (*=============TRANSPEC (if any)============>*)
     let trans_p param =
       if List.mem param.param_name rrvars then
         let t = convert_prim_to_obj param.param_type in
         let new_param = {param with
                          param_mod = NoMod;
                          param_type=t} in
         (true,new_param)
       else
         (false,param)
     in
     let flags,new_params2 = List.split (List.map (fun param -> trans_p param) new_params) in
     let (new_static_specs,new_dynamic_specs) =
       (*If it is an orignal proc, then translate
         Spec for aux_proc has been translated in advance*)
       if (is_aux == false) && (List.exists (fun (b:bool) -> b) flags) then
         let new_static_specs = trans_specs proc.proc_static_specs new_params2 flags no_pos in
         let new_dynamic_specs = trans_specs proc.proc_dynamic_specs new_params2 flags no_pos in
         (new_static_specs,new_dynamic_specs)
       else
         (proc.proc_static_specs,proc.proc_dynamic_specs)
     in
     (*<=============TRANSPEC (if any)============*)
     (* let () = print_endline ("addr_vars = " ^ (string_of_ident_list addr_vars)) in *)
     (*List of pass-by-val/ref params that have been taken address-of*)
     let val_params1,_ = List.partition (fun p -> List.mem p.param_name addr_vars) val_params in
     (* let ref_params1,_ = List.partition (fun p -> List.mem p.param_name addr_vars) ref_params in *)

        (*
          for each arg in val_params1:
          int_ptr ptr_arg = new int_ptr(arg);
          sub(arg |-> ptr_arg)[e1]
          delete(ptr_arg);

          for each arg in ref_params1:
          int_ptr ptr_arg = new int_ptr(arg);
          sub(arg |-> ptr_arg)[e1]
          arg = ptr_arg.val;
          delete(ptr_arg);
        *)
     let val_ptrs = List.map (fun p ->
         let name = (ptr_string^"_"^ p.param_name) in
         let t = convert_prim_to_obj p.param_type in
         {p with param_type=t; param_name = name}) val_params1 
     in
     (* let ref_ptrs = List.map (fun p -> *)
     (*                          let name = (ptr_string^"_"^ p.param_name) in *)
     (*                          let t = convert_prim_to_obj p.param_type in *)
     (*                          {p with param_type=t; param_name = name}) ref_params1  *)
     (* in *)
     let val_subst = List.map2 (fun v ptr -> (v.param_name,ptr.param_name)) val_params1 val_ptrs in
     (* let ref_subst = List.map2 (fun v ptr -> (v.param_name,ptr.param_name)) ref_params1 ref_ptrs in *)
     let all_subst = val_subst(* @ref_subst *) in

     (* let () = print_endline ("val_subst = " ^ (string_of_subst val_subst)) in *)
     (* let () = print_endline ("ref_subst = " ^ (string_of_subst ref_subst)) in *)
     let body2 = if (all_subst!=[]) then
         subst_exp body1 all_subst 
       else
         body1
     in
     (* let () = print_endline ("body2 (after all_subst) : \n" ^ (string_of_exp body2)) in *)

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
     let todo_unk = List.map (fun v -> E.add v.E.var_name (E.VarInfo v)) vinfos in
     (*Need to trans_exp_addr of
       addressable reference variables  : rvars (from hashtbl h)
       and addressable local variables
       Note that (rvars - addr_vars) may be non-empty
     *)

     let trans_vars = 
       if (is_aux) then
         (*trans everything*)
         Gen.BList.remove_dups_eq (=) (rvars@addr_vars)
       else
            (*
              rvars : addressable reference variables (due to this proc and its callers,callees)
              addr_vars : addressable variables of this procedure only
              rrvars : addressable reference variables of this procedure only
            *)
         (*trans everything, except those that are reference parameters of this proc*)
         Gen.BList.remove_dups_eq (=) (rvars@addr_vars)
         (* Gen.BList.difference_eq (=) (rvars@addr_vars) rrvars *)
     in
     (* let () = print_endline ("### [" ^ proc.proc_name ^ "] trans_vars:  " ^ (string_of_ident_list trans_vars)) in *)
     let body3 = trans_exp_addr prog body2 trans_vars in
     let _,inner_vars = List.split (E.visible_names ()) in
     (*those that were converted and need to be deleted
       Do not delete addressable reference parameters
     *)
     let tmp_vars =  Gen.BList.difference_eq (=) (rvars@addr_vars) rrvars in
     let vars = compute_vars_to_delete tmp_vars [] inner_vars in
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
     (* let () = print_endline ("new_body2: \n " ^ (string_of_exp new_body2)) in *)
     (* <<< Add code for pass-by-val variables that are addressed of*)
     (*Add code for pass-by-ref variables that are addressed of*)
     (* let tmp_ref = List.combine ref_params1 ref_ptrs in *)
     (* let new_body3 =  *)
     (*   if (tmp_ref!=[]) then *)
     (*   List.fold_left (fun e (x,ptrx) -> add_code_ref e (x,ptrx)) new_body2 tmp_ref *)
     (*   else *)
     (*     new_body2 *)
     (* in *)
     (* let () = print_endline ("### [" ^ proc.proc_name ^ "] new_body3: \n " ^ (string_of_exp new_body3)) in *)
     (* <<< Add code for pass-by-ref variables that are addressed of*)

     let () = E.pop_scope () in
     (* let () = E.clear () in *)
     let ptypes2 = List.map (fun p -> p.param_type) new_params2 in
     let new_mingled2 = mingle_name_enum prog proc.proc_name ptypes2 in
     let new_proc = 
       {proc with proc_return  = new_ret_t;
                  proc_mingled_name = new_mingled2;
                  proc_static_specs = new_static_specs;
                  proc_dynamic_specs = new_dynamic_specs;
                  proc_args = new_params2;
                  proc_body = (Some new_body2)}
     in
     (* let () = print_endline ("new_proc = " ^ (string_of_proc_decl new_proc)) in *)
     new_proc
  )


and trans_proc_decl prog (proc:proc_decl) (is_aux:bool): proc_decl =
  Debug.no_1 "trans_proc_decl"
    string_of_proc_decl string_of_proc_decl
    (fun _ ->  trans_proc_decl_x prog proc is_aux) proc

(*
  @param vs : addressable reference params
*)
(*inter-procedural analysis*)
let rec find_addr_inter_proc prog (proc:proc_decl) (vs:ident list): ident list =
  (*Identify list of addressable params ONLY inside proc_body*)
  let mn = proc.proc_name in
  let rvars,from_hashtbl = 
    (try
       (*look up*)
       let rvars = Hashtbl.find h mn in
       let dvars = Gen.BList.difference_eq (=) vs rvars in
       if (dvars=[]) then 
         (rvars,true) 
       else
         let new_rvars = (rvars@dvars) in
         (new_rvars,false)
     with | Not_found ->
       (vs,false)
    )
  in
  if (from_hashtbl) then rvars else
    (*if not found -> find*)
    (match proc.proc_body with
     | None -> 
       let () = Hashtbl.replace h proc.proc_name [] in
       []
     | Some e ->
       (* let () = print_endline ("find_addr_inter_proc: proc_name = " ^ proc.proc_name) in *)
       (*vars that have been taken address_of in proc body*)
       let addr_vars = find_addr e in
       (* if ((rvars@addr_vars) = []) then  *)
       (*   let () = Hashtbl.replace h proc.proc_name [] in *)
       (*   [] *)
       (* else *)
       (*reference params that have been taken address_of*)
       let params = List.filter (fun param ->
           (((List.mem param.param_name addr_vars) && (param.param_mod = RefMod))
            || (List.mem param.param_name rvars))
         ) proc.proc_args in
       (*create an entry for the hashtbl*)
       let p_names = List.map (fun p -> p.param_name) params in
       let () = Hashtbl.replace h proc.proc_name p_names in
       (*vars that have been passed as reference and 
         are addressable in callees of this proc*)
       (* let () = print_endline (proc.proc_name ^ " : vs" ^ (string_of_ident_list vs)) in *)
       (* let () = print_endline (proc.proc_name ^ " : addr_vars" ^ (string_of_ident_list addr_vars)) in *)
       (* let () = print_endline (proc.proc_name ^ " : rvars" ^ (string_of_ident_list rvars)) in *)
       (* let () = print_endline (proc.proc_name ^ " : p_names" ^ (string_of_ident_list p_names)) in *)
       let vars = find_addr_inter_exp prog proc e addr_vars in
       (* let () = print_endline (proc.proc_name ^ " : vars" ^ (string_of_ident_list vars)) in *)
       let vars = Gen.BList.remove_dups_eq (=) (p_names@vars) in
       let () = Hashtbl.replace h proc.proc_name vars in
       vars
    )

(*
  @param vs : addressible variables in the entire method body
  @return : addressible variables that are passed by reference
*)
and find_addr_inter_exp prog proc e (vs:ident list) : ident list =
  let rec helper e vs=
    match e with
    | Var v -> []
    | VarDecl v ->
      let vars = List.map (fun (id,e0,pos) ->
          match e0 with
          | None -> []
          | Some e0 -> helper e0 vs) v.exp_var_decl_decls
      in
      let vars = List.concat vars in
      vars
    | ConstDecl c ->
      let vars = List.map (fun (id,e0,pos) -> helper e0 vs) c.exp_const_decl_decls in
      let vars = List.concat vars in
      vars
    | Unary u ->
      let vars = helper u.exp_unary_exp vs in
      vars
    | ArrayAt b ->
      let vars1 =  helper b.exp_arrayat_array_base vs in
      let vars2 = List.concat (List.map (fun e -> helper e vs) b.exp_arrayat_index) in
      (vars1@vars2)
    | ArrayAlloc a ->
      let vars = List.concat (List.map (fun e -> helper e vs) a.exp_aalloc_dimensions) in
      vars
    | Assert _ -> []
    | Assign a ->
      let vs1 = helper a.exp_assign_lhs vs in
      let vs2 = helper a.exp_assign_rhs vs in
      (vs1@vs2)
    | Binary b ->
      let vs1 = helper b.exp_binary_oper1 vs in
      let vs2 = helper b.exp_binary_oper2 vs in
      (vs1@vs2)
    | Bind b ->
      let vars = helper b.exp_bind_body vs in 
      vars
    | Block b ->
      (*Note: no more Block after case_normalize_program*)
      let vars = helper b.exp_block_body vs in
      vars
    | BoolLit _ -> []
    | Break _ -> []
    | CallRecv {exp_call_recv_method = orig_mn;
                exp_call_recv_arguments = args;
                exp_call_recv_pos = pos}
    | CallNRecv {exp_call_nrecv_method = orig_mn;
                 exp_call_nrecv_arguments = args;
                 exp_call_nrecv_pos = pos} ->
      if (orig_mn=Globals.init_name ||
          orig_mn=Globals.finalize_name ||
          orig_mn=Globals.acquire_name ||
          orig_mn=Globals.release_name) 
      then
        []  (* ignore *)
      else
        let mn,args =
          if (orig_mn=Globals.fork_name) then
            let fn_exp = (List.hd args) in
            match fn_exp with
            | Var v ->
              (v.exp_var_name,List.tl args)
            | _ ->
              Error.report_error {Error.error_loc = no_pos; Error.error_text = ("[Pointers.ml] expecting a method name as the first parameter of a fork")}
          else
            (orig_mn,args)
        in
        (* let vars = List.concat (List.map (fun e -> helper e vs) args) in *)
        (try
           let decl = look_up_proc_def_raw prog.prog_proc_decls mn in
           let params = decl.proc_args in
           (*rvars is the old list of addressible variables in the hashtbl*)
           let rvars,from_hashtbl =
             (try
                (*look up*)
                let rvars = Hashtbl.find h mn in
                (rvars,true)
              with | Not_found ->
                (*not found -> find*)
                ([],false)
             ) in
           (*find list of addressible variables and their corresponding param 
             that are passed by reference to the procedure*)
           (* let () = print_endline ( "CallNRecv: proc " ^ mn ^ " : vs = " ^ (string_of_ident_list vs)) in *)
           let tmp =
             (try
                List.map2 (fun param arg ->
                    if (param.param_mod = RefMod) then
                      (match arg with
                       | Var v ->
                         (*if the actual arg is an addressable variable*)
                         if (List.mem v.exp_var_name vs) then
                           [v.exp_var_name,param.param_name]
                         else
                           []
                       | Member _ ->
                         [] (*TO CHECK: ignore at the moment*)
                       | _ ->
                         Error.report_error 
                           {Err.error_loc = pos;
                            Err.error_text = "Expecting only variables are passed by reference in procedure " ^ mn ^ ": arg = " ^ string_of_exp arg})
                    else []
                  ) params args
              with | _ ->
                let () = print_endline_quiet ("args = " ^ (pr_list string_of_exp args)) in
                let () = print_endline_quiet ("params = " ^ (string_of_param_list params)) in
                Error.report_error 
                  {Err.error_loc = pos;
                   Err.error_text = "Procedure " ^ orig_mn ^ " Args and Params not matched "})
           in
           (*pvars is the new list of addressable params*)
           let avars,pvars = List.split (List.concat tmp) in
           (* let () = print_endline (proc.proc_name ^ " :: CallNRecv: proc " ^ mn ^ " : avars = " ^ (string_of_ident_list avars)) in *)
           (* let () = print_endline (proc.proc_name ^ " :: CallNRecv: proc " ^ mn ^ " : pvars = " ^ (string_of_ident_list pvars)) in *)
           (*TO CHECK: recursive call ??? *)
           (*============FIXPOINT=========================>*)
           let rvars =
             let dvars = Gen.BList.difference_eq (=) pvars rvars in
             if ((dvars=[]) && (from_hashtbl=true)) 
             then
               (* let () = print_endline ( "CallNRecv: proc " ^ mn ^ " : fixed-point") in *)
               rvars  (*reach fix-point*)
             else
               let new_rvars = (rvars@dvars) in
               (* let () = print_endline ( "CallNRecv: proc " ^ mn ^ " : new_rvars = " ^ (string_of_ident_list new_rvars)) in *)
               (*re-compute the list of addressible reference parameters
                 for the proc decl*)
               find_addr_inter_proc prog decl new_rvars
           in
           (*<======================================*)
           (* let () = print_endline ( "CallNRecv: proc " ^ mn ^ " : rvars = " ^ (string_of_ident_list rvars)) in *)
           let fct param arg =
             if (List.mem param.param_name rvars) then
               (*identifer the variable name*)
               (match arg with
                | Var v ->
                  [v.exp_var_name]
                | _ ->
                  Error.report_error 
                    {Err.error_loc = pos;
                     Err.error_text = "Expecting only variables are passed by reference in procedure " ^ mn ^ ": arg = " ^ string_of_exp arg})
             else []
           in
           (*vars that are passed as addressable params*)
           let vars = List.map2 fct params args in
           let vars = List.concat vars in
           (* let () = print_endline (proc.proc_name ^ " :: CallNRecv: proc " ^ mn ^ " : rvars = " ^ (string_of_ident_list rvars)) in *)
           (* let () = print_endline (proc.proc_name ^ " :: CallNRecv: proc " ^ mn ^ " : vars = " ^ (string_of_ident_list vars)) in *)
           vars
         with Not_found ->
           Error.report_error 
             {Err.error_loc = pos;
              Err.error_text = "Procedure " ^ mn ^ " not found!"})
    | Cast c ->
      let vs = helper c.exp_cast_body vs in
      vs
    | Cond c ->
      let vs1 = helper c.exp_cond_condition vs in
      let vs2 = helper c.exp_cond_then_arm vs in
      let vs3 = helper c.exp_cond_else_arm vs in
      (vs1@vs2@vs3)
    | Finally f ->
      let vs = helper f.exp_finally_body vs in
      vs
    | Label ((pid,plbl),e0) ->
      let vs = helper e0 vs in
      vs
    | Member m ->
      let vs = helper m.exp_member_base vs in
      vs
    | New n ->
      let vs = List.concat (List.map (fun e -> helper e vs) n.exp_new_arguments) in
      vs
    | Try t ->
      let vs1 = helper t.exp_try_block vs in
      (*vars in try_block are still in scopes of catch_clauses
        and finally clause*)
      let vs2 = List.concat (List.map (fun e -> helper e vs) t.exp_catch_clauses) in
      let vs3 = List.concat (List.map (fun e -> helper e vs) t.exp_finally_clause) in
      (vs1@vs2@vs3)
    | Raise r -> (*Assume no pointers*)
      []
    | Catch _ -> (*assume no pointer*)
      []
    | Return r ->
      (match r.exp_return_val with
       | None -> []
       | Some e0 ->
         let vs = helper e0 vs in
         vs
      )
    | Seq s ->
      let vs1 = helper s.exp_seq_exp1 vs in
      let vs2 = helper s.exp_seq_exp2 (vs@vs1) in
      (vs1@vs2) (*TO CHECK: ??? *)
    | This _ -> (*assume no pointer *)
      []
    | While w ->
      let vs1 = helper w.exp_while_condition vs in
      let vs2 = helper w.exp_while_body vs in
      (*TO CHECK: not sure what exp_while_wrappings is for? *)
      let vs3 =
        (match w.exp_while_wrappings with
         | None -> []
         | Some (e0,_) ->
           helper e0 vs
        )
      in
      (vs1@vs2@vs3)
    | Par _ -> [] (* TODO: Par *)
    | Debug _
    | Dprint _
    | Empty _
    | FloatLit _
    | IntLit _
    | Java _
    | Null _
    | Time _
    | Unfold _
    | Barrier _ (*TO CHECK*)
    | Continue _ -> []
  in helper e vs

let trans_pointers_x (prog : prog_decl) : prog_decl =
  let gvar_decls = prog.prog_global_var_decls in
  let new_gvar_decls = List.map (x_add_1 trans_global_var_decl) gvar_decls in
  (* let procs = prog.prog_proc_decls in *)
  (*Empty hashtbl h*)
  let () = Hashtbl.clear h in
  let _ =
    (try
       List.map (fun proc -> find_addr_inter_proc prog proc []) prog.prog_proc_decls

     with | Not_found ->
       Error.report_error
         {Err.error_loc = no_pos;
          Err.error_text = "[trans_pointers] Exception when find_addr_inter_proc"})
  in
  (* let () = *)
  (*   (try *)
  (*        List.map (fun proc -> *)
  (*            let vars = Hashtbl.find h proc.proc_name in *)
  (*            if (vars!=[]) then *)
  (*            print_endline ("After find_addr_inter_proc --> " ^ proc.proc_name ^ " : " ^ string_of_ident_list vars) *)
  (*        ) prog.prog_proc_decls *)
  (*    with | Not_found -> *)
  (*        Error.report_error *)
  (*            {Err.error_loc = no_pos; *)
  (*             Err.error_text = "[trans_pointers] Exception when find_addr_inter_proc"}) *)
  (* in *)
  (* let () = print_endline ("start elimiating pointers in proc_decl..."); flush stdout in *)
  let new_procs = List.map (fun proc -> trans_proc_decl prog proc false) prog.prog_proc_decls in
  let new_procs1 = new_procs@(!aux_procs) in
  {prog with prog_global_var_decls = new_gvar_decls;
             prog_proc_decls = new_procs1;}

let trans_pointers (prog : prog_decl) : prog_decl =
  (* let pr x = (pr_list string_of_global_var_decl) x.Iast.prog_global_var_decls in *)
  let pr x = (string_of_program x) in
  Debug.no_1 "trans_pointers" pr pr trans_pointers_x prog
