#include "xdebug.cppo"
open VarGen
(*
  Runtime checker.

  Emit runtime checks.

  Compute checks that need to be done prior to each expression.
  Assignments: 
  Things like w.f.g = e will be flattened out to
  tmp1 = w.f;
  tmp1.g = e;

  Finding checks that need to be done prior to an expression. How?
  sequence, conditional -> push down, need to be done at the following:
  assignment, call, bind, suppose we have small binds.

  var tmp;
  tmp = bind v to (...f...) in { f }

  var tmp;
  if (v.color != curColor) throw
  tmp = v.f
*)

open Globals
open Solver
open Predcomp

module CF = Cformula
module CP = Cpure
module C = Cast
module I = Iast

let primitives =
  ["add___";
   "minus___";
   "mult___";
   "div___";
   "mod___";
   "eq___";
   "neq___";
   "lt___";
   "lte___";
   "gt___";
   "gte___";
   "land___";
   "lor___";
   "not___";
   "is_not_null___";
   "is_null___"]

let no_pp = ref ([] : string list)

let set_nopp arg = 
  let procs = Gen.split_by "," arg in
  no_pp := procs @ !no_pp

let no_field = ref ([] : string list)

let set_nofield arg =
  let flds = Gen.split_by "," arg in
  no_field := flds @ !no_field

(*
  Utility functions
*)

let write_to_file java_code file_name : unit =
  let ochn = open_out ("output/" ^ file_name) in
  output_string ochn (Buffer.contents java_code);
  close_out ochn

(*
  Compile a program to Java, with runtime checks inserted.

  - Predicates: each predicate c is compiled to a class and stored
  in a separate file named c_Checker.

  - Data declarations: Each data declaration is compiled to a class
  with the same name. A field named "color" is also added. Each data
  declaration is stored in a separate file with the same name.

  - Procedures: Each procedure p is compiled to
  + A class for precondition: p_Pre
  + A class for postcondition: p_Post
  + Body is instrumented.
  + All procedures are stored together in a file with the same name as 
  input file (with .java extension).

  - All input files are put in a subdirectory of the working directory.
  The name of the subdirectory is "output".
*)

let rec compile_prog (prog : C.prog_decl) source : unit =
  let java_code = Buffer.create 10240 in
  (* Compile data declarations *)
  let todo_unk = List.map 
      (fun ddef -> compile_data prog ddef java_code) 
      prog.C.prog_data_decls 
  in
  (* Compile predicates *)
  let pbvars_tmp = List.map
      (fun vdef -> compile_view prog vdef java_code)
      prog.C.prog_view_decls
  in
  let pbvars = List.concat pbvars_tmp in
  let () = compile_partially_bound_vars pbvars java_code in
  (* Compile procedures *)
  let () = Buffer.clear java_code in
  (* Compile specs *)
  (* 
     let todo_unk = List.map 
     (fun pdef -> compile_proc_spec prog pdef java_code) prog.C.old_proc_decls in
  *)
  let () = C.proc_decls_iter prog (fun pdef -> compile_proc_spec prog pdef java_code) in
  (* Compile bodies *)
  (* add class declaration *)
  let tmp = Filename.chop_extension (Filename.basename source) in
  let main_class = Gen.replace_minus_with_uscore tmp in
  let () = Buffer.add_string java_code ("public class " ^ main_class ^ " {\n") in
  (*
    let todo_unk = List.map (fun pdef -> 
    compile_proc_body prog pdef java_code) prog.C.old_proc_decls in
  *)
  let () = C.proc_decls_iter prog (fun pdef -> compile_proc_body prog pdef java_code) in
  let () = Buffer.add_string java_code ("\n}\n") in
  let tmp2 = Gen.replace_minus_with_uscore (Filename.chop_extension source) in
  write_to_file java_code (tmp2 ^ ".java")

and compile_data prog ddef java_code : unit = 
  if not (ddef.C.data_name = "String" || ddef.C.data_name = "Object") then begin
    Buffer.clear java_code;
    Cjava.java_of_data_decl prog ddef java_code;
    write_to_file java_code (ddef.C.data_name ^ ".java")
  end

and compile_view prog vdef java_code : (CP.spec_var list) =
  let data_def, pbvars = Predcomp.gen_view prog vdef in
  let pstr = Java.java_of_data2 data_def in
  Buffer.clear java_code;
  Buffer.add_string java_code pstr;
  write_to_file java_code (vdef.C.view_name ^ "_Checker.java");
  pbvars

and remove_dup_types (vars : CP.spec_var list) : CP.spec_var list = match vars with
  | (((CP.SpecVar (tv, v, _)) as h) :: rest) ->
    if List.exists 
        (fun (CP.SpecVar (t, _, _)) -> string_of_typ t = CP.name_of_type tv) rest
    then
      remove_dup_types rest
    else
      h :: (remove_dup_types rest)
  | [] -> []

and compile_partially_bound_vars (pbvars : CP.spec_var list) java_code : unit = 
  let pbvars = remove_dup_types pbvars in
  let pstr = Java.java_of_partially_bound_params2 pbvars in
  Buffer.clear java_code;
  Buffer.add_string java_code pstr;
  write_to_file java_code ("AugClasses.java")

and compile_proc_body (prog : C.prog_decl) (proc : C.proc_decl) java_code : unit =
  if Gen.is_some proc.C.proc_body then begin
    let body = Gen.unsome proc.C.proc_body in
    let cbody = compile_exp prog proc body in
    let cproc = {proc with 
                 C.proc_name = C.unmingle_name proc.C.proc_name;
                 C.proc_body = Some cbody} in
    Cjava.java_of_proc_decl prog cproc java_code
  end

and compile_proc_spec (prog : C.prog_decl) (proc : C.proc_decl) java_code : unit = 
  let r = Cformula.split_struc_formula (proc.C.proc_stk_of_static_specs # top) (* proc.C.proc_static_specs *) in
  match r with
  | [] -> 
    let pre = CF.mkTrue ( CF.mkNormalFlow ()) no_pos in
    let post = CF.mkTrue ( CF.mkNormalFlow ()) no_pos in
    let pre_outvars, pbvars = compile_pre prog proc pre java_code in
    compile_post prog proc post pre_outvars pbvars java_code		
  | [(pre, post)] -> 
    let pre_outvars, pbvars = compile_pre prog proc pre java_code in
    compile_post prog proc post pre_outvars pbvars java_code
  | _ -> failwith ("compile_proc: currently support only at most one pair of pre/post: " ^ proc.C.proc_name)

(*
  Each method is compiled to 
  - a preconditiion class
  - a postcondition class
  - a method with instrumented body

  invocations to precond and postcond are done at call sites to
  facilitate integration.

  Return value:
  first component: output vars of precond
  second component: partially bound output vars
*)
and compile_pre (prog : C.prog_decl) (proc : C.proc_decl) (pre : CF.formula) java_code : (CP.spec_var list * CP.spec_var list) =
  if List.mem (C.unmingle_name proc.C.proc_name) primitives then
    ([], [])
  else
    let pos = CF.pos_of_formula pre in
    let pre_fv = CF.fv pre in
    let fargs = proc.C.proc_args in
    let farg_names = List.map snd fargs in
    let farg_types = List.map fst fargs in
    let farg_spec_vars = List.map2 
        (fun n -> fun t -> CP.SpecVar (t, n, Unprimed)) 
        farg_names farg_types in
    let output_vars = Gen.BList.difference_eq CP.eq_spec_var pre_fv farg_spec_vars in
    (* build vmap *)
    let vmap = H.create 103 in
    let todo_unk = List.map 
        (fun fname -> H.add vmap fname (HExp ("this", fname, false))) farg_names in
    let () = Predcomp.precond_output := output_vars in
    let combined_exp, disj_procs, _ = 
      gen_formula prog pre vmap [] (*output_vars*) in
    let () = Predcomp.precond_output := [] in
    (* generate fields *)
    let pbvars = get_partially_bound_vars prog pre in
    let fields_tmp = CP.remove_dups_spec_var_list (farg_spec_vars @ pre_fv) in
    let fields = gen_fields fields_tmp pbvars pos in
    (* parameters for traverse *)
    let check_proc = 
      { I.proc_name = "traverse";
        I.proc_source = "source_file";
        I.proc_flags = [];
        I.proc_hp_decls = [];
        I.proc_mingled_name = "";
        I.proc_data_decl = None;
        I.proc_constructor = false;
        I.proc_args = [cur_color pos; new_color pos];
        I.proc_args_wi = List.map (fun p -> (p.I.param_name,Globals.I)) [cur_color pos; new_color pos];
        I.proc_ho_arg = None;
        I.proc_return = Bool;
        I.proc_static_specs = Iformula.mkETrueF ();
        I.proc_dynamic_specs = Iformula.mkEFalseF ();
        I.proc_body = Some combined_exp;
        I.proc_exceptions = [];
        I.proc_is_main = false;
        I.proc_is_while = false;
        I.proc_has_while_return = false;
        I.proc_is_invoked = false;
        I.proc_verified_domains = [];
        I.proc_file = "";
        I.proc_loc = no_pos;
        I.proc_test_comps = None } in
    let ddef = { I.data_name = (C.unmingle_name proc.C.proc_name) ^ "_PRE";
                 I.data_fields = fields;
                 I.data_pos = no_pos;
                 I.data_parent_name = "Object";
                 I.data_invs = [];
                 I.data_pure_inv = None;
                 I.data_is_template = false;
                 I.data_methods = check_proc :: disj_procs } in
    let () = check_proc.I.proc_data_decl <- Some ddef in
    let java_str = Java.java_of_data ddef [] in
    Buffer.add_string java_code "\n\n";
    Buffer.add_string java_code java_str;
    (output_vars, pbvars)

(*
  Compilation of postcondition:
  - All method parameters are input.
  - All output parameters from preconditions are input.

  Postcondition checker does not need to compute output vars.
*)
and compile_post (prog : C.prog_decl) (proc : C.proc_decl) (post : CF.formula) (pre_outvars : CP.spec_var list) (pbvars : CP.spec_var list) java_code : unit =
  if List.mem (C.unmingle_name proc.C.proc_name) primitives then
    ()
  else
    let pos = CF.pos_of_formula post in
    let post_fv = CF.fv post in
    let fargs = proc.C.proc_args in
    let farg_names = List.map snd fargs in
    let farg_types = List.map fst fargs in
    let farg_spec_vars = List.map2 
        (fun n -> fun t -> CP.SpecVar (t, n, Unprimed)) 
        farg_names farg_types in
    let farg_names =
      if proc.C.proc_return = C.void_type then
        farg_names
      else
        "res" :: farg_names 
    in
    let field_names = farg_names @ (List.map CP.name_of_spec_var pre_outvars) in
    (* build vmap *)
    let vmap = H.create 103 in
    let todo_unk = List.map 
        (fun fname -> H.add vmap fname (HExp ("this", fname, false))) field_names in
    (* compile formula *)
    let combined_exp, disj_procs, _ = gen_formula prog post vmap [] in
    (* generate fields *)
    let res = CP.SpecVar (proc.C.proc_return, "res", Unprimed) in
    let fields_tmp = 
      if proc.C.proc_return = C.void_type then
        CP.remove_dups_spec_var_list (farg_spec_vars @ post_fv @ pre_outvars)
      else
        CP.remove_dups_spec_var_list (res :: farg_spec_vars @ post_fv @ pre_outvars) 
    in
    (*
      let () = print_string ("Compiling " ^ proc.C.proc_name ^ "\n") in
      let () = print_string ((String.concat ", " (List.map CP.name_of_spec_var fields_tmp)) ^ "\n") in
    *)
    let fields = gen_fields fields_tmp pbvars pos in
    (* parameters for traverse *)
    let check_proc = 
      { I.proc_name = "traverse";
        I.proc_source = "source_file";
        I.proc_flags = [];
        I.proc_hp_decls = [];
        I.proc_mingled_name = "";
        I.proc_data_decl = None;
        I.proc_constructor = false;
        I.proc_args = [cur_color pos; new_color pos];
        I.proc_args_wi = List.map (fun p -> (p.I.param_name,Globals.I)) [cur_color pos; new_color pos];
        I.proc_ho_arg = None;
        I.proc_return = Bool;
        I.proc_static_specs = Iformula.mkETrueF ();
        I.proc_dynamic_specs = Iformula.mkEFalseF ();
        I.proc_body = Some combined_exp;
        I.proc_exceptions = [];
        I.proc_is_main = false;
        I.proc_is_while = false;
        I.proc_has_while_return = false;
        I.proc_is_invoked = false;
        I.proc_verified_domains = [];
        I.proc_file = "";
        I.proc_loc = no_pos;
        I.proc_test_comps =None } in
    let ddef = { I.data_name = (C.unmingle_name proc.C.proc_name) ^ "_POST";
                 I.data_fields = fields;
                 I.data_pos = no_pos;
                 I.data_parent_name = "Object";
                 I.data_invs = [];
                 I.data_pure_inv = None;
                 I.data_is_template = false;
                 I.data_methods = check_proc :: disj_procs } in
    let () = check_proc.I.proc_data_decl <- Some ddef in
    let java_str = Java.java_of_data ddef [] in
    Buffer.add_string java_code "\n\n";
    Buffer.add_string java_code java_str


and compile_exp prog proc (e0 : C.exp) : C.exp = match e0 with
  | C.Seq ({C.exp_seq_exp1 = e1;
            C.exp_seq_exp2 = e2} as e) ->
    let ce1 = compile_exp prog proc e1 in
    let ce2 = compile_exp prog proc e2 in
    C.Seq ({e with 
            C.exp_seq_exp1 = ce1;
            C.exp_seq_exp2 = ce2})
  | C.Cond ({C.exp_cond_then_arm = then_arm;
             C.exp_cond_else_arm = else_arm} as e) ->
    let cthen = compile_exp prog proc then_arm in
    let celse = compile_exp prog proc else_arm in
    C.Cond ({e with
             C.exp_cond_then_arm = cthen; 
             C.exp_cond_else_arm = celse})
  | C.Block ({C.exp_block_body = body} as e) ->
    let cbody = compile_exp prog proc body in
    C.Block ({e with C.exp_block_body = cbody})
  | C.Bind ({C.exp_bind_type = t_e0;
             C.exp_bind_bound_var = (t, v);
             C.exp_bind_pos = pos}) ->
    let mn = C.unmingle_name proc.C.proc_name in
    if !no_field = ["all"] || List.mem mn !no_field then 
      e0
    else
      let chk = C.CheckRef ({C.exp_check_ref_var = v;
                             C.exp_check_ref_pos = pos}) in
      let seq = C.mkSeq t_e0 chk e0 pos in
      seq
  | C.Assign ({C.exp_assign_lhs = lhs;
               C.exp_assign_rhs = rhs;
               C.exp_assign_pos = pos} as e) ->
    if C.is_cond rhs then
      (* 
	     This assignment was introduced by the Iast to Cast translation.
	     No effects on program execution.
	  *)
      compile_exp prog proc rhs
    else
      let mn = C.unmingle_name proc.C.proc_name in
      let normal_compile () =
        let bind_vars = find_binds rhs in
        let helper e (_, bv) =
          if !no_field = ["all"] || List.mem mn !no_field then 
            e
          else
            let chk = C.CheckRef ({C.exp_check_ref_var = bv;
                                   C.exp_check_ref_pos = pos}) in
            let seq = C.mkSeq C.void_type chk e pos in
            seq
        in
        let res = List.fold_left helper e0 bind_vars in
        res
      in
      if C.is_block rhs then
        let new_e = push_assignment_in lhs rhs pos in
        let crhs = compile_exp prog proc new_e in
        C.Assign ({e with C.exp_assign_rhs = crhs})
      else if C.is_call rhs then
        let call, result = compile_call prog proc rhs in
        if result = "" then
          normal_compile ()
        else
          let res_type = Gen.unsome (C.type_of_exp rhs) in
          let result_decl = C.VarDecl ({C.exp_var_decl_type = res_type;
                                        C.exp_var_decl_name = result;
                                        C.exp_var_decl_pos = pos}) in
          let result_e = C.Var ({C.exp_var_type = res_type;
                                 C.exp_var_name = result;
                                 C.exp_var_pos = pos}) in
          let new_assign = C.Assign ({C.exp_assign_lhs = lhs;
                                      C.exp_assign_rhs = result_e;
                                      C.exp_assign_pos = pos}) in
          let seq1 = C.mkSeq C.void_type call new_assign pos in
          let seq2 = C.mkSeq C.void_type result_decl seq1 pos in
          seq2
      else
        normal_compile ()
  | C.SCall _ ->
    fst (compile_call prog proc e0)
  | _ -> e0


(*
  Compile calls. If the call appear on rhs of an assignment,
  store the value of the call in a temporary that is returned
  as the second component.
*)
and compile_call prog proc (e0 : C.exp) : (C.exp * ident) = match e0 with
  | C.SCall ({C.exp_scall_method_name = mn0;
              C.exp_scall_arguments = vs;
              C.exp_scall_pos = pos}) -> begin
      let mn = C.unmingle_name mn0 in
      let caller_mn = C.unmingle_name proc.C.proc_name in
      if List.mem mn primitives || List.mem (caller_mn ^ ":" ^ mn) !no_pp then
        (e0, "")
      else
        (*let pdef = C.look_up_proc_def_raw prog.C.old_proc_decls mn0 in*)
        let pdef = C.look_up_proc_def_raw prog.C.new_proc_decls mn0 in
        let pre = 
          let r = Cformula.split_struc_formula (pdef.C.proc_stk_of_static_specs # top) (* pdef.C.proc_static_specs *) in 
          match r with
          | [(pre, post)] -> pre
          | [] -> CF.mkTrue (CF.mkNormalFlow ()) pos 
          | _ -> failwith ("compile_call: currently support only one pair of pre/post: " ^ mn)
        in
        let pre_fv = CF.fv pre in
        let fargs = pdef.C.proc_args in
        let farg_names = List.map snd fargs in
        let pre_fv_names = List.map CP.name_of_spec_var pre_fv in
        let output_vars = Gen.BList.difference_eq (=) pre_fv_names farg_names in
 (*
	  Create precondition checker.
	*)
        let pre_chkr_cls = mn ^ "_PRE" in
        let pre_chkr = fresh_name () in
        let pre_init_tmp = List.map2
            (fun farg -> fun aarg -> pre_chkr ^ "." ^ farg ^ " = " ^ aarg ^ ";") 
            farg_names vs in
        let pre_init = String.concat "\n" pre_init_tmp in
        let pos_str = Debug.string_of_pos pos in
        let pre_traverse_call = 
          "\nRTC.call();\n"
          ^ "if (!(" ^ pre_chkr ^ ".traverse(RTC.callStack[RTC.size - 1], RTC.curColor))) {\n"
          ^ "\tSystem.out.println(\"" ^ pos_str ^ "precondition violation.\");\n"
          ^ "\tSystem.exit(-1);\n"
          ^ "}\n" in
        let java_pre_str = 
          pre_chkr_cls ^ " " ^ pre_chkr ^ ";\n"
          ^ pre_chkr ^ " = new " ^ pre_chkr_cls ^ "();\n"
          ^ pre_init ^ pre_traverse_call in
        let java_pre = C.Java ({C.exp_java_code = java_pre_str;
                                C.exp_java_pos = pos}) in
 (*
	  Create postcondition checker.
	*)
        let post_chkr_cls = mn ^ "_POST" in
        let post_chkr = fresh_name () in
        let post_init_tmp1 = List.map2
            (fun farg -> fun aarg -> post_chkr ^ "." ^ farg ^ " = " ^ aarg ^ ";") 
            farg_names vs in
        let post_init_tmp2 = List.map
            (fun pre_v -> post_chkr ^ "." ^ pre_v ^ " = " ^ pre_chkr ^ "." ^ pre_v ^ ";")
            output_vars in
        let res = fresh_name () in
        let post_init_tmp3 =
          if pdef.C.proc_return = C.void_type then []
          else [post_chkr ^ ".res = " ^ res ^ ";"] in
        let post_init = String.concat "\n" 
            (post_init_tmp3 @ post_init_tmp1 @ post_init_tmp2) in
        let post_traverse_call = 
          "\nif (!(" ^ post_chkr ^ ".traverse(RTC.curColor, RTC.callStack[RTC.size - 1]))) {\n"
          ^ "\tSystem.out.println(\"" ^ pos_str ^ "postcondition violation.\");\n"
          ^ "\tSystem.exit(-1);\n"
          ^ "}\n" 
          ^ "RTC.ret();\n" in
        let java_post_str = 
          post_chkr_cls ^ " " ^ post_chkr ^ ";\n"
          ^ post_chkr ^ " = new " ^ post_chkr_cls ^ "();\n"
          ^ post_init ^ post_traverse_call in
        let java_post = C.Java ({C.exp_java_code = java_post_str;
                                 C.exp_java_pos = pos}) in
 (*
	  the call itself
	*)
        let call, result =
          if pdef.C.proc_return = C.void_type then
            (e0, "")
          else 
            let assign = C.Assign ({C.exp_assign_lhs = res;
                                    C.exp_assign_rhs = e0;
                                    C.exp_assign_pos = pos}) in
            (assign, res)
        in
 (*
	  Combine them.
	*)
        let seq1 = C.mkSeq C.void_type call java_post pos in
        let seq2 = C.mkSeq C.void_type java_pre seq1 pos in
        (seq2, result)
    end
  | _ -> failwith ("compile_call: " ^ (Cprinter.string_of_exp e0) ^ " unsupported.")

and push_assignment_in (lhs : ident) (rhs : C.exp) pos : C.exp = match rhs with
  | C.Seq ({C.exp_seq_exp1 = e1;
            C.exp_seq_exp2 = e2} as e) ->
    if C.is_unit e2 then
      C.Assign ({C.exp_assign_lhs = lhs;
                 C.exp_assign_rhs = e1;
                 C.exp_assign_pos = pos})
    else
      let new_e2 = push_assignment_in lhs e2 pos in
      let res = C.Seq ({e with C.exp_seq_exp2 = new_e2}) in
      res
  | C.Block ({C.exp_block_body = body} as e) ->
    let new_body = push_assignment_in lhs body pos in
    C.Block ({e with C.exp_block_body = new_body})
  | _ ->
    C.Assign ({C.exp_assign_lhs = lhs;
               C.exp_assign_rhs = rhs;
               C.exp_assign_pos = pos})

and find_binds (e0 : C.exp) : typed_ident list = match e0 with
  | C.Seq ({C.exp_seq_exp1 = e1;
            C.exp_seq_exp2 = e2}) 
  | C.Cond ({C.exp_cond_then_arm = e1;
             C.exp_cond_else_arm = e2}) ->
    let tmp1 = find_binds e1 in
    let tmp2 = find_binds e2 in
    tmp1 @ tmp2
  | C.Block ({C.exp_block_body = body}) -> find_binds body
  | C.Assign ({C.exp_assign_rhs = rhs}) -> find_binds rhs
  | C.Bind ({C.exp_bind_bound_var = bv}) -> [bv]
  | _ -> []
