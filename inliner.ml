#include "xdebug.cppo"
open VarGen
open Globals
open Iast

(*
  functions to be inlined, specified via command line
*)
let inlined_procs = ref ([] : string list)

let set_inlined arg =
  let procs = Gen.split_by "," arg in
  inlined_procs := procs @ !inlined_procs

(*
  inlining: transform a call in Iast to an expression block in Iast
*)

let is_inlined mn : bool = List.mem mn !inlined_procs

let rec inline (prog : prog_decl) (pdef : proc_decl) (e0 : exp) : exp = match e0 with
  | CallNRecv ({exp_call_nrecv_method = mn;
                exp_call_nrecv_arguments = args;
                exp_call_nrecv_pos = pos}) -> 
    begin
      (* assign actual args to formal args *)
      (* by-ref parameter: substitution *)
      if List.exists (fun p -> p.param_mod = RefMod) pdef.proc_args then
        Error.report_error { Error.error_text = "inline: ref parameter is not supported now";
                             Error.error_loc = pos }
      else if not (Gen.is_some pdef.proc_body) then
        Error.report_error { Error.error_text = "inline: can't inline primitive";
                             Error.error_loc = pos }
      else
        (* assign actual arguments to fresh vars *)
        let mkfvar param arg = 
          let fname = fresh_ty_var_name (param.param_type) pos.start_pos.Lexing.pos_lnum in
          (*-- 09.05.2008 *)
          (*let () = (print_string ("\n[inliner.ml, line 37]: fresh name = " ^ fname ^ "\n")) in*)
          (* 09.05.2008 --*)		
          (VarDecl { exp_var_decl_type = param.param_type;
                     exp_var_decl_decls = [(fname, Some arg, pos)];
                     exp_var_decl_pos = pos }, fname) in
        let tmp1 = List.map2 mkfvar pdef.proc_args args in
        let fresh_args, fresh_names = List.split tmp1 in

        (* assign fresh vars to formal arguments. This is to avoid name clashing 
           			   if actual and formal arguments have the same name. Put them in nested blocks. *)
        let mkvar param fname = VarDecl { exp_var_decl_type = param.param_type;
                                          exp_var_decl_decls = [(param.param_name, 
                                                                 Some (Var {exp_var_name = fname;
                                                                            exp_var_pos = pos}), pos)];
                                          exp_var_decl_pos = pos } in
        let var_defs = List.map2 mkvar pdef.proc_args fresh_names in

        let new_proc_body = remove_return (Gen.unsome pdef.proc_body) in
        let seq1 = List.fold_left (fun s -> fun vd -> mkSeq vd s pos) new_proc_body var_defs in
        (* make a block to localize formal args *)
        let block1 = Block { exp_block_body = seq1;
                             exp_block_jump_label = NoJumpLabel;
                             exp_block_local_vars = [];
                             exp_block_pos = pos } in
        let seq2 = List.fold_left (fun s -> fun vd -> mkSeq vd s pos) block1 fresh_args in
        let block2 = Block { exp_block_body = seq2;
                             exp_block_jump_label = NoJumpLabel;
                             exp_block_local_vars = [];
                             exp_block_pos = pos } in
   (*
			  print_string ("\nblock1:\n" ^ (Iprinter.string_of_exp block1) ^ "\n");
			  print_string ("\nblock2:\n" ^ (Iprinter.string_of_exp block2) ^ "\n");
			*)
        block2
    end
  | _ -> e0

and remove_return (e0 : exp) : exp = match e0 with
  | Return { exp_return_val = oe;
             exp_return_pos = pos } -> begin
      match oe with
      | Some e -> e
      | None -> Empty pos
    end
  | Seq { exp_seq_exp1 = e1;
          exp_seq_exp2 = e2;
          exp_seq_pos = pos } -> mkSeq (remove_return e1) (remove_return e2) pos
  | While ({ exp_while_body = e } as e1) -> While {e1 with exp_while_body = remove_return e}
  | Cond ({ exp_cond_then_arm = then_arm; 
            exp_cond_else_arm = else_arm } as e1) -> Cond {e1 with 
                                                           exp_cond_then_arm = remove_return then_arm;
                                                           exp_cond_else_arm = remove_return else_arm; }
  | Bind ({ exp_bind_body = e } as e1) -> Bind {e1 with exp_bind_body = remove_return e}
  | Block ({ exp_block_body = e } as e1) -> Block {e1 with exp_block_body = remove_return e}
  | _ -> e0
