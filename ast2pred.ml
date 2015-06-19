#include "xdebug.cppo"
open VarGen


(*
this module tranform an iast to pred
*)

open Globals
open Gen.Basic
open Wrapper
open Others
open Exc.GTable
open Printf
open Gen.Basic
open Gen.BList
open Mcpure_D
open Mcpure
open Label_only
open Typeinfer

module E = Env
module Err = Error
module I = Iast
module IF = Iformula
module IP = Ipure
module LO = Label_only.LOne
open IastUtil

let err_var = "#e"
let res_var = "#r"

type assert_err=
  | Safe
  | Unsafe
  | Unk
  | NotApp

let string_of_assert_err res= match res with
    | Safe -> "safe"
    | Unsafe -> "unsafe"
    | Unk -> "unknown"
    | NotApp -> "not applicable"

module Ast_sort= struct

  let sort_proc_decls (pl: proc_decl list) : proc_decl list =
    List.fast_sort (fun p1 p2 -> p1.proc_call_order - p2.proc_call_order) pl

  let same_call_scc p1 p2 = p1.proc_call_order == p2.proc_call_order

  (* returns (procs_wo_body, proc_mutual_rec list) *)
  (* The list of proc_decl must be sorted *)
  let re_proc_mutual (pl : proc_decl list) : (proc_decl list * ((proc_decl list) list) ) = 
    let (pr_prim, pr_rest) = List.partition is_primitive_proc pl in
    let rec helper acc pl = match pl with
      | [] -> if acc==[] then [] else [acc]
      | x::rest -> 
            begin
              match acc with
                | [] -> helper [x] rest
                | a::_ -> if same_call_scc a x then helper (x::acc) rest
                  else acc::(helper [x] rest)
            end
    in (pr_prim, helper [] pr_rest)


  module IG = Graph.Persistent.Digraph.Concrete(IdentComp)
  module IGO = Graph.Oper.P(IG)
  module IGC = Graph.Components.Make(IG)
  module IGP = Graph.Path.Check(IG)
  module IGN = Graph.Oper.Neighbourhood(IG)
  module IGT = Graph.Topological.Make(IG)

  let ex_args f a b = f b a

  let ngs_union gs = 
    List.fold_left IGO.union IG.empty gs 

  let addin_callgraph_of_exp (cg:IG.t) exp mnv : IG.t = 
    let f e =
      match e with
        | CallNRecv e ->
              (* let () = print_endline_quiet(mnv ^ " -> " ^ e.exp_icall_method_name) in *)
              Some (IG.add_edge cg mnv e.exp_call_nrecv_method)
        | CallRecv e ->
              (* let () = print_endline_quiet(mnv ^ " -> " ^ e.exp_scall_method_name) in *)
              Some (IG.add_edge cg mnv e.exp_call_recv_method)
        | _ -> None
    in
    fold_exp exp f ngs_union cg

  let addin_callgraph_of_proc cg proc : IG.t = 
    match proc.proc_body with
      | None -> cg
      | Some e -> addin_callgraph_of_exp cg e proc.proc_name

  let callgraph_of_prog prog : IG.t = 
    let cg = IG.empty in
    let pn pc = pc.proc_name in
    (*let mns = List.map pn prog.old_proc_decls in*)
    let mns = List.map pn prog.prog_proc_decls in 
    let cg = List.fold_right (ex_args IG.add_vertex) mns cg in
    List.fold_right (ex_args addin_callgraph_of_proc) prog.prog_proc_decls cg
    (* List.fold (fun acc pd -> ex_args addin_callgraph_of_proc pd acc) prog. cg *)


  let pr_proc_call_order p = 
    let n = p.proc_name in
    let c = p.proc_call_order in
    pr_pair pr_id string_of_int (n,c)

  let is_found (cp: prog_decl) (pname: Globals.ident) (scc: IG.V.t list) : bool =
    List.exists (fun m ->
        let mn = (look_up_proc_def_raw cp.prog_proc_decls m).proc_name in
        mn = pname) scc

  let find_scc_group (cp: prog_decl) (pname: Globals.ident) (scc_list: IG.V.t list list) : (IG.V.t list) =
    try List.find (fun scc -> is_found cp pname scc) scc_list
    with _ -> []

(* let rec irf_traverse_exp (cp: prog_decl) (exp: exp) (scc: IG.V.t list) : (exp * ident list) = *)
(*   match exp with *)
(*   | Label e ->  *)
(*     let ex, il = irf_traverse_exp cp e.exp_label_exp scc in *)
(*     (Label {e with exp_label_exp = ex}, il) *)
(*   | CheckRef _  *)
(*   | Java _ *)
(*   | Assert _ -> (exp, []) *)
(*   | Assign e ->  *)
(*     let ex, il = irf_traverse_exp cp e.exp_assign_rhs scc in *)
(*     (Assign {e with exp_assign_rhs = ex}, il) *)
(*   | BConst e -> (exp, []) *)
(*   | Barrier _ -> (exp,[]) *)
(*   | Bind e ->  *)
(*     let ex, il = irf_traverse_exp cp e.exp_bind_body scc in *)
(*     (Bind {e with exp_bind_body = ex}, il) *)
(*   | Block e ->  *)
(*     let ex, il = irf_traverse_exp cp e.exp_block_body scc in *)
(*     (Block {e with exp_block_body = ex}, il) *)
(*   | Cond e ->  *)
(*     let ex1, il1 = irf_traverse_exp cp e.exp_cond_then_arm scc in *)
(*     let ex2, il2 = irf_traverse_exp cp e.exp_cond_else_arm scc in *)
(*     (Cond {e with *)
(*              exp_cond_then_arm = ex1; exp_cond_else_arm = ex2}, il1@il2) *)
(*   | Cast e ->  *)
(*     let ex, il = irf_traverse_exp cp e.exp_cast_body scc in *)
(*     (Cast {e with exp_cast_body = ex}, il) *)
(*   | Catch e ->  *)
(*     let ex, il = irf_traverse_exp cp e.exp_catch_body scc in *)
(*     (Catch {e with exp_catch_body = ex}, il) *)
(*   | Debug _ *)
(*   | Dprint _ *)
(*   | FConst _  *)
(*   | IConst _ *)
(*   | New _ *)
(*   | Null _  *)
(*   | EmptyArray _  *)
(*   | Print _ -> (exp, []) *)
(*   | Seq e ->  *)
(*     let ex1, il1 = irf_traverse_exp cp e.exp_seq_exp1 scc in *)
(*     let ex2, il2 = irf_traverse_exp cp e.exp_seq_exp2 scc in *)
(*     (Seq {e with *)
(*             exp_seq_exp1 = ex1; exp_seq_exp2 = ex2}, il1@il2) *)
(*   | This _ *)
(*   | Time _ *)
(*   | Var _ *)
(*   | VarDecl _ *)
(*   | Unfold _ *)
(*   | Unit _ -> (exp, []) *)
(*   | While e -> *)
(*     let ex, il = irf_traverse_exp cp e.exp_while_body scc in *)
(*     (While {e with exp_while_body = ex}, il) *)
(*   | Sharp _ -> (exp, []) *)
(*   | Try e ->  *)
(*     let ex1, il1 = irf_traverse_exp cp e.exp_try_body scc in *)
(*     let ex2, il2 = irf_traverse_exp cp e.exp_catch_clause scc in *)
(*     (Try {e with *)
(*             exp_try_body = ex1; exp_catch_clause = ex2}, il1@il2) *)
(*   | ICall e ->  *)
(*     (ICall {e with exp_icall_is_rec = (is_found cp e.exp_icall_method_name scc)},  *)
(*      [e.exp_icall_method_name]) *)
(*   | SCall e ->  *)
(*     (SCall {e with exp_scall_is_rec = (is_found cp e.exp_scall_method_name scc)}, *)
(*      [e.exp_scall_method_name]) *)
(*   | Par e -> *)
(*     let cl, ill = List.split (List.map (fun c ->   *)
(*         let ce, il = irf_traverse_exp cp c.exp_par_case_body scc in *)
(*         { c with exp_par_case_body = ce }, il) e.exp_par_cases) *)
(*     in *)
(*     (Par { e with exp_par_cases = cl }, List.concat ill) *)


(* let irf_traverse_proc (cp: prog_decl) (proc: proc_decl) (scc: IG.V.t list) : proc_decl = *)
(*   let marked_rec_body, call_list = match proc.proc_body with *)
(*     | None -> None, [] *)
(*     | Some b ->  *)
(*       let body, cl = irf_traverse_exp cp b scc in *)
(*       Some body, cl *)
(*   in let is_rec = *)
(*     if (List.length scc) > 1 then true (\* Mutual recursive function *\) *)
(*     else List.exists (fun mn -> mn = proc.proc_name) call_list *)
(*   in { proc with *)
(*        proc_body = marked_rec_body; *)
(*        proc_is_recursive = is_rec } *)


(* let irf_traverse_prog (cp: prog_decl) (scc_list: IG.V.t list list) : prog_decl =  *)
(*   { cp with *)
(*      prog_proc_decls = List.map (fun proc -> *)
(*         irf_traverse_proc cp proc (find_scc_group cp proc.proc_name scc_list) *)
(*       ) cp.prog_proc_decls; *)
(*   } *)

(* let mark_recursive_call (cp: prog_decl) scc_list cg : prog_decl = *)
(*   irf_traverse_prog cp scc_list *)

  let mark_call_order_x (cp: prog_decl) scc_list cg : prog_decl =
    let _, fscc = IGC.scc cg in
    let tbl = List.map (fun p ->
        { p with proc_call_order = fscc p.proc_name }
    ) cp.prog_proc_decls in
    { cp with prog_proc_decls = tbl }

  let mark_call_order ip scc_list ig : prog_decl =
    let pr1 p = pr_list (fun c -> (pr_proc_call_order c) ^ "\n") 
      (List.filter (fun x -> x.proc_is_main)  p.prog_proc_decls) in
    let pr2 scc_list = pr_list (fun scc -> (pr_list (fun s -> s) scc) ^ "\n") scc_list in
    Debug.no_2 "mark_call_order" pr1 pr2 pr1
        (fun _ _ -> mark_call_order_x ip scc_list ig) ip scc_list


  (* Recursive call and call order detection *)
  (* irf = is_rec_field *)
  let mark_rec_and_call_order_x (cp: prog_decl) : prog_decl =
    let cg = callgraph_of_prog cp in
    let scc_arr = IGC.scc_array cg in
    let scc_list = Array.to_list scc_arr in
    (* let cp = mark_recursive_call cp scc_list cg in *)
    let cp = mark_call_order cp scc_list cg in
    let (prims, mutual_grps) = re_proc_mutual (sort_proc_decls cp.prog_proc_decls) in
    x_tinfo_hp (add_str "mutual scc" (pr_list (pr_list pr_proc_call_order))) mutual_grps no_pos;
    cp

  let mark_rec_and_call_order (cp: prog_decl) : prog_decl =
    let pr p = pr_list (pr_proc_call_order) 
      (List.filter (fun x -> not (x.proc_body == None)) p.prog_proc_decls) in
    Debug.no_1 "mark_rec_and_call_order" pr pr mark_rec_and_call_order_x cp

  let sort_call_graph prog=
    let new_prog = mark_rec_and_call_order prog in
    let proc_prim, proc_main = List.partition is_primitive_proc new_prog.prog_proc_decls in
  let sorted_proc_main = sort_proc_decls proc_main in
  let proc_scc = List.fold_left (fun a x -> match a with
      | [] -> [[x]]
      | xs::xss ->
        let i=(List.hd xs).proc_call_order in
        if i==x.proc_call_order then (x::xs)::xss
        else [x]::a
    ) [] sorted_proc_main in
  let proc_scc0 = List.rev proc_scc in
  {new_prog with  prog_proc_decls = sorted_proc_main@proc_prim}, proc_scc0

end;;


let exam_ass_error_proc iprog proc=
  match proc.I.proc_body with
    | Some e -> I.exists_assert_error iprog e
    | None -> false

let exam_ass_error_scc iprog scc=
  (*func call error*)
  List.exists (exam_ass_error_proc iprog) scc


let symex_gen_view_e iprog e=
  match e with
    | I.FloatLit {exp_float_lit_val = f;
      exp_float_lit_pos = l;} -> IP.FConst (f, l)
    | I.IntLit {exp_int_lit_val = i;
      exp_int_lit_pos = l} -> IP.IConst(i,l)
    | I.Null l -> IP.Null l
    | I.Var {exp_var_name = v;
      exp_var_pos = l} -> IP.Var((v, UnPrimed), l)

(*
  x=y ==> x=y

  if (a) then C_1 else C_2
  a /\ rec(C_1) \/ -a /\ rec(C_2)

*)
let symex_gen_view iprog proc_args  pos e0=
  let e_var = (IP.Ann_Exp (IP.Var ((err_var, Unprimed), no_pos)),Int,no_pos)
  let rec recf e h p= match e with
    | I.Assign e_ass -> true
    | I.Binary e_bin -> true
    | I.Cond e_cond -> true
    | I.CallRecv _ -> true
    | I.CallNRecv _ -> true
    | I.Empty _ -> h,p
    | I.BoolLit {exp_bool_lit_val=b;
      exp_bool_lit_pos=l;}-> h, IP.mkAnd p (IP.BForm ((IP.BConst (b,l), None),None)) pos
    | I.FloatLit _ -> h,p
    | I.IntLit _ -> h,p
    | I.Null _ -> h,p
    | I.Return _ -> true
    | I.Seq _ -> true
    | I.Unary _ -> true
    | I.Var _ -> h,p
    | I.VarDecl _ -> h,p
    | I.While _ -> let () = print_line "ast2pred.symex_gen_view: to handle" in h,p
    | _ -> h,p
  in
  ley int_p = IP.BForm (((IP.Eq (e_var, IP.IConst (0,no_pos), no_pos)),None),None) in
  let h, p = recf e0 IF.Emp int_p in
  h,p


let gen_view_from_proc iprog iproc=
  (*
    - pred name
    - parameter list = method.para + option res + #e
    - parse body
  *)
  let pred_name = iproc.I.proc_name ^ "_v" in
  let r_args = match iproc.I.proc_return with
    | Void -> []
    | _ -> let r_arg =  res_var in
      [r_arg]
  in
  let e_arg = err_var in
  let proc_args = (List.map (fun para -> para.I.param_name) iproc.I.proc_args) in
  let pred_args = proc_args @ r_args @ [e_arg] in
  let f_body = match iproc.I.proc_body with
    | Some body -> exe_gen_view iprog proc_args iproc.I.proc_loc body
    | None -> IP.mkTrue iproc.I.proc_loc
  in
  true

let gen_view_from_prog iprog iproc=
  false

(* O: safe, 1: unsafe, 2: unknown, 3: not applicaple (all method donot have assert error) *)
let verify_as_sat iprog=
  (* sort method call*)
  let niprog,scc_procs = Iast.Ast_sort.sort_call_graph iprog in
  (* look up assert error location *)
  if List.for_all (exam_ass_error_scc niprog) scc_procs then
    (* transform *)
    (* check sat *)
    NotApp
  else
    NotApp
