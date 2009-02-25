(* Created 21 Feb 2006 Simplify Iast to Cast *)
open Globals
  
module C = Cast
  
module E = Env
  
module Err = Error
  
module I = Iast
  
module U = Util
  
module IF = Iformula
  
module IP = Ipure
  
module CF = Cformula
  
module CP = Cpure
  
module H = Hashtbl
  
module TP = Tpdispatcher
  
module Chk = Checks
  
(* module VG = View_generator *)
type trans_exp_type =
  (C.exp * CP.typ)

  and spec_var_info =
  { mutable sv_info_kind : spec_var_kind
  }

  and spec_var_table =
  (ident, spec_var_info) H.t

  and spec_var_kind =
  | Known of CP.typ | Unknown

(************************************************************
Primitives handling stuff
************************************************************)
let prim_str =
  "int add___(int a, int b) requires true ensures res = a + b;
int minus___(int a, int b) requires true ensures res = a - b;
int mult___(int a, int b) requires true ensures true;
int div___(int a, int b) requires true ensures true;
int mod___(int a, int b) requires true ensures - b < res < b;
bool eq___(int a, int b) requires true ensures res & a = b or !res & a!= b;
bool eq___(bool a, bool b) requires true ensures res & a = b or !res & a!= b;
bool neq___(int a, int b) requires true ensures !res & a = b or res & a!= b;
bool neq___(bool a, bool b) requires true ensures !res & a = b or res & a!= b;
bool lt___(int a, int b) requires true ensures res & a < b or a >= b & !res;
bool lte___(int a, int b) requires true ensures res & a <= b or a > b & !res;
bool gt___(int a, int b) requires true ensures a > b & res or a <= b & !res;
bool gte___(int a, int b) requires true ensures a >= b & res or a < b & !res;
bool land___(bool a, bool b) requires true ensures a & b & res or !a & !res or !b & !res;
bool lor___(bool a, bool b) requires true ensures a & res or b & res or !a & !b & !res;
bool not___(bool a) requires true ensures a & !res or !a & res;
"
  
let prim_buffer = Buffer.create 1024
  
(* search prog and generate all eq, neq for all the data declaration,      *)
(* along with the ones in prim_str                                         *)
let gen_primitives (prog : I.prog_decl) : I.proc_decl list =
  let rec helper (ddecls : I.data_decl list) =
    match ddecls with
    | ddef :: rest ->
        let eq_str =
          "bool eq___(" ^
            (ddef.I.data_name ^
               (" a, " ^
                  (ddef.I.data_name ^
                     " b) requires true ensures res & a=b or a!=b & !res;\n"))) in
        let neq_str =
          "bool neq___(" ^
            (ddef.I.data_name ^
               (" a, " ^
                  (ddef.I.data_name ^
                     " b) requires true ensures a=b & !res or a!=b & res;\n"))) in
        let is_null_str =
          "bool is_null___(" ^
            (ddef.I.data_name ^
               (" a" ^
                  ") requires true ensures res & a=null or !res & a!=null;\n")) in
        let is_not_null_str =
          "bool is_not_null___(" ^
            (ddef.I.data_name ^
               (" a" ^
                  ") requires true ensures !res & a=null or res & a!=null;\n"))
        in
          (Buffer.add_string prim_buffer eq_str;
           Buffer.add_string prim_buffer neq_str;
           Buffer.add_string prim_buffer is_null_str;
           Buffer.add_string prim_buffer is_not_null_str;
           helper rest)
    | [] -> ()
  in
    (Buffer.add_string prim_buffer prim_str;
     helper prog.I.prog_data_decls;
     let all_prims = Buffer.contents prim_buffer in
     let input = Lexing.from_string all_prims in
     let prog = Iparser.program (Ilexer.tokenizer "primitives") input
     in prog.I.prog_proc_decls)
  
let op_map = Hashtbl.create 19
  
let _ =
  List.map (fun (op, func) -> Hashtbl.add op_map op func)
    [ (I.OpPlus, "add___"); (I.OpMinus, "minus___"); (I.OpMult, "mult___");
      (I.OpDiv, "div___"); (I.OpMod, "mod___"); (I.OpEq, "eq___");
      (I.OpNeq, "neq___"); (I.OpLt, "lt___"); (I.OpLte, "lte___");
      (I.OpGt, "gt___"); (I.OpGte, "gte___"); (I.OpLogicalAnd, "land___");
      (I.OpLogicalOr, "lor___"); (I.OpIsNull, "is_null___");
      (I.OpIsNotNull, "is_not_null___") ]
  
let get_binop_call (bop : I.bin_op) : ident =
  try Hashtbl.find op_map bop
  with
  | Not_found ->
      failwith
        ("binary operator " ^
           ((Iprinter.string_of_binary_op bop) ^ " is not supported"))
  
let assign_op_to_bin_op_map =
  [ (I.OpPlusAssign, I.OpPlus); (I.OpMinusAssign, I.OpMinus);
    (I.OpMultAssign, I.OpMult); (I.OpDivAssign, I.OpDiv);
    (I.OpModAssign, I.OpMod) ]
  
let bin_op_of_assign_op (aop : I.assign_op) =
  List.assoc aop assign_op_to_bin_op_map
  
(************************************************************
AST translation
************************************************************)
module Name =
  struct
    type t = ident
    
    let compare = compare
      
    let hash = Hashtbl.hash
      
    let equal = ( = )
      
  end
  
module NG = Graph.Imperative.Digraph.Concrete(Name)
  
module TopoNG = Graph.Topological.Make(NG)
  
module DfsNG = Graph.Traverse.Dfs(NG)
  
 
let node2_to_node prog (h0 : IF.h_formula_heap2) : IF.h_formula_heap =
	(* match named arguments with formal parameters to generate a list of    *)
	(* position-based arguments. If a parameter does not appear in args,     *)
	(* then it is instantiated to a fresh name.                              *)
  let rec match_args (params : ident list) args : IP.exp list =
    match params with
    | p :: rest ->
        let tmp1 = match_args rest args in
        let tmp2 = List.filter (fun a -> (fst a) = p) args in
        let tmp3 =
          (match tmp2 with
           | [ (_, IP.Var ((e1, e2), e3)) ] -> IP.Var ((e1, e2), e3)
           | _ ->
               let fn = ("Anon"^(fresh_trailer()))
               in
								(* let _ = (print_string ("\n[astsimp.ml, line 241]: fresh *)
								(* name = " ^ fn ^ "\n")) in                               *)
                 IP.Var ((fn, Unprimed), h0.IF.h_formula_heap2_pos)) in
        let tmp4 = tmp3 :: tmp1 in tmp4
    | [] -> []
  in
    try
      let vdef =
        I.look_up_view_def_raw prog.I.prog_view_decls
          h0.IF.h_formula_heap2_name in
      let hargs =
        match_args vdef.I.view_vars h0.IF.h_formula_heap2_arguments in
      let h =
        {
          IF.h_formula_heap_node = h0.IF.h_formula_heap2_node;
          IF.h_formula_heap_name = h0.IF.h_formula_heap2_name;
          IF.h_formula_heap_full = h0.IF.h_formula_heap2_full;
          IF.h_formula_heap_with_inv = h0.IF.h_formula_heap2_with_inv;
          IF.h_formula_heap_arguments = hargs;
          IF.h_formula_heap_pseudo_data = h0.IF.h_formula_heap2_pseudo_data;
          IF.h_formula_heap_pos = h0.IF.h_formula_heap2_pos;
        }
      in h
    with
    | Not_found ->
        let ddef =
          I.look_up_data_def h0.IF.h_formula_heap2_pos prog.I.prog_data_decls
            h0.IF.h_formula_heap2_name in
        let params = List.map (fun ((t, v), p) -> v) ddef.I.data_fields in
        let hargs = match_args params h0.IF.h_formula_heap2_arguments in
        let h =
          {
            IF.h_formula_heap_node = h0.IF.h_formula_heap2_node;
            IF.h_formula_heap_name = h0.IF.h_formula_heap2_name;
            IF.h_formula_heap_full = h0.IF.h_formula_heap2_full;
            IF.h_formula_heap_with_inv = h0.IF.h_formula_heap2_with_inv;
            IF.h_formula_heap_arguments = hargs;
            IF.h_formula_heap_pseudo_data = h0.IF.h_formula_heap2_pseudo_data;
            IF.h_formula_heap_pos = h0.IF.h_formula_heap2_pos;
          }
        in h
  
(* convert HeapNode2 to HeapNode *)
let rec convert_heap2_heap prog (h0 : IF.h_formula) : IF.h_formula =
  match h0 with
  | IF.Star (({ IF.h_formula_star_h1 = h1; IF.h_formula_star_h2 = h2 } as h))
      ->
      let tmp1 = convert_heap2_heap prog h1 in
      let tmp2 = convert_heap2_heap prog h2
      in
        IF.Star
          {
            (h)
            with
            IF.h_formula_star_h1 = tmp1;
            IF.h_formula_star_h2 = tmp2;
          }
  | IF.HeapNode2 h2 -> IF.HeapNode (node2_to_node prog h2)
  | _ -> h0

and convert_heap2 prog (f0 : IF.formula) : IF.formula =
  match f0 with
  | IF.Or (({ IF.formula_or_f1 = f1; IF.formula_or_f2 = f2 } as f)) ->
      let tmp1 = convert_heap2 prog f1 in
      let tmp2 = convert_heap2 prog f2
      in IF.Or { (f) with IF.formula_or_f1 = tmp1; IF.formula_or_f2 = tmp2; }
  | IF.Base (({ IF.formula_base_heap = h0 } as f)) ->
      let h = convert_heap2_heap prog h0
      in IF.Base { (f) with IF.formula_base_heap = h; }
  | IF.Exists (({ IF.formula_exists_heap = h0 } as f)) ->
      let h = convert_heap2_heap prog h0
      in IF.Exists { (f) with IF.formula_exists_heap = h; }
			
and convert_ext2 prog (f0:Iformula.ext_formula):Iformula.ext_formula = match f0 with
	| Iformula.ECase b -> Iformula.ECase {b with Iformula.formula_case_branches = (List.map (fun (c1,c2)-> (c1,(convert_struc2 prog c2))) b.Iformula.formula_case_branches)};
	| Iformula.EBase b -> Iformula.EBase{b with 
		 Iformula.formula_ext_base = convert_heap2 prog b.Iformula.formula_ext_base;
		 Iformula.formula_ext_continuation = List.map (fun e-> convert_ext2 prog e)  b.Iformula.formula_ext_continuation 
		}

and convert_struc2 prog (f0 : Iformula.struc_formula) : Iformula.struc_formula = 
	List.map (convert_ext2 prog) f0 
	
			  
let order_views (view_decls0 : I.view_decl list) : I.view_decl list =
	(* generate pairs (vdef.view_name, v) where v is a view appearing in     *)
	(* vdef                                                                  *)
  let rec gen_name_pairs_heap vname h =
    match h with
    | IF.Star { IF.h_formula_star_h1 = h1; IF.h_formula_star_h2 = h2 } ->
        (gen_name_pairs_heap vname h1) @ (gen_name_pairs_heap vname h2)
    | IF.HeapNode { IF.h_formula_heap_name = c } ->
        if c = vname
        then []
        else
          (try let _ = I.look_up_view_def_raw view_decls0 c in [ (vname, c) ]
           with | Not_found -> [])
    | _ -> [] in
  let rec gen_name_pairs vname (f : IF.formula) : (ident * ident) list =
    match f with
    | IF.Or { IF.formula_or_f1 = f1; IF.formula_or_f2 = f2 } ->
        (gen_name_pairs vname f1) @ (gen_name_pairs vname f2)
    | IF.Base { IF.formula_base_heap = h; IF.formula_base_pure = p } ->
        gen_name_pairs_heap vname h
    | IF.Exists { IF.formula_exists_heap = h; IF.formula_exists_pure = p } ->
        gen_name_pairs_heap vname h in
				
	let rec gen_name_pairs_ext vname (f:Iformula.ext_formula): (ident * ident) list = match f with
		| Iformula.ECase {Iformula.formula_case_branches = b}-> 
			List.fold_left (fun d (e1,e2) -> List.fold_left (fun a c -> a@(gen_name_pairs_ext vname c)) d e2) [] b 
		| Iformula.EBase {Iformula.formula_ext_base =fb;
		 				 Iformula.formula_ext_continuation = cont}-> List.fold_left (fun a c -> a@(gen_name_pairs_ext vname c)) (gen_name_pairs vname fb) cont  
		 in
	 	
	let gen_name_pairs_struc vname (f:Iformula.struc_formula): (ident * ident) list =
		List.fold_left (fun a c -> a@(gen_name_pairs_ext vname c) ) [] f 
		in
				
  let tmp =
    List.map
      (fun vdef -> gen_name_pairs_struc vdef.I.view_name vdef.I.view_formula)
      view_decls0 in
  let edges = List.concat tmp in
  let g = NG.create ()
  in
    (ignore
       (List.map
          (fun (v1, v2) -> NG.add_edge g (NG.V.create v1) (NG.V.create v2))
          edges);
     if DfsNG.has_cycle g
     then failwith "View definitions are mutually recursive"
     else ();
		(* take out the view names in reverse order *)
     let view_names = ref ([] : ident list) in
     let store_name n = view_names := n :: !view_names
     in
       (TopoNG.iter store_name g;
				(* now reorder the views *)
        let rec
          reorder_views (view_decls : I.view_decl list)
                        (ordered_names : ident list) =
          match ordered_names with
          | n :: rest ->
              let (n_view, rest_decls) =
                List.partition (fun v -> v.I.view_name = n) view_decls in
              let (rest_views, new_rest_decls) =
                reorder_views rest_decls rest
              in
								(* n_view should contain only one views *)
                ((n_view @ rest_views), new_rest_decls)
          | [] -> ([], view_decls) in
        let (r1, r2) = reorder_views view_decls0 !view_names in r1 @ r2))
  
let loop_procs : (C.proc_decl list) ref = ref []
  
(* let rec pick_coercions (procs : C.proc_decl list) : (C.proc_decl list * *)
(* C.proc_decl list) = match procs with | proc :: rest -> begin let        *)
(* rest_l2r, rest_r2l = pick_coercions rest in match                       *)
(* proc.C.proc_coercion_type with | C.Coercion -> (proc :: rest_l2r,       *)
(* rest_r2l) | C.Equiv -> (proc :: rest_l2r, proc :: rest_r2l) | C.Reverse *)
(* -> (rest_l2r, proc :: rest_r2l) | C.NotACoercion -> (rest_l2r,          *)
(* rest_r2l) end | [] -> ([], [])                                          *)
let rec (* overriding test *) (* field duplication test *)
  (* method duplication test *) (* field hiding test *) (*TODO: fix this *)
  (* keep the quantifiers generated by xpure *) (*Omega.pairwisecheck*)
	(* Isabelle.pairwisecheck let xform = CP.mkExists addr_vars new_xform'   *)
	(* (CF.pos_of_formula vdef.C.view_formula) in let xform =                *)
	(* Omega.pairwisecheck xform' in TODO: check entailment in the other way *)
	(* print_string ("\nxform' for view: " ^ vdef.C.view_name ^ "\n" ^       *)
	(* (Cprinter.string_of_pure_formula xform') ^ "\n"); print_string        *)
	(* ("\noriginal formula:\n" ^ (Cprinter.string_of_formula                *)
	(* vdef.C.view_formula)); print_string ("\nxform':\n" ^                  *)
	(* (Cprinter.string_of_pure_formula vdef.C.view_x_formula) ^ "\n");      *)
	(* H.add stab self {sv_info_kind = Unknown}; setting view_typed_vars     *)
	(* find_materialized_vars prog view_sv_vars cf let _ = print_string      *)
	(* ("mvars for " ^ vdef.I.view_name ^ ": " ^ (String.concat ", "         *)
	(* (List.map CP.name_of_spec_var mvars)) ^ "\n") in set by               *)
	(* Predcomp.gen_view print_string ("\n\nView " ^ cvdef.C.view_name ^     *)
	(* ":\n"); print_stab stab; This function can repeatedly unfold all      *)
	(* predicates used in the definition until no more parameter is          *)
	(* materialized or all parameters are materialized. Since there is a     *)
	(* finite number of parameters, the process terminates. if the heap part *)
	(* if non-empty, by well-founded condition, self must be pointing to a   *)
	(* node find the alias set containing p the body of while may be         *)
	(* skipped, so may the returns in there add parameter to the new scope   *)
	(* check pre/post list: build list of free vars and initial stab check   *)
	(* if res has the correct type, pre/post don't contain self check method *)
	(* body if U.empty dynamic_specs_list then [(CF.mkTrue proc.I.proc_loc,  *)
	(* CF.mkTrue proc.I.proc_loc)] else translating coercions, split them to *)
	(* left to right and right to left coercions translation of pre/post     *)
	(* condition: different translations for 2 directions. left-to-right     *)
	(* direction: LHS: precond, RHS: postcond right-to-left direction: RHS:  *)
	(* precond, LHS: postcond ???                                            *)
  (* translate the formulae *) (* compute universally quantified variables *)
	(* we only existentially quantify variables that are not already         *)
	(* universally quantified in the antecedent. find the names of the       *)
	(* predicates from the LHS and RHS of the coercion TODO: FIX IT else if  *)
	(* rhs_name = "" then Error.report_error { Err.error_loc =               *)
	(* IF.pos_of_formula coer.I.coercion_body; Err.error_text = "self must   *)
	(* point to a node in RHS" } print_string ("\ncoercion_head: " ^         *)
	(* (Cprinter.string_of_formula c_lhs) ^ "\n"); print_string              *)
	(* ("\ncoercion_body: " ^ (Cprinter.string_of_formula c_rhs) ^ "\n");    *)
	(* and trans_one_coercion (prog : I.prog_decl) (coer : I.coercion_decl)  *)
	(* : (C.coercion_decl list * C.coercion_decl list) = let stab1 =         *)
	(* H.create 103 in for left-to-right direction let l2r_pre =             *)
	(* trans_formula prog false [self] coer.I.coercion_head stab1 in let     *)
	(* l2r_fnames = List.map CP.name_of_spec_var (CF.fv l2r_pre) in let      *)
	(* l2r_post = trans_formula prog true (self :: l2r_fnames)               *)
	(* coer.I.coercion_body stab1 in for right-to-left direction let stab2 = *)
	(* H.create 103 in let r2l_pre = trans_formula prog false [self]         *)
	(* coer.I.coercion_body stab2 in let r2l_fnames = List.map               *)
	(* CP.name_of_spec_var (CF.fv r2l_pre) in let r2l_post = trans_formula   *)
	(* prog true (self :: r2l_fnames) coer.I.coercion_head stab2 in find the *)
	(* names of the predicates from the LHS and RHS of the coercion let      *)
	(* lhs_name = find_view_name l2r_pre self (IF.pos_of_formula             *)
	(* coer.I.coercion_head) in let rhs_name = find_view_name l2r_post self  *)
	(* (IF.pos_of_formula coer.I.coercion_body) in if lhs_name = "" then     *)
	(* Error.report_error { Err.error_loc = IF.pos_of_formula                *)
	(* coer.I.coercion_head; Err.error_text = "root pointer of node on LHS   *)
	(* must be self" } else if rhs_name = "" then Error.report_error {       *)
	(* Err.error_loc = IF.pos_of_formula coer.I.coercion_body;               *)
	(* Err.error_text = "self must point to a node in RHS" } else let l2r =  *)
	(* { C.coercion_head = l2r_pre; C.coercion_body = l2r_post;              *)
	(* C.coercion_head_view = lhs_name; C.coercion_body_view = rhs_name } in *)
	(* let r2l = { C.coercion_head = r2l_pre; C.coercion_body = r2l_post;    *)
	(* C.coercion_head_view = rhs_name; C.coercion_body_view = lhs_name } in *)
	(* print_string ("\ncoercion_head: " ^ (Cprinter.string_of_formula       *)
	(* c_lhs) ^ "\n"); print_string ("\ncoercion_body: " ^                   *)
	(* (Cprinter.string_of_formula c_rhs) ^ "\n"); match                     *)
	(* coer.I.coercion_type with | I.Left -> ([l2r], []) | I.Equiv ->        *)
	(* ([l2r], [r2l]) | I.Right -> ([], [r2l]) find the name of the view     *)
	(* pointed by v in f0 What are done by this function: - standard type    *)
	(* checking - flattening AST - alpha-renaming - substitute constant in   *)
	(* -- too much stuff inside one function What does it need to do its     *)
	(* job: - environment return value: - translated expression (having type *)
	(* C.exp (in second component)) - type of expression - whether this can  *)
	(* be assignment target, and if so, what is the target. used with        *)
	(* translating e1 = e2 translate two formulae using all visible names    *)
  (* build initial stab *) (* v0 could be alpha-converted *)
	(* let _ = (print_string ("\n[astsimp.ml, line 953]: fresh name = " ^ fn *)
	(* ^ "!!!!!!!!!!!\n\n")) in if not (I.contains_field rhs) then begin if  *)
	(* I.is_var rhs then begin match base_e with | I.Member                  *)
	(* ({I.exp_member_base = e1; I.exp_member_fields = fs1; I.exp_member_pos *)
	(* = pos1}) -> let new_ie = I.Assign ({I.exp_assign_op = aop;            *)
	(* I.exp_assign_lhs = I.Member ({I.exp_member_base = e1;                 *)
	(* I.exp_member_fields = fs1 @ fs; I.exp_member_pos = pos});             *)
	(* I.exp_assign_rhs = rhs; I.exp_assign_pos = pos_a}) in trans_exp prog  *)
	(* proc new_ie | _ -> begin let ce, te = trans_exp prog proc base_e in   *)
	(* let ce2, te2 = trans_exp prog proc rhs in let dname = C.name_of_type  *)
	(* te in if C.is_var ce then let res_e,_ = convert_to_bind prog          *)
	(* (C.get_var ce) dname fs (Some ce2) pos in (res_e, C.void_type) else   *)
	(* let fn = fresh_name () in let _ = (print_string ("\n[astsimp.ml, line *)
	(* 1007]: fresh name = " ^ fn ^ "!!!!!!!!!!!\n\n")) in let fn_decl =     *)
	(* C.VarDecl ({C.exp_var_decl_type = te; C.exp_var_decl_name = fn;       *)
	(* C.exp_var_decl_pos = pos}) in let init_fn = C.Assign                  *)
	(* ({C.exp_assign_lhs = fn; C.exp_assign_rhs = ce; C.exp_assign_pos =    *)
	(* pos}) in let fn_e, fn_t = convert_to_bind prog fn dname fs (Some ce2) *)
	(* pos in let seq1 = C.Seq ({C.exp_seq_type = fn_t; C.exp_seq_exp1 =     *)
	(* init_fn; C.exp_seq_exp2 = fn_e; C.exp_seq_pos = pos}) in let          *)
	(* local_vars = [(te, fn)] in this is the newly introduced variable in   *)
	(* this block let seq2 = C.Block ({C.exp_block_type = fn_t;              *)
	(* C.exp_block_body = C.Seq ({C.exp_seq_type = fn_t; C.exp_seq_exp1 =    *)
	(* fn_decl; C.exp_seq_exp2 = seq1; C.exp_seq_pos = pos});                *)
	(* C.exp_block_local_vars = local_vars; C.exp_block_pos = pos}) in       *)
	(* (seq2, fn_t) end end else begin in case RHS is a complex expression,  *)
	(* like x.f = y.g, introduce a local variable: tmp = y.g; x.f = tmp let  *)
	(* _, lhs_t = trans_exp prog proc lhs in I know this causes lhs to be    *)
	(* re-translated, but hopefully not too much work let lhs_it =           *)
	(* trans_type_back lhs_t in let fn = fresh_name () in let _ =            *)
	(* (print_string ("\n[astsimp.ml, line 1036]: fresh name = " ^ fn ^      *)
	(* "!!!!!!!!!!!\n\n")) in let fn_decl = I.VarDecl ({I.exp_var_decl_type  *)
	(* = lhs_it; I.exp_var_decl_decls = [(fn, Some rhs, pos)];               *)
	(* I.exp_var_decl_pos = pos}) in let lhs_a = I.Assign ({I.exp_assign_op  *)
	(* = aop; I.exp_assign_lhs = lhs; I.exp_assign_rhs = (I.Var              *)
	(* ({I.exp_var_name = fn; I.exp_var_pos = pos})); I.exp_assign_pos =     *)
	(* pos}) in let seq = I.Seq ({I.exp_seq_exp1 = fn_decl; I.exp_seq_exp2 = *)
	(* lhs_a; I.exp_seq_pos = pos}) in trans_exp prog proc seq end receiver  *)
	(* identifier and how to initialize it let _ = (print_string             *)
	(* ("\n[astsimp.ml, line 1164]: fresh name = " ^ fname ^                 *)
	(* "!!!!!!!!!!!\n\n")) in finding if "this" is the potential receiver    *)
	(* only static methods need to be considered if not (CP.are_same_types   *)
	(* te2 te3) then Err.report_error {Error.error_loc = pos;                *)
	(* Error.error_text = "two branches of if do not match"} else let _ =    *)
	(* (print_string ("\n[astsimp.ml, line 1296]: fresh name = " ^ fn ^      *)
	(* "!!!!!!!!!!!\n\n")) in only integers let _ = (print_string            *)
	(* ("\n[astsimp.ml, line 1443]: fresh name = " ^ fn ^                    *)
	(* "!!!!!!!!!!!\n\n")) in let _ = (print_string ("\n[astsimp.ml, line    *)
	(* 1469]: fresh name = " ^ fn ^ "!!!!!!!!!!!\n\n")) in                   *)
  (* only integers *) (* only integers *) (* decls can't be empty *)
	(* let _ = (print_string ("\n[astsimp.ml, line 1601]: fresh name = " ^   *)
	(* fn3 ^ "!!!!!!!!!!!\n\n")) in rev_fs: the reversed of the list of      *)
	(* field names. rhs_o: the optional rhs if the member access in on the   *)
	(* lhs of an assignment. This parameter is only significant for the last *)
	(* field access, i.e. the first in rev_fs. Any recursive call will have  *)
	(* a None for rhs_o. let _ = (print_string ("\n[astsimp.ml, line 1687]:  *)
	(* fresh name = " ^ fn2 ^ "!!!!!!!!!!!\n\n")) in now we have fn.f as the *)
	(* field access gen_names: generates fresh names for fields. It also     *)
	(* returns the name generated for the field being accessed (fn) as the   *)
	(* first component of the returned value let _ = (print_string           *)
	(* ("\n[astsimp.ml, line 1713]: fresh name = " ^ fn1 ^                   *)
	(* "!!!!!!!!!!!\n\n")) in gen_names: generates fresh names for fields.   *)
	(* It also returns the name generated for the field being accessed (fn)  *)
	(* as the first component of the returned value let _ = (print_string    *)
	(* ("\n[astsimp.ml, line 1772]: fresh name = " ^ fn ^                    *)
	(* "!!!!!!!!!!!\n\n")) in flattening call arguments: - assuming args and *)
	(* typs have the same length - introduce variables for arguments that    *)
	(* are complex expressions (not variables) - initialize the variables to *)
	(* expression that the variable substitutes - return the newly           *)
	(* introduced variable as a local variable (can be quantified after the  *)
	(* call) let _ = (print_string ("\n[astsimp.ml, line 1835]: fresh name = *)
	(* " ^ fn ^ "!!!!!!!!!!!\n\n")) in rest_e, init_e are assignments, so    *)
	(* they have type void found an enum with type c, treat it as int        *)
	(* assuming data otherwise convert subexpression e of ce to v=e if e is  *)
	(* non-void we don't need to go down ce1 here, as trans_exp already does *)
	(* that non-void e1, store the value to a dummy variable let _ =         *)
	(* (print_string ("\n[astsimp.ml, line 1943]: fresh name = " ^ fn ^      *)
	(* "!!!!!!!!!!!\n\n")) in translating formula - constraint type          *)
	(* inference - convert complex heap arguments to variables and           *)
	(* equalities - quantify: true for post/view/assert/assume: some         *)
	(* variables will be exist. quant. false for view: no variables in       *)
	(* precondition will be exist. quant. fvars: when quantify is true,      *)
	(* variables appearing in fvars are not quantified. f0: input formula    *)
  (* -- 19.05.2008 *) (* -- *)
	(* remove all keys but keys in fvars if quantify is true remove all keys *)
	(* but keys in fvars if quantify is true linearize heap/view variables   *)
	(* quantify is true for view definition and postcondition and false for  *)
	(* precondition. fvars are free variables, any occurrences of fvars      *)
	(* inside formula need linearized The function returns a linearized      *)
	(* formula with additional constraints for the newly-introduced          *)
	(* variables. It also returns a list of variables to be quantified. this *)
	(* function process the list of arguments of a heap node and determine   *)
	(* which one should be linearized. idents in used_names include          *)
	(* parameters/view vars and heap args and must be quantified return      *)
	(* value: new_used_names, vars to be heap args, vars to be quantified,   *)
	(* linking formula -- print_string ("Free var " ^ ve ^ ": " ^            *)
	(* (string_of_bool (List.mem ve fvars)) ^ "\n"); print_string ("Used     *)
	(* name " ^ ve ^ ": " ^ (string_of_bool (List.mem ve used_names)) ^      *)
	(* "\n"); -- if ve is a free var or ve already occurs, replace it by a   *)
	(* fresh name print_string ("[astsimp.ml, line 2073]: Fresh var " ^      *)
	(* (Cprinter.string_of_spec_var fresh_v) ^ "\n"); print_string           *)
	(* ("[astsimp.ml, line 2074]: quantify = " ^ (string_of_bool quantify) ^ *)
	(* "\n");                                                                *)
  (*****************************************************) (* 09.06.08 *)
  (* each fresh variable introduced must be existentially quantified - quantify them even if they are in precond *)
  (*(if quantify then*) (*else []) *)
  (*****************************************************)
  (* no need to add fresh_v to used_names since it   *)
  (* is a fresh variable, there's no other           *)
  (* occurences of fresh_v                           *)
  (* ve occurs for the first time *)
  (* if e is not a Var, it must be either null or arithmetic term (int_type) *)
  (* let _ = (print_string ("\n[astsimp.ml, line 2098]:    *)
									(* fresh name = " ^ fresh_n ^ "!!!!!!!!!!!\n\n")) in     *)
  (* let fresh_v = CP.SpecVar (IP.get_exp_type e, fresh_n, *)
  (* Unprimed) in                                          *)
  (* let quantified_var = if quantify then [fresh_v] else  *)
  (* [] in                                                 *)
  (* linearize_heap: - used_names: names already used, so any new          *)
  (* occurences in heap constraints must be quantified - f: input formula  *)
  (* return values: - #1: more used names - #2: variables to be quantified *)
  (* - #3: output formula - #4: formula to link newly introduced variables *)
  (* - #5: constraint over type variables                                  *)
  (* print_string ("linearize_heap: trans_view invoked."); *)
  (*TODO: find the data name of vdef *)
  (* -- for data node -- let ddef = I.look_up_data_def pos         *)
  (* prog.I.prog_data_decls c in                                   *)
  (* we can use c for tvar. The actual type can be determined  *)
  (* later on, during entailment let t_var = CP.SpecVar        *)
  (* (CP.OType c, c , Unprimed) in let type_constr =           *)
  (* CF.TypeSub ({CF.t_formula_sub_type_var = t_var;           *)
  (* CF.t_formula_sub_type_type = c}) in extension pointer let *)
  (* pname = I.look_up_parent_name pos prog.I.prog_data_decls  *)
  (* c in commented out on 09.06.08 : we have decided to       *)
  (* remove for now the type and extension information related *)
  (* to the OO extension let ext_name = gen_ext_name c pname   *)
  (* in let ext_var = CP.SpecVar (CP.OType ext_name, c ,       *)
  (* Unprimed) in -- 09.06.08 --                               *)
  (* if full then let ext_constr = CP.mkNull ext_var pos in    *)
  (* CP.mkAnd link_f_prim ext_constr pos else link_f_prim in   *)
  (* let _ = print_string ("link_f = " ^                       *)
  (* Cprinter.string_of_pure_formula link_f ^ "\n") in         *)
  (*c t_var :: ext_var ::*)
  (* 09.06.08: we have decided to remove for now the type      *)
  (* information related to the OO extension (new_used_names,  *)
  (* evars, new_h, link_f, type_constr)                        *)
  (* remove self from quantified variables *)
  (* at this point of time, no information about type is available,      *)
  (* hence the TypeTrue                                                  *)
  (* let pe = trans_pure_exp e stab in CP.BagIn (CP.SpecVar (C.int_type,   *)
  (* v, p), pe, pos) -- not OK because we might have other things besides  *)
  (* primitive int inside the bag                                          *)
  (* CP.BagNotIn (CP.SpecVar (C.int_type, v, p), pe, pos) *)
  (* for max and min I think is ok to consider int_type for now *)
  (* TODO: fix this dirty hack | Unknown -> Err.report_error         *)
  (* {Err.error_loc = pos; Err.error_text = "couldn't infer type for *)
				(* " ^ v}                                                          *)
  (* TODO: hack copied from above *)
  (* Err.report_error {Err.error_loc = pos; Err.error_text = v ^ "   *)
				(* is undefined"}                                                  *)
  (******************************************************************)
  (* Type reconstruction ********************************************)
  (* First collect type for all variables appearing in constraints, *)
  (* then use the info to transform constraints to correct forms    *)
  (* Collecting type information order: heap, then arithmetic, then *)
  (* pure pointer constraints. **************************************)
  (******************************************************************)
  (* the real type is t1 *) (* the real type is t2 *)
  (* returns var's binding if it is in stab. Otherwise returns Undetermined *)
  (* check to see if any uses of variables if qf conflicts with info stab *)
  (* H.add stab qv {sv_info_kind = Known C.int_type}; *)
  (* only allow integer variable to be quantified *) (* H.remove stab qv *)
  (* name shadowing is not allowed, hence this is not needed *)
  (* collect_type_info_var v stab (Known C.int_type) pos; *)
  (* collect_type_info_var v stab (Known C.int_type) pos; *)
  (* can only say a1, a2 have to have the same type *)
  (* make a1 and a2 point to the same entry *)
  (* since a2 is not a variable, if it's not null, it must be arithmetic term *)
  (* both are expressions *) (* null=null or null!=null --> nothing to do *)
  (* can only be arithmetic expression *)
  (* if c is a view, use the underlying data name *)
  (* if c is a view, then see if types of arguments of the view  *)
  (* has been determined                                         *)
  (* check if it is a data *)
  (* we know for sure that this view is based on a data node v     *)
  (* must be a pointer of type dname                               *)
  (* c is a view, get the types of the variables of c *)
  (* View vars and arguments must have same type. This is lars *)
  (* von trierdone by making equations between view vars and   *)
  (* corresponding arguments and do type inference over them   *)
  (* some debugging utilities *)
  (* try to get rid of minus and constant multiplication *)
  (* let r = match m with | None -> e0 | Some c -> let t1 = acc_mult m   *)
  (* e1 in let t2 = acc_mult m e2 in if (c>0) then Cpure.Max (t1,t2,l)   *)
  (* else Cpure.Min (t2,t1,l) in r                                       *)
  (* let r = match m with | None -> e0 | Some c -> let t1 = acc_mult m   *)
  (* e1 in let t2 = acc_mult m e2 in if (c>0) then Cpure.Min (t1,t2,l)   *)
  (* else Cpure.Max (t1,t2,l) in r bag expressions                       *)
  (* returns a pair of expressions-> to_stay, to_move (signs already         *)
  (* changed)                                                                *)
  (* bag expressions *) (* first is max of second and third *)
  (* first is min of second and third *) (* bag formulas *) trans_prog
  (prog0 : I.prog_decl) : C.prog_decl =
  let _ = I.build_hierarchy prog0 in
  let check_overridding = Chk.overridding_correct prog0 in
  let check_field_dup = Chk.no_field_duplication prog0 in
  let check_method_dup = Chk.no_method_duplication prog0 in
  let check_field_hiding = Chk.no_field_hiding prog0
  in
    if
      check_field_dup &&
        (check_method_dup && (check_overridding && check_field_hiding))
    then
      (let prims = gen_primitives prog0 in
       let prog =
         { (prog0) with I.prog_proc_decls = prims @ prog0.I.prog_proc_decls;
         }
       in
         (set_mingled_name prog;
          let all_names =
            (List.map (fun p -> p.I.proc_mingled_name)
               prog0.I.prog_proc_decls)
              @
              ((List.map (fun ddef -> ddef.I.data_name)
                  prog0.I.prog_data_decls)
                 @
                 (List.map (fun vdef -> vdef.I.view_name)
                    prog0.I.prog_view_decls)) in
          let dups = U.find_dups all_names
          in
            if not (U.empty dups)
            then
              (print_string
                 ("duplicated top-level name(s): " ^
                    ((String.concat ", " dups) ^ "\n"));
               failwith "Error detected")
            else
              (let tmp_views = order_views prog.I.prog_view_decls in
               let cviews = List.map (trans_view prog) tmp_views in
               let cdata =
                 List.map (trans_data prog) prog.I.prog_data_decls in
               let cprocs1 =
                 List.map (trans_proc prog) prog.I.prog_proc_decls in
               let cprocs = !loop_procs @ cprocs1 in
               let (l2r_coers, r2l_coers) = trans_coercions prog0 in
               let cprog =
                 {
                   C.prog_data_decls = cdata;
                   C.prog_view_decls = cviews;
                   C.prog_proc_decls = cprocs;
                   C.prog_left_coercions = l2r_coers;
                   C.prog_right_coercions = r2l_coers;
                 }
               in
                 (ignore
                    (List.map
                       (fun vdef ->
                          compute_view_x_formula cprog vdef !Globals.n_xpure)
                       cviews);
                  ignore
                    (List.map (fun vdef -> set_materialized_vars cprog vdef)
                       cviews);
                  ignore (C.build_hierarchy cprog);
                  cprog))))
    else failwith "Error detected"

and trans_data (prog : I.prog_decl) (ddef : I.data_decl) : C.data_decl =
  let trans_field ((t, c), pos) : C.typed_ident =
    ((trans_type prog t pos), c)
  in
    {
      C.data_name = ddef.I.data_name;
      C.data_fields = List.map trans_field ddef.I.data_fields;
      C.data_parent_name = ddef.I.data_parent_name;
      C.data_methods = List.map (trans_proc prog) ddef.I.data_methods;
      C.data_invs = [];
    }
and
  compute_view_x_formula (prog : C.prog_decl) (vdef : C.view_decl) (n : int)
                         =
  (if n > 0
   then
     (let pos = CF.pos_of_struc_formula vdef.C.view_formula in
      let (xform', addr_vars') =
        Solver.xpure_symbolic_no_exists_struc prog vdef.C.view_formula in
      let addr_vars = U.remove_dups addr_vars' in
      let new_xform' = TP.simplify xform' in
      let xform = new_xform' in
      let ctx =
        CF.build_context (CF.true_ctx pos) (CF.formula_of_pure xform pos) pos in
      let (rs, _) =
        Solver.heap_entail prog false false [ ctx ]
          (CF.formula_of_pure vdef.C.view_user_inv pos) pos
      in
        if not (U.empty rs)
        then
          (vdef.C.view_x_formula <- xform;
           vdef.C.view_addr_vars <- addr_vars;
           compute_view_x_formula prog vdef (n - 1))
        else
          Err.report_error
            {
              Err.error_loc = pos;
              Err.error_text =
                "view formula does not entail supplied invariant";
            })
   else ();
   if !Globals.print_x_inv && (n = 0)
   then
     (print_string
        ("\ncomputed invariant for view: " ^
           (vdef.C.view_name ^
              ("\n" ^
                 ((Cprinter.string_of_pure_formula vdef.C.view_x_formula) ^
                    "\n"))));
      print_string
        ("addr_vars: " ^
           ((String.concat ", "
               (List.map CP.name_of_spec_var vdef.C.view_addr_vars))
              ^ "\n\n")))
   else ())

and trans_view (prog : I.prog_decl) (vdef : I.view_decl) : C.view_decl =
  let stab = H.create 103 in
  let view_formula = convert_struc2 prog vdef.I.view_formula in
  let data_name = I.data_name_of_view prog.I.prog_view_decls view_formula
  in
    (vdef.I.view_data_name <- data_name;
     H.add stab self { sv_info_kind = Known (CP.OType data_name); };
     let cf =(trans_struc_formula prog true ((List.map (fun c-> (c,Unprimed))(self :: res :: vdef.I.view_vars)),	[]
		(*(List.map (fun c-> (c,Primed))(self :: res :: vdef.I.view_vars))*)) view_formula stab) in
     let pf = trans_pure_formula vdef.I.view_invariant stab in
		(* let _ = print_string ("pre: "^(Cprinter.string_of_pure_formula      *)
		(* pf)^"\n") in                                                        *)
     let pf = arith_simplify pf in
		(* let _ = print_string ("post: "^(Cprinter.string_of_pure_formula     *)
		(* pf)^"\n") in                                                        *)
     let cf_fv = List.map CP.name_of_spec_var (CF.struc_fv cf) in
     let pf_fv = List.map CP.name_of_spec_var (CP.fv pf)
     in
       if (List.mem res cf_fv) || (List.mem res pf_fv)
       then
         Err.report_error
           {
             Err.error_loc = IF.pos_of_struc_formula view_formula;
             Err.error_text =
               "res is not allowed in view definition or invariant";
           }
       else
         (let name_to_sv (v : ident) : CP.spec_var =
            try
              let vinfo = H.find stab v
              in
                match vinfo.sv_info_kind with
                | Known t -> CP.SpecVar (t, v, Unprimed)
                | Unknown ->
                    Err.report_error
                      {
                        Err.error_loc = IF.pos_of_struc_formula view_formula;
                        Err.error_text = "cstring_of_ouldn't infer type for " ^ v;
                      }
            with
            | Not_found ->
                Err.report_error
                  {
                    Err.error_loc = IF.pos_of_struc_formula view_formula;
                    Err.error_text = v ^ " is undefined";
                  } in
          let view_sv_vars = List.map name_to_sv vdef.I.view_vars in
          let get_vvar_type vvar =
            try
              let vinfo = H.find stab vvar
              in
                match vinfo.sv_info_kind with
                | Known t -> (t, vvar)
                | Unknown ->
                    Err.report_error
                      {
                        Err.error_loc = IF.pos_of_struc_formula view_formula;
                        Err.error_text = "couldn't infer type for " ^ vvar;
                      }
            with
            | Not_found ->
                failwith
                  ("trans_view: serious error: " ^
                     (vvar ^ " is not found in stab")) in
          let typed_vars = List.map get_vvar_type vdef.I.view_vars in
          let _ = vdef.I.view_typed_vars <- typed_vars in
          let mvars = [] in
          let cvdef =
            {
              C.view_name = vdef.I.view_name;
              C.view_vars = view_sv_vars;
              C.view_modes = vdef.I.view_modes;
              C.view_partially_bound_vars = [];
              C.view_materialized_vars = mvars;
              C.view_data_name = data_name;
              C.view_formula = cf;
              C.view_x_formula = pf;
              C.view_addr_vars = [];
              C.view_user_inv = pf;
            }
          in
            (Debug.devel_pprint ("\n" ^ (Cprinter.string_of_view_decl cvdef))
               (CF.pos_of_struc_formula cf);
             cvdef)))

and set_materialized_vars prog cdef =
  let mvars =
    find_materialized_vars prog cdef.C.view_vars cdef.C.view_formula
  in
    (if true
     then
       (print_string
          ("\nInput parameters of predicate " ^ (cdef.C.view_name ^ ": "));
        print_string
          ((String.concat ", " (List.map CP.name_of_spec_var mvars)) ^ "\n"))
     else ();
     cdef.C.view_materialized_vars <- mvars;
     cdef)

and find_materialized_vars prog params (f0 : CF.struc_formula) : CP.spec_var list =
  let tmp0 = find_struc_mvars prog params f0 in
  let all_mvars = ref tmp0 in
  let ef = ref f0 in
  let quit_loop = ref false
  in
    (while not !quit_loop do ef := Solver.expand_all_struc_preds prog !ef;
       (let tmp1 = find_struc_mvars prog params !ef in
        let tmp2 = CP.remove_dups (tmp1 @ !all_mvars) in
        let tmp3 = CP.difference tmp2 !all_mvars
        in if U.empty tmp3 then quit_loop := true else all_mvars := tmp3)
       done;
     !all_mvars)
		
and find_struc_mvars prog (params : CP.spec_var list) (f0: CF.struc_formula): CP.spec_var list  =
	let rec helper (f0: CF.struc_formula) (pures:CP.formula): CP.spec_var list = 
			let rec find_ext_mvars (pures:CP.formula) (f: CF.ext_formula): Cpure.spec_var list = match f with 
				| Cformula.ECase b -> let mvars = CP.remove_dups (List.fold_left (fun a (c1,c2) -> 
							a@(helper c2 (Cpure.mkAnd c1 pures no_pos))) [] b.Cformula.formula_case_branches) in
					(CP.intersect mvars params)
				| Cformula.EBase b ->	
						let e = helper b.Cformula.formula_ext_continuation pures in
						let be = find_mvars prog params b.Cformula.formula_ext_base pures in
						let res = CP.difference (Util.remove_dups (e@be)) (b.Cformula.formula_ext_explicit_inst @ b.Cformula.formula_ext_implicit_inst) in
						(CP.intersect res params)	in	
		CP.remove_dups (List.fold_left (fun a c-> a@ (find_ext_mvars pures c)) [] f0) in
		(helper f0 (Cpure.mkTrue no_pos) )
	
	
and find_mvars prog (params : CP.spec_var list) (f0 : CF.formula)(pure:CP.formula) :
  CP.spec_var list =
  match f0 with
  | CF.Or { CF.formula_or_f1 = f1; CF.formula_or_f2 = f2 } ->
      let mvars1 = find_mvars prog params f1 pure in
      let mvars2 = find_mvars prog params f2 pure in
      let mvars = CP.remove_dups (mvars1 @ mvars2) in
      let tmp = CP.intersect mvars params in tmp
  | CF.Base { CF.formula_base_heap = hf; CF.formula_base_pure = pf ; CF.formula_base_pos = pos} ->
      let mvars = find_mvars_heap prog params hf (Cpure.mkAnd pure pf pos) in
      let tmp = CP.intersect mvars params in tmp
  | CF.Exists
      {
        CF.formula_exists_qvars = qvars;
        CF.formula_exists_heap = hf;
        CF.formula_exists_pure = pf;
				CF.formula_exists_pos = pos
      } ->
      let mvars1 = (find_mvars_heap prog params hf (Cpure.mkAnd pure pf pos)) in
      let mvars = CP.difference mvars1 qvars in
      let tmp = CP.intersect mvars params in tmp

and find_mvars_heap prog params hf pf =
  match hf with
  | CF.HTrue | CF.HFalse -> []
  | _ ->
      let eqns = Solver.ptr_equations pf in
      let asets = Solver.alias eqns in
      let self_aset =
        Solver.get_aset asets (CP.SpecVar (CP.OType "", self, Unprimed))
      in self_aset

and all_paths_return (e0 : I.exp) : bool =
  match e0 with
  | I.Assert _ -> false
  | I.Assign _ -> false
  | I.Binary _ -> false
  | I.Bind e -> all_paths_return e.I.exp_bind_body
  | I.Block e -> all_paths_return e.I.exp_block_body
  | I.BoolLit _ -> false
  | I.Break _ -> false
  | I.CallNRecv _ -> false
  | I.CallRecv _ -> false
  | I.Cast _ -> false
  | I.Cond e ->
      (all_paths_return e.I.exp_cond_then_arm) &&
        (all_paths_return e.I.exp_cond_else_arm)
  | I.ConstDecl _ -> false
  | I.Continue _ -> false
  | I.Debug _ -> false
  | I.Dprint _ -> false
  | I.Empty _ -> false
  | I.FloatLit _ -> false
  | I.IntLit _ -> false
  | I.Java _ -> false
  | I.Member _ -> false
  | I.New _ -> false
  | I.Null _ -> false
  | I.Return _ -> true
  | I.Seq e ->
      (all_paths_return e.I.exp_seq_exp1) ||
        (all_paths_return e.I.exp_seq_exp2)
  | I.This _ -> false
  | I.Unary _ -> false
  | I.Var _ -> false
  | I.VarDecl _ -> false
  | I.While _ -> false
  | I.Unfold _ -> false

and check_return (proc : I.proc_decl) : bool =
  match proc.I.proc_body with
  | None -> true
  | Some e ->
      if
        (not (I.are_same_type I.void_type proc.I.proc_return)) &&
          (not (all_paths_return e))
      then false
      else true


and trans_proc (prog : I.prog_decl) (proc : I.proc_decl) : C.proc_decl =
  let dup_names =
    U.find_one_dup (fun a1 a2 -> a1.I.param_name = a2.I.param_name)
      proc.I.proc_args
  in
    if not (U.empty dup_names)
    then
      (let p = List.hd dup_names
       in
         Err.report_error
           {
             Err.error_loc = p.I.param_loc;
             Err.error_text =
               "parameter " ^ (p.I.param_name ^ " is duplicated");
           })
    else
      if not (check_return proc)
      then
        Err.report_error
          {
            Err.error_loc = proc.I.proc_loc;
            Err.error_text =
              "not all paths of " ^ (proc.I.proc_name ^ " contain a return");
          }
      else
        (E.push_scope ();
         (let all_args =
            if U.is_some proc.I.proc_data_decl
            then
              (let cdef = U.unsome proc.I.proc_data_decl in
               let this_arg =
                 {
                   I.param_type = I.Named cdef.I.data_name;
                   I.param_name = this;
                   I.param_mod = I.NoMod;
                   I.param_loc = proc.I.proc_loc;
                 }
               in this_arg :: proc.I.proc_args)
            else proc.I.proc_args in
          let p2v (p : I.param) =
            {
              E.var_name = p.I.param_name;
              E.var_alpha = p.I.param_name;
              E.var_type = p.I.param_type;
            } in
          let vinfos = List.map p2v all_args in
          let _ =
            List.map (fun v -> E.add v.E.var_name (E.VarInfo v)) vinfos in
          let cret_type = trans_type prog proc.I.proc_return proc.I.proc_loc in
          let free_vars = List.map (fun p -> p.I.param_name) all_args in
          let stab = H.create 103 in
          let add_param p =
            H.add stab p.I.param_name
              {
                sv_info_kind =
                  Known (trans_type prog p.I.param_type p.I.param_loc);
              }
          in
            (ignore (List.map add_param all_args);
						 let tshp = List.fold_left (fun (a1,a2) c-> 
							((c.Iast.param_name,Unprimed)::a1,							
							match c.Iast.param_mod with
								| Iast.NoMod -> a2
								| Iast.RefMod -> (c.Iast.param_name,Primed)::a2)) ([],[(res,Unprimed)]) proc.Iast.proc_args in
             let static_specs_list,tg1 =
               trans_specs prog  free_vars tshp proc.I.proc_static_specs stab  cret_type in
             let dynamic_specs_list,tg2 =
               trans_specs prog  free_vars tshp proc.I.proc_dynamic_specs stab cret_type in
														
             let body =
               match proc.I.proc_body with
               | None -> None
               | Some e -> let (b, tb) = trans_exp prog proc (tg1@tg2) e in Some b in
             let args =
               List.map
                 (fun p ->
                    ((trans_type prog p.I.param_type p.I.param_loc),
                     (p.I.param_name)))
                 proc.I.proc_args in
             let by_names_tmp =
               List.filter (fun p -> p.I.param_mod = I.RefMod)
                 proc.I.proc_args in
             let new_pt p = trans_type prog p.I.param_type p.I.param_loc in
             let by_names =
               List.map
                 (fun p -> CP.SpecVar (new_pt p, p.I.param_name, Unprimed))
                 by_names_tmp in
             let final_static_specs_list =
               if U.empty static_specs_list
               then
                 Cast.mkMultiSpec no_pos
               else static_specs_list in
             let final_dynamic_specs_list = dynamic_specs_list in
             let cproc =
               {
                 C.proc_name = proc.I.proc_mingled_name;
                 C.proc_args = args;
                 C.proc_return =
                   trans_type prog proc.I.proc_return proc.I.proc_loc;
                 C.proc_static_specs = final_static_specs_list;
                 C.proc_dynamic_specs = final_dynamic_specs_list;
                 C.proc_by_name_params = by_names;
                 C.proc_body = body;
                 C.proc_loc = proc.I.proc_loc;
               }
             in (E.pop_scope (); cproc))))

and trans_coercions (prog : I.prog_decl) :
  ((C.coercion_decl list) * (C.coercion_decl list)) =
  let tmp =
    List.map (fun coer -> trans_one_coercion prog coer)
      prog.I.prog_coercion_decls in
  let (tmp1, tmp2) = List.split tmp in
  let tmp3 = List.concat tmp1 in let tmp4 = List.concat tmp2 in (tmp3, tmp4)

and trans_one_coercion (prog : I.prog_decl) (coer : I.coercion_decl) :
  ((C.coercion_decl list) * (C.coercion_decl list)) =
  let stab = H.create 103 in
	let na_ch = Iformula.convert_anonym_to_exist coer.I.coercion_head in
	let n_ch = Iformula.norm_formula [(self,Unprimed)]false na_ch in
  let c_lhs = trans_formula prog n_ch stab in
  let lhs_fnames = List.map CP.name_of_spec_var (CF.fv c_lhs) in
  let compute_univ () =
    let (h, p, _) = CF.split_components c_lhs in
    let pvars = CP.fv p in
    let hvars = CF.h_fv h in
    let univ_vars = CP.difference pvars hvars in CP.remove_dups univ_vars in
  let univ_vars = compute_univ () in
  let lhs_fnames =
    Util.difference lhs_fnames (List.map CP.name_of_spec_var univ_vars) in
	let n_cb = Iformula.convert_anonym_to_exist coer.I.coercion_body in
	let n_cb = Iformula.norm_formula (List.map (fun c-> (c,Unprimed)) (self::lhs_fnames))(U.empty univ_vars)  n_cb in
  let c_rhs = trans_formula prog n_cb stab in
  let rhs_fnames = List.map CP.name_of_spec_var (CF.fv c_rhs) in
	let n_ch = Iformula.norm_formula (List.map (fun c-> (c,Unprimed)) (self::rhs_fnames)) true  na_ch in
  let c_lhs_exist = trans_formula prog  n_ch stab in
  let lhs_name =
    find_view_name c_lhs self (IF.pos_of_formula coer.I.coercion_head) in
  let rhs_name =
    try find_view_name c_rhs self (IF.pos_of_formula coer.I.coercion_body)
    with | _ -> ""
  in
    if lhs_name = ""
    then
      Error.report_error
        {
          Err.error_loc = IF.pos_of_formula coer.I.coercion_head;
          Err.error_text = "root pointer of node on LHS must be self";
        }
    else
      (let c_coer =
         {
           C.coercion_name = coer.I.coercion_name;
           C.coercion_head = c_lhs;
           C.coercion_body = c_rhs;
           C.coercion_univ_vars = univ_vars;
           C.coercion_head_exist = c_lhs_exist;
           C.coercion_head_view = lhs_name;
           C.coercion_body_view = rhs_name;
         }
       in
         match coer.I.coercion_type with
         | I.Left -> ([ c_coer ], [])
         | I.Equiv -> ([ c_coer ], [ c_coer ])
         | I.Right -> ([], [ c_coer ]))

and find_view_name (f0 : CF.formula) (v : ident) pos =
  match f0 with
  | CF.Base
      {
        CF.formula_base_heap = h;
        CF.formula_base_pure = _;
        CF.formula_base_pos = _
      } |
      CF.Exists
        {
          CF.formula_exists_qvars = _;
          CF.formula_exists_heap = h;
          CF.formula_exists_pure = _;
          CF.formula_exists_pos = _
        }
      ->
      let rec find_view_heap h0 =
        (match h0 with
         | CF.Star
             {
               CF.h_formula_star_h1 = h1;
               CF.h_formula_star_h2 = h2;
               CF.h_formula_star_pos = _
             } ->
             let name1 = find_view_heap h1 in
             let name2 = find_view_heap h2
             in
               if name1 = ""
               then name2
               else
                 if name2 = ""
                 then name1
                 else
                   Err.report_error
                     {
                       Err.error_loc = pos;
                       Err.error_text = v ^ " must point to only one view";
                     }
         | CF.DataNode
             {
               CF.h_formula_data_node = p;
               CF.h_formula_data_name = c;
               CF.h_formula_data_arguments = _;
               CF.h_formula_data_pos = _
             } ->
             if (CP.name_of_spec_var p) = v
             then
               Err.report_error
                 {
                   Err.error_loc = pos;
                   Err.error_text = v ^ " must point to a view";
                 }
             else ""
         | CF.ViewNode
             {
               CF.h_formula_view_node = p;
               CF.h_formula_view_name = c;
               CF.h_formula_view_arguments = _;
               CF.h_formula_view_pos = _
             } -> if (CP.name_of_spec_var p) = v then c else ""
         | CF.HTrue | CF.HFalse -> "")
      in find_view_heap h
  | CF.Or _ ->
      Err.report_error
        {
          Err.error_loc = pos;
          Err.error_text =
            "Pre- and post-conditions of coercion rules must not be disjunctive";
        }

and trans_exp (prog : I.prog_decl) (proc : I.proc_decl) (tg:(ident*primed) list) (ie : I.exp) :
  trans_exp_type =
  match ie with
  | I.Unfold { I.exp_unfold_var = (v, p); I.exp_unfold_pos = pos } ->
      ((C.Unfold
          {
            C.exp_unfold_var = CP.SpecVar (CP.OType "", v, p);
            C.exp_unfold_pos = pos;
          }),
       C.void_type)
  | I.Assert
      {
        I.exp_assert_asserted_formula = assert_f_o;
        I.exp_assert_assumed_formula = assume_f_o;
        I.exp_assert_pos = pos
      } ->
      let tmp_names = E.visible_names () in
      let all_names =
        List.map (fun (t, n) -> ((trans_type prog t pos), n)) tmp_names in
      let free_vars = List.map snd all_names in
      let stab = H.create 19
      in
        (ignore
           (List.map (fun (t, n) -> H.add stab n { sv_info_kind = Known t; })
              all_names);
				 let p_h,p_h2 = List.fold_left (fun (a1,a2) c-> (((c.Iast.param_name,Unprimed)::a1),((c.Iast.param_name,Unprimed)::(c.Iast.param_name,Primed)::a2))) ([],[]) proc.Iast.proc_args in
				 let visible_vars = (Util.difference (snd (List.split (E.visible_names()))) (List.map (fun c-> c.Iast.param_name) proc.Iast.proc_args)) in
				 let known = Util.remove_dups (p_h2@(Util.difference tg p_h)@ (List.map(fun c-> (c,Primed)) visible_vars)) in
         let assert_cf_o =
           (match assert_f_o with
            | Some f -> 
							(*let p_v, p_w = List.fold_left (fun (a1,a2) c-> match c.Iast.param_mod with
																															| Iast.RefMod -> (a1,(c.Iast.param_name::a2))
																															| Iast.NoMod-> ((c.Iast.param_name::a1),a2) ) ([],[]) proc.Iast.proc_args in*)
							(*let p_p = (res,Primed)::(List.map (fun c-> (c,Primed)) p_w) in*)		
													
 							Some (trans_struc_formula prog false (known,(res,Unprimed)::(List.map (fun c-> (c,Unprimed)) visible_vars)) f stab)
            | None -> None) in
         let assume_cf_o =
           (match assume_f_o with
            | None -> None
            | Some f -> 
							let normalized_f = Iformula.norm_formula known false f in							
							Some (trans_formula prog normalized_f stab)) in
         let assert_e =
           C.Assert
             {
               C.exp_assert_asserted_formula = assert_cf_o;
               C.exp_assert_assumed_formula = assume_cf_o;
               C.exp_assert_pos = pos;
             }
         in (assert_e, C.void_type))
  | I.Assign
      {
        I.exp_assign_op = aop;
        I.exp_assign_lhs = lhs;
        I.exp_assign_rhs = rhs;
        I.exp_assign_pos = pos_a
      } ->
      (match aop with
       | I.OpAssign ->
           (match lhs with
            | I.Var { I.exp_var_name = v0; I.exp_var_pos = pos } ->
                let (ce1, te1) = trans_exp prog proc tg lhs in
                let (ce2, te2) = trans_exp prog proc tg rhs
                in
                  if not (sub_type te2 te1)
                  then
                    Err.report_error
                      {
                        Err.error_loc = pos;
                        Err.error_text = "lhs and rhs do not match";
                      }
                  else
                    (let v = C.get_var ce1 in
                     let assign_e =
                       C.Assign
                         {
                           C.exp_assign_lhs = v;
                           C.exp_assign_rhs = ce2;
                           C.exp_assign_pos = pos;
                         }
                     in
                       if C.is_var ce1
                       then (assign_e, C.void_type)
                       else
                         (let seq_e =
                            C.Seq
                              {
                                C.exp_seq_type = C.void_type;
                                C.exp_seq_exp1 = ce1;
                                C.exp_seq_exp2 = assign_e;
                                C.exp_seq_pos = pos;
                              }
                          in (seq_e, C.void_type)))
            | I.Member
                {
                  I.exp_member_base = base_e;
                  I.exp_member_fields = fs;
                  I.exp_member_pos = pos
                } ->
                let (rhs_c, rhs_t) = trans_exp prog proc tg rhs in
                let (fn, new_var) =
                  (match rhs_c with
                   | C.Var { C.exp_var_name = v } -> (v, false)
                   | _ -> let fn = (fresh_var_name (Cprinter.string_of_typ rhs_t) pos.Lexing.pos_lnum) in (fn, true)) in
                let fn_var =
                  C.Var
                    {
                      C.exp_var_type = rhs_t;
                      C.exp_var_name = fn;
                      C.exp_var_pos = pos;
                    } in
                let (tmp_e, tmp_t) =
                  flatten_to_bind prog proc tg base_e (List.rev fs) (Some fn_var) pos in
                let fn_decl =
                  if new_var
                  then
                    C.VarDecl
                      {
                        C.exp_var_decl_type = rhs_t;
                        C.exp_var_decl_name = fn;
                        C.exp_var_decl_pos = pos;
                      }
                  else C.Unit pos in
                let init_fn =
                  if new_var
                  then
                    C.Assign
                      {
                        C.exp_assign_lhs = fn;
                        C.exp_assign_rhs = rhs_c;
                        C.exp_assign_pos = pos;
                      }
                  else C.Unit pos in
                let seq1 = C.mkSeq tmp_t init_fn tmp_e pos in
                let seq2 = C.mkSeq tmp_t fn_decl seq1 pos
                in
                  if new_var
                  then
                    ((C.Block
                        {
                          C.exp_block_type = tmp_t;
                          C.exp_block_body = seq2;
                          C.exp_block_local_vars = [ (rhs_t, fn) ];
                          C.exp_block_pos = pos;
                        }),
                     tmp_t)
                  else (seq2, tmp_t)
            | _ ->
                Err.report_error
                  {
                    Err.error_loc = pos_a;
                    Err.error_text = "lhs is not an lvalue";
                  })
       | _ ->
           let bop = bin_op_of_assign_op aop in
           let new_rhs =
             I.Binary
               {
                 I.exp_binary_op = bop;
                 I.exp_binary_oper1 = lhs;
                 I.exp_binary_oper2 = rhs;
                 I.exp_binary_pos = pos_a;
               } in
           let new_assign =
             I.Assign
               {
                 I.exp_assign_op = I.OpAssign;
                 I.exp_assign_lhs = lhs;
                 I.exp_assign_rhs = new_rhs;
                 I.exp_assign_pos = pos_a;
               }
           in trans_exp prog proc tg new_assign)
  | I.Binary
      {
        I.exp_binary_op = b_op;
        I.exp_binary_oper1 = e1;
        I.exp_binary_oper2 = e2;
        I.exp_binary_pos = pos
      } ->
      if (I.is_null e1) || (I.is_null e2)
      then
        (let (e1_prim, e2_prim) =
           if I.is_null e2 then (e1, e2) else (e2, e1) in
         let new_op =
           match b_op with
           | I.OpEq -> I.OpIsNull
           | I.OpNeq -> I.OpIsNotNull
           | _ ->
               Err.report_error
                 {
                   Err.error_loc = pos;
                   Err.error_text = "null can only be used with == or !=";
                 } in
         let b_call = get_binop_call new_op in
         let new_e =
           I.CallNRecv
             {
               I.exp_call_nrecv_method = b_call;
               I.exp_call_nrecv_arguments = [ e1_prim ];
               I.exp_call_nrecv_pos = pos;
             }
         in trans_exp prog proc tg new_e)
      else
        (let b_call = get_binop_call b_op in
         let new_e =
           I.CallNRecv
             {
               I.exp_call_nrecv_method = b_call;
               I.exp_call_nrecv_arguments = [ e1; e2 ];
               I.exp_call_nrecv_pos = pos;
             }
         in trans_exp prog proc tg new_e)
  | I.Bind
      {
        I.exp_bind_bound_var = v;
        I.exp_bind_fields = vs;
        I.exp_bind_body = e;
        I.exp_bind_pos = pos
      } ->
      (try
         let vinfo_tmp = E.look_up v
         in
           match vinfo_tmp with
           | E.VarInfo vi ->
               (match vi.E.var_type with
                | I.Named c ->
                    let ddef =
                      I.look_up_data_def pos prog.I.prog_data_decls c
                    in
                      if
                        ( != ) (List.length vs)
                          (List.length ddef.I.data_fields)
                      then
                        Err.report_error
                          {
                            Err.error_loc = pos;
                            Err.error_text =
                              "bind " ^
                                (v ^ ": different number of variables");
                          }
                      else
                        (E.push_scope ();
                         (let _ =
                            List.map2
                              (fun vi ti ->
                                 let alpha = E.alpha_name vi
                                 in
                                   E.add vi
                                     (E.VarInfo
                                        {
                                          E.var_name = vi;
                                          E.var_alpha = alpha;
                                          E.var_type = ti;
                                        }))
                              vs
                              (List.map fst (List.map fst ddef.I.data_fields)) in
                          let vs_types =
                            List.map
                              (fun fld ->
                                 trans_type prog (fst (fst fld)) (snd fld))
                              ddef.I.data_fields in
                          let vt = trans_type prog vi.E.var_type pos in
                          let (ce, te) = trans_exp prog proc tg e in
                          let _ = E.pop_scope ()
                          in
                            ((C.Bind
                                {
                                  C.exp_bind_type = te;
                                  C.exp_bind_bound_var = (vt, v);
                                  C.exp_bind_fields =
                                    List.combine vs_types vs;
                                  C.exp_bind_body = ce;
                                  C.exp_bind_pos = pos;
                                }),
                             te)))
                | I.Prim _ ->
                    Err.report_error
                      {
                        Err.error_loc = pos;
                        Err.error_text = v ^ " is not a data type";
                      }
                | I.Array _ ->
                    Err.report_error
                      {
                        Err.error_loc = pos;
                        Err.error_text = v ^ " is not a data type";
                      })
           | _ ->
               Err.report_error
                 {
                   Err.error_loc = pos;
                   Err.error_text = v ^ " is not a data type";
                 }
       with
       | Not_found ->
           Err.report_error
             { Err.error_loc = pos; Err.error_text = v ^ " is not defined"; })
  | I.Block { I.exp_block_body = e; I.exp_block_pos = pos } ->
      (E.push_scope ();
       let (ce, te) = trans_exp prog proc tg e in
       let tmp_local_vars = E.names_on_top () in
       let local_vars =
         List.map (fun (t, n) -> ((trans_type prog t pos), n)) tmp_local_vars
       in
         (E.pop_scope ();
          ((C.Block
              {
                C.exp_block_type = te;
                C.exp_block_body = ce;
                C.exp_block_local_vars = local_vars;
                C.exp_block_pos = pos;
              }),
           te)))
  | I.BoolLit { I.exp_bool_lit_val = b; I.exp_bool_lit_pos = pos } ->
      ((C.BConst { C.exp_bconst_val = b; C.exp_bconst_pos = pos; }), C.
       bool_type)
  | I.CallRecv
      {
        I.exp_call_recv_receiver = recv;
        I.exp_call_recv_method = mn;
        I.exp_call_recv_arguments = args;
        I.exp_call_recv_pos = pos
      } ->
      let (crecv, crecv_t) = trans_exp prog proc tg recv in
      let (recv_ident, recv_init, new_recv_ident) =
        (match crecv with
         | C.Var { C.exp_var_name = v } -> (v, (C.Unit pos), false)
         | _ ->
             let fname = (fresh_var_name (Cprinter.string_of_typ crecv_t) (pos.Lexing.pos_lnum)) in
             let fdecl =
               C.VarDecl
                 {
                   C.exp_var_decl_type = crecv_t;
                   C.exp_var_decl_name = fname;
                   C.exp_var_decl_pos = pos;
                 } in
             let finit =
               C.Assign
                 {
                   C.exp_assign_lhs = fname;
                   C.exp_assign_rhs = crecv;
                   C.exp_assign_pos = pos;
                 } in
             let seq = C.mkSeq C.void_type fdecl finit pos
             in (fname, seq, true)) in
      let tmp= List.map (trans_exp prog proc tg ) args in
      let (cargs, cts) = List.split tmp in
      let mingled_mn = C.mingle_name mn cts in
      let class_name = C.name_of_type crecv_t
      in
        (try
           let cdef =
             I.look_up_data_def pos prog.I.prog_data_decls class_name in
           let all_methods = I.look_up_all_methods prog cdef in
           let pdef = I.look_up_proc_def_mingled_name all_methods mingled_mn
           in
             if ( != ) (List.length args) (List.length pdef.I.proc_args)
             then
               Err.report_error
                 {
                   Err.error_loc = pos;
                   Err.error_text = "number of arguments does not match";
                 }
             else
               (let parg_types =
                  List.map
                    (fun p -> trans_type prog p.I.param_type p.I.param_loc)
                    pdef.I.proc_args
                in
                  if
                    List.exists2 (fun t1 t2 -> not (sub_type t1 t2)) cts
                      parg_types
                  then
                    Err.report_error
                      {
                        Err.error_loc = pos;
                        Err.error_text = "argument types do not match";
                      }
                  else
                    (let ret_ct =
                       trans_type prog pdef.I.proc_return pdef.I.proc_loc in
                     let positions = List.map I.get_exp_pos args in
                     let (local_vars, init_seq, arg_vars) =
                       trans_args (U.combine3 cargs cts positions) in
                     let visi_names = E.visible_names () in
                     let visi_svars =
                       List.map
                         (fun (t, n) ->
                            CP.SpecVar (trans_type prog t pos, n, Primed))
                         visi_names in
                     let call_e =
                       C.ICall
                         {
                           C.exp_icall_type = ret_ct;
                           C.exp_icall_receiver = recv_ident;
                           C.exp_icall_receiver_type = crecv_t;
                           C.exp_icall_method_name = mingled_mn;
                           C.exp_icall_arguments = arg_vars;
                           C.exp_icall_visible_names = visi_svars;
                           C.exp_icall_pos = pos;
                         } in
                     let seq1 = C.mkSeq ret_ct init_seq call_e pos in
                     let seq2 = C.mkSeq ret_ct recv_init seq1 pos in
                     let blk =
                       C.Block
                         {
                           C.exp_block_type = ret_ct;
                           C.exp_block_body = seq2;
                           C.exp_block_local_vars =
                             (if new_recv_ident
                              then [ (crecv_t, recv_ident) ]
                              else []) @ local_vars;
                           C.exp_block_pos = pos;
                         }
                     in (blk, ret_ct)))
         with
         | Not_found ->
             Err.report_error
               {
                 Err.error_loc = pos;
                 Err.error_text =
                   "procedure " ^ (mingled_mn ^ " is not found");
               })
  | I.CallNRecv
      {
        I.exp_call_nrecv_method = mn;
        I.exp_call_nrecv_arguments = args;
        I.exp_call_nrecv_pos = pos
      } ->
			let tmp= List.map (trans_exp prog proc tg) args in
      let (cargs, cts) = List.split tmp in
      let mingled_mn = C.mingle_name mn cts in
      let this_recv =
        if U.is_some proc.I.proc_data_decl
        then
          (let cdef = U.unsome proc.I.proc_data_decl in
           let tmp1 = I.look_up_all_methods prog cdef in
           let tmp2 =
             List.exists (fun p -> p.I.proc_mingled_name = mingled_mn) tmp1
           in tmp2)
        else false
      in
        if this_recv
        then
          (let call_recv =
             I.CallRecv
               {
                 I.exp_call_recv_receiver = I.This { I.exp_this_pos = pos; };
                 I.exp_call_recv_method = mingled_mn;
                 I.exp_call_recv_arguments = args;
                 I.exp_call_recv_pos = pos;
               }
           in trans_exp prog proc tg call_recv)
        else
          (try
             let pdef =
               I.look_up_proc_def_mingled_name prog.I.prog_proc_decls
                 mingled_mn
             in
               if ( != ) (List.length args) (List.length pdef.I.proc_args)
               then
                 Err.report_error
                   {
                     Err.error_loc = pos;
                     Err.error_text = "number of arguments does not match";
                   }
               else
                 (let parg_types =
                    List.map
                      (fun p -> trans_type prog p.I.param_type p.I.param_loc)
                      pdef.I.proc_args
                  in
                    if
                      List.exists2 (fun t1 t2 -> not (sub_type t1 t2)) cts
                        parg_types
                    then
                      Err.report_error
                        {
                          Err.error_loc = pos;
                          Err.error_text = "argument types do not match";
                        }
                    else
                      if Inliner.is_inlined mn
                      then
                        (let inlined_exp = Inliner.inline prog pdef ie
                         in trans_exp prog proc tg inlined_exp)
                      else
                        (let ret_ct =
                           trans_type prog pdef.I.proc_return pdef.I.proc_loc in
                         let positions = List.map I.get_exp_pos args in
                         let (local_vars, init_seq, arg_vars) =
                           trans_args (U.combine3 cargs cts positions) in
                         let visi_names = E.visible_names () in
                         let visi_svars =
                           List.map
                             (fun (t, n) ->
                                CP.SpecVar (trans_type prog t pos, n, Primed))
                             visi_names in
                         let call_e =
                           C.SCall
                             {
                               C.exp_scall_type = ret_ct;
                               C.exp_scall_method_name = mingled_mn;
                               C.exp_scall_arguments = arg_vars;
                               C.exp_scall_visible_names = visi_svars;
                               C.exp_scall_pos = pos;
                             } in
                         let seq_1 = C.mkSeq ret_ct init_seq call_e pos
                         in
                           ((C.Block
                               {
                                 C.exp_block_type = ret_ct;
                                 C.exp_block_body = seq_1;
                                 C.exp_block_local_vars = local_vars;
                                 C.exp_block_pos = pos;
                               }),
                            ret_ct )))
           with
           | Not_found ->
               Err.report_error
                 {
                   Err.error_loc = pos;
                   Err.error_text =
                     "procedure " ^ (mingled_mn ^ " is not found");
                 })
  | I.Cond
      {
        I.exp_cond_condition = e1;
        I.exp_cond_then_arm = e2;
        I.exp_cond_else_arm = e3;
        I.exp_cond_pos = pos
      } ->
      let (ce1, te1) = trans_exp prog proc tg e1
      in
        if not (CP.are_same_types te1 C.bool_type)
        then
          Err.report_error
            {
              Error.error_loc = pos;
              Error.error_text = "conditional expression is not bool";
            }
        else
          (let (ce2', te2) = trans_exp prog proc tg e2 in
           let (ce3', te3) = trans_exp prog proc tg e3 in
           let ce2 = insert_dummy_vars ce2' pos in
           let ce3 = insert_dummy_vars ce3' pos
           in
             match ce1 with
             | C.Var
                 { C.exp_var_type = _; C.exp_var_name = v; C.exp_var_pos = _
                 } ->
                 ((C.Cond
                     {
											 C.exp_cond_type = te2;
                       C.exp_cond_condition = v;
                       C.exp_cond_then_arm = ce2;
                       C.exp_cond_else_arm = ce3;
                       C.exp_cond_pos = pos;
                     }),
                  te2)
             | _ ->
                 let fn = (fresh_var_name "bool" pos.Lexing.pos_lnum) in
                 let vd =
                   C.VarDecl
                     {
                       C.exp_var_decl_type = C.bool_type;
                       C.exp_var_decl_name = fn;
                       C.exp_var_decl_pos = pos;
                     } in
                 let init_e =
                   C.Assign
                     {
                       C.exp_assign_lhs = fn;
                       C.exp_assign_rhs = ce1;
                       C.exp_assign_pos = pos;
                     } in
                 let cond_e =
                   C.Cond
                     {
                       C.exp_cond_type = te2;
                       C.exp_cond_condition = fn;
                       C.exp_cond_then_arm = ce2;
                       C.exp_cond_else_arm = ce3;
                       C.exp_cond_pos = pos;
                     } in
                 let tmp_e1 =
                   C.Seq
                     {
                       C.exp_seq_type = te2;
                       C.exp_seq_exp1 = init_e;
                       C.exp_seq_exp2 = cond_e;
                       C.exp_seq_pos = pos;
                     } in
                 let tmp_e2 =
                   C.Seq
                     {
                       C.exp_seq_type = te2;
                       C.exp_seq_exp1 = vd;
                       C.exp_seq_exp2 = tmp_e1;
                       C.exp_seq_pos = pos;
                     }
                 in (tmp_e2, te2))
  | I.Debug { I.exp_debug_flag = flag; I.exp_debug_pos = pos } ->
      ((C.Debug { C.exp_debug_flag = flag; C.exp_debug_pos = pos; }), C.
       void_type)
  | I.Dprint { I.exp_dprint_string = str; I.exp_dprint_pos = pos } ->
      let tmp_visib_names = E.visible_names () in
      let tmp_visib_names =
        List.filter (fun v -> I.is_named_type (fst v)) tmp_visib_names in
      let visib_names = List.map snd tmp_visib_names in
      let ce =
        C.Dprint
          {
            C.exp_dprint_string = str;
            C.exp_dprint_visible_names = visib_names;
            C.exp_dprint_pos = pos;
          }
      in (ce, C.void_type)
  | I.Empty pos -> ((C.Unit pos), C.void_type)
  | I.IntLit { I.exp_int_lit_val = i; I.exp_int_lit_pos = pos } ->
      ((C.IConst { C.exp_iconst_val = i; C.exp_iconst_pos = pos; }), C.
       int_type)
  | I.Java { I.exp_java_code = jcode; I.exp_java_pos = pos } ->
      ((C.Java { C.exp_java_code = jcode; C.exp_java_pos = pos; }), C.
       void_type)
  | I.Member
      {
        I.exp_member_base = e;
        I.exp_member_fields = fs;
        I.exp_member_pos = pos
      } -> flatten_to_bind prog proc tg e (List.rev fs) None pos
  | I.New
      {
        I.exp_new_class_name = c;
        I.exp_new_arguments = args;
        I.exp_new_pos = pos
      } ->
      let data_def = I.look_up_data_def pos prog.I.prog_data_decls c in
      let all_fields = I.look_up_all_fields prog data_def in
      let field_types = List.map (fun f -> fst (fst f)) all_fields in
      let nargs = List.length args
      in
        if ( != ) nargs (List.length field_types)
        then
          Err.report_error
            {
              Err.error_loc = pos;
              Err.error_text = "number of arguments does not match";
            }
        else
          (
					 let tmp= List.map (trans_exp prog proc tg) args in
           let (cargs, cts) = List.split tmp in
           let parg_types =
             List.map (fun ft -> trans_type prog ft pos) field_types
           in
             if
               List.exists2 (fun t1 t2 -> not (sub_type t1 t2)) cts
                 parg_types
             then
               Err.report_error
                 {
                   Err.error_loc = pos;
                   Err.error_text = "argument types do not match";
                 }
             else
               (let positions = U.repeat pos nargs in
                let (local_vars, init_seq, arg_vars) =
                  trans_args (U.combine3 cargs cts positions) in
                let new_e =
                  C.New
                    {
                      C.exp_new_class_name = c;
                      C.exp_new_parent_name = data_def.I.data_parent_name;
                      C.exp_new_arguments = List.combine parg_types arg_vars;
                      C.exp_new_pos = pos;
                    } in
                let new_t = CP.OType c in
                let seq_e = C.mkSeq new_t init_seq new_e pos
                in
                  ((C.Block
                      {
                        C.exp_block_type = new_t;
                        C.exp_block_body = seq_e;
                        C.exp_block_local_vars = local_vars;
                        C.exp_block_pos = pos;
                      }),
                   new_t)))
  | I.Null pos -> ((C.Null pos), (CP.OType ""))
  | I.Return { I.exp_return_val = oe; I.exp_return_pos = pos } ->
      let cret_type = trans_type prog proc.I.proc_return proc.I.proc_loc
      in
        (match oe with
         | None ->
             if CP.are_same_types cret_type C.void_type
             then
               ((C.Return
                   {
                     C.exp_return_type = C.void_type;
                     C.exp_return_val = None;
                     C.exp_return_pos = pos;
                   }),
                C.void_type)
             else
               Err.report_error
                 {
                   Err.error_loc = proc.I.proc_loc;
                   Err.error_text =
                     "return statement for procedures with non-void return type need a value";
                 }
         | Some e ->
             let (ce, ct) = trans_exp prog proc tg e
             in
               if sub_type ct cret_type
               then
                 ((C.Return
                     {
                       C.exp_return_type = C.void_type;
                       C.exp_return_val = Some ce;
                       C.exp_return_pos = pos;
                     }),
                  C.void_type)
               else
                 Err.report_error
                   {
                     Err.error_loc = proc.I.proc_loc;
                     Err.error_text = "return type doesn't match";
                   })
  | I.Seq { I.exp_seq_exp1 = e1; I.exp_seq_exp2 = e2; I.exp_seq_pos = pos }
      ->
      let (ce1', te1) = trans_exp prog proc tg e1 in
      let (ce2 , te2) = trans_exp prog proc tg e2 in
      let ce1 = insert_dummy_vars ce1' pos
      in
        ((C.Seq
            {
              C.exp_seq_type = te2;
              C.exp_seq_exp1 = ce1;
              C.exp_seq_exp2 = ce2;
              C.exp_seq_pos = pos;
            }),
         te2)
  | I.This { I.exp_this_pos = pos } ->
      if U.is_some proc.I.proc_data_decl
      then
        (let cdef = U.unsome proc.I.proc_data_decl in
         let ct = CP.OType cdef.I.data_name
         in ((C.This { C.exp_this_type = ct; C.exp_this_pos = pos; }), ct))
      else
        Err.report_error
          {
            Err.error_loc = pos;
            Err.error_text =
              "\"this\" can only be used in members of a class";
          }
  | I.Unary
      { I.exp_unary_op = u_op; I.exp_unary_exp = e; I.exp_unary_pos = pos }
      ->
      (match u_op with
       | I.OpNot ->
           let u_call = "not___" in
           let call_e =
             I.CallNRecv
               {
                 I.exp_call_nrecv_method = u_call;
                 I.exp_call_nrecv_arguments = [ e ];
                 I.exp_call_nrecv_pos = pos;
               }
           in trans_exp prog proc tg call_e
       | I.OpPostInc ->
           let fn = (fresh_var_name "int" pos.Lexing.pos_lnum) in
           let fn_decl =
             I.VarDecl
               {
                 I.exp_var_decl_type = I.int_type;
                 I.exp_var_decl_decls = [ (fn, (Some e), pos) ];
                 I.exp_var_decl_pos = pos;
               } in
           let add1_e =
             I.Binary
               {
                 I.exp_binary_op = I.OpPlus;
                 I.exp_binary_oper1 = e;
                 I.exp_binary_oper2 =
                   I.IntLit
                     { I.exp_int_lit_val = 1; I.exp_int_lit_pos = pos; };
                 I.exp_binary_pos = pos;
               } in
           let assign_e =
             I.Assign
               {
                 I.exp_assign_op = I.OpAssign;
                 I.exp_assign_lhs = e;
                 I.exp_assign_rhs = add1_e;
                 I.exp_assign_pos = pos;
               } in
           let seq1 =
             I.Seq
               {
                 I.exp_seq_exp1 = assign_e;
                 I.exp_seq_exp2 =
                   I.Var { I.exp_var_name = fn; I.exp_var_pos = pos; };
                 I.exp_seq_pos = pos;
               } in
           let seq2 =
             I.Seq
               {
                 I.exp_seq_exp1 = fn_decl;
                 I.exp_seq_exp2 = seq1;
                 I.exp_seq_pos = pos;
               }
           in
             trans_exp prog proc tg
               (I.Block { I.exp_block_body = seq2; I.exp_block_pos = pos; })
       | I.OpPostDec ->
           let fn = (fresh_var_name "int" pos.Lexing.pos_lnum) in
           let fn_decl =
             I.VarDecl
               {
                 I.exp_var_decl_type = I.int_type;
                 I.exp_var_decl_decls = [ (fn, (Some e), pos) ];
                 I.exp_var_decl_pos = pos;
               } in
           let sub1_e =
             I.Binary
               {
                 I.exp_binary_op = I.OpMinus;
                 I.exp_binary_oper1 = e;
                 I.exp_binary_oper2 =
                   I.IntLit
                     { I.exp_int_lit_val = 1; I.exp_int_lit_pos = pos; };
                 I.exp_binary_pos = pos;
               } in
           let assign_e =
             I.Assign
               {
                 I.exp_assign_op = I.OpAssign;
                 I.exp_assign_lhs = e;
                 I.exp_assign_rhs = sub1_e;
                 I.exp_assign_pos = pos;
               } in
           let seq1 =
             I.Seq
               {
                 I.exp_seq_exp1 = assign_e;
                 I.exp_seq_exp2 =
                   I.Var { I.exp_var_name = fn; I.exp_var_pos = pos; };
                 I.exp_seq_pos = pos;
               } in
           let seq2 =
             I.Seq
               {
                 I.exp_seq_exp1 = fn_decl;
                 I.exp_seq_exp2 = seq1;
                 I.exp_seq_pos = pos;
               }
           in
             trans_exp prog proc tg
               (I.Block { I.exp_block_body = seq2; I.exp_block_pos = pos; })
       | I.OpPreInc ->
           let add1_e =
             I.Binary
               {
                 I.exp_binary_op = I.OpPlus;
                 I.exp_binary_oper1 = e;
                 I.exp_binary_oper2 =
                   I.IntLit
                     { I.exp_int_lit_val = 1; I.exp_int_lit_pos = pos; };
                 I.exp_binary_pos = pos;
               } in
           let assign_e =
             I.Assign
               {
                 I.exp_assign_op = I.OpAssign;
                 I.exp_assign_lhs = e;
                 I.exp_assign_rhs = add1_e;
                 I.exp_assign_pos = pos;
               } in
           let seq =
             I.Seq
               {
                 I.exp_seq_exp1 = assign_e;
                 I.exp_seq_exp2 = e;
                 I.exp_seq_pos = pos;
               }
           in
             trans_exp prog proc tg
               (I.Block { I.exp_block_body = seq; I.exp_block_pos = pos; })
       | I.OpPreDec ->
           let sub1_e =
             I.Binary
               {
                 I.exp_binary_op = I.OpMinus;
                 I.exp_binary_oper1 = e;
                 I.exp_binary_oper2 =
                   I.IntLit
                     { I.exp_int_lit_val = 1; I.exp_int_lit_pos = pos; };
                 I.exp_binary_pos = pos;
               } in
           let assign_e =
             I.Assign
               {
                 I.exp_assign_op = I.OpAssign;
                 I.exp_assign_lhs = e;
                 I.exp_assign_rhs = sub1_e;
                 I.exp_assign_pos = pos;
               } in
           let seq =
             I.Seq
               {
                 I.exp_seq_exp1 = assign_e;
                 I.exp_seq_exp2 = e;
                 I.exp_seq_pos = pos;
               }
           in
             trans_exp prog proc tg
               (I.Block { I.exp_block_body = seq; I.exp_block_pos = pos; })
       | _ -> failwith "u_op not supported yet")
  | I.Var { I.exp_var_name = v; I.exp_var_pos = pos } ->
      (try
         let vinfo_tmp = E.look_up v
         in
           match vinfo_tmp with
           | E.VarInfo vi ->
               let ct = trans_type prog vi.E.var_type pos
               in
                 ((C.Var
                     {
                       C.exp_var_type = ct;
                       C.exp_var_name = vi.E.var_alpha;
                       C.exp_var_pos = pos;
                     }),
                  ct)
           | E.ConstInfo ci ->
               let ct = trans_type prog ci.E.const_type pos
               in ((ci.E.const_value), ct)
           | E.EnumInfo ei ->
               let ct = trans_type prog ei.E.enum_type pos
               in
                 ((C.IConst
                     {
                       C.exp_iconst_val = ei.E.enum_value;
                       C.exp_iconst_pos = pos;
                     }),
                  ct)
       with
       | Not_found ->
           Err.report_error
             { Err.error_loc = pos; Err.error_text = v ^ " is not defined"; })
  | I.VarDecl
      {
        I.exp_var_decl_type = t;
        I.exp_var_decl_decls = decls;
        exp_var_decl_pos = tpos
      } ->
      let ct = trans_type prog t tpos in
      let rec helper ds =
        (match ds with
         | [ (v, oe, pos) ] ->
             if E.name_clash v
             then
               Err.report_error
                 {
                   Err.error_loc = pos;
                   Err.error_text = v ^ " is already declared";
                 }
             else
               (let alpha = E.alpha_name v
                in
                  (E.add v
                     (E.VarInfo
                        {
                          E.var_name = v;
                          E.var_alpha = alpha;
                          E.var_type = t;
                        });
                   let init_val =
                     match oe with
                     | Some e ->
                         let (tmp_e, tmp_t) = trans_exp prog proc tg e
                         in
                           if sub_type tmp_t ct
                           then tmp_e
                           else
                             Err.report_error
                               {
                                 Err.error_loc = pos;
                                 Err.error_text =
                                   "initializer doesn't match variable type";
                               }
                     | None -> default_value ct pos in
                   let init_e =
                     C.Assign
                       {
                         C.exp_assign_lhs = alpha;
                         C.exp_assign_rhs = init_val;
                         C.exp_assign_pos = pos;
                       } in
                   let var_decl =
                     C.VarDecl
                       {
                         C.exp_var_decl_type = ct;
                         C.exp_var_decl_name = alpha;
                         C.exp_var_decl_pos = pos;
                       }
                   in
                     C.Seq
                       {
                         C.exp_seq_type = C.void_type;
                         C.exp_seq_exp1 = var_decl;
                         C.exp_seq_exp2 = init_e;
                         C.exp_seq_pos = pos;
                       }))
         | (v, oe, pos) :: rest ->
             let crest = helper rest in
             let ce = helper [ (v, oe, pos) ]
             in
               C.Seq
                 {
                   C.exp_seq_type = C.void_type;
                   C.exp_seq_exp1 = ce;
                   C.exp_seq_exp2 = crest;
                   C.exp_seq_pos = pos;
                 }
         | [] -> failwith "trans_exp: VarDecl has an empty declaration list")
      in ((helper decls), C.void_type)
  | I.While
      {
        I.exp_while_condition = cond;
        I.exp_while_body = body;
        I.exp_while_specs = prepost;
        I.exp_while_pos = pos
      } ->
      let tvars = E.visible_names () in
      let w_args =
        List.map
          (fun tv -> I.Var { I.exp_var_name = snd tv; I.exp_var_pos = pos; })
          tvars in
      let fn3 = fresh_name () in
      let w_name =
        fn3 ^
          ("_" ^
             (U.replace_path_sep_with_uscore
                (U.replace_dot_with_uscore (string_of_loc pos)))) in
      let w_body_1 = convert_while_body body w_name w_args in
      let w_body_2 =
        I.Block
          {
            I.exp_block_body =
              I.Seq
                {
                  I.exp_seq_exp1 = w_body_1;
                  I.exp_seq_exp2 =
                    I.CallNRecv
                      {
                        I.exp_call_nrecv_method = w_name;
                        I.exp_call_nrecv_arguments = w_args;
                        I.exp_call_nrecv_pos = pos;
                      };
                  I.exp_seq_pos = pos;
                };
            I.exp_block_pos = pos;
          } in
      let w_body =
        I.Block
          {
            I.exp_block_body =
              I.Cond
                {
                  I.exp_cond_condition = cond;
                  I.exp_cond_then_arm = w_body_2;
                  I.exp_cond_else_arm = I.Empty pos;
                  I.exp_cond_pos = pos;
                };
            I.exp_block_pos = pos;
          } in
      let w_formal_args =
        List.map
          (fun tv ->
             {
               I.param_type = fst tv;
               I.param_name = snd tv;
               I.param_mod = I.RefMod;
               I.param_loc = pos;
             })
          tvars in
      let w_proc =
        {
          I.proc_name = w_name;
          I.proc_mingled_name =
            mingle_name_enum prog w_name (List.map fst tvars);
          I.proc_data_decl = proc.I.proc_data_decl;
          I.proc_constructor = false;
          I.proc_args = w_formal_args;
          I.proc_return = I.void_type;
          I.proc_static_specs = prepost;
          I.proc_dynamic_specs = [];
          I.proc_body = Some w_body;
          I.proc_loc = pos;
        } in
      let w_call =
        I.CallNRecv
          {
            I.exp_call_nrecv_method = w_name;
            I.exp_call_nrecv_arguments = w_args;
            I.exp_call_nrecv_pos = pos;
          } in
      let new_prog =
        { (prog) with I.prog_proc_decls = w_proc :: prog.I.prog_proc_decls; } in
      let (iw_call, _) = trans_exp new_prog w_proc tg w_call in
      let cw_proc = trans_proc new_prog w_proc
      in (loop_procs := cw_proc :: !loop_procs; (iw_call, C.void_type))
  | _ -> failwith (Iprinter.string_of_exp ie)

and default_value (t : CP.typ) pos : C.exp =
  match t with
  | CP.Prim Int -> C.IConst { C.exp_iconst_val = 0; C.exp_iconst_pos = pos; }
  | CP.Prim Bool ->
      C.BConst { C.exp_bconst_val = false; C.exp_bconst_pos = pos; }
  | CP.Prim Float ->
      C.FConst { C.exp_fconst_val = 0.0; C.exp_fconst_pos = pos; }
  | CP.Prim Void ->
      failwith
        "default_value: void in variable declaration should have been rejected by parser"
  | CP.Prim Bag ->
      failwith "default_value: bag can only be used for constraints"
  | CP.OType c -> C.Null pos

and sub_type (t1 : CP.typ) (t2 : CP.typ) =
  let it1 = trans_type_back t1 in
  let it2 = trans_type_back t2 in I.sub_type it1 it2

and trans_type (prog : I.prog_decl) (t : I.typ) (pos : loc) : CP.typ =
  match t with
  | I.Prim p -> CP.Prim p
  | I.Named c ->
      (try
         let _ = I.look_up_data_def_raw prog.I.prog_data_decls c
         in CP.OType c
       with
       | Not_found ->
           (try
              let _ = I.look_up_enum_def_raw prog.I.prog_enum_decls c
              in CP.Prim Int
            with
            | Not_found ->
                Err.report_error
                  {
                    Err.error_loc = pos;
                    Err.error_text = c ^ " is neither data nor enum type";
                  }))
  | I.Array _ ->
      Err.report_error
        {
          Err.error_loc = pos;
          Err.error_text = "trans_type: array is not supported yet";
        }
and
  flatten_to_bind prog proc tg (base : I.exp) (rev_fs : ident list)
                  (rhs_o : C.exp option) pos =
  match rev_fs with
  | f :: rest ->
      let (cbase, base_t) = flatten_to_bind prog proc tg base rest None pos in
      let (fn, new_var) =
        (match cbase with
         | C.Var { C.exp_var_name = v } -> (v, false)
         | _ -> let fn2 = (fresh_var_name (Cprinter.string_of_typ base_t) pos.Lexing.pos_lnum) in (fn2, true)) in
      let fn_decl =
        if new_var
        then
          C.VarDecl
            {
              C.exp_var_decl_type = base_t;
              C.exp_var_decl_name = fn;
              C.exp_var_decl_pos = pos;
            }
        else C.Unit pos in
      let init_fn =
        if new_var
        then
          C.Assign
            {
              C.exp_assign_lhs = fn;
              C.exp_assign_rhs = cbase;
              C.exp_assign_pos = pos;
            }
        else C.Unit pos in
      let dname = CP.name_of_type base_t in
      let ddef = I.look_up_data_def pos prog.I.prog_data_decls dname in
      let rec gen_names (fn : ident) (flist : I.typed_ident list) :
        ((I.typed_ident option) * (ident list)) =
        (match flist with
         | [] -> (None, [])
         | f :: rest ->
             let fn1 = fresh_trailer () in
             let fresh_fn = (snd f) ^"_"^(string_of_int pos.Lexing.pos_lnum)^ fn1 in
             let (tmp, new_rest) = gen_names fn rest
             in
               if (snd f) = fn
               then ((Some (fst f, fresh_fn)), (fresh_fn :: new_rest))
               else (tmp, (fresh_fn :: new_rest))) in
      let all_fields = I.look_up_all_fields prog ddef in
      let field_types =
        List.map (fun f -> trans_type prog (fst (fst f)) pos) all_fields in
      let (tmp1, fresh_names) = gen_names f (List.map fst all_fields)
      in
        if not (U.is_some tmp1)
        then
          Err.report_error
            {
              Err.error_loc = pos;
              Err.error_text = "field " ^ (f ^ " is not accessible");
            }
        else
          (let (vt, fresh_v) = U.unsome tmp1 in
           let ct = trans_type prog vt pos in
           let (bind_body, bind_type) =
             match rhs_o with
             | None ->
                 ((C.Var
                     {
                       C.exp_var_type = ct;
                       C.exp_var_name = fresh_v;
                       C.exp_var_pos = pos;
                     }),
                  ct)
             | Some rhs_e ->
                 let rhs_t = C.type_of_exp rhs_e
                 in
                   if (U.is_some rhs_t) && (sub_type (U.unsome rhs_t) ct)
                   then
                     ((C.Assign
                         {
                           C.exp_assign_lhs = fresh_v;
                           C.exp_assign_rhs = rhs_e;
                           C.exp_assign_pos = pos;
                         }),
                      C.void_type)
                   else
                     Err.report_error
                       {
                         Err.error_loc = pos;
                         Err.error_text = "lhs and rhs do not match";
                       } in
           let bind_e =
             C.Bind
               {
                 C.exp_bind_type = bind_type;
                 C.exp_bind_bound_var = ((CP.OType dname), fn);
                 C.exp_bind_fields = List.combine field_types fresh_names;
                 C.exp_bind_body = bind_body;
                 C.exp_bind_pos = pos;
               } in
           let seq1 = C.mkSeq bind_type init_fn bind_e pos in
           let seq2 = C.mkSeq bind_type fn_decl seq1 pos
           in
             if new_var
             then
               ((C.Block
                   {
                     C.exp_block_type = bind_type;
                     C.exp_block_body = seq2;
                     C.exp_block_local_vars = [ (base_t, fn) ];
                     C.exp_block_pos = pos;
                   }),
                bind_type)
             else (seq2, bind_type))
  | [] -> trans_exp prog proc tg base

and convert_to_bind prog (v : ident) (dname : ident) (fs : ident list)
  (rhs : C.exp option) pos : trans_exp_type =
  match fs with
  | f :: rest ->
      (try
         let ddef = I.look_up_data_def_raw prog.I.prog_data_decls dname in
         let rec gen_names (fn : ident) (flist : I.typed_ident list) :
           ((I.typed_ident option) * (ident list)) =
           match flist with
           | [] -> (None, [])
           | f :: rest ->
               let fn = fresh_name () in
               let fresh_fn = (snd f)^(string_of_int pos.Lexing.pos_lnum) ^ fn in
               let (tmp, new_rest) = gen_names fn rest
               in
                 if (snd f) = fn
                 then ((Some (fst f, fresh_fn)), (fresh_fn :: new_rest))
                 else (tmp, (fresh_fn :: new_rest)) in
         let field_types =
           List.map (fun f -> trans_type prog (fst (fst f)) pos)
             ddef.I.data_fields in
         let (tmp1, fresh_names) =
           gen_names f (List.map fst ddef.I.data_fields)
         in
           if not (U.is_some tmp1)
           then
             Err.report_error
               {
                 Err.error_loc = pos;
                 Err.error_text = "can't follow field " ^ f;
               }
           else
             (let (vt, fresh_v) = U.unsome tmp1 in
              let ct = trans_type prog vt pos in
              let (bind_body, bind_type) =
                if U.empty rest
                then
                  (match rhs with
                   | None ->
                       ((C.Var
                           {
                             C.exp_var_type = ct;
                             C.exp_var_name = fresh_v;
                             C.exp_var_pos = pos;
                           }),
                        ct)
                   | Some rhs_e ->
                       let rhs_t = C.type_of_exp rhs_e
                       in
                         if
                           (U.is_some rhs_t) &&
                             (sub_type (U.unsome rhs_t) ct)
                         then
                           ((C.Assign
                               {
                                 C.exp_assign_lhs = fresh_v;
                                 C.exp_assign_rhs = rhs_e;
                                 C.exp_assign_pos = pos;
                               }),
                            C.void_type)
                         else
                           Err.report_error
                             {
                               Err.error_loc = pos;
                               Err.error_text = "lhs and rhs do not match";
                             })
                else
                  convert_to_bind prog fresh_v (I.name_of_type vt) rest rhs
                    pos
              in
                ((C.Bind
                    {
                      C.exp_bind_type = bind_type;
                      C.exp_bind_bound_var = ((CP.OType dname), v);
                      C.exp_bind_fields =
                        List.combine field_types fresh_names;
                      C.exp_bind_body = bind_body;
                      C.exp_bind_pos = pos;
                    }),
                 bind_type))
       with
       | Not_found ->
           Err.report_error
             {
               Err.error_loc = pos;
               Err.error_text = "can't follow field " ^ f;
             })
  | [] -> failwith "convert_to_bind: empty field list"

and trans_type_back (te : CP.typ) : I.typ =
  match te with | CP.Prim p -> I.Prim p | CP.OType n -> I.Named n

and trans_args (args : (C.exp * CP.typ * loc) list) :
  ((C.typed_ident list) * C.exp * (ident list)) =
  match args with
  | arg :: rest ->
      let (rest_local_vars, rest_e, rest_names) = trans_args rest
      in
        (match arg with
         | (C.Var { C.exp_var_type = _; C.exp_var_name = v; C.exp_var_pos = _
              },
            _, _) -> (rest_local_vars, rest_e, (v :: rest_names))
         | (arg_e, at, pos) ->
             let fn = fresh_var_name (Cprinter.string_of_typ at) pos.Lexing.pos_lnum in
             let fn_decl =
               C.VarDecl
                 {
                   C.exp_var_decl_type = at;
                   C.exp_var_decl_name = fn;
                   C.exp_var_decl_pos = pos;
                 } in
             let fn_init =
               C.Assign
                 {
                   C.exp_assign_lhs = fn;
                   C.exp_assign_rhs = arg_e;
                   C.exp_assign_pos = pos;
                 } in
             let seq1 = C.mkSeq C.void_type fn_init rest_e pos in
             let seq2 = C.mkSeq C.void_type fn_decl seq1 pos in
             let local_var = (at, fn)
             in ((local_var :: rest_local_vars), seq2, (fn :: rest_names)))
  | [] -> ([], (C.Unit no_pos), [])

and get_type_name_for_mingling (prog : I.prog_decl) (t : I.typ) : ident =
  match t with
  | I.Prim _ -> I.name_of_type t
  | I.Named c ->
      (try let _ = I.look_up_enum_def_raw prog.I.prog_enum_decls c in "int"
       with | Not_found -> c)
  | I.Array _ ->
      failwith "get_type_name_for_mingling: array is not supported yet"

and mingle_name_enum prog (m : ident) (targs : I.typ list) =
  let param_tnames =
    String.concat "~" (List.map (get_type_name_for_mingling prog) targs)
  in m ^ ("$" ^ param_tnames)

and set_mingled_name (prog : I.prog_decl) =
  let rec helper1 (pdecls : I.proc_decl list) =
    match pdecls with
    | pdef :: rest ->
        let ptypes = List.map (fun p -> p.I.param_type) pdef.I.proc_args
        in
          (pdef.I.proc_mingled_name <-
             mingle_name_enum prog pdef.I.proc_name ptypes;
           helper1 rest)
    | [] -> () in
  let rec helper2 (cdecls : I.data_decl list) =
    match cdecls with
    | cdef :: rest -> (helper1 cdef.I.data_methods; helper2 rest)
    | [] -> ()
  in (helper1 prog.I.prog_proc_decls; helper2 prog.I.prog_data_decls)

and convert_while_body (body0 : I.exp) (w_call : ident)
  (w_args : I.exp list) : I.exp =
  match body0 with
  | I.Break pos ->
      I.Return { I.exp_return_val = None; I.exp_return_pos = pos; }
  | I.Continue pos ->
      I.CallNRecv
        {
          I.exp_call_nrecv_method = w_call;
          I.exp_call_nrecv_arguments = w_args;
          I.exp_call_nrecv_pos = pos;
        }
  | I.Block { I.exp_block_body = e; I.exp_block_pos = pos } ->
      let ce = convert_while_body e w_call w_args
      in I.Block { I.exp_block_body = ce; I.exp_block_pos = pos; }
  | I.Cond
      {
        I.exp_cond_condition = e1;
        I.exp_cond_then_arm = e2;
        I.exp_cond_else_arm = e3;
        I.exp_cond_pos = pos
      } ->
      let ce2 = convert_while_body e2 w_call w_args in
      let ce3 = convert_while_body e3 w_call w_args
      in
        I.Cond
          {
            I.exp_cond_condition = e1;
            I.exp_cond_then_arm = ce2;
            I.exp_cond_else_arm = ce3;
            I.exp_cond_pos = pos;
          }
  | I.Seq { I.exp_seq_exp1 = e1; I.exp_seq_exp2 = e2; I.exp_seq_pos = pos }
      ->
      let ce1 = convert_while_body e1 w_call w_args in
      let ce2 = convert_while_body e2 w_call w_args
      in
        I.Seq
          { I.exp_seq_exp1 = ce1; I.exp_seq_exp2 = ce2; I.exp_seq_pos = pos;
          }
  | I.While
      {
        I.exp_while_condition = e1;
        I.exp_while_body = e2;
        I.exp_while_specs = prepost;
        I.exp_while_pos = pos
      } ->
      let ce2 = convert_while_body e2 w_call w_args
      in
        I.While
          {
            I.exp_while_condition = e1;
            I.exp_while_body = ce2;
            I.exp_while_specs = prepost;
            I.exp_while_pos = pos;
          }
  | _ -> body0

and insert_dummy_vars (ce : C.exp) (pos : loc) : C.exp =
  match ce with
  | C.Seq
      {
        C.exp_seq_type = t;
        C.exp_seq_exp1 = ce1;
        C.exp_seq_exp2 = ce2;
        C.exp_seq_pos = pos
      } ->
      let new_ce2 = insert_dummy_vars ce2 pos
      in
        C.Seq
          {
            C.exp_seq_type = t;
            C.exp_seq_exp1 = ce1;
            C.exp_seq_exp2 = new_ce2;
            C.exp_seq_pos = pos;
          }
  | _ ->
      (match C.type_of_exp ce with
       | None -> ce
       | Some t ->
           if CP.are_same_types t C.void_type
           then ce
           else
             (let fn = fresh_var_name (Cprinter.string_of_typ t) pos.Lexing.pos_lnum in
              let fn_decl =
                C.VarDecl
                  {
                    C.exp_var_decl_type = t;
                    C.exp_var_decl_name = fn;
                    C.exp_var_decl_pos = pos;
                  } in
              let assign_e =
                C.Assign
                  {
                    C.exp_assign_lhs = fn;
                    C.exp_assign_rhs = ce;
                    C.exp_assign_pos = pos;
                  } in
              let local_vars = [ (t, fn) ] in
              let seq =
                C.Seq
                  {
                    C.exp_seq_type = C.void_type;
                    C.exp_seq_exp1 = fn_decl;
                    C.exp_seq_exp2 = assign_e;
                    C.exp_seq_pos = pos;
                  } in
              let block_e =
                C.Block
                  {
                    C.exp_block_type = C.void_type;
                    C.exp_block_body = seq;
                    C.exp_block_local_vars = local_vars;
                    C.exp_block_pos = pos;
                  }
              in block_e))


and trans_specs (prog : I.prog_decl) (tshp:((ident*primed)list)*((ident*primed)list))(f : Iast.multi_spec) stab (cret_type:CP.typ) : Cast.multi_spec*((ident*primed) list) =
	
	 let helper2 (ve, pe) stab pos =
							try
			         let ve_info = H.find stab ve
			         in
			           (match ve_info.sv_info_kind with
			            | Known t -> CP.SpecVar (t, ve, pe)
			            | Unknown ->
			                Err.report_error
			                  {
			                    Err.error_loc = pos;
			                    Err.error_text = "couldn't infer type for " ^ ve;
			                  })
							with Not_found ->   
								Err.report_error
			                  {
			                    Err.error_loc =  pos;
			                    Err.error_text = "couldn't infer type for " ^ ve^", could it be an unused var?";
			                  }			
						 in
	
	let rec trans_spec_h (fvars : ident list)(pre_fv: ident list)(f0 : Iast.multi_spec) : Cast.multi_spec =
	
	let rec trans_spec (fvars: ident list)(pre_fv:ident list)(f0:Iast.spec):Cast.spec = match f0 with
			| Iast.SCase b-> 				
				Cast.SCase ({	
					Cast.scase_branches = List.map (fun (c1,c2)->
						let rm = arith_simplify (trans_pure_formula c1 stab)in
						let pre_fv  = pre_fv @(List.map Cpure.name_of_spec_var (Cpure.fv rm)) in
						(rm,(trans_spec_h fvars pre_fv c2))) b.Iast.scase_branches ;
					Cast.scase_pos = b.Iast.scase_pos })				
			| Iast.SRequires b->			
					let nb = trans_formula prog  b.Iast.srequires_base stab in
					let ex_inst = List.map (fun qv -> helper2 qv stab  b.Iast.srequires_pos) b.Iast.srequires_explicit_inst in 
					let ex_imp =  List.map (fun qv -> helper2 qv stab  b.Iast.srequires_pos) b.Iast.srequires_implicit_inst in
					Cast.SRequires({
							Cast.srequires_explicit_inst = ex_inst;
							Cast.srequires_implicit_inst = ex_imp;
							Cast.srequires_base = nb;
							Cast.srequires_continuation = trans_spec_h (fvars@(List.map Cpure.name_of_spec_var (Cformula.fv nb))@pre_fv) [] b.Iast.srequires_continuation ;
							Cast.srequires_pos = b.Iast.srequires_pos		
						})
			| Iast.SEnsure b-> 
				(*add res, self*)
				 let _ = H.add stab res { sv_info_kind = Known cret_type; } in
				  let nb = trans_formula prog true (self::res::(fvars@pre_fv)) b.Iast.sensures_base stab in				
				 let _ = H.remove stab res in
				Cast.SEnsure ({
						Cast.sensures_base = nb ;
						Cast.sensures_pos = b.Iast.sensures_pos
		})	in
		List.map (trans_spec fvars pre_fv) f0
	in

		let f = Iast.rename_bound_vars_specs f in	
		let f = Iast.float_out_exps_from_heap_spec f in
		let f,tshp = Iast.normalize_spec tshp f in
		let r = trans_spec_h fvars [] f in
		let cfvhp	= List.map (fun c-> helper2 c stab no_pos) (fst tshp) in
		let _ = spec_case_coverage cfvhp r in
		let tmp_vars  =  (Cast.spec_post_fv r) in 
		let post_fv = List.map CP.name_of_spec_var tmp_vars in
		let pre_fv = List.map CP.name_of_spec_var (Util.difference (Cast.spec_fv r) tmp_vars) in
	   if (List.mem self pre_fv) || (List.mem self post_fv)
                 then
                   Err.report_error
                     {
                       Err.error_loc = Cast.pos_of_specs r;
                       Err.error_text =
                         "self is not allowed in pre/postcondition";
                     }
                 else
                   if List.mem res pre_fv
                   then
                     Err.report_error
                       {
                         Err.error_loc = Cast.pos_of_specs r;
                         Err.error_text =
                           "res is not allowed in precondition";
                       }
                   else
                     (try
                        let resinfo = H.find stab res
                        in
                          match resinfo.sv_info_kind with
                          | Known t ->
                              if sub_type t cret_type
                              then (r,tshp)
                              else
                                Err.report_error
                                  {
                                    Err.error_loc = Cast.pos_of_specs r;
                                    Err.error_text =
                                      "res is used inconsistently";
                                  }
                          | Unknown ->
                              Err.report_error
                                {
                                  Err.error_loc = Cast.pos_of_specs r;
                                  Err.error_text = "can't infer type for res";
                                }
                      with | Not_found -> (r,tshp))
	 
and spec_case_coverage (instant:Cpure.spec_var list)(fb:Cast.multi_spec): bool =
	let rec ext_case_coverage (instant:Cpure.spec_var list)(f1:Cast.spec):bool = match f1 with
		| Cast.SRequires b-> spec_case_coverage (instant@(b.Cast.srequires_explicit_inst)@(b.Cast.srequires_implicit_inst)) b.Cast.srequires_continuation
		| Cast.SEnsure b-> true
		| Cast.SCase b->
			let r1,r2 = List.split b.Cast.scase_branches in
			let all = List.fold_left (fun a c->(Cpure.mkOr a c no_pos) ) (Cpure.mkFalse b.Cast.scase_pos) r1  in
			let _ = if not(Util.subset (Cpure.fv all) instant) then Error.report_error {  Err.error_loc = b.Cast.scase_pos;
                    	Err.error_text = "all guard free vars must be instantiated";} in
			let _ = if (Tpdispatcher.is_sat(Cpure.Not (all,no_pos))) then Error.report_error {  Err.error_loc = b.Cast.scase_pos;
                    	Err.error_text = "the guards don't cover the whole domain";} 	in
											
			let rec p_check (p:Cpure.formula list):bool = match p with
				| [] -> false 
				| p1::p2 -> if (List.fold_left (fun a c-> a ||(Tpdispatcher.is_sat(Cpure.mkAnd p1 c no_pos))) false p2 ) then true else p_check p2 in
			
			let _ = if (p_check r1) then Error.report_error {  Err.error_loc = b.Cast.scase_pos;
                    	Err.error_text = "the guards are not disjoint";} in
											
											
			let _ = List.map (spec_case_coverage instant) r2 in true	in
	let _ = List.map (ext_case_coverage instant) fb in true


and case_coverage (instant:Cpure.spec_var list)(f:Cformula.struc_formula): bool =
	let rec ext_case_coverage (instant:Cpure.spec_var list)(f1:Cformula.ext_formula):bool = match f1 with
		| Cformula.EBase b -> case_coverage (instant@(b.Cformula.formula_ext_explicit_inst)@(b.Cformula.formula_ext_implicit_inst))b.Cformula.formula_ext_continuation
		| Cformula.ECase b -> 
			let r1,r2 = List.split b.Cformula.formula_case_branches in
			let all = List.fold_left (fun a c->(Cpure.mkOr a c no_pos) ) (Cpure.mkFalse b.Cformula.formula_case_pos) r1  in
			let _ = if not(Util.subset (Cpure.fv all) instant) then Error.report_error {  Err.error_loc = b.Cformula.formula_case_pos;
                    	Err.error_text = "all guard free vars must be instantiated";} in
			let _ = if (Tpdispatcher.is_sat(Cpure.Not (all,no_pos))) then Error.report_error {  Err.error_loc = b.Cformula.formula_case_pos;
                    	Err.error_text = "the guards don't cover the whole domain";} 	in
											
			let rec p_check (p:Cpure.formula list):bool = match p with
				| [] -> false 
				| p1::p2 -> if (List.fold_left (fun a c-> a ||(Tpdispatcher.is_sat(Cpure.mkAnd p1 c no_pos))) false p2 ) then true else p_check p2 in
				
			let _ = if (p_check r1) then Error.report_error {  Err.error_loc = b.Cformula.formula_case_pos;
                    	Err.error_text = "the guards are not disjoint";} in
											
			let _ = List.map (case_coverage instant) r2 in true	in
	let _ = List.map (ext_case_coverage instant) f in true


and trans_struc_formula (prog : I.prog_decl) (quantify : bool) (hp:((ident*primed)list * (ident*primed)list))(f0 : IF.struc_formula) stab : CF.struc_formula = 
	 
	let trans_var (ve, pe) = try let ve_info = H.find stab ve in
           (match ve_info.sv_info_kind with
            | Known t -> CP.SpecVar (t, ve, pe)
            | Unknown ->Err.report_error{Err.error_loc = no_pos;Err.error_text = "couldn't infer type for " ^ ve;})
				with Not_found ->   
					Err.report_error{Err.error_loc = no_pos;Err.error_text = "couldn't infer type for " ^ ve^", could it be an unused var?";}in

	let rec trans_struc_formula_hlp (hp:((ident*primed)list * (ident*primed)list)) (f0 : IF.struc_formula) :CF.struc_formula = 
	let rec trans_ext_formula (hp:((ident*primed)list * (ident*primed)list)) (f0 : IF.ext_formula) stab : CF.ext_formula = match f0 with
		| Iformula.ECase b-> 	
			Cformula.ECase {
				Cformula.formula_case_branches = List.map (fun (c1,c2)-> ((arith_simplify (trans_pure_formula c1 stab)),(trans_struc_formula_hlp c2)))
					 b.Iformula.formula_case_branches;
				Cformula.formula_case_pos = b.Iformula.formula_case_pos}			
		| Iformula.EBase b-> 			
			let nc = trans_struc_formula_hlp b.Iformula.formula_ext_continuation in
			let nb = trans_formula prog b.Iformula.formula_ext_base stab in
			let ex_inst = List.map trans_var b.Iformula.formula_ext_explicit_inst in
			let ext_impl = List.map trans_var b.Iformula.formula_ext_implicit_inst in
			Cformula.EBase {
			Cformula.formula_ext_explicit_inst = ex_inst;
		 	Cformula.formula_ext_implicit_inst = ext_impl;
		 	Cformula.formula_ext_base = nb;
		 	Cformula.formula_ext_continuation = nc;
		 	Cformula.formula_ext_pos = b.Iformula.formula_ext_pos} in
		let r = List.map (fun c-> trans_ext_formula hp c stab) f0 in
		r in
		let f0 = Iformula.rename_bound_vars_struc f0 in
		let f0 = Iformula.float_out_exps_from_heap_struc f0 in
		let f0,_ = Iformula.normalize_struc hp f0 in
		let r = trans_struc_formula_hlp (fst hp) f0 in
		let cfvhp = List.map trans_var (fst hp) in
		let _ = case_coverage cfvhp r in
		r
		
		
and trans_formula (prog : I.prog_decl) (f0 : IF.formula) stab : CF.formula =
  let f3 = convert_heap2 prog f0 in
  let f1 = float_out_min_max f3 in
		trans_formula1 prog f1 stab 


and trans_formula1 prog f0 stab : CF.formula =
  match f0 with
  | IF.Or
      { IF.formula_or_f1 = f1; IF.formula_or_f2 = f2; IF.formula_or_pos = pos
      } ->
      let tf1 = trans_formula1 prog f1 stab in
      let tf2 = trans_formula1 prog f2 stab
      in CF.mkOr tf1 tf2 pos
  | IF.Base
      {
        IF.formula_base_heap = h;
        IF.formula_base_pure = p;
        IF.formula_base_pos = pos
      } ->
      (collect_type_info_pure p stab;
       collect_type_info_heap prog h stab;
       let ch = linearize_formula prog f0 stab
       in
         (if quantify
          then
            (let tmp_stab = H.create 103
             in
               (U.copy_keys fvars stab tmp_stab;
                H.clear stab;
                U.copy_keys fvars tmp_stab stab))
          else ();
          ch))
  | IF.Exists
      {
        IF.formula_exists_qvars = qvars;
        IF.formula_exists_heap = h;
        IF.formula_exists_pure = p;
        IF.formula_exists_pos = pos
      } ->
      (collect_type_info_pure p stab;
       collect_type_info_heap prog h stab;
       let helper1 (ve, pe) stab =
				try
         let ve_info = H.find stab ve
         in
           (match ve_info.sv_info_kind with
            | Known t -> CP.SpecVar (t, ve, pe)
            | Unknown ->
                Err.report_error
                  {
                    Err.error_loc = pos;
                    Err.error_text = "couldn't infer type for " ^ ve;
                  })
				with Not_found ->   
					Err.report_error
                  {
                    Err.error_loc = pos;
                    Err.error_text = "couldn't infer type for " ^ ve^", could it be an unused var?";
                  }			
			 in
       let f1 =
         IF.Base
           {
             IF.formula_base_heap = h;
             IF.formula_base_pure = p;
             IF.formula_base_pos = pos;
           } in
       let ch = linearize_formula prog quantify fvars f1 stab in
       let qsvars = List.map (fun qv -> helper1 qv stab) qvars in
       let ch = CF.push_exists qsvars ch in
         (if quantify
          then
            (let tmp_stab = H.create 103 in
             let fvars = (List.map fst qvars) @ fvars
             in
               (U.copy_keys fvars stab tmp_stab;
                H.clear stab;
                U.copy_keys fvars tmp_stab stab))
          else ();
          ch))
and
  linearize_formula (prog : I.prog_decl) (quantify : bool)
                    (fvars : ident list) (f0 : IF.formula)
                    (stab : spec_var_table) =
  let rec match_exp (used_names : ident list) (hargs : IP.exp list) pos :
    ((ident list) * (CP.spec_var list) * (CP.spec_var list) * CP.formula) =
    match hargs with
    | e :: rest ->
        let (new_used_names, e_hvars, e_evars, e_link) =
          (match e with
           | IP.Var ((ve, pe), pos_e) ->
               (try
                  let ve_info = H.find stab ve in
                  let ve_sv =
                    match ve_info.sv_info_kind with
                    | Known t -> CP.SpecVar (t, ve, pe)
                    | Unknown ->
                        Err.report_error
                          {
                            Err.error_loc = pos_e;
                            Err.error_text = "couldn't infer type for " ^ ve;
                          }
                  in
                    if (List.mem ve fvars) || (List.mem ve used_names)
                    then
                      (let fresh_v = CP.fresh_spec_var ve_sv in
                       let link_f =
                         CP.mkEqExp (CP.mkVar fresh_v pos_e)
                           (CP.mkVar ve_sv pos_e) pos_e in
                       let quantified_var = [ fresh_v ]
                       in (used_names, [ fresh_v ], quantified_var, link_f))
                    else
                      (let quantified_var =
                         if quantify then [ ve_sv ] else []
                       in
                         ((ve :: used_names), [ ve_sv ], quantified_var,
                          (CP.mkTrue pos_e)))
                with
                | Not_found ->
                    Err.report_error
                      {
                        Err.error_loc = pos_e;
                        Err.error_text = ve ^ " is undefined";
                      })
           | _ ->
               let pos_e = IP.pos_of_exp e in
               let fresh_type =
                 if IP.is_null e
                 then CP.OType ""
                 else if IP.is_bag e then C.bag_type else C.int_type in
							 let fresh_n = fresh_var_name (Cprinter.string_of_typ fresh_type) pos_e.Lexing.pos_lnum in
               let fresh_v = CP.SpecVar (fresh_type, fresh_n, Unprimed) in
               let link_f =
                 CP.mkEqExp (CP.mkVar fresh_v pos_e) (trans_pure_exp e stab)
                   pos_e in
               let quantified_var = [ fresh_v ]
               in (used_names, [ fresh_v ], quantified_var, link_f)) in
        let (rest_used_names, rest_hvars, rest_evars, rest_link) =
          match_exp new_used_names rest pos in
        let hvars = e_hvars @ rest_hvars in
        let evars = e_evars @ rest_evars in
        let link_f = CP.mkAnd e_link rest_link pos
        in (rest_used_names, hvars, evars, link_f)
    | [] -> (used_names, [], [], (CP.mkTrue pos)) in
  let rec linearize_heap used_names (f : IF.h_formula) pos :
    ((ident list) * (CP.spec_var list) * CF.h_formula * CP.formula * CF.
     t_formula) =
    match f with
    | IF.HeapNode2 h2 ->
        let h = node2_to_node prog h2 in
        let fh = IF.HeapNode h in linearize_heap used_names fh pos
    | IF.HeapNode
        {
          IF.h_formula_heap_node = (v, p);
          IF.h_formula_heap_name = c;
          IF.h_formula_heap_arguments = exps;
          IF.h_formula_heap_full = full;
          IF.h_formula_heap_pos = pos
        } ->
        (try
           let vdef = I.look_up_view_def_raw prog.I.prog_view_decls c in
           let (new_used_names, hvars, evars, link_f) =
             match_exp used_names exps pos in
           let c0 =
             if vdef.I.view_data_name = ""
             then (let _ = trans_view prog vdef in vdef.I.view_data_name)
             else vdef.I.view_data_name in
           let new_v = CP.SpecVar (CP.OType c0, v, p) in
           let new_h =
             CF.ViewNode
               {
                 CF.h_formula_view_node = new_v;
                 CF.h_formula_view_name = c;
                 CF.h_formula_view_arguments = hvars;
                 CF.h_formula_view_modes = vdef.I.view_modes;
                 CF.h_formula_view_coercible = true;
                 CF.h_formula_view_origins = [];
                 CF.h_formula_view_pos = pos;
               }
           in (new_used_names, evars, new_h, link_f, CF.TypeTrue)
         with
         | Not_found ->
             let (new_used_names, hvars, evars, link_f_prim) =
               match_exp used_names exps pos in
             let new_v = CP.SpecVar (CP.OType c, v, p) in
             let link_f = link_f_prim in
             let new_h =
               CF.DataNode
                 {
                   CF.h_formula_data_node = new_v;
                   CF.h_formula_data_name = c;
                   CF.h_formula_data_arguments = hvars;
                   CF.h_formula_data_pos = pos;
                 }
             in (new_used_names, evars, new_h, link_f, CF.TypeTrue))
    | IF.Star
        {
          IF.h_formula_star_h1 = f1;
          IF.h_formula_star_h2 = f2;
          IF.h_formula_star_pos = pos
        } ->
        let (new_used_names1, qv1, lf1, link1, type1) =
          linearize_heap used_names f1 pos in
        let (new_used_names2, qv2, lf2, link2, type2) =
          linearize_heap new_used_names1 f2 pos in
        let tmp_h = CF.mkStarH lf1 lf2 pos in
        let tmp_link = CP.mkAnd link1 link2 pos in
        let tmp_type = CF.mkAndType type1 type2
        in (new_used_names2, (qv1 @ qv2), tmp_h, tmp_link, tmp_type)
    | IF.HTrue -> (used_names, [], CF.HTrue, (CP.mkTrue pos), CF.TypeTrue)
    | IF.HFalse -> (used_names, [], CF.HFalse, (CP.mkTrue pos), CF.TypeFalse) in
  let linearize_base used_names base =
    let h = base.IF.formula_base_heap in
    let p = base.IF.formula_base_pure in
    let pos = base.IF.formula_base_pos in
    let (_, h_evars, new_h, link_f, type_f) =
      linearize_heap used_names h pos in
    let cp = trans_pure_formula p stab in
    let new_p = CP.mkAnd cp link_f pos in
	(* let _ = print_string ("pre: "^(Cprinter.string_of_pure_formula        *)
	(* new_p)^"\n") in                                                       *)
    let new_p = arith_simplify new_p in
		(* let _ = print_string ("post: "^(Cprinter.string_of_pure_formula     *)
		(* new_p)^"\n") in   *)
    let tmp_evars4 =
      if quantify
      then
        (let tmp_evars1 = CP.fv new_p in
         let excluded_evars = fvars in
         let tmp_evars2 =
           List.filter
             (function
              | CP.SpecVar (_, v, _) -> not (List.mem v excluded_evars))
             tmp_evars1 in
         let tmp_evars3 = U.remove_dups (h_evars @ tmp_evars2) in tmp_evars3)
      else h_evars in
    let tmp_evars =
      List.filter (function | CP.SpecVar (_, v, _) -> ( != ) v self)
        tmp_evars4 in
    let result = CF.mkExists tmp_evars new_h new_p type_f pos
    in
      (if not (Util.empty tmp_evars)
       then
         Debug.pprint
           ("linearize_constraint: " ^
              ((String.concat ", "
                  (List.map Cprinter.string_of_spec_var tmp_evars))
                 ^ " are quantified\n"))
           pos
       else ();
       result)
  in
    match f0 with
    | IF.Or
        {
          IF.formula_or_f1 = f1;
          IF.formula_or_f2 = f2;
          IF.formula_or_pos = pos
        } ->
        let lf1 = linearize_formula prog quantify fvars f1 stab in
        let lf2 = linearize_formula prog quantify fvars f2 stab in
        let result = CF.mkOr lf1 lf2 pos in result
    | IF.Base base -> linearize_base [] base
    | IF.Exists
        {
          IF.formula_exists_heap = h;
          IF.formula_exists_pure = p;
          IF.formula_exists_pos = pos
        } ->
        let base =
          {
            IF.formula_base_heap = h;
            IF.formula_base_pure = p;
            IF.formula_base_pos = pos;
          }
        in linearize_base [] base

and trans_pure_formula (f0 : IP.formula) stab : CP.formula =
  match f0 with
  | IP.BForm bf -> CP.BForm (trans_pure_b_formula bf stab)
  | IP.And (f1, f2, pos) ->
      let pf1 = trans_pure_formula f1 stab in
      let pf2 = trans_pure_formula f2 stab in CP.mkAnd pf1 pf2 pos
  | IP.Or (f1, f2, pos) ->
      let pf1 = trans_pure_formula f1 stab in
      let pf2 = trans_pure_formula f2 stab in CP.mkOr pf1 pf2 pos
  | IP.Not (f, pos) -> let pf = trans_pure_formula f stab in CP.mkNot pf pos
  | IP.Forall ((v, p), f, pos) ->
      let pf = trans_pure_formula f stab in
      let v_type =
				try 
        let v_info = H.find stab v
        in
          (match v_info.sv_info_kind with
           | Known t -> t
           | Unknown ->
               Err.report_error
                 {
                   Err.error_loc = pos;
                   Err.error_text = "couldn't infer type for " ^ v;
                 })
				with Not_found -> Err.report_error
                 {
                   Err.error_loc = pos;
                   Err.error_text = "couldn't infer type for " ^ v;
                 } in
      let sv = CP.SpecVar (v_type, v, p) in CP.mkForall [ sv ] pf pos
  | IP.Exists ((v, p), f, pos) ->
      let pf = trans_pure_formula f stab in
      let v_type =
				try
        let v_info = H.find stab v
        in
          (match v_info.sv_info_kind with
           | Known t -> t
           | Unknown ->
               Err.report_error
                 {
                   Err.error_loc = pos;
                   Err.error_text = "couldn't infer type for " ^ v;
                 })
				with Not_found ->  
					Err.report_error
                 {
                   Err.error_loc = pos;
                   Err.error_text = "couldn't infer type for " ^ v;
                 } in
      let sv = CP.SpecVar (v_type, v, p) in CP.mkExists [ sv ] pf pos

and trans_pure_b_formula (b0 : IP.b_formula) stab : CP.b_formula =
  match b0 with
  | IP.BConst (b, pos) -> CP.BConst (b, pos)
  | IP.BVar ((v, p), pos) -> CP.BVar (CP.SpecVar (C.bool_type, v, p), pos)
  | IP.Lt (e1, e2, pos) ->
      let pe1 = trans_pure_exp e1 stab in
      let pe2 = trans_pure_exp e2 stab in CP.mkLt pe1 pe2 pos
  | IP.Lte (e1, e2, pos) ->
      let pe1 = trans_pure_exp e1 stab in
      let pe2 = trans_pure_exp e2 stab in CP.mkLte pe1 pe2 pos
  | IP.Gt (e1, e2, pos) ->
      let pe1 = trans_pure_exp e1 stab in
      let pe2 = trans_pure_exp e2 stab in CP.mkGt pe1 pe2 pos
  | IP.Gte (e1, e2, pos) ->
      let pe1 = trans_pure_exp e1 stab in
      let pe2 = trans_pure_exp e2 stab in CP.mkGte pe1 pe2 pos
  | IP.Eq (e1, e2, pos) ->
      let pe1 = trans_pure_exp e1 stab in
      let pe2 = trans_pure_exp e2 stab in CP.mkEq pe1 pe2 pos
  | IP.Neq (e1, e2, pos) ->
      let pe1 = trans_pure_exp e1 stab in
      let pe2 = trans_pure_exp e2 stab in CP.mkNeq pe1 pe2 pos
  | IP.EqMax (e1, e2, e3, pos) ->
      let pe1 = trans_pure_exp e1 stab in
      let pe2 = trans_pure_exp e2 stab in
      let pe3 = trans_pure_exp e3 stab in CP.EqMax (pe1, pe2, pe3, pos)
  | IP.EqMin (e1, e2, e3, pos) ->
      let pe1 = trans_pure_exp e1 stab in
      let pe2 = trans_pure_exp e2 stab in
      let pe3 = trans_pure_exp e3 stab in CP.EqMin (pe1, pe2, pe3, pos)
  | IP.BagIn ((v, p), e, pos) ->
      let pe = trans_pure_exp e stab
      in
        (try
           let v_info = H.find stab v
           in
             match v_info.sv_info_kind with
             | Known t ->
                 let sv = CP.SpecVar (t, v, p) in CP.BagIn (sv, pe, pos)
             | Unknown ->
                 Err.report_error
                   {
                     Err.error_loc = pos;
                     Err.error_text = "couldn't infer type for " ^ v;
                   }
         with
         | Not_found ->
             Err.report_error
               { Err.error_loc = pos; Err.error_text = v ^ " is undefined"; })
  | IP.BagNotIn ((v, p), e, pos) ->
      let pe = trans_pure_exp e stab
      in
        (try
           let v_info = H.find stab v
           in
             match v_info.sv_info_kind with
             | Known t ->
                 let sv = CP.SpecVar (t, v, p) in CP.BagNotIn (sv, pe, pos)
             | Unknown ->
                 Err.report_error
                   {
                     Err.error_loc = pos;
                     Err.error_text = "couldn't infer type for " ^ v;
                   }
         with
         | Not_found ->
             Err.report_error
               { Err.error_loc = pos; Err.error_text = v ^ " is undefined"; })
  | IP.BagSub (e1, e2, pos) ->
      let pe1 = trans_pure_exp e1 stab in
      let pe2 = trans_pure_exp e2 stab in CP.BagSub (pe1, pe2, pos)
  | IP.BagMax ((v1, p1), (v2, p2), pos) ->
      CP.BagMax (CP.SpecVar (C.int_type, v1, p1),
        CP.SpecVar (C.bag_type, v2, p2), pos)
  | IP.BagMin ((v1, p1), (v2, p2), pos) ->
      CP.BagMin (CP.SpecVar (C.int_type, v1, p1),
        CP.SpecVar (C.bag_type, v2, p2), pos)

and trans_pure_exp (e0 : IP.exp) stab : CP.exp =
  match e0 with
  | IP.Null pos -> CP.Null pos
  | IP.Var ((v, p), pos) ->
      (try
         let v_info = H.find stab v
         in
           match v_info.sv_info_kind with
           | Known t -> let sv = CP.SpecVar (t, v, p) in CP.Var (sv, pos)
           | Unknown ->
               let sv = CP.SpecVar (CP.OType "", v, p) in CP.Var (sv, pos)
       with
       | Not_found ->
           let sv = CP.SpecVar (CP.OType "", v, p) in CP.Var (sv, pos))
  | IP.IConst (c, pos) -> CP.IConst (c, pos)
  | IP.Add (e1, e2, pos) ->
      CP.Add (trans_pure_exp e1 stab, trans_pure_exp e2 stab, pos)
  | IP.Subtract (e1, e2, pos) ->
      CP.Subtract (trans_pure_exp e1 stab, trans_pure_exp e2 stab, pos)
  | IP.Mult (c, e, pos) -> CP.Mult (c, trans_pure_exp e stab, pos)
  | IP.Max (e1, e2, pos) ->
      CP.Max (trans_pure_exp e1 stab, trans_pure_exp e2 stab, pos)
  | IP.Min (e1, e2, pos) ->
      CP.Min (trans_pure_exp e1 stab, trans_pure_exp e2 stab, pos)
  | IP.Bag (elist, pos) -> CP.Bag (trans_pure_exp_list elist stab, pos)
  | IP.BagUnion (elist, pos) ->
      CP.BagUnion (trans_pure_exp_list elist stab, pos)
  | IP.BagIntersect (elist, pos) ->
      CP.BagIntersect (trans_pure_exp_list elist stab, pos)
  | IP.BagDiff (e1, e2, pos) ->
      CP.BagDiff (trans_pure_exp e1 stab, trans_pure_exp e2 stab, pos)

and trans_pure_exp_list (elist : IP.exp list) stab : CP.exp list =
  match elist with
  | [] -> []
  | e :: rest -> (trans_pure_exp e stab) :: (trans_pure_exp_list rest stab)

and unify_var_kind (k1 : spec_var_kind) (k2 : spec_var_kind) :
  spec_var_kind option =
  match k1 with
  | Unknown -> Some k2
  | Known t1 ->
      (match k2 with
       | Unknown -> Some k1
       | Known t2 ->
           (match t1 with
            | CP.Prim _ -> if t1 = t2 then Some k1 else None
            | CP.OType c1 ->
                (match t2 with
                 | CP.Prim _ -> None
                 | CP.OType c2 ->
                     if c1 = ""
                     then Some k2
                     else
                       if c2 = ""
                       then Some k1
                       else
                         if c1 = c2
                         then Some k1
                         else
                           if sub_type t1 t2
                           then Some k1
                           else if sub_type t2 t1 then Some k2 else None)))

and get_var_kind (var : ident) (stab : spec_var_table) =
  try let r = H.find stab var in r.sv_info_kind with | Not_found -> Unknown

and set_var_kind (var : ident) (k : spec_var_kind) (stab : spec_var_table) =
  try let r = H.find stab var in (r.sv_info_kind <- k; r)
  with | Not_found -> (H.add stab var { sv_info_kind = k; }; H.find stab var)

and collect_type_info_var (var : ident) stab (var_kind : spec_var_kind) pos =
  try
    let k = H.find stab var in
    let tmp = unify_var_kind k.sv_info_kind var_kind
    in
      match tmp with
      | Some tmp_k -> k.sv_info_kind <- tmp_k
      | None -> report_error pos (var ^ " is used inconsistently")
  with | Not_found -> H.add stab var { sv_info_kind = var_kind; }

and collect_type_info_pure (p0 : IP.formula) (stab : spec_var_table) : unit =
  match p0 with
  | IP.BForm b -> collect_type_info_b_formula b stab
  | IP.And (p1, p2, pos) | IP.Or (p1, p2, pos) ->
      (collect_type_info_pure p1 stab; collect_type_info_pure p2 stab)
  | IP.Not (p1, pos) -> collect_type_info_pure p1 stab
  | IP.Forall ((qv, qp), qf, pos) | IP.Exists ((qv, qp), qf, pos) ->
      if H.mem stab qv
      then
        Err.report_error
          {
            Err.error_loc = pos;
            Err.error_text = qv ^ " shallows outer name";
          }
      else collect_type_info_pure qf stab

and collect_type_info_b_formula b0 stab =
  match b0 with
  | IP.BConst _ -> ()
  | IP.BVar ((bv, bp), pos) ->
      collect_type_info_var bv stab (Known C.bool_type) pos
  | IP.Lt (a1, a2, pos) | IP.Lte (a1, a2, pos) | IP.Gt (a1, a2, pos) |
      IP.Gte (a1, a2, pos) ->
      (collect_type_info_arith a1 stab; collect_type_info_arith a2 stab)
  | IP.EqMin (a1, a2, a3, pos) | IP.EqMax (a1, a2, a3, pos) ->
      (collect_type_info_arith a1 stab;
       collect_type_info_arith a2 stab;
       collect_type_info_arith a2 stab)
  | IP.BagIn ((v, p), e, pos) ->
      (collect_type_info_var v stab Unknown pos;
       collect_type_info_bag e stab)
  | IP.BagNotIn ((v, p), e, pos) ->
      (collect_type_info_var v stab Unknown pos;
       collect_type_info_bag e stab)
  | IP.BagSub (e1, e2, pos) ->
      (collect_type_info_bag e1 stab; collect_type_info_bag e2 stab)
  | IP.BagMax ((v1, p1), (v2, p2), pos) ->
      (collect_type_info_var v1 stab (Known C.int_type) pos;
       collect_type_info_var v2 stab (Known C.bag_type) pos)
  | IP.BagMin ((v1, p1), (v2, p2), pos) ->
      (collect_type_info_var v1 stab (Known C.int_type) pos;
       collect_type_info_var v2 stab (Known C.bag_type) pos)
  | IP.Eq (a1, a2, pos) | IP.Neq (a1, a2, pos) ->
      if (IP.is_var a1) && (IP.is_var a2)
      then
        (let va1 = IP.name_of_var a1 in
         let va2 = IP.name_of_var a2 in
         let k1 = get_var_kind va1 stab in
         let k2 = get_var_kind va2 stab in
         let r = unify_var_kind k1 k2
         in
           match r with
           | Some k ->
               let r = set_var_kind va1 k stab in H.replace stab va2 r
           | None ->
               (print_stab stab;
                Err.report_error
                  {
                    Err.error_loc = pos;
                    Err.error_text =
                      "type-mismatch in equation (1): " ^
                        (Iprinter.string_of_b_formula b0);
                  }))
      else
        if (IP.is_var a1) || (IP.is_var a2)
        then
          (let (a1', a2') = if IP.is_var a1 then (a1, a2) else (a2, a1) in
           let va1' = IP.name_of_var a1' in
           let k1 = get_var_kind va1' stab in
           let (k2, _) =
             if IP.is_null a2'
             then
               ((Known (CP.OType "")),
                (collect_type_info_pointer a2' (Known (CP.OType "")) stab))
             else
               if IP.is_bag a2'
               then ((Known C.bag_type), (collect_type_info_bag a2' stab))
               else ((Known C.int_type), (collect_type_info_arith a2' stab)) in
           let r = unify_var_kind k1 k2
           in
             match r with
             | Some k -> ignore (set_var_kind va1' k stab)
             | None ->
                 Err.report_error
                   {
                     Err.error_loc = pos;
                     Err.error_text =
                       "type-mismatch in equation (2): " ^
                         (Iprinter.string_of_b_formula b0);
                   })
        else
          if (IP.is_null a1) && (IP.is_null a2)
          then ()
          else
            if (not (IP.is_null a1)) && (not (IP.is_null a2))
            then
              if (IP.is_bag a1) && (IP.is_bag a2)
              then
                (collect_type_info_bag a1 stab;
                 collect_type_info_bag a2 stab)
              else
                (collect_type_info_arith a1 stab;
                 collect_type_info_arith a2 stab)
            else
              Err.report_error
                {
                  Err.error_loc = pos;
                  Err.error_text =
                    "type-mismatch in equation (3): " ^
                      (Iprinter.string_of_b_formula b0);
                }

and collect_type_info_arith a0 stab =
  match a0 with
  | IP.Null pos ->
      Err.report_error
        {
          Err.error_loc = pos;
          Err.error_text = "null is not allowed in arithmetic term";
        }
  | IP.Var ((sv, sp), pos) ->
      collect_type_info_var sv stab (Known C.int_type) pos
  | IP.IConst _ -> ()
  | IP.Add (a1, a2, pos) | IP.Subtract (a1, a2, pos) | IP.Max (a1, a2, pos) |
      IP.Min (a1, a2, pos) ->
      (collect_type_info_arith a1 stab; collect_type_info_arith a2 stab)
  | IP.Mult (c, a1, pos) -> collect_type_info_arith a1 stab
  | IP.BagDiff _ | IP.BagIntersect _ | IP.BagUnion _ | IP.Bag _ ->
      failwith "collect_type_info_arith: encountered bag constraint"

and collect_type_info_bag_content a0 stab =
  match a0 with
  | IP.Null pos ->
      Err.report_error
        {
          Err.error_loc = pos;
          Err.error_text = "null is not allowed in arithmetic term";
        }
  | IP.Var ((sv, sp), pos) -> collect_type_info_var sv stab Unknown pos
  | IP.IConst _ -> ()
  | IP.Add (a1, a2, pos) | IP.Subtract (a1, a2, pos) | IP.Max (a1, a2, pos) |
      IP.Min (a1, a2, pos) ->
      (collect_type_info_arith a1 stab; collect_type_info_arith a2 stab)
  | IP.Mult (c, a1, pos) -> collect_type_info_arith a1 stab
  | IP.BagDiff _ | IP.BagIntersect _ | IP.BagUnion _ | IP.Bag _ ->
      failwith "collect_type_info_arith: encountered bag constraint"

and collect_type_info_bag (e0 : IP.exp) stab =
  match e0 with
  | IP.Var ((sv, sp), pos) ->
      collect_type_info_var sv stab (Known C.bag_type) pos
  | IP.Bag ((a :: rest), pos) ->
      (collect_type_info_bag_content a stab;
       collect_type_info_bag (IP.Bag (rest, pos)) stab)
  | IP.Bag ([], pos) -> ()
  | IP.BagUnion ((a :: rest), pos) ->
      (collect_type_info_bag a stab;
       collect_type_info_bag (IP.BagUnion (rest, pos)) stab)
  | IP.BagUnion ([], pos) -> ()
  | IP.BagIntersect ((a :: rest), pos) ->
      (collect_type_info_bag a stab;
       collect_type_info_bag (IP.BagIntersect (rest, pos)) stab)
  | IP.BagIntersect ([], pos) -> ()
  | IP.BagDiff (a1, a2, pos) ->
      (collect_type_info_bag a1 stab; collect_type_info_bag a2 stab)
  | IP.Min _ | IP.Max _ | IP.Mult _ | IP.Subtract _ | IP.Add _ | IP.IConst _
      | IP.Null _ ->
      failwith "collect_type_info_bag: encountered arithmetic constraint"

and collect_type_info_pointer (e0 : IP.exp) (k : spec_var_kind) stab =
  match e0 with
  | IP.Null _ -> ()
  | IP.Var ((sv, sp), pos) -> collect_type_info_var sv stab k pos
  | _ ->
      Err.report_error
        {
          Err.error_loc = IP.pos_of_exp e0;
          Err.error_text = "arithmetic is not allowed in pointer term";
        }

and collect_type_info_heap prog (h0 : IF.h_formula) stab =
  match h0 with
  | IF.Star
      {
        IF.h_formula_star_h1 = h1;
        IF.h_formula_star_h2 = h2;
        IF.h_formula_star_pos = pos
      } ->
      (collect_type_info_heap prog h1 stab;
       collect_type_info_heap prog h2 stab)
  | IF.HeapNode2 h2 ->
      let h = node2_to_node prog h2 in
      let fh = IF.HeapNode h in collect_type_info_heap prog fh stab
  | IF.HeapNode
      {
        IF.h_formula_heap_node = (v, p);
        IF.h_formula_heap_name = c;
        IF.h_formula_heap_arguments = ies;
        IF.h_formula_heap_pos = pos
      } ->
      let dname =
        (try
           let vdef = I.look_up_view_def_raw prog.I.prog_view_decls c
           in
             (if not (U.empty vdef.I.view_typed_vars)
              then
                (let rec helper exps tvars =
                   match (exps, tvars) with
                   | ([], []) -> []
                   | (e :: rest1, t :: rest2) ->
                       let tmp = helper rest1 rest2
                       in
                         (match e with
                          | IP.Var ((v, p), pos) -> ((fst t), v) :: tmp
                          | _ -> tmp)
                   | _ ->
                       Err.report_error
                         {
                           Err.error_loc = pos;
                           Err.error_text =
                             "number of arguments for view " ^
                               (c ^ " does not match");
                         } in
                 let tmp = helper ies vdef.I.view_typed_vars
                 in
                   ignore
                     (List.map
                        (fun (t, n) ->
                           collect_type_info_var n stab (Known t) pos)
                        tmp))
              else ();
              vdef.I.view_data_name)
         with
         | Not_found ->
             (try
                (ignore (I.look_up_data_def_raw prog.I.prog_data_decls c); c)
              with
              | Not_found ->
                  Err.report_error
                    {
                      Err.error_loc = pos;
                      Err.error_text = c ^ " is neither a data nor view name";
                    })) in
      let check_ie st ie t =
        ((match t with
          | CP.Prim Bool ->
              if IP.is_var ie
              then
                collect_type_info_var (IP.name_of_var ie) st
                  (Known C.bool_type) (IP.pos_of_exp ie)
              else
                Err.report_error
                  {
                    Err.error_loc = IP.pos_of_exp ie;
                    Err.error_text = "expecting type bool";
                  }
          | CP.Prim Int -> collect_type_info_arith ie st
          | CP.Prim _ -> ()
          | CP.OType _ -> collect_type_info_pointer ie (Known t) st);
         st)
      in
        (if not (dname = "")
         then collect_type_info_var v stab (Known (CP.OType dname)) pos
         else ();
         (try
            let ddef = I.look_up_data_def_raw prog.I.prog_data_decls c in
            let fields = I.look_up_all_fields prog ddef
            in
              if (List.length ies) = (List.length fields)
              then
                (let typs =
                   List.map (fun f -> trans_type prog (fst (fst f)) pos)
                     fields in
                 let _ = List.fold_left2 check_ie stab ies typs in ())
              else
                Err.report_error
                  {
                    Err.error_loc = pos;
                    Err.error_text =
                      "number of arguments for data " ^
                        (c ^ " does not match");
                  }
          with
          | Not_found ->
              (try
                 let vdef = I.look_up_view_def_raw prog.I.prog_view_decls c
                 in
                   if (List.length ies) = (List.length vdef.I.view_vars)
                   then
                     (let mk_eq v ie =
                        let pos = IP.pos_of_exp ie
                        in IP.mkEqExp (IP.Var ((v, Unprimed), pos)) ie pos in
                      let all_eqns = List.map2 mk_eq vdef.I.view_vars ies in
                      let tmp_form =
                        List.fold_left (fun f1 f2 -> IP.mkAnd f1 f2 pos)
                          (IP.mkTrue pos) all_eqns
                      in collect_type_info_pure tmp_form stab)
                   else
                     Err.report_error
                       {
                         Err.error_loc = pos;
                         Err.error_text =
                           "number of arguments for view " ^
                             (c ^ " does not match");
                       }
               with
               | Not_found ->
                   report_error pos
                     (c ^ " is neither a view nor data declaration"))))
  | IF.HTrue | IF.HFalse -> ()

and get_spec_var_stab (v : ident) stab pos =
  try
    let v_info = H.find stab v
    in
      match v_info.sv_info_kind with
      | Known t -> let sv = CP.SpecVar (t, v, Unprimed) in sv
      | Unknown ->
          Err.report_error
            { Err.error_loc = pos; Err.error_text = v ^ " is undefined"; }
  with
  | Not_found ->
      Err.report_error
        { Err.error_loc = pos; Err.error_text = v ^ " is undefined"; }

and print_spec_var_kind (k : spec_var_kind) =
  match k with | Unknown -> "Unk" | Known t -> (Cprinter.string_of_typ t)^" "

and print_stab (stab : spec_var_table) =
  let p k i =
    print_string
      (k ^ (" --> " ^ ((print_spec_var_kind i.sv_info_kind) ^ "\n")))
  in (print_string "\n"; H.iter p stab; print_string "\n")

and simp_mult (e : Cpure.exp) : Cpure.exp =
  let rec normalize_add m lg (x : Cpure.exp) : Cpure.exp =
    match x with
    | Cpure.Add (e1, e2, l) ->
        let t1 = normalize_add m l e2 in normalize_add (Some t1) l e1
    | _ -> (match m with | None -> x | Some e -> Cpure.Add (e, x, lg)) in
  let rec acc_mult m e0 =
    match e0 with
    | Cpure.Null _ -> e0
    | Cpure.Var (v, l) ->
        let r = (match m with | None -> e0 | Some c -> Cpure.Mult (c, e0, l))
        in r
    | Cpure.IConst (v, l) ->
        let r =
          (match m with | None -> e0 | Some c -> Cpure.IConst (c * v, l))
        in r
    | Cpure.Add (e1, e2, l) ->
        normalize_add None l (Cpure.Add (acc_mult m e1, acc_mult m e2, l))
    | Cpure.Subtract (e1, e2, l) ->
        normalize_add None l
          (Cpure.Add (acc_mult m e1,
             acc_mult
               (match m with | None -> Some (- 1) | Some c -> Some (- c)) e2,
             l))
    | Cpure.Mult (c, e1, l) ->
        let r =
          (match m with
           | None -> acc_mult (Some c) e1
           | Some c1 -> acc_mult (Some (c1 * c)) e1)
        in r
    | Cpure.Max (e1, e2, l) ->
        Err.report_error
          {
            Err.error_loc = l;
            Err.error_text =
              "got Max !! (Should have already been simplified )";
          }
    | Cpure.Min (e1, e2, l) ->
        Err.report_error
          {
            Err.error_loc = l;
            Err.error_text =
              "got Min !! (Should have already been simplified )";
          }
    | Cpure.Bag (el, l) -> Cpure.Bag (List.map (acc_mult m) el, l)
    | Cpure.BagUnion (el, l) -> Cpure.BagUnion (List.map (acc_mult m) el, l)
    | Cpure.BagIntersect (el, l) ->
        Cpure.BagIntersect (List.map (acc_mult m) el, l)
    | Cpure.BagDiff (e1, e2, l) ->
        Cpure.BagDiff (acc_mult m e1, acc_mult m e2, l)
  in acc_mult None e

and split_sums (e : Cpure.exp) : ((Cpure.exp option) * (Cpure.exp option)) =
  match e with
  | Cpure.Null _ -> ((Some e), None)
  | Cpure.Var _ -> ((Some e), None)
  | Cpure.IConst (v, l) ->
      if v > 0
      then ((Some e), None)
      else
        if v < 0
        then (None, (Some (Cpure.IConst (- v, l))))
        else (None, None)
  | Cpure.Add (e1, e2, l) ->
      let (ts1, tm1) = split_sums e1 in
      let (ts2, tm2) = split_sums e2 in
      let tsr =
        (match (ts1, ts2) with
         | (None, None) -> None
         | (None, Some r1) -> ts2
         | (Some r1, None) -> ts1
         | (Some r1, Some r2) -> Some (Cpure.Add (r1, r2, l))) in
      let tmr =
        (match (tm1, tm2) with
         | (None, None) -> None
         | (None, Some r1) -> tm2
         | (Some r1, None) -> tm1
         | (Some r1, Some r2) -> Some (Cpure.Add (r1, r2, l)))
      in (tsr, tmr)
  | Cpure.Subtract (e1, e2, l) ->
      Err.report_error
        {
          Err.error_loc = l;
          Err.error_text =
            "got subtraction !! (Should have already been simplified )";
        }
  | Cpure.Mult (v, e1, l) ->
      let (ts, tm) = split_sums e1 in
      let r =
        (match (ts, tm) with
         | (None, None) -> (None, None)
         | (Some r1, None) ->
             if v > 0
             then ((Some (Cpure.Mult (v, r1, l))), None)
             else
               if v == 0
               then (None, None)
               else (None, (Some (Cpure.Mult (- v, r1, l))))
         | (None, Some r1) ->
             if v > 0
             then (None, (Some (Cpure.Mult (v, r1, l))))
             else
               if v == 0
               then (None, None)
               else ((Some (Cpure.Mult (- v, r1, l))), None)
         | _ -> ((Some e), None))
      in r
  | Cpure.Max (e1, e2, l) ->
      Err.report_error
        {
          Err.error_loc = l;
          Err.error_text =
            "got Max !! (Should have already been simplified )";
        }
  | Cpure.Min (e1, e2, l) ->
      Err.report_error
        {
          Err.error_loc = l;
          Err.error_text =
            "got Min !! (Should have already been simplified )";
        }
  | Cpure.Bag (e1, l) -> ((Some e), None)
  | Cpure.BagUnion (e1, l) -> ((Some e), None)
  | Cpure.BagIntersect (e1, l) -> ((Some e), None)
  | Cpure.BagDiff (e1, e2, l) -> ((Some e), None)

and move_lr (lhs : Cpure.exp option) (lsm : Cpure.exp option)
  (rhs : Cpure.exp option) (rsm : Cpure.exp option) l :
  (Cpure.exp * Cpure.exp) =
  let nl =
    match (lhs, rsm) with
    | (None, None) -> Cpure.IConst (0, l)
    | (Some e, None) -> e
    | (None, Some e) -> e
    | (Some e1, Some e2) -> Cpure.Add (e1, e2, l) in
  let nr =
    match (rhs, lsm) with
    | (None, None) -> Cpure.IConst (0, l)
    | (Some e, None) -> e
    | (None, Some e) -> e
    | (Some e1, Some e2) -> Cpure.Add (e1, e2, l)
  in (nl, nr)
	
	
and purge_mult (e : Cpure.exp): Cpure.exp = match e with
	| Cpure.Null _ -> e
  | Cpure.Var _ -> e
  | Cpure.IConst _ -> e
  | Cpure.Add (e1, e2, l) -> Cpure.Add((purge_mult e1), (purge_mult e2), l)
  | Cpure.Subtract (e1, e2, l) -> Cpure.Subtract((purge_mult e1), (purge_mult e2), l)
  | Cpure.Mult (i, a, l) -> if (i == 0) then Cpure.IConst (0, l)
										else if (i == 1) then (purge_mult a) 
													else 
														let inter = purge_mult a in
														let r = 
														match inter with
														| Cpure.IConst(v, _) -> if (v == 0) then inter
																									else Cpure.IConst(i * v, l)
														| _ -> Cpure.Mult(i, inter, l) in r
													 
  | Cpure.Max (e1, e2, l) -> Cpure.Max((purge_mult e1), (purge_mult e2), l)
  | Cpure.Min (e1, e2, l) -> Cpure.Min((purge_mult e1), (purge_mult e2), l)
  | Cpure.Bag (el, l) -> Cpure.Bag ((List.map purge_mult el), l)
  | Cpure.BagUnion (el, l) -> Cpure.BagUnion ((List.map purge_mult el), l)
  | Cpure.BagIntersect (el, l) -> Cpure.BagIntersect ((List.map purge_mult el), l)
  | Cpure.BagDiff (e1, e2, l) -> Cpure.BagDiff ((purge_mult e1), (purge_mult e2), l)

and arith_simplify (pf : Cpure.formula) : Cpure.formula = 

	let do_all e1 e2 l =
			let t1 = simp_mult e1 in
      let t2 = simp_mult e2 in
      let (lhs, lsm) = split_sums t1 in
      let (rhs, rsm) = split_sums t2 in
      let (lh, rh) = move_lr lhs lsm rhs rsm l in
			let lh = purge_mult lh in
			let rh = purge_mult rh in
			 (lh, rh) in

  match pf with
  | Cpure.BForm b ->
      let r =
        (match b with
         | Cpure.BConst _ -> b
         | Cpure.BVar _ -> b
         | Cpure.Lt (e1, e2, l) ->
             let lh, rh = do_all e1 e2 l in
						 Cpure.Lt (lh, rh, l)
         | Cpure.Lte (e1, e2, l) ->
             let lh, rh = do_all e1 e2 l in
             Cpure.Lte (lh, rh, l)
         | Cpure.Gt (e1, e2, l) ->
             let lh, rh = do_all e1 e2 l in
						 Cpure.Gt (lh, rh, l)
         | Cpure.Gte (e1, e2, l) ->
             let lh, rh = do_all e1 e2 l in
						 Cpure.Gte (lh, rh, l)
         | Cpure.Eq (e1, e2, l) ->
             let lh, rh = do_all e1 e2 l in
						 Cpure.Eq (lh, rh, l)
         | Cpure.Neq (e1, e2, l) ->
             let lh, rh = do_all e1 e2 l in
						 Cpure.Neq (lh, rh, l)
         | Cpure.EqMax (e1, e2, e3, l) ->
						 let ne1 = simp_mult e1 in
						 let ne2 = simp_mult e2 in
						 let ne3 = simp_mult e3 in
						 let ne1 = purge_mult ne1 in
						 let ne2 = purge_mult ne2 in
						 let ne3 = purge_mult ne3 in
						 if (!Tpdispatcher.tp == Tpdispatcher.Mona) then
							  let (s1, m1) = split_sums ne1 in
								let (s2, m2) = split_sums ne2 in
								let (s3, m3) = split_sums ne3 in
								match (s1, s2, s3, m1, m2, m3) with
									| None, None, None, None, None, None -> Cpure.BConst (true, l)
									| Some e11, Some e12, Some e13, None, None, None -> 
										let e11 = purge_mult e11 in
										let e12 = purge_mult e12 in
										let e13 = purge_mult e13 in
										Cpure.EqMax (e11, e12, e13, l)
									| None, None, None, Some e11, Some e12, Some e13 -> 
										let e11 = purge_mult e11 in
										let e12 = purge_mult e12 in
										let e13 = purge_mult e13 in
										Cpure.EqMin (e11, e12, e13, l)
									| _ -> 
										 Cpure.EqMax (ne1, ne2, ne3, l)
							else 
             		Cpure.EqMax (ne1, ne2, ne3, l)
         | Cpure.EqMin (e1, e2, e3, l) ->
						 let ne1 = simp_mult e1 in
						 let ne2 = simp_mult e2 in
						 let ne3 = simp_mult e3 in
						 let ne1 = purge_mult ne1 in
						 let ne2 = purge_mult ne2 in
						 let ne3 = purge_mult ne3 in
						 if (!Tpdispatcher.tp == Tpdispatcher.Mona) then
							  let (s1, m1) = split_sums ne1 in
								let (s2, m2) = split_sums ne2 in
								let (s3, m3) = split_sums ne3 in
								match (s1, s2, s3, m1, m2, m3) with
									| None, None, None, None, None, None -> Cpure.BConst (true, l)
									| Some e11, Some e12, Some e13, None, None, None -> 
											let e11 = purge_mult e11 in
											let e12 = purge_mult e12 in
											let e13 = purge_mult e13 in
											Cpure.EqMin (e11, e12, e13, l)
									| None, None, None, Some e11, Some e12, Some e13 -> 
											let e11 = purge_mult e11 in
											let e12 = purge_mult e12 in
											let e13 = purge_mult e13 in
											Cpure.EqMax (e11, e12, e13, l)
									| _ -> Cpure.EqMin (ne1, ne2, ne3, l)
							else
             		Cpure.EqMin (ne1, ne2, ne3, l)
         | Cpure.BagIn (v, e1, l) -> Cpure.BagIn (v, purge_mult (simp_mult e1), l)
         | Cpure.BagNotIn (v, e1, l) -> Cpure.BagNotIn (v, purge_mult (simp_mult e1), l)
         | Cpure.BagSub (e1, e2, l) ->
             Cpure.BagSub (simp_mult e1, simp_mult e2, l)
         | Cpure.BagMin _ -> b
         | Cpure.BagMax _ -> b)
      in Cpure.BForm r
  | Cpure.And (f1, f2, loc) ->
      Cpure.And (arith_simplify f1, arith_simplify f2, loc)
  | Cpure.Or (f1, f2, loc) ->
      Cpure.Or (arith_simplify f1, arith_simplify f2, loc)
  | Cpure.Not (f1, loc) -> Cpure.Not (arith_simplify f1, loc)
  | Cpure.Forall (v, f1, loc) -> Cpure.Forall (v, arith_simplify f1, loc)
  | Cpure.Exists (v, f1, loc) -> Cpure.Exists (v, arith_simplify f1, loc)


and float_out_exp_min_max (e: Ipure.exp): (Ipure.exp * (Ipure.formula * (string list) ) option) = match e with 
	| Ipure.Null _ -> (e, None)
  | Ipure.Var _ -> (e, None)
  | Ipure.IConst _ -> (e, None)
  | Ipure.Add (e1, e2, l) ->
			let ne1, np1 = float_out_exp_min_max e1 in
			let ne2, np2 = float_out_exp_min_max e2 in
			let r = match (np1, np2) with
					| None, None -> None
					| Some p, None -> Some p
					| None, Some p -> Some p
					| Some (p1, l1), Some (p2, l2) -> Some ((Ipure.And (p1, p2, l)), (List.rev_append l1 l2))in
			(Ipure.Add (ne1, ne2, l), r) 
  | Ipure.Subtract (e1, e2, l) ->
			let ne1, np1 = float_out_exp_min_max e1 in
			let ne2, np2 = float_out_exp_min_max e2 in
			let r = match (np1, np2) with
					| None, None -> None
					| Some p, None -> Some p
					| None, Some p -> Some p
					| Some (p1, l1), Some (p2, l2) -> Some ((Ipure.And (p1, p2, l)), (List.rev_append l1 l2))in
			(Ipure.Subtract (ne1, ne2, l), r) 
  | Ipure.Mult (c, e1, l) ->
			let ne1, np1 = float_out_exp_min_max e1 in
			(Ipure.Mult (c, ne1, l), np1)
						 
  | Ipure.Max (e1, e2, l) ->
			let ne1, np1 = float_out_exp_min_max e1 in
			let ne2, np2 = float_out_exp_min_max e2 in
			let new_name = ("max"^(fresh_trailer())) in
			let nv = Ipure.Var((new_name, Unprimed), l) in
			let t = Ipure.BForm (Ipure.EqMax(nv, ne1, ne2, l)) in 
			let r = match (np1, np2) with
					| None, None -> Some (t,[new_name])
					| Some (p1, l1), None -> Some ((Ipure.And(p1, t, l)), (new_name:: l1))
					| None, Some (p1, l1) -> Some ((Ipure.And(p1, t, l)), (new_name:: l1))
					| Some (p1, l1), Some (p2, l2) -> Some ((Ipure.And ((Ipure.And (p1, t, l)), p2, l)), new_name:: (List.rev_append l1 l2)) in
			(nv, r) 
			
			
  | Ipure.Min (e1, e2, l) ->
			let ne1, np1 = float_out_exp_min_max e1 in
			let ne2, np2 = float_out_exp_min_max e2 in
			let new_name = ("min"^(fresh_trailer())) in
			let nv = Ipure.Var((new_name, Unprimed), l) in
			let t = Ipure.BForm (Ipure.EqMin(nv, ne1, ne2, l)) in 
			let r = match (np1, np2) with
					| None, None -> Some (t,[new_name])
					| Some (p1, l1), None -> Some ((Ipure.And(p1, t, l)), (new_name:: l1))
					| None, Some (p2, l2) -> Some ((Ipure.And(p2, t, l)), (new_name:: l2))
					| Some (p1, l1), Some (p2, l2) -> Some ((Ipure.And ((Ipure.And (p1, t, l)), p2, l)), new_name:: (List.rev_append l1 l2)) in
			(nv, r) 
	
		(* bag expressions *)
  | Ipure.Bag (le, l) ->
			let ne1, np1 = List.split (List.map float_out_exp_min_max le) in
			let r = List.fold_left (fun a c -> match (a, c)with
				  | None, None -> None
					| Some p, None -> Some p
					| None, Some p -> Some p
					| Some (p1, l1), Some (p2, l2) -> Some ((Ipure.And (p1, p2, l)), (List.rev_append l1 l2))) None np1 in
			(Ipure.Bag (ne1, l), r)
  | Ipure.BagUnion (le, l) ->
			let ne1, np1 = List.split (List.map float_out_exp_min_max le) in
			let r = List.fold_left (fun a c -> match (a, c)with
				  | None, None -> None
					| Some p, None -> Some p
					| None, Some p -> Some p
					| Some (p1, l1), Some (p2, l2) -> Some ((Ipure.And (p1, p2, l)), (List.rev_append l1 l2))) None np1 in
			(Ipure.BagUnion (ne1, l), r)
  | Ipure.BagIntersect (le, l) ->
			let ne1, np1 = List.split (List.map float_out_exp_min_max le) in
			let r = List.fold_left (fun a c -> match (a, c)with
				  | None, None -> None
					| Some p, None -> Some p
					| None, Some p -> Some p
					| Some (p1, l1), Some (p2, l2) -> Some ((Ipure.And (p1, p2, l)), List.rev_append l1 l2)) None np1 in
			(Ipure.BagIntersect (ne1, l), r)
  | Ipure.BagDiff (e1, e2, l) ->
			let ne1, np1 = float_out_exp_min_max e1 in
			let ne2, np2 = float_out_exp_min_max e2 in
			let r = match (np1, np2) with
					| None, None -> None
					| Some p, None -> Some p
					| None, Some p -> Some p
					| Some (p1, l1), Some (p2, l2) -> Some ((Ipure.And (p1, p2, l)), (List.rev_append l1 l2)) in
			(Ipure.BagDiff (ne1, ne2, l), r) 

and float_out_pure_min_max (p : Ipure.formula) : Ipure.formula =
		
		let add_exists (t: Ipure.formula)(np1: (Ipure.formula * (string list))option)(np2: (Ipure.formula * (string list))option) l: Ipure.formula = 
			let r, ev = match np1 with
							| None -> (t,[])
							| Some (p1, ev1) -> (Ipure.And (t, p1, l), ev1) in
			let r, ev2 = match np2 with 
							| None -> (r, ev)
							| Some (p1, ev1) -> (Ipure.And(r, p1, l), (List.rev_append ev1 ev)) in 
		  List.fold_left (fun a c -> (Ipure.Exists ((c, Unprimed), a, l))) r ev2 in
							
				
		let rec float_out_b_formula_min_max (b: Ipure.b_formula): Ipure.formula = match b with
			| Ipure.BConst _ -> Ipure.BForm b
		  | Ipure.BVar _ -> Ipure.BForm b
		  | Ipure.Lt (e1, e2, l) ->
						let ne1, np1 = float_out_exp_min_max e1 in
						let ne2, np2 = float_out_exp_min_max e2 in
						let t = Ipure.BForm (Ipure.Lt (ne1, ne2, l)) in
						add_exists t np1 np2 l
		  | Ipure.Lte (e1, e2, l) ->
						let ne1, np1 = float_out_exp_min_max e1 in
						let ne2, np2 = float_out_exp_min_max e2 in
						let t = Ipure.BForm (Ipure.Lte (ne1, ne2, l)) in
						add_exists t np1 np2 l
		  | Ipure.Gt (e1, e2, l) ->
						let ne1, np1 = float_out_exp_min_max e1 in
						let ne2, np2 = float_out_exp_min_max e2 in
						let t = Ipure.BForm (Ipure.Gt (ne1, ne2, l)) in
						add_exists t np1 np2 l
		  | Ipure.Gte (e1, e2, l) ->
						let ne1, np1 = float_out_exp_min_max e1 in
						let ne2, np2 = float_out_exp_min_max e2 in
						let t = Ipure.BForm (Ipure.Gte (ne1, ne2, l)) in
						add_exists t np1 np2 l
		  | Ipure.Eq (e1, e2, l) ->
						let r = match e1 with
							| Ipure.Min(v1, v2, v3) -> let r2 = match e2 with
																	| Ipure.Null _
																	| Ipure.IConst _
																	| Ipure.Var _ ->
																			 let ne1 , np1 = float_out_exp_min_max v1 in
																			 let ne2 , np2 = float_out_exp_min_max v2 in
																			 let t = Ipure.BForm(Ipure.EqMin(e2, ne1, ne2, l)) in
																			 add_exists t np1 np2 l
																	| _ -> 
																			 let ne1, np1 = float_out_exp_min_max e1 in
																			 let ne2, np2 = float_out_exp_min_max e2 in
																			 let t = Ipure.BForm (Ipure.Eq (ne1, ne2, l)) in
																			 add_exists t np1 np2 l  in r2
							| Ipure.Max(v1, v2, v3) -> let r2 = match e2 with
																						| Ipure.Null _
																						| Ipure.IConst _
																						| Ipure.Var _ ->
																								 let ne1 , np1 = float_out_exp_min_max v1 in
																								 let ne2 , np2 = float_out_exp_min_max v2 in
																								 let t = Ipure.BForm(Ipure.EqMax(e2, ne1, ne2, l)) in
																								 add_exists t np1 np2 l
																						| _ -> 
																							let ne1, np1 = float_out_exp_min_max e1 in
																							let ne2, np2 = float_out_exp_min_max e2 in
																							let t = Ipure.BForm (Ipure.Eq (ne1, ne2, l)) in
																							add_exists t np1 np2 l 
																			in r2
							| Ipure.Null _
							| Ipure.IConst _
							| Ipure.Var _ -> let r2 = match e2 with
																					| Ipure.Min (v1, v2, v3) ->
																						 	 let ne1 , np1 = float_out_exp_min_max v1 in
																							 let ne2 , np2 = float_out_exp_min_max v2 in
																							 let t = Ipure.BForm(Ipure.EqMin(e1, ne1, ne2, l)) in
																							 add_exists t np1 np2 l
																					| Ipure.Max (v1, v2, v3) ->
																							 let ne1 , np1 = float_out_exp_min_max v1 in
																							 let ne2 , np2 = float_out_exp_min_max v2 in
																							 let t = Ipure.BForm(Ipure.EqMax(e1, ne1, ne2, l)) in
																							 add_exists t np1 np2 l
																					| _ -> 
																						let ne1, np1 = float_out_exp_min_max e1 in
																						let ne2, np2 = float_out_exp_min_max e2 in
																						let t = Ipure.BForm (Ipure.Eq (ne1, ne2, l)) in
																						add_exists t np1 np2 l 
																in r2
							| _ ->
									let ne1, np1 = float_out_exp_min_max e1 in
									let ne2, np2 = float_out_exp_min_max e2 in
									let t = Ipure.BForm (Ipure.Eq (ne1, ne2, l)) in
									add_exists t np1 np2 l 
							in r
		  | Ipure.Neq (e1, e2, l) ->
						let ne1, np1 = float_out_exp_min_max e1 in
						let ne2, np2 = float_out_exp_min_max e2 in
						let t = Ipure.BForm (Ipure.Neq (ne1, ne2, l)) in
						add_exists t np1 np2 l
		  | Ipure.EqMax (e1, e2, e3, l) ->
						let ne1, np1 = float_out_exp_min_max e1 in
						let ne2, np2 = float_out_exp_min_max e2 in
						let ne3, np3 = float_out_exp_min_max e3 in
						let t = Ipure.BForm (Ipure.EqMax (ne1, ne2, ne3, l)) in
						let t = add_exists t np1 np2 l in
						let r = match np3 with 
							| None -> t
							| Some (p1, l1) -> List.fold_left (fun a c -> (Ipure.Exists ((c, Unprimed), a, l))) (Ipure.And(t, p1, l)) l1 in r
		  | Ipure.EqMin (e1, e2, e3, l) ->
						let ne1, np1 = float_out_exp_min_max e1 in
						let ne2, np2 = float_out_exp_min_max e2 in
						let ne3, np3 = float_out_exp_min_max e3 in
						let t = Ipure.BForm (Ipure.EqMin (ne1, ne2, ne3, l)) in
						let t = add_exists t np1 np2 l in
						let r = match np3 with 
							| None -> t
							| Some (p1, l1) -> List.fold_left (fun a c -> Ipure.Exists ((c, Unprimed), a, l)) (Ipure.And(t, p1, l)) l1 in r
		  | Ipure.BagIn (v, e, l) -> 
							let ne1, np1 = float_out_exp_min_max e in
							let r = match np1 with
								| None -> Ipure.BForm (Ipure.BagIn(v, ne1, l))
								| Some (r, l1) -> List.fold_left (fun a c -> Ipure.Exists ((c, Unprimed), a, l)) (Ipure.And(Ipure.BForm (Ipure.BagIn(v, ne1, l)), r, l)) l1 in r 
		  | Ipure.BagNotIn (v, e, l) -> 
							let ne1, np1 = float_out_exp_min_max e in
							let r = match np1 with
								| None -> Ipure.BForm (Ipure.BagNotIn(v, ne1, l))
								| Some (r, l1) -> List.fold_left (fun a c -> Ipure.Exists ((c, Unprimed), a, l)) (Ipure.And(Ipure.BForm (Ipure.BagIn(v, ne1, l)), r, l)) l1 in r
		  | Ipure.BagSub (e1, e2, l) ->
					let ne1, np1 = float_out_exp_min_max e1 in
					let ne2, np2 = float_out_exp_min_max e2 in
					let t = Ipure.BForm (Ipure.BagSub (ne1, ne2, l)) in
					add_exists t np1 np2 l
		  | Ipure.BagMin _ -> Ipure.BForm b
		  | Ipure.BagMax _ -> Ipure.BForm b	
			in		 
		match p with
			| Ipure.BForm b -> (float_out_b_formula_min_max b)
  		| Ipure.And (f1, f2, l) -> Ipure.And((float_out_pure_min_max f1), (float_out_pure_min_max f2), l)
  		| Ipure.Or (f1, f2, l) -> Ipure.Or((float_out_pure_min_max f1), (float_out_pure_min_max f2), l)
  		| Ipure.Not (f1, l) -> Ipure.Not((float_out_pure_min_max f1), l)
  		| Ipure.Forall (v, f1, l) -> Ipure.Forall (v, (float_out_pure_min_max f1), l)
  		| Ipure.Exists (v, f1, l) -> Ipure.Exists (v, (float_out_pure_min_max f1), l)
		

and float_out_heap_min_max (h : Iformula.h_formula) :
  (Iformula.h_formula * (Ipure.formula option)) =
  match h with
  | Iformula.Star
      {
        Iformula.h_formula_star_h1 = f1;
        Iformula.h_formula_star_h2 = f2;
        Iformula.h_formula_star_pos = l
      } ->
      let (nf1, np1) = float_out_heap_min_max f1 in
      let (nf2, np2) = float_out_heap_min_max f2 in
      let np =
        (match (np1, np2) with
         | (None, None) -> None
         | (Some _, None) -> np1
         | (None, Some _) -> np2
         | (Some e1, Some e2) -> Some (Ipure.And (e1, e2, l)))
      in
        ((Iformula.Star
            {
              Iformula.h_formula_star_h1 = nf1;
              Iformula.h_formula_star_h2 = nf2;
              Iformula.h_formula_star_pos = l;
            }),
         np)
  | Iformula.HeapNode h1->
		  let args = h1.Iformula.h_formula_heap_arguments in
			let l = h1.Iformula.h_formula_heap_pos in
      let nl, new_p =
				List.fold_left
             (fun (a, c) d -> 
	        match d with
		| Ipure.Null _ 
		| Ipure.IConst _
		| Ipure.Var _ -> (d:: a, c)
		| _ -> 
				let new_name = fresh_var_name "ptr" l.Lexing.pos_lnum in 
				let nv = Ipure.Var((new_name, Unprimed), l) in
				(nv:: a, match c with
												| None -> Some (float_out_pure_min_max (Ipure.BForm (Ipure.Eq (nv, d, l))) )
												| Some s -> Some (Ipure.And ((float_out_pure_min_max (Ipure.BForm (Ipure.Eq (nv, d, l)))), s, l)))) ([], None) args in
        ((Iformula.HeapNode { h1 with Iformula.h_formula_heap_arguments = (List.rev nl);}), new_p)
  | Iformula.HeapNode2 h1 ->
			let args = h1.Iformula.h_formula_heap2_arguments in
			let l = h1.Iformula.h_formula_heap2_pos in
      let nl, new_p =
				List.fold_left
             (fun (a, c) (d1,d2) -> 
	        match d2 with
		| Ipure.Null _ 
		| Ipure.IConst _
		| Ipure.Var _ -> ((d1,d2):: a, c)
		| _ -> 
				let new_name = fresh_var_name "ptr" l.Lexing.pos_lnum in 
				let nv = Ipure.Var((new_name, Unprimed), l) in
				((d1,nv):: a, match c with
												| None -> Some (float_out_pure_min_max (Ipure.BForm (Ipure.Eq (nv, d2, l))) )
												| Some s -> Some (Ipure.And ((float_out_pure_min_max (Ipure.BForm (Ipure.Eq (nv, d2, l))) ), s, l)))) ([], None) args in
        ((Iformula.HeapNode2 { h1 with Iformula.h_formula_heap2_arguments = (List.rev nl);}), new_p)
  | Iformula.HTrue -> (h, None)
  | Iformula.HFalse -> (h, None)

and float_out_min_max (f : Iformula.formula) : Iformula.formula =
  match f with
  | Iformula.Base
      {
        Iformula.formula_base_pos = l;
        Iformula.formula_base_heap = h0;
        Iformula.formula_base_pure = p0
      } ->
      let (nh, nhpf) = float_out_heap_min_max h0 in
      let np = float_out_pure_min_max p0 in
        Iformula.Base
          {
            Iformula.formula_base_pos = l;
            Iformula.formula_base_heap = nh;
            Iformula.formula_base_pure =
              (match nhpf with
               | None -> np
               | Some e1 -> Ipure.And (np, e1, l));
          }
  | Iformula.Exists
      {
        Iformula.formula_exists_qvars = qv;
        Iformula.formula_exists_heap = h0;
        Iformula.formula_exists_pure = p0;
        Iformula.formula_exists_pos = l
      } ->
      let (nh, nhpf) = float_out_heap_min_max h0 in
      let np = float_out_pure_min_max p0 in
        Iformula.Exists
          {
            Iformula.formula_exists_qvars = qv;
            Iformula.formula_exists_heap = nh;
            Iformula.formula_exists_pure =
              (match nhpf with
               | None -> np
               | Some e1 -> (Ipure.And (np, e1, l)));
            Iformula.formula_exists_pos = l;
          }
  | Iformula.Or
      {
        Iformula.formula_or_f1 = f1;
        Iformula.formula_or_f2 = f2;
        Iformula.formula_or_pos = l
      } ->
      Iformula.Or
        {
          Iformula.formula_or_f1 = float_out_min_max f1;
          Iformula.formula_or_f2 = float_out_min_max f2;
          Iformula.formula_or_pos = l;
        }
				