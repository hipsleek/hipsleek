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

(*
module VHD = struct
			type t = ident
			let compare c1 c2 = String.compare c1 c2
			let hash c = Hashtbl.hash c
			let equal c1 c2 = (String.compare c1 c2) = 0
		end
module VH = Graph.Persistent.Digraph.Concrete(VHD)
module SVH = Graph.Components.Make(VH)			
*)

type trans_exp_type =
  (C.exp * CP.typ)

  and spec_var_info =
  { mutable sv_info_kind : spec_var_kind;
    id: int;
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
and string_of_stab stab = Hashtbl.fold 
		(fun c1 c2 a -> 
			a^"; ("^c1^" "^
			(match c2.sv_info_kind with 
				| Unknown -> "unknown" 
				| Known d-> 
			Cprinter.string_of_typ d )^")") stab ""
	
and string_of_var_kind k = (match k with 
		| Unknown -> "unknown" 
		| Known d-> 
	("known "^(Cprinter.string_of_typ d)) )
	
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
     in 
	 (*let _ = print_string ("\n primitives: "^(Iprinter.string_of_program prog)^"\n") in*)
	 
	 prog.I.prog_proc_decls)
  
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
  
(***********************************************)
(* 17.04.2008 *)
(* add existential quantifiers for the anonymous vars - those that start with "Anon_" *)
(***********************************************)
let rec

	(* - added 17.04.2008 - checks if the heap formula contains anonymous    *)
	(* vars                                                                  *)
  (* as h*) (* as h*)
	(* let _ = print_string("[astsimpl.ml, line 163]: anonymous var: " ^ id  *)
	(* ^ "\n") in                                                            *)
  look_for_anonymous_h_formula (h0 : IF.h_formula) : (ident * primed) list =
  match h0 with
  | IF.Star { IF.h_formula_star_h1 = h1; IF.h_formula_star_h2 = h2 } ->
      let tmp1 = look_for_anonymous_h_formula h1 in
      let tmp2 = look_for_anonymous_h_formula h2 in List.append tmp1 tmp2
  | IF.HeapNode { IF.h_formula_heap_arguments = args } ->
      let tmp1 = look_for_anonymous_exp_list args in tmp1
  | _ -> []

and look_for_anonymous_exp_list (args : IP.exp list) :
  (ident * primed) list =
  match args with
  | h :: rest ->
      List.append (look_for_anonymous_exp h)
        (look_for_anonymous_exp_list rest)
  | _ -> []

and look_for_anonymous_exp (arg : IP.exp) : (ident * primed) list =
  match arg with
  | IP.Var ((id, p), _) ->
      if
        ((String.length id) > 5) &&
          ((String.compare (String.sub id 0 5) "Anon_") == 0)
      then [ (id, p) ]
      else []
  | IP.Add (e1, e2, _) | IP.Subtract (e1, e2, _) | IP.Max (e1, e2, _) |
      IP.Min (e1, e2, _) | IP.BagDiff (e1, e2, _) ->
      List.append (look_for_anonymous_exp e1) (look_for_anonymous_exp e2)
  | IP.Mult (_, e1, _) -> look_for_anonymous_exp e1
  | IP.Bag (e1, _) | IP.BagUnion (e1, _) | IP.BagIntersect (e1, _) ->
      look_for_anonymous_exp_list e1
  | _ -> []

and convert_anonym_to_exist (f0 : IF.formula) : IF.formula =
  match f0 with
  | (* - added 17.04.2008 - in case the formula contains anonymous vars ->   *)
			(* transforms them into existential vars (transforms IF.formula_base *)
			(* to IF.formula_exists)                                             *)
      IF.Or (({ IF.formula_or_f1 = f1; IF.formula_or_f2 = f2 } as f)) ->
      let tmp1 = convert_anonym_to_exist f1 in
      let tmp2 = convert_anonym_to_exist f2
      in IF.Or { (f) with IF.formula_or_f1 = tmp1; IF.formula_or_f2 = tmp2; }
  | IF.Base
      {
        IF.formula_base_heap = h0;
        IF.formula_base_pure = p0;
        IF.formula_base_branches = br0;
        IF.formula_base_pos = l0
      } -> (*as f*)
      let tmp1 = look_for_anonymous_h_formula h0
      in
        if ( != ) (List.length tmp1) 0
        then
          IF.Exists
            {
              IF.formula_exists_heap = h0;
              IF.formula_exists_qvars = tmp1;
              IF.formula_exists_pure = p0;
              IF.formula_exists_branches = br0;
              IF.formula_exists_pos = l0;
            }
        else f0
  | IF.Exists
      (({ IF.formula_exists_heap = h0; IF.formula_exists_qvars = q0 } as f))
      ->
      let tmp1 = look_for_anonymous_h_formula h0
      in
        if ( != ) (List.length tmp1) 0
        then
          (let rec append_no_duplicates (l1 : (ident * primed) list)
             (l2 : (ident * primed) list) : (ident * primed) list =
             match l1 with
             | h :: rest ->
                 if List.mem h l2
                 then append_no_duplicates rest l2
                 else h :: (append_no_duplicates rest l2)
             | [] -> l2
           in
             IF.Exists
               {
                 (f)
                 with
                 IF.formula_exists_heap = h0;
                 IF.formula_exists_qvars = append_no_duplicates tmp1 q0;
               })
        else (* make sure that the var is not already there *) f0
  
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
	| Iformula.EAssume b-> Iformula.EAssume (convert_heap2 prog b)
	| Iformula.ECase b -> Iformula.ECase {b with Iformula.formula_case_branches = (List.map (fun (c1,c2)-> (c1,(convert_struc2 prog c2))) b.Iformula.formula_case_branches)};
	| Iformula.EBase b -> Iformula.EBase{b with 
		 Iformula.formula_ext_base = convert_heap2 prog b.Iformula.formula_ext_base;
		 Iformula.formula_ext_continuation = List.map (fun e-> convert_ext2 prog e)  b.Iformula.formula_ext_continuation 
		}

and convert_struc2 prog (f0 : Iformula.struc_formula) : Iformula.struc_formula = 
	List.map (convert_ext2 prog ) f0 
	  
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
		| Iformula.EAssume b-> (gen_name_pairs vname b)
		| Iformula.ECase {Iformula.formula_case_branches = b}-> 
			List.fold_left (fun d (e1,e2) -> List.fold_left (fun a c -> a@(gen_name_pairs_ext vname c)) d e2) [] b 
		| Iformula.EBase {Iformula.formula_ext_base =fb;
		 				 Iformula.formula_ext_continuation = cont}-> List.fold_left 
									(fun a c -> a@(gen_name_pairs_ext vname c)) (gen_name_pairs vname fb) cont  
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
  (* first is min of second and third *) (* bag formulas *) 
  trans_prog (prog0 : I.prog_decl) : C.prog_decl =
  let _ = I.build_hierarchy prog0 in
  let check_overridding = Chk.overridding_correct prog0 in
  let check_field_dup = Chk.no_field_duplication prog0 in
  let check_method_dup = Chk.no_method_duplication prog0 in
  let check_field_hiding = Chk.no_field_hiding prog0 in
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
              (
							 (*let _ = print_string ("pre norm :"^(Iprinter.string_of_program prog)) in*)
							 let prog = case_normalize_program prog in
							 (*let _ = print_string ("post norm :"^(Iprinter.string_of_program prog)) in*)
							 let tmp_views = order_views prog.I.prog_view_decls in
               let cviews = List.map (trans_view prog) tmp_views in
			   let cdata =
                 List.map (trans_data prog) prog.I.prog_data_decls in
			   let cprocs1 =
                 List.map (trans_proc prog) prog.I.prog_proc_decls in
               let cprocs = !loop_procs @ cprocs1 in
			   
               let (l2r_coers, r2l_coers) = trans_coercions prog in
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
                  let cprog = (add_pre_to_cprog cprog) in
				  sat_warnings cprog ;
				  let c = if !Globals.enable_case_inference then case_inference prog cprog else cprog in
				  let _ = if !Globals.print_core then print_string (Cprinter.string_of_program c) else () in
				  c))))
    else failwith "Error detected"

and add_pre_to_cprog cprog = 
{cprog with C.prog_proc_decls = List.map (fun c-> 
	{c with 
	 Cast.proc_static_specs_with_pre = add_pre cprog c.Cast.proc_static_specs;
	 Cast.proc_dynamic_specs_with_pre = add_pre cprog c.Cast.proc_dynamic_specs;
	}

) cprog.C.prog_proc_decls;}	

and sat_warnings cprog = 

	let _ = List.map (fun c -> 
		let unsat_list = Solver.find_unsat cprog c.Cast.view_un_struc_formula in
		if ((List.length unsat_list)> 0) then print_string ("the view body for "^c.Cast.view_name^" contains unsat branch(es) :"^
					(List.fold_left (fun a c-> a^"\n   "^(Cprinter.string_of_formula c)) "" unsat_list)^"\n") else ()) cprog.Cast.prog_view_decls in
	()
	
	
	
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
      let (xform', xform_b, addr_vars') =
        Solver.xpure_symbolic_no_exists prog vdef.Cast.view_un_struc_formula(*view_formula *)in
      let addr_vars = U.remove_dups addr_vars' in
	  (*let _ = print_string ("\n!!! "^(vdef.Cast.view_name)^" struc: \n"^(Cprinter.string_of_struc_formula vdef.Cast.view_formula)^"\n\n here1 \n un:"^
						(Cprinter.string_of_formula  vdef.Cast.view_un_struc_formula)^"\n\n\n"^
						(Cprinter.string_of_pure_formula xform')^"\n\n\n");flush stdout in	*)
      let new_xform' = TP.simplify  xform' in
      let xform = new_xform' in
      let formula1 = CF.replace_branches xform_b (CF.formula_of_pure xform pos) in
      let ctx =
        CF.build_context (CF.true_ctx pos) formula1 pos in
      let formula = CF.replace_branches (snd vdef.C.view_user_inv) (CF.formula_of_pure (fst vdef.C.view_user_inv) pos) in
      let (rs, _) =
        Solver.heap_entail prog false false [ ctx ] formula pos
      in
        if not (U.empty rs)
        then
          (vdef.C.view_x_formula <- (xform, xform_b);
           vdef.C.view_addr_vars <- addr_vars;
           compute_view_x_formula prog vdef (n - 1))
        else
			(*let _ = print_string 
				(
					(Cprinter.string_of_formula vdef.Cast.view_un_struc_formula)^"\n"^
					(Cprinter.string_of_formula formula1)^"\n"^(Cprinter.string_of_formula formula)) in*)
          Err.report_error
            {
              Err.error_loc = pos;
              Err.error_text = "view formula does not entail supplied invariant\n";})
   else ();
   if !Globals.print_x_inv && (n = 0)
   then
     (print_string
        ("\ncomputed invariant for view: " ^
           (vdef.C.view_name ^
              ("\n" ^
                 ((Cprinter.string_of_pure_formula_branches (vdef.C.view_x_formula)) ^
                    "\n"))));
      print_string
        ("addr_vars: " ^
           ((String.concat ", "
               (List.map CP.name_of_spec_var vdef.C.view_addr_vars))
              ^ "\n\n")))
   else ())

   
and fill_view_param_types (prog : I.prog_decl) (vdef : I.view_decl) =
	if (String.length vdef.I.view_data_name) = 0 then
		(
			let r = I.data_name_of_view prog.I.prog_view_decls vdef.I.view_formula in
			vdef.I.view_data_name<- r;	
		  let pos = IF.pos_of_struc_formula vdef.I.view_formula in
		  let nstab = H.create 103 in
		  let _ = H.add nstab self { sv_info_kind = Known (CP.OType vdef.I.view_data_name);id = fresh_int ()} in
		  let _ = collect_type_info_struc_f prog vdef.I.view_formula nstab in
          let view_sv_vars = List.map (fun c-> trans_var (c,Unprimed) nstab pos) vdef.I.view_vars in
		  let typed_vars = List.map ( fun (Cpure.SpecVar (c1,c2,c3))-> (c1,c2)) view_sv_vars in
		  let _ = H.clear nstab in
          let _ = vdef.I.view_typed_vars <- typed_vars in
		())
	else ()
   
and trans_view (prog : I.prog_decl) (vdef : I.view_decl) : C.view_decl =
  let stab = H.create 103 in
  let view_formula1 = vdef.I.view_formula in
  (*let recs = rec_grp prog in*)
  let data_name = if (String.length vdef.I.view_data_name) = 0  then  I.data_name_of_view prog.I.prog_view_decls view_formula1
					else vdef.I.view_data_name in
    (vdef.I.view_data_name <- data_name;
     H.add stab self { sv_info_kind = Known (CP.OType data_name);id = fresh_int () };
     let cf =
       trans_struc_formula prog true (self :: vdef.I.view_vars) vdef.I.view_formula
         stab false (Cpure.Prim Void) in
     let (inv, inv_b) = vdef.I.view_invariant in
     let pf = trans_pure_formula inv stab in
     let pf_b = List.map (fun (n, f) -> (n, trans_pure_formula f stab)) inv_b in
     let pf_b_fvs = List.flatten (List.map (fun (n, f) -> List.map CP.name_of_spec_var (CP.fv pf)) pf_b) in
		(* let _ = print_string ("pre: "^(Cprinter.string_of_pure_formula      *)
		(* pf)^"\n") in                                                        *)
     let pf = Cpure.arith_simplify pf in
		(* let _ = print_string ("post: "^(Cprinter.string_of_pure_formula     *)
		(* pf)^"\n") in                                                        *)
     let cf_fv = List.map CP.name_of_spec_var (CF.struc_fv cf) in
     let pf_fv = List.map CP.name_of_spec_var (CP.fv pf)
     in
       if (List.mem res cf_fv) || (List.mem res pf_fv) || (List.mem res pf_b_fvs)
       then
         Err.report_error
           {
             Err.error_loc = IF.pos_of_struc_formula view_formula1;
             Err.error_text =
               "res is not allowed in view definition or invariant";
           }
       else(
		  let pos = IF.pos_of_struc_formula view_formula1 in
          let view_sv_vars = List.map (fun c-> trans_var (c,Unprimed) stab pos) vdef.I.view_vars in
		  let typed_vars = List.map ( fun (Cpure.SpecVar (c1,c2,c3))-> (c1,c2)) view_sv_vars in
          let _ = vdef.I.view_typed_vars <- typed_vars in
          let mvars = [] in
		  let n_un_str =  Cformula.struc_to_formula cf in
		  let bc = match (compute_base_case cf) with
				| None -> None
				| Some s -> (flatten_base_case s (Cpure.SpecVar ((Cpure.OType data_name), self, Unprimed))) in
          let cvdef =
            {
              C.view_name = vdef.I.view_name;
              C.view_vars = view_sv_vars;
              C.view_labels = vdef.I.view_labels;
              C.view_modes = vdef.I.view_modes;
              C.view_partially_bound_vars = [];
              C.view_materialized_vars = mvars;
              C.view_data_name = data_name;
              C.view_formula = cf;
              C.view_x_formula = (pf, pf_b);
              C.view_addr_vars = [];
              C.view_user_inv = (pf, pf_b);
			  C.view_un_struc_formula = n_un_str;
			  C.view_base_case = bc;
			  C.view_case_vars = Util.intersect view_sv_vars (Cformula.guard_vars cf)
            }
          in
            (Debug.devel_pprint ("\n" ^ (Cprinter.string_of_view_decl cvdef))
               (CF.pos_of_struc_formula cf);
             cvdef)))

and rec_grp prog :ident list =
	let r = List.map (fun c-> (c.Iast.view_name, (Iformula.view_node_types_struc c.Iast.view_formula))) prog.Iast.prog_view_decls in	
	(*let vh = VH.empty in
	let vh = List.fold_left  (fun a (c1,c2)-> 
		(List.fold_left (fun b c -> VH.add_edge b c1 c) a c2)) vh r in	
	let sccs = SVH.scc_list vh in
	let sccs = List.filter (fun c-> (List.length c)>1)sccs in
	let _ = print_string ("\n gf:"^(string_of_int (List.length sccs))^"\n") in
	let sccs = List.fold_left (fun a (c1,c2)-> if (List.mem c1 c2) then a else [c1]::a)sccs r in
	let _ = print_string ("\n sscs:"^(List.fold_left (fun a c-> a^"\n"^(Cprinter.string_of_ident_list c " "))"" sccs)^"\n") in*)
	let sccs = List.fold_left (fun a (c1,c2)-> if (List.mem c1 c2) then c1::a else a) [] r in
	let rec trans_cl (l:ident list):ident list =
		let int_l = List.fold_left (fun a (c1,c2)-> if (List.exists (fun c-> List.mem c l) c2) then c1::a else a) l r in
		let int_l = Util.remove_dups int_l in
		if (List.length int_l)=(List.length l) then int_l
		else trans_cl int_l in
	let recs = trans_cl sccs in
	let recs = Util.difference recs (List.map (fun c-> c.Iast.data_name)prog.Iast.prog_data_decls) in
	(*let _ = print_string ("\n recs: "^(Cprinter.string_of_ident_list recs " ")^"\n") in*)
	recs
		
				
and flatten_base_case (f:Cformula.struc_formula)(self:Cpure.spec_var):(Cpure.formula * (Cpure.formula*((string*Cpure.formula)list))) option = 
    let sat_subno = ref 0 in
	let rec get_pure (f:Cformula.formula):(Cpure.formula*((string*Cpure.formula) list)) = match f with
		| Cformula.Or b->
				let b1,br1 = (get_pure b.Cformula.formula_or_f1) in
				let b2,br2 = (get_pure b.Cformula.formula_or_f2) in
				((Cpure.mkOr b1 b2 no_pos), Cpure.or_branches br1 br2)
		| Cformula.Base b -> (b.Cformula.formula_base_pure, b.Cformula.formula_base_branches)
		| Cformula.Exists b-> let l = List.map (fun (c1,c2)-> (c1, Cpure.mkExists b.Cformula.formula_exists_qvars c2 no_pos)) b.Cformula.formula_exists_branches in
					(Cpure.mkExists b.Cformula.formula_exists_qvars b.Cformula.formula_exists_pure no_pos, l)

	and symp_struc_to_formula (f0:Cformula.struc_formula):(Cpure.formula*((string*Cpure.formula) list)) = 
		let rec ext_to_formula (f:Cformula.ext_formula):(Cpure.formula*((string*Cpure.formula) list)) = match f with
			| Cformula.ECase b-> 
				if (List.length b.Cformula.formula_case_branches) <>1 then Error.report_error { Err.error_loc = no_pos; Err.error_text = "error: base case filtering malfunction"}
				else 
					let c1,c2 = List.hd b.Cformula.formula_case_branches in (*push existential dismissed*)
					let b2,br2 = (symp_struc_to_formula c2) in
					 ((Cpure.mkOr (Cpure.Not (c1,no_pos)) b2 no_pos),br2)
			| Cformula.EBase b-> 
					let b1,br1 = (get_pure b.Cformula.formula_ext_base) in
					let b2,br2 = (symp_struc_to_formula b.Cformula.formula_ext_continuation) in
					let r1 = Cpure.mkAnd b1 b2 no_pos in
					let r2 = Cpure.merge_branches br1 br2 in
					let ev = (*b.Cformula.formula_ext_explicit_inst@b.Cformula.formula_ext_implicit_inst@*)b.Cformula.formula_ext_exists in
					let r2 = List.map (fun (c1,c2)-> (c1,(Cpure.mkExists ev c2 no_pos))) r2 in
					let r1 = (Cpure.mkExists ev r1 no_pos) in
					(r1,r2)
			| _ -> Error.report_error { Err.error_loc = no_pos; Err.error_text = "error: view definitions should not contain assume formulas"}in	
		if (List.length f0)<>1 then ((Cpure.mkTrue no_pos),[])
		else ext_to_formula (List.hd f0)  in
	
	match (List.hd f) with
	| Cformula.EBase b-> 
		let ba,br = symp_struc_to_formula f in
		let ba' = Cpure.add_null ba self in
		let is_sat = if br = [] then 
			let sat = TP.is_sat ba' ((string_of_int !Solver.sat_no) ^ "." ^ (string_of_int !sat_subno)) in
			(Debug.devel_pprint ("SAT #" ^ (string_of_int !Solver.sat_no) ^ "." ^ (string_of_int !sat_subno)) no_pos;
			sat_subno := !sat_subno+1;
			sat)
        else 
			let sat = (TP.is_sat ba' ((string_of_int !Solver.sat_no) ^ "." ^ (string_of_int !sat_subno))) in
			Debug.devel_pprint ("SAT #" ^ (string_of_int !Solver.sat_no) ^ "." ^ (string_of_int !sat_subno)) no_pos;
			sat_subno := !sat_subno+1;
			if not sat then 
				false
			else List.for_all (fun (_,c)-> 
				let sat = TP.is_sat (Cpure.add_null c self) ((string_of_int !Solver.sat_no) ^ "." ^ (string_of_int !sat_subno)) in
				Debug.devel_pprint ("SAT #" ^ (string_of_int !Solver.sat_no) ^ "." ^ (string_of_int !sat_subno)) no_pos;
				sat_subno := !sat_subno+1;
				sat) br in
		if (not is_sat) then None
		else
		(*let saset = Solver.get_aset (Solver.alias(Solver.ptr_equations ba)) self in*)
			let ba' = Cpure.drop_null ba self false in
			let br' = List.map (fun (c1,c2)-> (c1,(Cpure.drop_null c2 self false)) ) br in
			let base_case = Cpure.BForm (Cpure.Eq ((Cpure.Var (self,no_pos)),(Cpure.Null no_pos),no_pos)) in
			Some (base_case,(ba',br'))		
	| Cformula.ECase b-> if (List.length b.Cformula.formula_case_branches) <>1 then Error.report_error { Err.error_loc = no_pos; Err.error_text = "error: base case filtering malfunction"}
				else 
					let (c1,c2) = List.hd b.Cformula.formula_case_branches in
					Some(c1,(symp_struc_to_formula c2))
	| _ -> Error.report_error 
	{ Err.error_loc = no_pos; Err.error_text = "error: view definitions should not contain assume formulas"}

		
and compute_base_case (*recs*) (cf:Cformula.struc_formula) : Cformula.struc_formula option = 
 (*let isRec (d:Cformula.formula): bool = 
		(List.length(List.filter (fun c -> List.mem c recs)(Cformula.view_node_types d)))>0 in*)
 let rec helper (cf:Cformula.ext_formula) : Cformula.struc_formula option = match cf with
	| Cformula.ECase b -> 
		let l = List.fold_left (fun a (c1,c2) -> 
								match (compute_base_case c2 ) with
									| None -> a (*(c1,[(Cformula.mkEFalse pos)]) *)
									| Some s ->(c1,s)::a) [] b.Cformula.formula_case_branches in
		if ((List.length l) > 0) then Some [(Cformula.ECase {b with Cformula.formula_case_branches = [List.hd l]})]
		else None		
	| Cformula.EBase b -> begin
		match (Cformula.filter_heap b.Cformula.formula_ext_base) with
		| None -> None
		| Some d-> 
			if (List.length b.Cformula.formula_ext_continuation )>0 then
			match (compute_base_case b.Cformula.formula_ext_continuation ) with
				| None -> None
				| Some s -> Some [(Cformula.EBase {b with Cformula.formula_ext_continuation = s; Cformula.formula_ext_base=d })]
			else Some [(Cformula.EBase {b with Cformula.formula_ext_continuation = []; Cformula.formula_ext_base=d })]
		end
	| Cformula.EAssume b-> Err.report_error{ Err.error_loc = no_pos; Err.error_text = "error: view definitions should not contain assume formulas"} in
 match (List.length cf) with
	| 0 -> None
	| 1 -> helper (List.hd cf)
	| _ -> let l = List.fold_left (fun a c-> 
								match helper c with 
									| None -> a
									| Some d -> d@a ) [] cf in
			match (List.length l) with
			| 1 -> Some l
			| _ -> None

and set_materialized_vars prog cdef =
  let mvars =
    find_materialized_vars prog cdef.C.view_vars (*cdef.C.view_formula*) cdef.C.view_un_struc_formula
  in
 (cdef.C.view_materialized_vars <- mvars; cdef)

and find_materialized_vars prog params (f0 : CF.formula) : CP.spec_var list =
  let tmp0 = find_mvars prog params f0 in
  let all_mvars = ref tmp0 in
  let ef = ref f0 in
  let quit_loop = ref false
  in
    (while not !quit_loop do ef := Solver.expand_all_preds prog !ef true;
       (let tmp1 = find_mvars prog params !ef in
        let tmp2 = CP.remove_dups (tmp1 @ !all_mvars) in
        let tmp3 = CP.difference tmp2 !all_mvars
        in if U.empty tmp3 then quit_loop := true else all_mvars := tmp3)
       done;
     !all_mvars)

and find_mvars prog (params : CP.spec_var list) (f0 : CF.formula) :
  CP.spec_var list =
  match f0 with
  | CF.Or { CF.formula_or_f1 = f1; CF.formula_or_f2 = f2 } ->
      let mvars1 = find_mvars prog params f1 in
      let mvars2 = find_mvars prog params f2 in
      let mvars = CP.remove_dups (mvars1 @ mvars2) in
      let tmp = CP.intersect mvars params in tmp
  | CF.Base { CF.formula_base_heap = hf; CF.formula_base_pure = pf } ->
      let mvars = find_mvars_heap prog params hf pf in
      let tmp = CP.intersect mvars params in tmp
  | CF.Exists
      {
        CF.formula_exists_qvars = qvars;
        CF.formula_exists_heap = hf;
        CF.formula_exists_pure = pf
      } ->
      let mvars1 = find_mvars_heap prog params hf pf in
      let mvars = CP.difference mvars1 qvars in
      let tmp = CP.intersect mvars params in tmp

and find_mvars_heap prog params hf pf =
  match hf with
  | CF.HTrue | CF.HFalse -> []
  | _ ->
      let eqns = Solver.ptr_equations pf in
      let asets = Context.alias eqns in
      let self_aset =
        Context.get_aset asets (CP.SpecVar (CP.OType "", self, Unprimed))
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
        (
			E.push_scope ();
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
          let cret_type =
            trans_type prog proc.I.proc_return proc.I.proc_loc in
          let free_vars = List.map (fun p -> p.I.param_name) all_args in
          let stab = H.create 103 in
          let add_param p =
            H.add stab p.I.param_name
              {
                sv_info_kind =
                  Known (trans_type prog p.I.param_type p.I.param_loc);
				id = fresh_int ()
              }
          in
            (ignore (List.map add_param all_args);
			 let _ = H.add stab res { sv_info_kind = Known cret_type;id = fresh_int () } in
			 let static_specs_list = trans_struc_formula prog true free_vars proc.I.proc_static_specs stab true cret_type in
			(* let _ = print_string ("\n new specs: "^(Cprinter.string_of_struc_formula static_specs_list)^"\n") in*)
			 let dynamic_specs_list = trans_struc_formula prog true free_vars proc.I.proc_dynamic_specs stab true cret_type in
			 let _ = H.remove stab res in
             let body =
               match proc.I.proc_body with
               | None -> None
               | Some e -> let (b, tb) = trans_exp prog proc e in Some b in
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
			 let static_specs_list  = Cformula.plug_ref_vars static_specs_list by_names in
			 let dynamic_specs_list = Cformula.plug_ref_vars dynamic_specs_list by_names in
             let final_static_specs_list =
               if U.empty static_specs_list
               then Cast.mkEAssume proc.I.proc_loc
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
				 C.proc_static_specs_with_pre =  [];
				 C.proc_dynamic_specs_with_pre =  [];
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
  let _ = collect_type_info_formula prog coer.I.coercion_head stab in
  let _ = collect_type_info_formula prog coer.I.coercion_body stab in
  (*let _ = print_string ("\n"^(string_of_stab stab)^"\n") in*)
  let c_lhs = trans_formula prog false [ self ] false coer.I.coercion_head stab in
  let lhs_fnames = List.map CP.name_of_spec_var (CF.fv c_lhs) in
  let compute_univ () =
    let (h, p, _, _) = CF.split_components c_lhs in
    let pvars = CP.fv p in
    let hvars = CF.h_fv h in
    let univ_vars = CP.difference pvars hvars in CP.remove_dups univ_vars in
  let univ_vars = compute_univ () in
  let lhs_fnames =
    Util.difference lhs_fnames (List.map CP.name_of_spec_var univ_vars) in
  let c_rhs =
    trans_formula prog (U.empty univ_vars) (self :: lhs_fnames) false
      coer.I.coercion_body stab in
  let rhs_fnames = List.map CP.name_of_spec_var (CF.fv c_rhs) in
  let c_lhs_exist =
    trans_formula prog true (self :: rhs_fnames) false coer.I.coercion_head stab in
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

and trans_exp (prog : I.prog_decl) (proc : I.proc_decl) (ie : I.exp) :
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
           (List.map (fun (t, n) -> H.add stab n { sv_info_kind = Known t;id = fresh_int () })
              all_names);
         let assert_cf_o =
           (match assert_f_o with
            | Some f -> Some (trans_struc_formula prog false free_vars (fst f) stab false (Cpure.Prim Void))
            | None -> None) in
         let assume_cf_o =
           (match assume_f_o with
            | None -> None
            | Some f -> Some (trans_formula prog false free_vars true f stab)) in
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
                let (ce1, te1) = trans_exp prog proc lhs in
                let (ce2, te2) = trans_exp prog proc rhs
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
                let (rhs_c, rhs_t) = trans_exp prog proc rhs in
                let (fn, new_var) =
                  (match rhs_c with
                   | C.Var { C.exp_var_name = v } -> (v, false)
                   | _ -> let fn = (fresh_var_name (Cprinter.string_of_typ rhs_t) pos.start_pos.Lexing.pos_lnum) in (fn, true)) in
                let fn_var =
                  C.Var
                    {
                      C.exp_var_type = rhs_t;
                      C.exp_var_name = fn;
                      C.exp_var_pos = pos;
                    } in
                let (tmp_e, tmp_t) =
                  flatten_to_bind prog proc base_e (List.rev fs)
                    (Some fn_var) pos in
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
           in trans_exp prog proc new_assign)
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
         in trans_exp prog proc new_e)
      else
        (let b_call = get_binop_call b_op in
         let new_e =
           I.CallNRecv
             {
               I.exp_call_nrecv_method = b_call;
               I.exp_call_nrecv_arguments = [ e1; e2 ];
               I.exp_call_nrecv_pos = pos;
             }
         in trans_exp prog proc new_e)
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
                          let (ce, te) = trans_exp prog proc e in
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
       let (ce, te) = trans_exp prog proc e in
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
      let (crecv, crecv_t) = trans_exp prog proc recv in
      let (recv_ident, recv_init, new_recv_ident) =
        (match crecv with
         | C.Var { C.exp_var_name = v } -> (v, (C.Unit pos), false)
         | _ ->
             let fname = (fresh_var_name (Cprinter.string_of_typ crecv_t) (pos.start_pos.Lexing.pos_lnum)) in
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
      let tmp = List.map (trans_exp prog proc) args in
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
      let tmp = List.map (trans_exp prog proc) args in
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
           in trans_exp prog proc call_recv)
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
                         in trans_exp prog proc inlined_exp)
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
                            ret_ct)))
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
      let (ce1, te1) = trans_exp prog proc e1
      in
        if not (CP.are_same_types te1 C.bool_type)
        then
          Err.report_error
            {
              Error.error_loc = pos;
              Error.error_text = "conditional expression is not bool";
            }
        else
          (let (ce2', te2) = trans_exp prog proc e2 in
           let (ce3', te3) = trans_exp prog proc e3 in
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
                 let fn = (fresh_var_name "bool" pos.start_pos.Lexing.pos_lnum) in
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
      } -> flatten_to_bind prog proc e (List.rev fs) None pos
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
          (let tmp = List.map (trans_exp prog proc) args in
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
             let (ce, ct) = trans_exp prog proc e
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
      let (ce1', te1) = trans_exp prog proc e1 in
      let (ce2, te2) = trans_exp prog proc e2 in
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
           in trans_exp prog proc call_e
       | I.OpPostInc ->
           let fn = (fresh_var_name "int" pos.start_pos.Lexing.pos_lnum) in
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
             trans_exp prog proc
               (I.Block { I.exp_block_body = seq2; I.exp_block_pos = pos; })
       | I.OpPostDec ->
           let fn = (fresh_var_name "int" pos.start_pos.Lexing.pos_lnum) in
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
             trans_exp prog proc
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
             trans_exp prog proc
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
             trans_exp prog proc
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
                         let (tmp_e, tmp_t) = trans_exp prog proc e
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
      let (iw_call, _) = trans_exp new_prog w_proc w_call in
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
  flatten_to_bind prog proc (base : I.exp) (rev_fs : ident list)
                  (rhs_o : C.exp option) pos =
  match rev_fs with
  | f :: rest ->
      let (cbase, base_t) = flatten_to_bind prog proc base rest None pos in
      let (fn, new_var) =
        (match cbase with
         | C.Var { C.exp_var_name = v } -> (v, false)
         | _ -> let fn2 = (fresh_var_name (Cprinter.string_of_typ base_t) pos.start_pos.Lexing.pos_lnum) in (fn2, true)) in
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
             let fresh_fn = (snd f) ^"_"^(string_of_int pos.start_pos.Lexing.pos_lnum)^ fn1 in
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
  | [] -> trans_exp prog proc base

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
               let fresh_fn = (snd f)^(string_of_int pos.start_pos.Lexing.pos_lnum) ^ fn in
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
             let fn = fresh_var_name (Cprinter.string_of_typ at) pos.start_pos.Lexing.pos_lnum in
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
             (let fn = fresh_var_name (Cprinter.string_of_typ t) pos.start_pos.Lexing.pos_lnum in
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

and case_coverage (instant:Cpure.spec_var list)(f:Cformula.struc_formula): bool =
	let sat_subno  = ref 0 in
	let rec ext_case_coverage (instant:Cpure.spec_var list)(f1:Cformula.ext_formula):bool = match f1 with
		| Cformula.EAssume b ->  true
		| Cformula.EBase b -> case_coverage (instant@
											(b.Cformula.formula_ext_explicit_inst)@
											(b.Cformula.formula_ext_implicit_inst)@
											(b.Cformula.formula_ext_exists)
											)b.Cformula.formula_ext_continuation
		| Cformula.ECase b -> 
			let r1,r2 = List.split b.Cformula.formula_case_branches in
			let all = List.fold_left (fun a c->(Cpure.mkOr a c no_pos) ) (Cpure.mkFalse b.Cformula.formula_case_pos) r1  in
			let _ = if not(Util.subset (Cpure.fv all) instant) then 
					let _ = print_string (
					(List.fold_left (fun a c1-> a^" "^ (Cprinter.string_of_spec_var c1)) "\nall:" (Cpure.fv all))^"\n"^
					(List.fold_left (fun a c1-> a^" "^ (Cprinter.string_of_spec_var c1)) "instant:" instant)^"\n")in			
			Error.report_error {  Err.error_loc = b.Cformula.formula_case_pos;
                    	Err.error_text = "all guard free vars must be instantiated";} in
			let _ = 
				let sat = Tpdispatcher.is_sat(Cpure.Not (all,no_pos)) ((string_of_int !Solver.sat_no) ^ "." ^ (string_of_int !sat_subno)) in
				Debug.devel_pprint ("SAT #" ^ (string_of_int !Solver.sat_no) ^ "." ^ (string_of_int !sat_subno)) no_pos;
				sat_subno := !sat_subno+1;
				if sat then Error.report_error {  Err.error_loc = b.Cformula.formula_case_pos;
                    	Err.error_text = "the guards don't cover the whole domain";} 	in
											
			let rec p_check (p:Cpure.formula list):bool = match p with
				| [] -> false 
				| p1::p2 -> if (List.fold_left (fun a c-> 
					let sat =  Tpdispatcher.is_sat(Cpure.mkAnd p1 c no_pos) ((string_of_int !Solver.sat_no) ^ "." ^ (string_of_int !sat_subno)) in
					Debug.devel_pprint ("SAT #" ^ (string_of_int !Solver.sat_no) ^ "." ^ (string_of_int !sat_subno)) no_pos;
					sat_subno := !sat_subno+1;
					a ||sat) false p2 ) then true else p_check p2 in
				
			let _ = if (p_check r1) then Error.report_error {  Err.error_loc = b.Cformula.formula_case_pos;
                    	Err.error_text = "the guards are not disjoint";} in
											
			let _ = List.map (case_coverage instant) r2 in true	in
	let _ = List.map (ext_case_coverage instant) f in true

and trans_var (ve, pe) stab pos =try
         let ve_info = H.find stab ve
         in
           (match ve_info.sv_info_kind with
            | Known t -> CP.SpecVar (t, ve, pe)
            | Unknown ->
                Err.report_error
                  {
                    Err.error_loc = pos;
                    Err.error_text = "couldn't infer type for " ^ ve^(match pe with |Unprimed->""|Primed -> "'")^" in "^(string_of_stab stab)^"\n";
                  })
				with Not_found ->   
					Err.report_error
                  {
                    Err.error_loc = pos;
                    Err.error_text = "couldn't infer type for " ^ ve^(match pe with |Unprimed->""|Primed -> "'")^" in "^(string_of_stab stab)^"\n, could it be an unused var?\n";
                  }			
  
and add_pre (prog :C.prog_decl) (f:Cformula.struc_formula):Cformula.struc_formula = 
	let rec inner_add_pre (pf:Cpure.formula) (branches: (branch_label * CP.formula) list) (f:Cformula.struc_formula): Cformula.struc_formula =
			let rec helper (pf:Cpure.formula) (branches: (branch_label * CP.formula) list) (f:Cformula.ext_formula):Cformula.ext_formula=
			match f with
				| Cformula.ECase ({
							Cformula.formula_case_branches = cb;				
							} as b) ->
					Cformula.ECase
						{
							b 
							with 
								Cformula.formula_case_branches = List.map (fun (c1,c2)->
									(c1,(inner_add_pre (Cpure.mkAnd c1 pf no_pos) branches c2))) cb}
				 
				| Cformula.EBase({
					 Cformula.formula_ext_exists = ext_exists_vars;
					 Cformula.formula_ext_base = fb;
					 Cformula.formula_ext_continuation = fc;} as b)	->
					 let (xpure_pre2_prim, xpure_pre2_prim_b) = Solver.xpure_consumed_pre prog fb in
					 let new_pf = Cpure.mkAnd pf (Cpure.mkExists ext_exists_vars xpure_pre2_prim no_pos) no_pos in
					 let new_branches = Cpure.merge_branches (Cpure.mkExistsBranches ext_exists_vars xpure_pre2_prim_b no_pos) branches in
					 Cformula.EBase{b with 
						Cformula.formula_ext_continuation = inner_add_pre new_pf new_branches fc;
					 }
				| Cformula.EAssume (ref_vars, bf) ->
					Cformula.EAssume (ref_vars, (Cformula.normalize bf (CF.replace_branches branches (CF.formula_of_pure pf no_pos)) no_pos))
			in	List.map (helper pf branches ) f 
    in inner_add_pre (Cpure.mkTrue no_pos) [] f
  
and trans_struc_formula (prog : I.prog_decl) (quantify : bool) (fvars : ident list)
  (f0 : Iformula.struc_formula) stab (sp:bool)(cret_type:Cpure.typ): Cformula.struc_formula = 
	let rec trans_struc_formula_hlp (f0 : IF.struc_formula)(fvars : ident list) :CF.struc_formula = 
	(*let _ = print_string ("\n formula: "^(Iprinter.string_of_struc_formula "" f0)^"\n pre trans stab: "^(string_of_stab stab)^"\n") in*)
		let rec trans_ext_formula (f0 : IF.ext_formula) stab : CF.ext_formula = match f0 with
			| Iformula.EAssume b->	(*add res, self*)
					 (*let _ = H.add stab res { sv_info_kind = Known cret_type; } in*)
					 let nb = trans_formula prog true (self::res::fvars) false b stab in				
					 (*let _ = H.remove stab res in*)
					Cformula.EAssume ([],nb)
			| Iformula.ECase b-> 	
				Cformula.ECase {
					Cformula.formula_case_exists = [];
					Cformula.formula_case_branches = List.map (fun (c1,c2)-> ((Cpure.arith_simplify (trans_pure_formula c1 stab)),
						(trans_struc_formula_hlp c2 fvars)))
						 b.Iformula.formula_case_branches;
					Cformula.formula_case_pos = b.Iformula.formula_case_pos}			
			| Iformula.EBase b-> 			
				let nc = trans_struc_formula_hlp b.Iformula.formula_ext_continuation 
								(fvars @ (fst (List.split(Iformula.heap_fv b.Iformula.formula_ext_base))))in
				let nb = trans_formula prog quantify fvars false b.Iformula.formula_ext_base stab in
				let ex_inst = List.map (fun c-> trans_var c stab b.Iformula.formula_ext_pos) b.Iformula.formula_ext_explicit_inst in
				let ext_impl = List.map (fun c-> trans_var c stab b.Iformula.formula_ext_pos) b.Iformula.formula_ext_implicit_inst in
				let ext_exis = List.map (fun c-> trans_var c stab b.Iformula.formula_ext_pos) b.Iformula.formula_ext_exists in
				Cformula.EBase {
					Cformula.formula_ext_explicit_inst = ex_inst;
				 	Cformula.formula_ext_implicit_inst = ext_impl;
					Cformula.formula_ext_exists = ext_exis;
				 	Cformula.formula_ext_base = nb;
				 	Cformula.formula_ext_continuation = nc;
				 	Cformula.formula_ext_pos = b.Iformula.formula_ext_pos} in
		let r = List.map (fun c-> trans_ext_formula c stab) f0 in
		r in
	let _ = collect_type_info_struc_f prog f0 stab in	
	let r = trans_struc_formula_hlp f0 fvars in
	let cfvhp1 = List.map (fun c-> trans_var (c,Primed) stab (Iformula.pos_of_struc_formula f0)) fvars in
	let cfvhp2 = List.map (fun c-> trans_var (c,Unprimed) stab (Iformula.pos_of_struc_formula f0)) fvars in
	let cfvhp = cfvhp1@cfvhp2 in
	let _ = case_coverage cfvhp r in
	let tmp_vars  =  (Cformula.struc_post_fv r) in 
	let post_fv = List.map CP.name_of_spec_var tmp_vars in
	let pre_fv = List.map CP.name_of_spec_var (Util.difference (Cformula.struc_fv r) tmp_vars) in
	let r = if ((List.mem self pre_fv) || (List.mem self post_fv))&&sp then
                   Err.report_error { Err.error_loc = Cformula.pos_of_struc_formula r; Err.error_text ="self is not allowed in pre/postcondition";}
                 else if List.mem res pre_fv then
                     Err.report_error{ Err.error_loc = Cformula.pos_of_struc_formula r; Err.error_text = "res is not allowed in precondition";}
                   else if sp then
						(try
                        let resinfo = H.find stab res in
                          match resinfo.sv_info_kind with
                          | Known t ->
                              if sub_type t cret_type
                              then r
                              else
                                Err.report_error{Err.error_loc = Cformula.pos_of_struc_formula r;Err.error_text ="res is used inconsistently";}
                          | Unknown ->Err.report_error{Err.error_loc = Cformula.pos_of_struc_formula r;Err.error_text = "can't infer type for res";}
                      with | Not_found -> r)
					  else r  in
	let _ = type_store_clean_up r stab in
	r
			  
and trans_formula (prog : I.prog_decl) (quantify : bool) (fvars : ident list) sep_collect
  (f0 : IF.formula) stab : CF.formula =
  (*let f3 = convert_heap2 prog f0 in*)
	(*let _ = print_string ("pre: "^(Iprinter.string_of_formula f3)^"\n post: "^(Iprinter.string_of_formula f1)^"\n") in*)
  (*let f2 =
    if quantify || !Globals.anon_exist
    then convert_anonym_to_exist f1
    else f1
  in *)
 (* let ret = trans_formula1 prog quantify fvars sep_collect f0 stab in
  ret

and trans_formula1 prog quantify fvars sep_collect f0 stab : CF.formula =*)
  match f0 with
  | IF.Or
      { IF.formula_or_f1 = f1; IF.formula_or_f2 = f2; IF.formula_or_pos = pos
      } ->
      let tf1 = trans_formula prog quantify fvars sep_collect f1 stab in
      let tf2 = trans_formula prog quantify fvars sep_collect f2 stab
      in CF.mkOr tf1 tf2 pos
  | IF.Base
      {
        IF.formula_base_heap = h;
        IF.formula_base_pure = p;
        IF.formula_base_branches = br;
        IF.formula_base_pos = pos
      } ->
      (let _ = if sep_collect then 
	   (collect_type_info_pure (IF.flatten_branches p br) stab;
		collect_type_info_heap prog h stab) else () in 
       let ch = linearize_formula prog f0 stab in
       (*let ch1 = linearize_formula prog false [] f0 stab in*)
         let _ = if sep_collect then (if quantify
          then
            (let tmp_stab = H.create 103
             in
               (U.copy_keys fvars stab tmp_stab;
                H.clear stab;
                U.copy_keys fvars tmp_stab stab))
          else ()) else () in 
          ch)
  | IF.Exists
      {
        IF.formula_exists_qvars = qvars;
        IF.formula_exists_heap = h;
        IF.formula_exists_pure = p;
        IF.formula_exists_branches = br;
        IF.formula_exists_pos = pos
      } ->
      (let _ = if sep_collect then (collect_type_info_pure (IF.flatten_branches p br) stab;
		collect_type_info_heap prog h stab) else () in 
       let f1 =
         IF.Base
           {
             IF.formula_base_heap = h;
             IF.formula_base_pure = p;
             IF.formula_base_branches = br;
             IF.formula_base_pos = pos;
           } in
       let ch = linearize_formula prog f1 stab in
       let qsvars = List.map (fun qv -> trans_var qv stab pos) qvars in
       let ch = CF.push_exists qsvars ch in
        let _ = if sep_collect then(if quantify
          then
            (let tmp_stab = H.create 103 in
             let fvars = (List.map fst qvars) @ fvars
             in
               (U.copy_keys fvars stab tmp_stab;
                H.clear stab;
                U.copy_keys fvars tmp_stab stab))
          else ())else () in
          ch)
and
  linearize_formula (prog : I.prog_decl)  (f0 : IF.formula)(stab : spec_var_table) =		
  let rec match_exp (hargs : (IP.exp * branch_label) list) pos : (CP.spec_var list) =
    match hargs with
    | (e, label) :: rest ->
        let e_hvars = match e with
           | IP.Var ((ve, pe), pos_e) -> trans_var (ve, pe) stab pos_e
           | _ -> Err.report_error { Err.error_loc = (Iformula.pos_of_formula f0); Err.error_text = ("malfunction with float out exp: "^(Iprinter.string_of_formula f0)); }in
        let rest_hvars = match_exp rest pos in
        let hvars = e_hvars :: rest_hvars in
		hvars
    | [] -> [] in
  let rec linearize_heap (f : IF.h_formula) pos : ( CF.h_formula * CF.t_formula) =    match f with
    | IF.HeapNode2 h2 -> Err.report_error { Err.error_loc = (Iformula.pos_of_formula f0); Err.error_text = "malfunction with convert to heap node"; }
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
           let labels = vdef.I.view_labels in
           (*let tmpp = List.combine exps labels in*)
           let hvars = match_exp (List.combine exps labels) pos in
           let c0 =
             if vdef.I.view_data_name = "" then 
				(fill_view_param_types prog vdef;
				 (*let _ = trans_view prog vdef in*)
				 vdef.I.view_data_name)
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
           in (new_h, CF.TypeTrue)
         with
         | Not_found ->
             let labels = List.map (fun _ -> "") exps in
             let hvars = match_exp (List.combine exps labels) pos in
             let new_v = CP.SpecVar (CP.OType c, v, p) in
             let new_h =
               CF.DataNode
                 {
                   CF.h_formula_data_node = new_v;
                   CF.h_formula_data_name = c;
                   CF.h_formula_data_arguments = hvars;
                   CF.h_formula_data_pos = pos;
                 }
             in ( new_h, CF.TypeTrue))
    | IF.Star
        {
          IF.h_formula_star_h1 = f1;
          IF.h_formula_star_h2 = f2;
          IF.h_formula_star_pos = pos
        } ->
        let (lf1, type1) = linearize_heap f1 pos in
        let (lf2, type2) = linearize_heap f2 pos in
        let tmp_h = CF.mkStarH lf1 lf2 pos in
        let tmp_type = CF.mkAndType type1 type2 in 
		(tmp_h, tmp_type)
    | IF.HTrue ->  (CF.HTrue, CF.TypeTrue)
    | IF.HFalse -> (CF.HFalse, CF.TypeFalse) in
  let linearize_base base pos =
    let h = base.IF.formula_base_heap in
    let p = base.IF.formula_base_pure in
    let br = base.IF.formula_base_branches in
    let pos = base.IF.formula_base_pos in
    let (new_h, type_f) = linearize_heap h pos in
    let new_p = trans_pure_formula p stab in
    let new_p = Cpure.arith_simplify new_p in
    let new_br = List.map (fun (l, f) -> (l, (trans_pure_formula f stab))) br in
    let new_br = List.map (fun (l, f) -> (l, Cpure.arith_simplify f)) new_br in
    (new_h, new_p, type_f, new_br) in
    match f0 with
    | IF.Or
        {
          IF.formula_or_f1 = f1;
          IF.formula_or_f2 = f2;
          IF.formula_or_pos = pos
        } ->
        let lf1 = linearize_formula prog f1 stab in
        let lf2 = linearize_formula prog f2 stab in
        let result = CF.mkOr lf1 lf2 pos in result
    | IF.Base base -> 
		let nh,np,nt,nb = (linearize_base base base.Iformula.formula_base_pos) in
		CF.mkBase nh np nt nb base.Iformula.formula_base_pos 
    | IF.Exists
        {
          IF.formula_exists_heap = h; 
          IF.formula_exists_pure = p;
          IF.formula_exists_branches = br;
		  IF.formula_exists_qvars = qvars;
          IF.formula_exists_pos = pos
        } ->
        let base ={
            IF.formula_base_heap = h;
            IF.formula_base_pure = p;
            IF.formula_base_branches = br;
            IF.formula_base_pos = pos;
          } in 
		let nh,np,nt,nb = linearize_base base pos in
		CF.mkExists (List.map (fun c-> trans_var c stab pos) qvars) nh np nt nb pos 
		

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
      let v_type = Cpure.type_of_spec_var (trans_var (v,Unprimed) stab pos) in
      let sv = CP.SpecVar (v_type, v, p) in CP.mkForall [ sv ] pf pos
  | IP.Exists ((v, p), f, pos) ->
      let pf = trans_pure_formula f stab in
      let sv = trans_var (v,p) stab pos in
	  CP.mkExists [ sv ] pf pos

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
      in CP.BagIn ((trans_var (v,p) stab pos), pe, pos)
  | IP.BagNotIn ((v, p), e, pos) ->
      let pe = trans_pure_exp e stab
      in CP.BagNotIn ((trans_var (v,p) stab pos), pe, pos)
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
  | IP.Var ((v, p), pos) -> CP.Var ((trans_var (v,p) stab pos),pos)
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
  with | Not_found -> (H.add stab var { sv_info_kind = k;id = (fresh_int ()) }; H.find stab var)

and set_var_kind2 (var1 : ident) (var2 : ident) (k : spec_var_kind) (stab : spec_var_table) =
	let r1 = try  Some (H.find stab var1) with | Not_found ->None in 
	let r2 = try  Some (H.find stab var2) with | Not_found ->None in 
	let _ = match (r1,r2) with
	| None, None -> let c = { sv_info_kind = k; id = fresh_int ()} in
						(H.add stab var1 c;H.add stab var2 c)
	| ((Some a1) , None) ->	(a1.sv_info_kind <- k ; (H.add stab var2 a1))
	| None , (Some a2) ->   (a2.sv_info_kind <- k ; (H.add stab var1 a2))
	| (Some a1) , (Some a2) -> (a1.sv_info_kind <-k ; 
							let a2_keys = Hashtbl.fold (fun i v a-> if (v.id = a2.id) then i::a else a) stab [] in
							let _ = List.map (fun c-> Hashtbl.replace stab c a1) a2_keys in ()) in ()
(*H.find stab var let r = set_var_kind va1 k stab in H.replace stab va2 r*)

  
and collect_type_info_var (var : ident) stab (var_kind : spec_var_kind) pos =
  try
    let k = H.find stab var in
    let tmp = unify_var_kind k.sv_info_kind var_kind
    in
      match tmp with
      | Some tmp_k -> k.sv_info_kind <- tmp_k
      | None -> report_error pos (var ^ " is used inconsistently")
  with | Not_found -> H.add stab var { sv_info_kind = var_kind; id = fresh_int ()}

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
       collect_type_info_arith a3 stab)
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
	let _ = 
      if (IP.is_var a1) && (IP.is_var a2)
      then
        (let va1 = IP.name_of_var a1 in
         let va2 = IP.name_of_var a2 in
         let k1 = get_var_kind va1 stab in
         let k2 = get_var_kind va2 stab in
         let r = unify_var_kind k1 k2 in
		 (*let _ = print_string ("\n equality: "^va1^" "^va2^" "^(string_of_var_kind k1)^"  "^(string_of_var_kind k2)^" "^
		  (match r with | None -> "" |Some r -> (string_of_var_kind r))^"\n") in*)
           match r with
           | Some k ->
				set_var_kind2 va1 va2 k stab 
               (*let r = set_var_kind va1 k stab in H.replace stab va2 r*)
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
                (collect_type_info_pointer a1' (Known (CP.OType "")) stab))
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
                } in
	(*let _ = print_string ("\n new stab: "^(string_of_stab stab)^"\n") in *)()

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

and collect_type_info_formula prog f0 stab = 
	(*let _ = print_string ("collecting types for:\n"^(Iprinter.string_of_formula f0)^"\n") in*)
	match f0 with
	| Iformula.Or b-> ( collect_type_info_formula prog b.Iformula.formula_or_f1 stab;
						collect_type_info_formula prog b.Iformula.formula_or_f2 stab)
	| Iformula.Exists b -> (collect_type_info_pure b.Iformula.formula_exists_pure stab;
							let _ = List.map (fun (c1,c2)->collect_type_info_pure c2 stab) b.Iformula.formula_exists_branches in
							collect_type_info_heap prog b.Iformula.formula_exists_heap stab)
	| Iformula.Base b ->(collect_type_info_pure b.Iformula.formula_base_pure stab;
							let _ = List.map (fun (c1,c2)->collect_type_info_pure c2 stab) b.Iformula.formula_base_branches in
							collect_type_info_heap prog b.Iformula.formula_base_heap stab)

and type_store_clean_up (f:Cformula.struc_formula) stab = () (*if stab to big,  -> get list of quantified vars, remove them from stab*)
							
and collect_type_info_struc_f prog (f0:Iformula.struc_formula) stab = 
	let rec inner_collector (f0:Iformula.struc_formula) = 
		let rec helper (f0:Iformula.ext_formula) = match f0 with
			| Iformula.EAssume b-> let _ = collect_type_info_formula prog b stab in ()
			| Iformula.ECase b ->  let _ = List.map (fun (c1,c2)->
											let _ = collect_type_info_pure c1 stab in
											inner_collector c2) b.Iformula.formula_case_branches in ()
			| Iformula.EBase b ->  
								   let _ = collect_type_info_formula prog b.Iformula.formula_ext_base stab in
								   let _ = inner_collector b.Iformula.formula_ext_continuation in ()								
			in
		let _ = List.map helper f0 in 
		() in
	inner_collector f0

		
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
			  let _ = if (String.length vdef.I.view_data_name) = 0  then fill_view_param_types prog vdef in
			  (*let _ = print_string ("\n searching for: "^c^" got: "^vdef.I.view_data_name^"-"^vdef.I.view_name^"-\n") in*)
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
				  (*let _ = print_string (Iprinter.string_of_program prog) in*)
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
		(*let _ = print_string ("\nlf:"^c^"\nfnd:"^dname) in*)
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

and ilinearize_formula (f:Iformula.formula)(h:(ident*primed) list): Iformula.formula*((ident*primed) list) = 
	let fe = Iformula.all_fv f in
	let fh = Iformula.heap_fv f in
	let ex = Util.difference fh h in
	let need_quant = Util.difference fe (fh@h) in
	(*let _ = print_string ("\n\n rr: "^(Iprinter.string_of_formula f)^"\n"^
										(List.fold_left(fun a (c,d)-> a^" "^c^(Iprinter.string_of_primed d)) "" h)^"\n"
				) in
	let _  = print_string("\n\n all_fv"^
		(List.fold_left(fun a (c,d)-> a^" "^c^(Iprinter.string_of_primed d)) "" fe)^
		"\n"^
		(List.fold_left (fun a (c,d)-> a^" "^c^(Iprinter.string_of_primed d)) "" ex)^"\n")in*)
	let _ = if not (List.for_all(fun (c1,c2)->c2==Unprimed)ex) then Err.report_error{ 
													Err.error_loc = Iformula.pos_of_formula f; 
													Err.error_text = "existential vars should not be primed"; } in
	(*let h1 = Util.difference fe ex in*)	
	let f= Iformula.push_exists need_quant f in
	(match !Globals.instantiation_variants with 
		| 0
		| 3 
		| 5 ->((Iformula.push_exists ex f),ex) 
		| _ ->(f,ex))

and case_normalize_pure_formula hp b f = f

(*moved the liniarization to case_normalize_renamed_formula*)
and case_normalize_renamed_formula prog (h:(ident*primed) list)(b:bool)(f:Iformula.formula):Iformula.formula* ((ident*primed)list) = 
	(*existential wrapping and other magic tricks*)

	let rec match_exp (used_names : (ident*primed) list) (hargs : (IP.exp * branch_label) list) pos :
    (((ident*primed) list) * ((ident*primed) list) * ((ident*primed) list) * (IP.formula * (branch_label * IP.formula) list)) = match hargs with
    | (e, label) :: rest ->
        let (new_used_names, e_hvars, e_evars, (e_link, e_link_br)) = match e with
           | IP.Var (v, pos_e) ->
               (try
                  if (List.mem v h) || (List.mem v used_names) then(*existential wrapping and liniarization*)
                      (let fresh_v = (Ipure.fresh_old_name (fst v)),(snd v) in
                       let link_f = IP.mkEqExp (IP.Var (fresh_v,pos_e)) e pos_e in
                       let quantified_var = [ fresh_v ]
                       in (used_names, [ fresh_v ], quantified_var, if label = "" then (link_f, []) else (IP.mkTrue pos_e, [label, link_f])))
                    else
                      (let quantified_var = if b then [ v ] else []
                       in((v :: used_names), [ v ], quantified_var,(IP.mkTrue pos_e, [])))
                with
                | Not_found -> Err.report_error{ Err.error_loc = pos_e; Err.error_text = (fst v) ^ " is undefined"; })
           | _ -> Err.report_error { Err.error_loc = (Iformula.pos_of_formula f); Err.error_text = "malfunction with float out exp in normalizing"; } in
        let (rest_used_names, rest_hvars, rest_evars, (rest_link, rest_link_br)) = match_exp new_used_names rest pos in
        let hvars = e_hvars @ rest_hvars in
        let evars = e_evars @ rest_evars in
        let link_f = IP.mkAnd e_link rest_link pos in
        let link_f_br = IP.merge_branches e_link_br rest_link_br in
        (rest_used_names, hvars, evars, (link_f, link_f_br))
    | [] -> (used_names, [], [], ((IP.mkTrue pos), [])) in
	
	let rec linearize_heap (used_names:((ident*primed) list)) (f : IF.h_formula):
    (((ident*primed) list) * ((ident*primed) list) * Iformula.h_formula * (Ipure.formula * (branch_label * Ipure.formula) list)) =
	    match f with
	    | IF.HeapNode2 b -> Error.report_error {Error.error_loc = b.Iformula.h_formula_heap2_pos; Error.error_text = "malfunction: heap node 2 still present"}  
	    | IF.HeapNode b ->
			let pos = b.Iformula.h_formula_heap_pos in
	        let labels = try
	           let vdef = I.look_up_view_def_raw prog.I.prog_view_decls b.IF.h_formula_heap_name in
	           vdef.I.view_labels
			   with
				| Not_found ->List.map (fun _ -> "") b.Iformula.h_formula_heap_arguments in	
			let _ = if (List.length b.Iformula.h_formula_heap_arguments) != (List.length labels) then
				Error.report_error {Error.error_loc = pos; Error.error_text = "predicate "^b.IF.h_formula_heap_name^" does not have the correct number of arguments"}  
				in
	        let (new_used_names, hvars, evars, (link_f, link_f_br)) =
	             match_exp used_names (List.combine b.Iformula.h_formula_heap_arguments labels) pos in
			let hvars = List.map (fun c-> Ipure.Var (c,pos)) hvars in
	           let new_h = IF.HeapNode{ b with IF.h_formula_heap_arguments = hvars}
	           in (new_used_names, evars, new_h, (link_f, link_f_br))
	    | IF.Star
	        {
	          IF.h_formula_star_h1 = f1;
	          IF.h_formula_star_h2 = f2;
	          IF.h_formula_star_pos = pos
	        } ->
	        let (new_used_names1, qv1, lf1, (link1, link1_br)) =
	          linearize_heap used_names f1 in
	        let (new_used_names2, qv2, lf2, (link2, link2_br)) =
	          linearize_heap new_used_names1 f2 in
	        let tmp_h = IF.mkStar lf1 lf2 pos in
	        let tmp_link = IP.mkAnd link1 link2 pos in
	        let tmp_link_br = IP.merge_branches link1_br link2_br in
	        (new_used_names2, (qv1 @ qv2), tmp_h, (tmp_link, tmp_link_br))
	    | IF.HTrue ->  (used_names, [], IF.HTrue, (IP.mkTrue no_pos, []))
	    | IF.HFalse -> (used_names, [], IF.HFalse, (IP.mkTrue no_pos, [])) in
		
	
	let normalize_base heap p br pos : Iformula.formula* ((ident*primed)list) =
	    let (nu, h_evars, new_h, (link_f, link_f_br)) = linearize_heap [] heap in
	    let cp = case_normalize_pure_formula h b p in
	    let new_p = Ipure.mkAnd cp link_f pos in
	    let new_br = List.map (fun (l, f) -> (l, (case_normalize_pure_formula h b f))) br in
		let new_br = IP.merge_branches new_br link_f_br in
	    let tmp_evars =
	        (let tmp_evars1 = Ipure.fv cp in
	         let excluded_evars = h in
	         let tmp_evars2 = List.filter(fun c-> (not(List.mem c excluded_evars))&&((fst c)!=self)) (if b then h_evars @tmp_evars1 else h_evars) in
	         let tmp_evars3 = U.remove_dups tmp_evars2 in tmp_evars3)in
	    let result = Iformula.mkExists tmp_evars new_h new_p new_br pos in
		let used_vars = Util.difference nu tmp_evars in
	      if not (Util.empty tmp_evars)  then
	         Debug.pprint ("linearize_constraint: " ^
	              ((String.concat ", "
	                  (List.map fst tmp_evars))
	                 ^ " are quantified\n")) pos
	       else ();
		   (result,used_vars)  in  
	
	let rec helper (f:Iformula.formula):Iformula.formula* ((ident*primed)list) = match f with
	    | Iformula.Or b -> 
		let f1,l1 = (helper b.Iformula.formula_or_f1) in
		let f2,l2 = (helper b.Iformula.formula_or_f2) in
		(Iformula.Or {b with Iformula.formula_or_f1 = f1; Iformula.formula_or_f2 = f2}, (Util.remove_dups (l1@l2)))
	    | Iformula.Base b -> normalize_base  b.Iformula.formula_base_heap 
											   b.Iformula.formula_base_pure 
											   b.Iformula.formula_base_branches 
											   b.Iformula.formula_base_pos
	    | Iformula.Exists b-> normalize_base b.Iformula.formula_exists_heap 
											 b.Iformula.formula_exists_pure 
											 b.Iformula.formula_exists_branches 
											 b.Iformula.formula_exists_pos in
	helper f

and case_normalize_formula prog (h:(ident*primed) list)(b:bool)(f:Iformula.formula):Iformula.formula* ((ident*primed)list) = 
	(*called for data invariants and assume formulas ... rename bound, convert_struc2 float out exps from heap struc*)	
	let f = convert_heap2 prog f in
	let f = Iformula.float_out_exps_from_heap f in
	let f = Iformula.float_out_min_max f in
	let f = Iformula.rename_bound_vars f in
	case_normalize_renamed_formula prog h b f
			
and case_normalize_struc_formula prog (h:(ident*primed) list)(p:(ident*primed) list)(f:Iformula.struc_formula) (lax_implicit:bool):Iformula.struc_formula* ((ident*primed)list) = 	
	let nf = convert_struc2 prog f in
	let nf = Iformula.float_out_exps_from_heap_struc nf in
	let nf = Iformula.float_out_struc_min_max nf in
	(*let _ = print_string ("\n b rename "^(Iprinter.string_of_struc_formula "" nf))in*)
	let nf = Iformula.rename_bound_var_struc_formula nf in
	(*let _ = print_string ("\n after ren: "^(Iprinter.string_of_struc_formula "" nf)^"\n") in*)
	(*convert anonym to exists*)
	let rec helper (h:(ident*primed) list)(f0:Iformula.struc_formula):Iformula.struc_formula* ((ident*primed)list) = 
		let helper1 (f:Iformula.ext_formula):Iformula.ext_formula * ((ident*primed)list) = match f with
		| Iformula.EAssume b-> 
					let onb = convert_anonym_to_exist b in
					let hp = (Util.remove_dups(h@p))in
					let nb,nh = case_normalize_renamed_formula prog hp false onb in
					let nb,ne = ilinearize_formula nb hp in
					let vars_list = Iformula.all_fv nb in
					(*let _ = print_string ("\n nb: "^(Iprinter.string_of_formula nb)^" \n "^
						(List.fold_left(fun a (c,d)-> a^" "^c^(Iprinter.string_of_primed d)) "" vars_list)^"\n"^
						(List.fold_left(fun a (c,d)-> a^" "^c^(Iprinter.string_of_primed d)) "" p)^"\n"^
						(List.fold_left(fun a (c,d)-> a^" "^c^(Iprinter.string_of_primed d)) "" nh)^"\n"^
						(List.fold_left(fun a (c,d)-> a^" "^c^(Iprinter.string_of_primed d)) "" ne)^"\n"
						) in*)
					(Iformula.EAssume nb,(Util.difference vars_list p)) 
		| Iformula.ECase b->
			let r1,r2 = List.fold_left (fun (a1,a2)(c1,c2)->
									let r12 = Util.intersect (Ipure.fv c1) h in
									let r21,r22 = helper h c2 in
									(((c1,r21)::a1),r12::r22::a2)
					) ([],[]) b.Iformula.formula_case_branches in				
					(Iformula.ECase ({
						Iformula.formula_case_branches = r1;
						Iformula.formula_case_pos = b.Iformula.formula_case_pos
						}),(Util.remove_dups (List.concat r2)))			
		| Iformula.EBase b->		
				let nh0 = b.Iformula.formula_ext_explicit_inst in
				let _ = if (List.length (Util.intersect h nh0))>0 then 
						Error.report_error {Error.error_loc = b.Iformula.formula_ext_pos;
							Error.error_text = "the late instantiation variables collide with the used vars"}
					else true in
				let h1 = Util.remove_dups (h@nh0) in
				let onb = convert_anonym_to_exist b.Iformula.formula_ext_base in
				let h0prm = Util.difference(Iformula.heap_fv onb) h1 in
				let h0h0prm = Util.remove_dups (nh0@h0prm) in
				let h1prm = Util.remove_dups (h1@h0prm) in
				let _ = if (List.length (List.filter (fun (c1,c2)-> c2==Primed) h0h0prm))>0 then
						Error.report_error {Error.error_loc = b.Iformula.formula_ext_pos; Error.error_text = "should not have prime vars"} else true in
				let _ = if (List.length (Util.intersect(h0h0prm) p))>0 then 	
						Error.report_error {Error.error_loc = b.Iformula.formula_ext_pos; Error.error_text = "post variables should not appear here"} else true in
				let nc,h2 = helper h1prm b.Iformula.formula_ext_continuation in	
				let implvar = if lax_implicit then 
						Util.difference (Iformula.unbound_heap_fv onb(*b.Iformula.formula_ext_base*)) h1
						else Util.difference h2 h1 in
				let nb,h3 = case_normalize_renamed_formula prog (*(Util.remove_dups(h1@implvar))*) h false onb in
				let global_ex = Util.difference (Iformula.struc_free_vars nc) (h@implvar@nh0@p) in
				let _ = if (List.length global_ex)>0 then print_string ("formula: "^
					(Iprinter.string_of_formula nb)^"\nglobals: "^
							(Iprinter.string_of_var_list global_ex)^"\n")else () in
				let nb,ex = ilinearize_formula nb (h@implvar@nh0@global_ex) in
				
				let heap_vars = (Iformula.heap_fv onb)@(Iformula.struc_hp_fv nc) in
				let global_ex_non_heap = Util.difference global_ex heap_vars in
				let global_ex_heap  = Util.intersect global_ex heap_vars in
				let ex_non_heap = Util.difference ex heap_vars in
				let ex_heap  = Util.intersect ex heap_vars in				
				
				let (global_ex,implvar,expl,ex) = match !Globals.instantiation_variants with
				| 1 -> (global_ex_non_heap,implvar,b.Iformula.formula_ext_explicit_inst@ex_heap@global_ex_heap,ex_non_heap)
				| 2 -> (global_ex_non_heap,[],implvar@b.Iformula.formula_ext_explicit_inst@ex_heap@global_ex_heap,ex_non_heap)				
				| 4 -> (global_ex_non_heap,implvar@b.Iformula.formula_ext_explicit_inst@ex_heap@global_ex_heap,[],ex_non_heap)				
				| 0 -> (global_ex,implvar,b.Iformula.formula_ext_explicit_inst,ex)
				| 3 -> (global_ex,implvar@b.Iformula.formula_ext_explicit_inst, [] ,ex)				
				| 5 -> (global_ex,[], implvar@b.Iformula.formula_ext_explicit_inst,ex)				
				| _ -> (global_ex,implvar,b.Iformula.formula_ext_explicit_inst,ex)
				in
				
				let h3 = Util.difference h3 ex in
				let _ = if (*(!Globals.instantiation_variants=0 || !Globals.instantiation_variants=3 || !Globals.instantiation_variants=5)&&*)(List.length (*(Util.difference implvar (Iformula.fv onb))*)
								(Util.difference implvar heap_vars))>0 then 
						let _ = print_string ("h2 vars: "^(Iprinter.string_of_var_list h2)^"\n") in
						let _ = print_string ("h1 vars: "^(Iprinter.string_of_var_list h1)^"\n") in
						let _ = print_string ("h1 vars: "^(Iprinter.string_of_var_list h3)^"\n") in
						let _ = print_string ("\n--> "^
							(Iprinter.string_of_var_list h1prm)^"\n"^
							"\n impl: "^(Iprinter.string_of_var_list implvar)^"\nanon to exist base: "^
							(Iprinter.string_of_formula onb)^"\n new_base: "^
							(Iprinter.string_of_formula nb)^"\n new_cont: "^
							(Iprinter.string_of_struc_formula "" nc)^"\n") in
						Error.report_error {Error.error_loc = b.Iformula.formula_ext_pos; Error.error_text = ("malfunction: some implicit vars are not heap_vars\n")} else true in
				let r = (Iformula.EBase ({
					Iformula.formula_ext_base = nb;
					Iformula.formula_ext_implicit_inst =implvar;					
					Iformula.formula_ext_explicit_inst = expl;
					Iformula.formula_ext_exists = global_ex;
					Iformula.formula_ext_continuation = nc;
					Iformula.formula_ext_pos = b.Iformula.formula_ext_pos}),(Util.remove_dups (h2@h3)))in
				(*let _ = print_string ("\n normalized: "^(Iprinter.string_of_ext_formula (fst r))^"\n before: "^(Iprinter.string_of_ext_formula f)^"\n") in*)
				r in
	if (List.length f0)=0 then
		([],[])
	else
		let ll1,ll2 = List.split (List.map helper1 f0) in
		(ll1, (Util.remove_dups (List.concat ll2))) in	
	(helper h nf)
	
and case_normalize_coerc prog (cd: Iast.coercion_decl):Iast.coercion_decl = 
	(*let helper (f:Iformula.formula):Iformula.formula = 
		let nf = convert_heap2 prog f in
		let nf = convert_anonym_to_exist nf in		
		let nf = Iformula.float_out_exps_from_heap nf in
		let nf = Iformula.float_out_min_max nf in		
		nf in*)
	let nch = fst(case_normalize_formula prog [] false cd.Iast.coercion_head) in
	let ncb = fst(case_normalize_formula prog [] false cd.Iast.coercion_body) in
	(*let _ = print_string ("\n got: "^cd.Iast.coercion_name^"\n"^(Iprinter.string_of_formula cd.Iast.coercion_head)^"\n"^(Iprinter.string_of_formula nch)) in
	let _ = print_string ("\n got: "^cd.Iast.coercion_name^"\n"^(Iprinter.string_of_formula cd.Iast.coercion_body)^"\n"^(Iprinter.string_of_formula ncb)) in*)
	{ Iast.coercion_type = cd.Iast.coercion_type;
	  Iast.coercion_name = cd.Iast.coercion_name;
	  Iast.coercion_head = nch;
	  Iast.coercion_body = ncb;
	  Iast.coercion_proof = cd.Iast.coercion_proof}
		
and ren_list_concat (l1:((ident*ident) list)) (l2:((ident*ident) list)):((ident*ident) list) = 
			let fl2 = List.map (fun (c1,c2)-> c1) l2 in
			let nl1 = List.filter (fun (c1,c2)-> not (List.mem c1 fl2)) l1 in (nl1@l2)
and subid (ren:(ident*ident) list) (i:ident) :ident = 
		let nl = List.filter (fun (c1,c2)-> (String.compare c1 i)==0) ren in
		if (List.length nl )> 0 then let _,l2 = List.hd nl in l2
			else i 			
and rename_exp (ren:(ident*ident) list) (f:Iast.exp):Iast.exp = 
	
	let rec helper (ren:(ident*ident) list) (f:Iast.exp):Iast.exp =   match f with
	  | Iast.Assert b ->
		Iast.Assert{Iast.exp_assert_asserted_formula = (match b.Iast.exp_assert_asserted_formula with
									| None -> None
									| Some f-> Some 
										((Iformula.subst_struc 
											(List.fold_left(fun a (c1,c2)-> 
																((c1,Unprimed),(c2,Unprimed))::
																((c1,Primed),(c2,Primed))::a
															) [] ren) (fst f)),(snd f)));
		 Iast.exp_assert_assumed_formula = (match b.Iast.exp_assert_assumed_formula with
			| None -> None
			| Some f -> Some (Iformula.subst (List.fold_left(fun a (c1,c2)-> ((c1,Unprimed),(c2,Unprimed))::((c1,Primed),(c2,Primed))::a) [] ren) f));
		 Iast.exp_assert_pos = b.Iast.exp_assert_pos}
	  | Iast.Assign b->
		Iast.Assign	{  Iast.exp_assign_op = b.Iast.exp_assign_op;
					   Iast.exp_assign_lhs = helper ren b.Iast.exp_assign_lhs;
					   Iast.exp_assign_rhs = helper ren b.Iast.exp_assign_rhs;
					   Iast.exp_assign_pos = b.Iast.exp_assign_pos}
	  | Iast.Binary b->
		Iast.Binary { b with 
					   Iast.exp_binary_oper1 = helper ren b.Iast.exp_binary_oper1;
					   Iast.exp_binary_oper2 = helper ren b.Iast.exp_binary_oper2;}
	  | Iast.Bind b->
			let nren = ren_list_concat ren (List.map (fun c-> (c,Ipure.fresh_old_name c)) b.Iast.exp_bind_fields) in	 
			(*let _ = print_string ((List.fold_left(fun a (c1,c2)-> a^"("^c1^","^c2^") ") "\n renaming: " ren)^"\n") in*)
			Iast.Bind { b with 
					 Iast.exp_bind_bound_var = subid ren b.Iast.exp_bind_bound_var;
					 Iast.exp_bind_fields = List.map (fun c-> subid nren c) b.Iast.exp_bind_fields;
					 Iast.exp_bind_body = helper nren b.Iast.exp_bind_body}
	  | Iast.Block b-> Iast.Block{b with Iast.exp_block_body = helper ren b.Iast.exp_block_body}

	  | Iast.FloatLit _
	  | Iast.IntLit _
	  | Iast.Java _	  
	  | Iast.Null _
	  | Iast.Break _
	  | Iast.Continue _
	  | Iast.Empty _
	  | Iast.ConstDecl _
	  | Iast.Debug _
	  | Iast.Dprint _
	  | Iast.This _
	  | Iast.BoolLit _ -> f
	  | Iast.VarDecl b -> 
		Iast.VarDecl {b with Iast.exp_var_decl_decls = List.map (fun (c1,c2,c3)-> (c1, 
																					(match c2 with 
																					| None-> None
																					| Some e-> Some (helper ren e)), c3)) b.Iast.exp_var_decl_decls }
	  | Iast.CallRecv b -> Iast.CallRecv{b with
					  Iast.exp_call_recv_receiver = helper ren b.Iast.exp_call_recv_receiver;
					  Iast.exp_call_recv_arguments = List.map (helper ren) b.Iast.exp_call_recv_arguments}
	  | Iast.CallNRecv b -> Iast.CallNRecv{b with Iast.exp_call_nrecv_arguments = List.map (helper ren) b.Iast.exp_call_nrecv_arguments}
	  | Iast.Cast b -> Iast.Cast{b with Iast.exp_cast_body =  helper ren b.Iast.exp_cast_body}
	  | Iast.Cond b -> Iast.Cond {b with 
				 Iast.exp_cond_condition = helper ren b.Iast.exp_cond_condition;
				 Iast.exp_cond_then_arm = helper ren b.Iast.exp_cond_then_arm;
				 Iast.exp_cond_else_arm = helper ren b.Iast.exp_cond_else_arm}	  
	  | Iast.Member b ->
			Iast.Member {b with 
				   Iast.exp_member_base = helper ren b.Iast.exp_member_base;
				   Iast.exp_member_fields = List.map (subid ren ) b.Iast.exp_member_fields}
	  | Iast.New b-> 
			Iast.New {b with Iast.exp_new_arguments = List.map (helper ren) b.Iast.exp_new_arguments}
	  | Iast.Return b ->  Iast.Return {b with Iast.exp_return_val = match b.Iast.exp_return_val with
											| None -> None
											| Some f -> Some (rename_exp ren f)}
	  | Iast.Seq b -> Iast.Seq 
				{ Iast.exp_seq_exp1 = rename_exp ren b.Iast.exp_seq_exp1;
				  Iast.exp_seq_exp2 =rename_exp ren b.Iast.exp_seq_exp2;
				  Iast.exp_seq_pos = b.Iast.exp_seq_pos }	  
	  
	  | Iast.Unary b-> Iast.Unary {b with Iast.exp_unary_exp = rename_exp ren b.Iast.exp_unary_exp}
	  | Iast.Unfold b-> Iast.Unfold{b with Iast.exp_unfold_var = ((subid ren (fst b.Iast.exp_unfold_var)),(snd b.Iast.exp_unfold_var))}
	  | Iast.Var b -> Iast.Var{b with Iast.exp_var_name = subid ren b.Iast.exp_var_name}
	  | Iast.While b-> Iast.While{
				  Iast.exp_while_condition = rename_exp ren b.Iast.exp_while_condition;
				  Iast.exp_while_body = rename_exp ren b.Iast.exp_while_body;
				  Iast.exp_while_specs = Iformula.subst_struc (List.fold_left(fun a (c1,c2)-> ((c1,Unprimed),(c2,Unprimed))::((c1,Primed),(c2,Primed))::a) [] ren) b.Iast.exp_while_specs;
				  Iast.exp_while_pos = b.Iast.exp_while_pos}
	  in
 helper ren f 

and case_normalize_exp prog (h: (ident*primed) list) (p: (ident*primed) list)(f:Iast.exp) :
			Iast.exp*((ident*primed) list)*((ident*primed) list)*((ident*ident) list) =  match f with
	| Iast.Assert b->
				let asrt_nf,nh = match b.Iast.exp_assert_asserted_formula with
					| None -> (None,h)
					| Some f -> 
						let r, _ = case_normalize_struc_formula prog h p (fst f) true in
						(Some (r,(snd f)),h) in
				let assm_nf  = match b.Iast.exp_assert_assumed_formula with
					| None-> None 
					| Some f -> 
							Some (fst (case_normalize_formula prog nh false f))in
				(Iast.Assert { Iast.exp_assert_asserted_formula = asrt_nf;
				   	Iast.exp_assert_assumed_formula = assm_nf;
				    Iast.exp_assert_pos = b.Iast.exp_assert_pos}, h, p, [])
  | Iast.Assign b-> 
					let l1,_,_,_ = case_normalize_exp prog h p b.Iast.exp_assign_lhs in
					let l2,_,_,_ = case_normalize_exp prog h p b.Iast.exp_assign_rhs in
		    (Iast.Assign{ Iast.exp_assign_op = b.Iast.exp_assign_op;
				   Iast.exp_assign_lhs = l1;
				   Iast.exp_assign_rhs = l2;
				   Iast.exp_assign_pos = b.Iast.exp_assign_pos},h,p,[])
  | Iast.Binary b->
					let l1,_,_,_ = case_normalize_exp prog h p b.Iast.exp_binary_oper1 in
					let l2,_,_,_ = case_normalize_exp prog h p b.Iast.exp_binary_oper2 in
					(Iast.Binary {Iast.exp_binary_op = b.Iast.exp_binary_op;
				   Iast.exp_binary_oper1 = l1;
				   Iast.exp_binary_oper2 = l2;
				   Iast.exp_binary_pos = b.Iast.exp_binary_pos},h,p,[])
  | Iast.Bind b ->
				let r,nh,np,_ =   case_normalize_exp prog h p b.Iast.exp_bind_body in
				(Iast.Bind {b with Iast.exp_bind_body =r},h,p,[])  
  | Iast.Block b->
				let r,_,_,_ = case_normalize_exp prog h p b.Iast.exp_block_body in
				(Iast.Block { b with Iast.exp_block_body = r},h,p,[])
  | Iast.Continue _ 
  | Iast.Debug _ 
  | Iast.Dprint _ 
  | Iast.Empty _ 
  | Iast.FloatLit _ 
  | Iast.IntLit _ 
  | Iast.Java _ 
	| Iast.BoolLit _
	| Iast.Null _  
	| Iast.Unfold _ 
  | Iast.Var _
  | Iast.This _ 
  | Iast.Break _ -> (f,h,p,[])
  | Iast.CallNRecv b ->
					let nl = List.map (fun c-> let r1,_,_,_ = case_normalize_exp prog h p c in r1) b.Iast.exp_call_nrecv_arguments in
 					(Iast.CallNRecv{b with Iast.exp_call_nrecv_arguments = nl },h,p,[]) 
	| Iast.CallRecv b->
					let a1,_,_,_ = case_normalize_exp prog h p b.Iast.exp_call_recv_receiver in
					let nl = List.map (fun c-> let r1,_,_,_ = case_normalize_exp prog h p c in r1) b.Iast.exp_call_recv_arguments in
					(Iast.CallRecv{b with 
						Iast.exp_call_recv_receiver = a1;
						Iast.exp_call_recv_arguments = nl},h,p,[])
  | Iast.Cast b->
			let nb,_,_,_ = case_normalize_exp prog h p b.Iast.exp_cast_body in
			(Iast.Cast {b with Iast.exp_cast_body= nb},h,p,[])
  | Iast.Cond b->
			let ncond,_,_,_ = case_normalize_exp prog h p b.Iast.exp_cond_condition in	
			let nthen,_,_,_ = case_normalize_exp prog h p b.Iast.exp_cond_then_arm in
			let nelse,_,_,_ = case_normalize_exp prog h p b.Iast.exp_cond_else_arm in
			(Iast.Cond {b with 
					Iast.exp_cond_condition= ncond;
					Iast.exp_cond_then_arm= nthen;
					Iast.exp_cond_else_arm= nelse;},h,p,[])
  | Iast.ConstDecl b->
				let ndecl,nren = List.fold_left (fun (a1,a2) (c1,c2,c3)-> 
					let nn = (Ipure.fresh_old_name c1) in
					let ne,_,_,_ = case_normalize_exp prog h p c2 in
					((nn,ne,c3)::a1,(c1,nn)::a2)) ([],[]) b.Iast.exp_const_decl_decls in
				let nvl = List.map (fun (c1,c2)-> c1) nren in
				let nvlprm = List.map (fun c-> (c,Primed)) nvl in
				let nh = nvlprm@h in
				let np = (List.map (fun c->(c,Primed))nvl)@p in
				(Iast.ConstDecl {b with Iast.exp_const_decl_decls = ndecl;},nh,np,nren)
  | Iast.Member b ->
				let nb,_,_,_ = case_normalize_exp prog h p b.Iast.exp_member_base in
				(Iast.Member {b with Iast.exp_member_base = nb},h,p,[]) 
  | Iast.New b->
			let nl = List.map (fun c-> let r1,_,_,_ = case_normalize_exp prog h p c in r1) b.Iast.exp_new_arguments in
			(Iast.New  {b with Iast.exp_new_arguments =nl},h,p,[])
  | Iast.Return b -> 
			(Iast.Return {b with Iast.exp_return_val= match b.Iast.exp_return_val with | None -> None | Some f -> 
				let r,_,_,_ = (case_normalize_exp prog h p f) in 	Some r},h,p,[])
  | Iast.Seq b -> 
			let l1,nh,np,ren = case_normalize_exp prog h p b.Iast.exp_seq_exp1 in
			let l2 = rename_exp ren b.Iast.exp_seq_exp2 in
			let l2 ,nh,np,ren2 = case_normalize_exp prog nh np l2 in
			let aux_ren = (ren_list_concat ren ren2) in
			(*let _ = print_string ((List.fold_left(fun a (c1,c2)-> a^"("^c1^","^c2^") ") "\n var2 decl renaming: " aux_ren)^"\n") in*)
			(Iast.Seq ({ Iast.exp_seq_exp1 = l1; Iast.exp_seq_exp2 = l2; Iast.exp_seq_pos = b.Iast.exp_seq_pos }),
										nh,
										np,
										aux_ren)
  | Iast.Unary b -> 
			let l1,_,_,_ = case_normalize_exp prog h p b.Iast.exp_unary_exp in
					(Iast.Unary {b with Iast.exp_unary_exp = l1},h,p,[])
  | Iast.VarDecl b -> 		
				let ndecl,nren = List.fold_left (fun (a1,a2) (c1,c2,c3)->
					let nn = (Ipure.fresh_old_name c1) in
					let ne = match c2 with
						| None -> None 
						| Some f-> let ne,_,_,_ = case_normalize_exp prog h p f in Some ne in
					((nn,ne,c3)::a1,(c1,nn)::a2)) ([],[]) b.Iast.exp_var_decl_decls in
				let nvl = List.map (fun (c1,c2)-> c2) nren in
				let nvlprm = List.map (fun c-> (c,Primed)) nvl in
				let nh = nvlprm@h in
				let np = (List.map (fun c->(c,Primed))nvl)@p in
				(Iast.VarDecl {b with Iast.exp_var_decl_decls = ndecl;},nh,np,nren)		
  | Iast.While b->
			let nc,nh,np,_ = case_normalize_exp prog h p b.Iast.exp_while_condition in
			let nb,nh,np,_ = case_normalize_exp prog nh np b.Iast.exp_while_body in
			let ns,_ = case_normalize_struc_formula prog h p b.Iast.exp_while_specs false in
			(Iast.While {b with Iast.exp_while_condition=nc; Iast.exp_while_body=nb;Iast.exp_while_specs = ns},h,p,[])



and case_normalize_data prog (f:Iast.data_decl):Iast.data_decl =
	let h = List.map (fun (c1,_)-> ((snd c1),Unprimed) ) f.Iast.data_fields in  
	{f with Iast.data_invs = List.map (fun c-> fst(case_normalize_formula prog h false c)) f.Iast.data_invs}

and case_normalize_proc prog (f:Iast.proc_decl):Iast.proc_decl = 
		let h = (List.map (fun c1-> (c1.Iast.param_name,Unprimed)) f.Iast.proc_args) in
		let h_prm = (List.map (fun c1-> (c1.Iast.param_name,Primed)) f.Iast.proc_args) in
		let p = (res,Unprimed)::(List.map (fun c1-> (c1.Iast.param_name,Primed)) (List.filter (fun c-> c.Iast.param_mod == Iast.RefMod) f.Iast.proc_args)) in
		let nst,h11 = case_normalize_struc_formula prog h p f.Iast.proc_static_specs false in
		let ndn, h12 = case_normalize_struc_formula prog h p f.Iast.proc_dynamic_specs false in
		let h1 = Util.remove_dups (h11@h12) in 
		let h2 = Util.remove_dups (h@h_prm@(Util.difference h1 h)) in
	 	let nb = match f.Iast.proc_body with None -> None | Some f->
			let r,_,_,_ = (case_normalize_exp prog h2 [(res,Unprimed)] f) in			
			Some r in
				{f with Iast.proc_static_specs =nst;
								Iast.proc_dynamic_specs = ndn;			
								Iast.proc_body = nb;
				}

and case_normalize_program (prog: Iast.prog_decl):Iast.prog_decl=
	 let tmp_views = order_views prog.I.prog_view_decls in
	 let tmp_views = List.map (fun c-> 
					let h = (self,Unprimed)::(res,Unprimed)::(List.map (fun c-> (c,Unprimed)) c.Iast.view_vars ) in
					let p = (self,Primed)::(res,Primed)::(List.map (fun c-> (c,Primed)) c.Iast.view_vars ) in
					let wf,_ = case_normalize_struc_formula prog h p c.Iast.view_formula false in
					{ c with Iast.view_formula = 	wf;}) tmp_views in
	 let prog = {prog with Iast.prog_view_decls = tmp_views} in
	 let cdata = List.map (case_normalize_data prog) prog.I.prog_data_decls in
	 let prog = {prog with Iast.prog_data_decls = cdata} in
	 let procs1 = List.map (case_normalize_proc prog) prog.I.prog_proc_decls in
	 let prog = {prog with Iast.prog_proc_decls = procs1} in
	 let coer1 = List.map (case_normalize_coerc prog) prog.Iast.prog_coercion_decls in	 
	 {  Iast.prog_data_decls = cdata;
		Iast.prog_global_var_decls = prog.Iast.prog_global_var_decls; (* Global variable *)
	    Iast.prog_enum_decls = prog.Iast.prog_enum_decls;
		Iast.prog_view_decls = tmp_views;
		Iast.prog_proc_decls = procs1;
		Iast.prog_coercion_decls = coer1 }
	


and line_split (br_cnt:int)(br_n:int)(cons:CP.b_formula)(line:(Cpure.constraint_rel*(int* Cpure.b_formula *(Cpure.spec_var list))) list)
	:Cpure.b_formula*int list * int list =
	(*let _ = print_string ("\n line split start "^(Cprinter.string_of_b_formula cons)^"\n") in*)
	try
	let line = List.map (fun (c1,(c2,c3,_))-> (c1,c2,c3)) line in
	let arr = List.sort (fun (c1,c2,c3) (d1,d2,d3) -> compare c2 d2 ) line in
	let branches = if (List.length arr)=0 then []
					else 
						let (c1,c2,c3) = List.hd arr in
						List.fold_left (fun crt_list (c1,c2,c3)-> 
										let crt_n,crt_br_list = List.hd crt_list in
										if (c2=crt_n) then 
												(crt_n,(c1,c3)::crt_br_list)::(List.tl crt_list)
											else (c2,[(c1,c3)])::crt_list) [(c2,[(c1,c3)])] (List.tl arr) in
											
	(*let _ = print_string ("\n line split: "^
		(List.fold_left (fun a (c1,c2)-> a^"\n"^(string_of_int c1)^"-> "^
				(List.fold_left (fun a (c1,c2)->a^", ("^(Cprinter.string_of_constraint_relation c1)^","^
							(Cprinter.string_of_b_formula c2)^")") "" c2)) "" branches)^"\n") in*)
	let l1,l2,n = List.fold_left (fun (l1,l2,n) (br_index,br_list)-> 
		if (br_index=br_cnt) then (br_index::l1,l2,n)
		else (*consistencies with relations of a single branch*)
			let (contr,con_f) = List.fold_left (fun (a1,a2)(rel,con) -> match rel with
				| Cpure.Unknown -> (a1,a2)
				| Cpure.Subsumed 
				| Cpure.Subsuming -> raise Not_found
				| Cpure.Equal -> begin match a1 with
									| None -> (Some false,a2) 
									| Some false -> (a1,a2)
									| Some true -> raise Not_found end
				| Cpure.Contradicting -> begin match a1 with
									| None -> (Some true,Some con) 
									| Some false ->  raise Not_found 
									| Some true -> match a2 with
													| None -> raise Not_found 
													| Some s-> if (Cpure.equalBFormula con s) then (a1,a2)
																else raise Not_found end										
										) (None,None) br_list in
			(*consistencies across all branches*)
			match contr with
				| None -> raise Not_found
				| Some false -> (br_index::l1,l2,n)
				| Some true -> 
					match (n,con_f) with
					| None, Some s -> (l1,br_index::l2, Some s)
					| _, None ->  raise Not_found
					| Some s1, Some s2 -> if (Cpure.equalBFormula s1 s2) then  (l1,br_index::l2, n)
											else raise Not_found
	) ([],[],None) branches in	
	match n with
	| None -> (cons, [],[])
	| Some n -> (n, l1,l2)
	with _ -> (cons, [],[])
	
	
	
and splitter (f_list_init:(Cpure.formula*Cformula.ext_formula) list) (v1:Cpure.spec_var list) : Cformula.struc_formula list =
	(*let _ = print_string ("\n splitter got: "^(
		List.fold_left (fun a (c1,c2)-> a^"\n"^(Cprinter.string_of_pure_formula c1)^"--"^
								(Cprinter.string_of_ext_formula c2)) "" f_list_init)
	^"\n" ) in
	let _ = print_string ("\n vars: "^(Cprinter.string_of_spec_var_list v1)^"\n") in*)
	if (List.length v1)<1 then [(snd (List.split f_list_init))]
		else match (List.length f_list_init) with
			| 0 -> raise Not_found
			| 1 -> [[(snd (List.hd f_list_init))]]
			| _ ->
				let crt_v = List.hd v1 in
				let rest_vars = List.tl v1 in	
				let br_cnt = List.length f_list_init in
				let f_list = List.map (fun (c1,c2)-> 
					let aset = Context.get_aset ( Context.alias ((crt_v, crt_v) :: (Solver.ptr_equations c1))) crt_v in
					let aset = List.filter (fun c-> (String.compare "null" (Cpure.name_of_spec_var c))!=0) aset in
					let eqs = (Solver.get_equations_sets c1 aset)in
					let eqs = (Solver.transform_null eqs) in
					(*let _ = print_string ("\n aset: "^(Cprinter.string_of_spec_var_list aset)) in
					let _ = print_string ("\n eqs: "^(List.fold_left (fun a c-> a^" -- "^(Cprinter.string_of_b_formula c)) "" eqs )) in*)
					(c1,c2,aset,eqs)) f_list_init in
				let f_a_list = Util.add_index f_list in
				let constr_list = List.concat (List.map (fun (x,(c1,c2,c3,c4))->
									List.map (fun c-> (x,c,c3)) c4) f_a_list) in
				let constr_list = Util.remove_dups_f constr_list 
					(fun (x1,c1,_)(x2,c2,_)-> (x1=x2)&&(Cpure.equalBFormula c1 c2)) in
				let constr_array = Array.of_list constr_list in
				let sz = Array.length constr_array in
				let matr = Array.make_matrix sz sz Cpure.Unknown in

				let filled_matr = 
					Array.mapi(fun x c->(Array.mapi (fun y c->
						if (x>y) then 
							Cpure.compute_constraint_relation 
								(constr_array.(x)) 
								(constr_array.(y)) 
						else if x=y then 
						Cpure.Equal else 
						matr.(x).(y) 
						) c)) matr in
				let filled_matr = Array.mapi(fun x c->(Array.mapi (fun y c->
						if (x<y) then filled_matr.(y).(x)
						else filled_matr.(x).(y)) c)) filled_matr in
				(*
				let _ = print_string ("\n constr_array: "^(List.fold_left (fun a (x,c,c3)-> a^" \n( "^
				(string_of_int x)^","^(Cprinter.string_of_b_formula c)^",   "^
				(Cprinter.string_of_spec_var_list c3))"" constr_list)^"\n") in
				let _ = print_string ("\n matr: "^( Array.fold_right (fun c a-> a^(
					Array.fold_right (fun c a-> a^" "^(Cprinter.string_of_constraint_relation c )) c "\n ")
				) filled_matr "")^"\n") in*)
						
				let splitting_constraints = Array.mapi (fun x (br_n,cons,_)->
					let line_pair =List.combine (Array.to_list filled_matr.(x)) constr_list in
					let neg_cons,l1,l2 = line_split br_cnt br_n cons line_pair in
					let l1_br = List.map (fun c1-> let (_,(v1,v2,_,_))=List.find (fun c2->(fst c2)=c1) f_a_list in (v1,v2)) l1 in
					let l2_br = List.map (fun c1-> let (_,(v1,v2,_,_))=List.find (fun c2->(fst c2)=c1) f_a_list in (v1,v2)) l2 in
					((Cpure.BForm cons),(Cpure.BForm neg_cons),l1_br,l2_br)
					) constr_array in
					
					
					
				let splitting_constraints = 
					List.filter (fun (_,_,l1,l2)-> ((List.length l2)>0 && (List.length l1)>0)) (Array.to_list splitting_constraints) in
				if (List.length splitting_constraints)>0 then
				List.concat (List.map (fun (constr,neg_constr,l1,l2)->
					let nf1 = splitter l1 rest_vars in
					let nf2 = splitter l2 rest_vars in
					List.concat (List.map (fun c1-> List.map (fun c2-> 
					[Cformula.ECase{					
						Cformula.formula_case_branches =[(constr,c1);(neg_constr,c2)];
						Cformula.formula_case_exists = [];
						Cformula.formula_case_pos = no_pos;
					}]) nf2) nf1)					
				) splitting_constraints)
				else splitter f_list_init rest_vars

and move_instantiations (f:Cformula.struc_formula):Cformula.struc_formula*(Cpure.spec_var list) = 
	let rec helper (f:Cformula.ext_formula):Cformula.ext_formula*(Cpure.spec_var list) = match f with
	| Cformula.EBase b->
		let nc, vars = move_instantiations b.Cformula.formula_ext_continuation in
		let qvars, nf = Cformula.split_quantifiers b.Cformula.formula_ext_base in
		let global_ex, imp_inst = (b.Cformula.formula_ext_exists, b.Cformula.formula_ext_implicit_inst) in
		let n_qvars = Util.difference qvars vars in
		let n_globals = Util.difference global_ex vars in
		let inst_from_qvars = Util.difference vars qvars in
		let inst_from_global = Util.difference vars global_ex in
		(Cformula.EBase {b with 
			Cformula.formula_ext_continuation = nc;
			Cformula.formula_ext_base = Cformula.push_exists n_qvars nf ;
			Cformula.formula_ext_exists = n_globals;
			Cformula.formula_ext_implicit_inst = b.Cformula.formula_ext_implicit_inst @ inst_from_global @ inst_from_qvars;
		},(Util.difference vars (inst_from_qvars@inst_from_global)))
	| Cformula.ECase b-> 
		let new_cases, var_list = 
			List.split 
				(List.map 
					(fun (c1,c2)-> 
						let nf , vars = move_instantiations c2 in
						((c1,nf), (vars@(Cpure.fv c1)))
					) 
					b.Cformula.formula_case_branches) in
		(
		(Cformula.ECase {b with 
		Cformula.formula_case_branches = new_cases}),
		(List.concat var_list))			
	| Cformula.EAssume b-> (f,[]) in
	let forms, vars = List.split (List.map helper f) in
	(forms, (List.concat vars))
				
and formula_case_inference cp (f_ext:Cformula.struc_formula)(v1:Cpure.spec_var list) : Cformula.struc_formula = 


		(*let _ = print_string ("init f: "^(Cprinter.string_of_struc_formula f_ext)^"\n") in*)
		let r = try 
			let f_list = List.map (fun c->
				let d = match c with
						| Cformula.EBase b-> if (List.length b.Cformula.formula_ext_continuation)>0 then
							   Error.report_error { Error.error_loc = no_pos; Error.error_text ="malfunction: trying to infer case guard on a struc formula"}
								else b.Cformula.formula_ext_base 
						| _ -> Error.report_error { Error.error_loc = no_pos; Error.error_text ="malfunction: trying to infer case guard on a struc formula"}
						in
				let not_fact,nf_br = (Solver.xpure cp d) in
				let fact =  Solver.normalize_to_CNF not_fact no_pos in
				let fact = Cpure.drop_disjunct fact in
				let fact = Cpure.rename_top_level_bound_vars fact in
				let fact,_,_(*all,exist*) = Cpure.float_out_quantif fact in
				let fact = Cpure.check_not fact in
				(fact,c)
				) f_ext in
			
			let r = List.hd (splitter f_list v1) in
			fst (move_instantiations (Cformula.clean_case_guard_redundancy r []))
			
		with _ -> f_ext in
		(*let _ = print_string ("final f: "^(Cprinter.string_of_struc_formula r)^"\n") in*)
		r
	
and view_case_inference cp (ivl:Iast.view_decl list) (cv:Cast.view_decl):Cast.view_decl = 
		try
			let iv = List.find (fun c->c.Iast.view_name = cv.Cast.view_name) ivl in
			if (iv.Iast.try_case_inference) then
				let sf = (CP.SpecVar (CP.OType cv.Cast.view_data_name, self, Unprimed)) in
				let f = formula_case_inference cp cv.Cast.view_formula [sf] in
				{cv with 


					Cast.view_formula = f; 
					Cast.view_case_vars =Util.intersect (sf::cv.C.view_vars) (Cformula.guard_vars f); }
			else cv
		with _ -> cv 	
	
and case_inference (ip: Iast.prog_decl) (cp:Cast.prog_decl):Cast.prog_decl = 
	{cp with Cast.prog_view_decls = List.map (view_case_inference cp ip.Iast.prog_view_decls) cp.Cast.prog_view_decls}
	
