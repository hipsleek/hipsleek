 (* Created 21 Feb 2006 Simplify Iast to Cast *)
open Globals
open Exc.GTable 
open Printf
open Gen.Basic
open Gen.BList
open Perm
open Mcpure_D
open Mcpure
open Label_only
  
module C = Cast
module E = Env
module Err = Error
module I = Iast
module IF = Iformula
module IP = Ipure
module CF = Cformula
(* module GV = Globalvars*)
module CP = Cpure
module MCP = Mcpure
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
  (C.exp * typ)

  and spec_var_info =
  { mutable sv_info_kind : spec_var_kind;
    id: int;
  }

  and spec_var_table =
  (ident, spec_var_info) H.t

  and spec_var_kind = typ
  (* | Known of typ | Unknown *)

(* list of scc views that are in mutual-recursion *)
let view_scc : (ident list) list ref = ref []

(* list of views that are recursive *)
let view_rec : (ident list) ref = ref []

(* if no processed, conservatively assume a view is recursive *)
let is_view_recursive (n:ident) = 
  if (!view_scc)==[] then (
      (* report_warning no_pos "view_scc is empty : not processed yet?"; *)
      true)
  else List.mem n !view_rec 




let type_table : (spec_var_table ref) = ref (Hashtbl.create 19)

(** An Hoa : List of undefined data types **)
let undef_data_types = ref([] : (string * loc) list)


(** An Hoa : Alias for the Scriptarguments.inter, necessary because this module
			is compiled prior to Scriptarguments.
 **)
let inter = ref false

(* let op_map = Hashtbl.create 19 *)

(************************************************************
Primitives handling stuff
************************************************************)
(* Add a primitive function update___. Note: it is supposed to be dynamically inserted depending on the available types. *)
let string_of_stab stab = Hashtbl.fold
		(fun c1 c2 a ->
			a^"; ("^c1^" "^
			(
                (* match c2.sv_info_kind with  *)
				(* | Unknown -> "unknown"  *)
				(* | Known d->  *)
			string_of_typ c2.sv_info_kind )^")") stab ""

and string_of_var_kind k = string_of_typ k
  (* (match k with  *)
  (*   	| Unknown -> "unknown"  *)
  (*   	| Known d->  *)
  (*   ("known "^(string_of_typ d)) ) *)

let res_retrieve stab clean_res fl =
	if clean_res then  
		try 
			let r = Some (Hashtbl.find stab res_name) in
			(if (CF.subsume_flow !raisable_flow_int (exlist # get_hash fl)) 
            then (Hashtbl.remove stab res_name) 
            else ());
			r
		with Not_found -> None
	else None

let res_retrieve stab clean_res fl =
  let pr = pr_id in
  Debug.no_eff_2 "res_retrieve" [true]
      string_of_stab
      pr pr_no
      (fun _ _ -> res_retrieve stab clean_res fl) stab fl

	
let res_replace stab rl clean_res fl =
	if clean_res&&(CF.subsume_flow !raisable_flow_int (exlist # get_hash fl)) then 
		((Hashtbl.remove stab res_name);
		match rl with 
			| None -> () 
			| Some e-> Hashtbl.add stab res_name e) 
	else ()
	
let res_replace stab rl clean_res fl =
  let pr = pr_id in
  Debug.no_eff_2 "res_replace" [true]
      string_of_stab
      pr pr_no
      (fun _ _ -> res_replace stab rl clean_res fl) stab fl

let prim_buffer = Buffer.create 1024

(* search prog and generate all eq, neq for all the data declaration,      *)
(* along with the ones in prim_str                                         *)
let gen_primitives (prog : I.prog_decl) : (I.proc_decl list) * (I.rel_decl list) = (* AN HOA : modify return types *)
  let rec helper (ddecls : I.data_decl list) =
    match ddecls with
    | ddef :: rest ->
        let eq_str =
          "bool eq___(" ^
            (ddef.I.data_name ^
               (" a, " ^
                  (ddef.I.data_name ^
                     " b) case { a=b -> requires true ensures res ; a!=b -> requires true ensures !res;}\n"))) in
        let neq_str =
          "bool neq___(" ^
            (ddef.I.data_name ^
               (" a, " ^
                  (ddef.I.data_name ^
                     " b)case { a=b -> requires true ensures !res ; a!=b -> requires true ensures res;}\n"))) in
        let is_null_str =
          "bool is_null___(" ^
            (ddef.I.data_name ^
               (" a" ^
                  ") case { a=null -> requires true ensures res ; a!=null -> requires true ensures !res;}\n")) in
        let is_not_null_str =
          "bool is_not_null___(" ^
            (ddef.I.data_name ^
               (" a" ^
                  ") case { a=null -> requires true ensures !res ; a!=null -> requires true ensures res;}\n"))
        in
          (Buffer.add_string prim_buffer eq_str;
           Buffer.add_string prim_buffer neq_str;
           Buffer.add_string prim_buffer is_null_str;
           Buffer.add_string prim_buffer is_not_null_str;
           helper rest)
    | [] -> ()
  in
    (
     (*let _ = print_string ("\n primitives: "^prim_str^"\n") in*)
     helper prog.I.prog_data_decls;
     let all_prims = Buffer.contents prim_buffer in
     let prog = Parser.parse_hip_string "primitives" all_prims in
		(* An Hoa : print out the primitive relations parsed -- Problem : no relation parsed! *)
		(* let _ = print_endline "Primitive relations : " in *)
		(* let _ = List.map (fun x -> print_endline x.I.rel_name) prog.I.prog_rel_decls in *)
		(* An Hoa : THIS IS NOT THE PLACE THE PRIMITIVES IN prelude.ss IS ADDED! *)

	 (* AN HOA : modify to return the list of primitive relations *)
	 (prog.I.prog_proc_decls, prog.I.prog_rel_decls))
     (* let input = Lexing.from_string all_prims in *)
     (* input_file_name := "primitives"; *)
     (* let prog = Iparser.program (Ilexer.tokenizer "primitives") input *)
     (* in  *)
	 (* (\*let _ = print_string ("\n primitives: "^(Iprinter.string_of_program prog)^"\n") in*\) *)
	 
	 (* prog.I.prog_proc_decls) *)


let gen_primitives (prog : I.prog_decl) : (I.proc_decl list) * (I.rel_decl list) 
      = (* AN HOA : modify return types *)
	(*  let prd = pr_list Iprinter.string_of_proc_decl in*)
   let pr = pr_pair pr_no (pr_list Iprinter.string_of_rel_decl) in
  Debug.no_1 "gen_primitives" pr_no pr gen_primitives prog
  
let op_map = Hashtbl.create 19
  
let _ =
  List.map (fun (op, func) -> Hashtbl.add op_map op func)
    [ (I.OpPlus, "add___"); (I.OpMinus, "minus___"); (I.OpMult, "mult___");
      (I.OpDiv, "div___"); (I.OpMod, "mod___"); (I.OpEq, "eq___");
      (I.OpNeq, "neq___"); (I.OpLt, "lt___"); (I.OpLte, "lte___");
      (I.OpGt, "gt___"); (I.OpGte, "gte___"); (I.OpLogicalAnd, "land___");
      (I.OpLogicalOr, "lor___"); (I.OpIsNull, "is_null___");
      (I.OpIsNotNull, "is_not_null___");
    ]

(**
 * Function of signature 
 *     T[] update(T[] array, int index, T value)
 *     T   array_get_elm_at(T[] array, int index)
 * that returns an array identical to array except the value at "index" is "value"
 * and returns the value of array[index]
 *)
let array_update_call = "update___"
let array_access_call = "array_get_elm_at___"
let array_allocate_call = "aalloc___"
	  
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

let check_shallow_var = ref true
  
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

module NGComponents = Graph.Components.Make(NG)
  

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
  | IF.HeapNode { IF.h_formula_heap_arguments = args;
                  IF.h_formula_heap_perm = perm; (*LDK*)
                } ->
      let ps = get_iperm perm in
      let tmp1 = look_for_anonymous_exp_list (ps@args) in tmp1
  | _ -> []

and look_for_anonymous_exp_list (args : IP.exp list) :
  (ident * primed) list =
  match args with
  | h :: rest ->
      List.append (look_for_anonymous_exp h)
        (look_for_anonymous_exp_list rest)
  | _ -> []

and anon_var (id, p) = 
  if ((String.length id) > 5) &&
	  ((String.compare (String.sub id 0 5) "Anon_") == 0)
  then [ (id, p) ]
  else []

and look_for_anonymous_exp (arg : IP.exp) : (ident * primed) list =
  match arg with
  | IP.Var (b1, _) -> anon_var b1
  | IP.Add (e1, e2, _) | IP.Subtract (e1, e2, _) | IP.Max (e1, e2, _) |
      IP.Min (e1, e2, _) | IP.BagDiff (e1, e2, _) ->
      List.append (look_for_anonymous_exp e1) (look_for_anonymous_exp e2)
  | IP.Mult (e1, e2, _) | IP.Div (e1, e2, _) ->
      List.append (look_for_anonymous_exp e1) (look_for_anonymous_exp e2)
  | IP.Bag (e1, _) | IP.BagUnion (e1, _) | IP.BagIntersect (e1, _) -> look_for_anonymous_exp_list e1
  | IP.ListHead (e1, _) | IP.ListTail (e1, _) | IP.ListLength (e1, _) | IP.ListReverse (e1, _) -> look_for_anonymous_exp e1
  | IP.List (e1, _) | IP.ListAppend (e1, _) -> look_for_anonymous_exp_list e1
  | IP.ListCons (e1, e2, _) -> (look_for_anonymous_exp e1) @ (look_for_anonymous_exp e2)
  | _ -> []

and convert_anonym_to_exist_one_formula (f0 : IF.one_formula) : ( ((ident * primed) list) * IF.one_formula) =
  let tmp1 = look_for_anonymous_h_formula f0.IF.formula_heap in
  (tmp1,f0)

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
		IF.formula_base_flow = fl0;
		IF.formula_base_and = a0;
        IF.formula_base_pos = l0
      } -> (*as f*)
      let tmp1 = look_for_anonymous_h_formula h0 in
      let tmp = List.map convert_anonym_to_exist_one_formula a0 in
      let vars,a1 = List.split tmp in
      let vars = List.concat vars in
      let tmp1=tmp1@vars
      in
        if ( != ) (List.length tmp1) 0
        then
          IF.Exists
            {
              IF.formula_exists_heap = h0;
              IF.formula_exists_qvars = tmp1;
              IF.formula_exists_pure = p0;
              IF.formula_exists_flow = fl0;
              IF.formula_exists_and = a1;
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

let node2_to_node_x prog (h0 : IF.h_formula_heap2) : IF.h_formula_heap =
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
    let args = h0.IF.h_formula_heap2_arguments in
    let hargs =
      if args==[] then [] (* don't convert if empty *)
      else
        match_args vdef.I.view_vars h0.IF.h_formula_heap2_arguments in
    let h =
      {
          IF.h_formula_heap_node = h0.IF.h_formula_heap2_node;
          IF.h_formula_heap_name = h0.IF.h_formula_heap2_name;
	      IF.h_formula_heap_derv = h0.IF.h_formula_heap2_derv;
	      IF.h_formula_heap_imm = h0.IF.h_formula_heap2_imm;
          IF.h_formula_heap_full = h0.IF.h_formula_heap2_full;
          IF.h_formula_heap_with_inv = h0.IF.h_formula_heap2_with_inv;
          IF.h_formula_heap_perm = h0.IF.h_formula_heap2_perm;
          IF.h_formula_heap_arguments = hargs;
          IF.h_formula_heap_pseudo_data = h0.IF.h_formula_heap2_pseudo_data;
          IF.h_formula_heap_pos = h0.IF.h_formula_heap2_pos;
		  IF.h_formula_heap_label = h0.IF.h_formula_heap2_label;
      }
    in h
  with
    | Not_found ->
          let ddef =
            I.look_up_data_def h0.IF.h_formula_heap2_pos prog.I.prog_data_decls
                h0.IF.h_formula_heap2_name in
          let params = List.map I.get_field_name ddef.I.data_fields (* An Hoa : un-hard-code *) in
          let hargs = match_args params h0.IF.h_formula_heap2_arguments in
          let h =
            {
                IF.h_formula_heap_node = h0.IF.h_formula_heap2_node;
                IF.h_formula_heap_name = h0.IF.h_formula_heap2_name;
	            IF.h_formula_heap_derv = h0.IF.h_formula_heap2_derv;
	            IF.h_formula_heap_imm = h0.IF.h_formula_heap2_imm;
                IF.h_formula_heap_full = h0.IF.h_formula_heap2_full;
                IF.h_formula_heap_with_inv = h0.IF.h_formula_heap2_with_inv;
                IF.h_formula_heap_arguments = hargs;
            IF.h_formula_heap_perm = h0.IF.h_formula_heap2_perm;
                IF.h_formula_heap_pseudo_data = h0.IF.h_formula_heap2_pseudo_data;
                IF.h_formula_heap_pos = h0.IF.h_formula_heap2_pos;
			    IF.h_formula_heap_label = h0.IF.h_formula_heap2_label;
            }
          in h

let node2_to_node prog (h0 : IF.h_formula_heap2) : IF.h_formula_heap =
  Debug.no_1 "node2_to_node"
      (fun f -> Iprinter.string_of_h_formula (IF.HeapNode2 f) )
      (fun f -> Iprinter.string_of_h_formula (IF.HeapNode f))
      (fun _ -> node2_to_node_x prog h0) h0

(* convert HeapNode2 to HeapNode *)
let rec convert_heap2_heap prog (h0 : IF.h_formula) : IF.h_formula =
  match h0 with
    | IF.Star (({ IF.h_formula_star_h1 = h1; IF.h_formula_star_h2 = h2 } as h))
        -> let tmp1 = convert_heap2_heap prog h1 in
        let tmp2 = convert_heap2_heap prog h2
        in IF.Star { (h) with
            IF.h_formula_star_h1 = tmp1;
            IF.h_formula_star_h2 = tmp2; }
    | IF.Conj (({ IF.h_formula_conj_h1 = h1; IF.h_formula_conj_h2 = h2 } as h))
        -> let tmp1 = convert_heap2_heap prog h1 in
        let tmp2 = convert_heap2_heap prog h2
        in IF.Conj { (h) with
            IF.h_formula_conj_h1 = tmp1;
            IF.h_formula_conj_h2 = tmp2; }
    | IF.Phase (({ IF.h_formula_phase_rd = h1; IF.h_formula_phase_rw = h2 } as h))
        -> let tmp1 = convert_heap2_heap prog h1 in
        let tmp2 = convert_heap2_heap prog h2
        in IF.Phase { (h) with
            IF.h_formula_phase_rd = tmp1;
            IF.h_formula_phase_rw = tmp2; }
    | IF.HeapNode2 h2 -> IF.HeapNode (node2_to_node prog h2)
    | IF.HRel _
    | IF.HTrue | IF.HFalse | IF.HEmp | IF.HeapNode _ -> h0

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

and convert_struc2 prog (f0:IF.struc_formula):IF.struc_formula = match f0 with
  | IF.EAssume (b,tag)-> IF.EAssume ((convert_heap2 prog b),tag)
  | IF.ECase b -> IF.ECase {b with IF.formula_case_branches = map_l_snd (convert_struc2 prog) b.IF.formula_case_branches};
  | IF.EBase b -> IF.EBase{b with 
		IF.formula_struc_base = convert_heap2 prog b.IF.formula_struc_base;
		IF.formula_struc_continuation = map_opt (convert_struc2 prog) b.IF.formula_struc_continuation}
  | IF.EInfer b -> IF.EInfer {b with IF.formula_inf_continuation = convert_struc2 prog b.IF.formula_inf_continuation}
  | IF.EList b -> IF.EList (map_l_snd (convert_struc2 prog) b)
  | IF.EOr b -> IF.EOr {b with
					IF.formula_struc_or_f1 = convert_struc2 prog b.IF.formula_struc_or_f1;
					IF.formula_struc_or_f2 = convert_struc2 prog b.IF.formula_struc_or_f2;}

	  
let order_views (view_decls0 : I.view_decl list) : I.view_decl list =
  (* generate pairs (vdef.view_name, v) where v is a view appearing in     *)
  (* vdef                                                                  *)
  let rec gen_name_pairs_heap vname h =
    match h with
      | IF.Star { IF.h_formula_star_h1 = h1; IF.h_formula_star_h2 = h2 } ->
            (gen_name_pairs_heap vname h1) @ (gen_name_pairs_heap vname h2)
      | IF.HeapNode { IF.h_formula_heap_name = c } ->
            (* if c = vname *)
            (* then [] *)
            (* else *)
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
  
  let rec gen_name_pairs_struc vname (f:IF.struc_formula): (ident * ident) list = match f with
	| IF.EAssume (b,_)-> (gen_name_pairs vname b)
	| IF.ECase b -> fold_l_snd (gen_name_pairs_struc vname) b.IF.formula_case_branches
	| IF.EBase {IF.formula_struc_base =fb; IF.formula_struc_continuation = cont}-> 
		(gen_name_pairs vname fb) @(fold_opt (gen_name_pairs_struc vname) cont)
    | IF.EInfer b -> gen_name_pairs_struc vname b.IF.formula_inf_continuation
	| IF.EList b ->  fold_l_snd (gen_name_pairs_struc vname) b
	| IF.EOr b -> (gen_name_pairs_struc vname b.IF.formula_struc_or_f1)@(gen_name_pairs_struc vname b.IF.formula_struc_or_f2)
  in
 
  let gen_name_pairs_struc vname (f:IF.struc_formula): (ident * ident) list =
    Debug.no_1 "gen_name_pairs_struc" pr_id (pr_list (pr_pair pr_id pr_id)) 
        (fun _ -> gen_name_pairs_struc vname f) vname in

  let build_graph vdefs =
    let tmp =
      List.map
          (fun vdef -> gen_name_pairs_struc vdef.I.view_name vdef.I.view_formula)
          vdefs in
    let selfrec = List.filter (fun l -> List.exists (fun (x,y) -> x=y) l) tmp in
    let selfrec = List.map (fun l -> fst (List.hd l)) selfrec in

    let edges = List.concat tmp in
    let g = NG.create () in
    let _ = (List.map
        (fun (v1, v2) -> NG.add_edge g (NG.V.create v1) (NG.V.create v2))
        edges) in
    let scclist = NGComponents.scc_list g in
    let mr = List.filter (fun l -> (List.length l)>1) scclist in
    let str = pr_list (pr_list pr_id) mr in
    let mutrec = List.concat mr in
    let selfrec = (Gen.BList.difference_eq (=) selfrec mutrec) in
    (* let _ = print_endline ("Self Rec :"^selfstr) in *)
    view_rec := selfrec@mutrec ;
    view_scc := scclist ;
    if not(mr==[]) 
    then report_warning no_pos ("View definitions "^str^" are mutually recursive") ;
    g
        (* if DfsNG.has_cycle g *)
        (* then failwith "View definitions are mutually recursive" *)
        (* else g *)
  in

  let g = build_graph view_decls0 in

  (* take out the view names in reverse order *)
  let view_names = ref ([] : ident list) in
  let store_name n = view_names := n :: !view_names in
  let _ = (TopoNG.iter store_name g) in

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
  let (r1, r2) = reorder_views view_decls0 !view_names 
  in r1 @ r2

let order_views (view_decls0 : I.view_decl list) : I.view_decl list =
  let pr x = string_of_ident_list (List.map (fun v -> v.I.view_name) x) in 
  Debug.no_1 "order_views" pr pr order_views  view_decls0
  
let loop_procs : (C.proc_decl list) ref = ref []
   
let rec seq_elim (e:C.exp):C.exp = match e with
  | C.Label b -> C.Label {b with C.exp_label_exp = seq_elim b.C.exp_label_exp;}
  | C.Assert _ -> e
	(*| C.ArrayAt b -> C.ArrayAt {b with C.exp_arrayat_index = (seq_elim b.C.exp_arrayat_index); } (* An Hoa *)*)
	(*| C.ArrayMod b -> C.ArrayMod {b with C.exp_arraymod_lhs = C.arrayat_of_exp (seq_elim (C.ArrayAt b.C.exp_arraymod_lhs)); C.exp_arraymod_rhs = (seq_elim b.C.exp_arraymod_rhs); } (* An Hoa *)*) 
  | C.Assign b -> C.Assign {b with C.exp_assign_rhs = (seq_elim b.C.exp_assign_rhs); }  
  | C.Bind b ->  C.Bind {b with C.exp_bind_body = (seq_elim b.C.exp_bind_body);}
  | C.Barrier _ -> e
  | C.ICall _ -> e
  | C.SCall _ -> e
  | C.Block b-> Cast.Block {b with Cast.exp_block_body = seq_elim b.C.exp_block_body}
  | C.Cast b -> C.Cast {b with C.exp_cast_body = (seq_elim b.C.exp_cast_body)}
  | C.Catch b -> Error.report_error {Error.error_loc = b.C.exp_catch_pos; Error.error_text = ("malformed cast, unexpecte catch clause")}
  | C.Cond b -> C.Cond {b with C.exp_cond_then_arm  = (seq_elim b.C.exp_cond_then_arm);
							   C.exp_cond_else_arm  = (seq_elim b.C.exp_cond_else_arm);}
  | C.CheckRef _ -> e
  | C.BConst _ -> e
  | C.Debug _ 
  | C.Dprint _
  | C.FConst _
  | C.IConst _ 
  | C.Print _ 
  | C.Java _ -> e
	(*| C.ArrayAlloc a -> C.ArrayAlloc {a with (* An Hoa *)
		exp_aalloc_dimension = (seq_elim a.C.exp_aalloc_dimension); }*)
  | C.New _ -> e
  | C.Null _ -> e
	| C.EmptyArray _ -> e (* An Hoa *)
  | C.Sharp _ -> e
  | C.Seq b -> if (!seq_to_try) then 
					  C.Try ({	C.exp_try_type = b.C.exp_seq_type;
								C.exp_try_path_id = fresh_strict_branch_point_id "";
								C.exp_try_body =  (seq_elim b.C.exp_seq_exp1);
								C.exp_catch_clause = (C.Catch{
														  C.exp_catch_flow_type = !norm_flow_int;
														  C.exp_catch_flow_var = None;
														  C.exp_catch_var = Some (Void, 
														  (fresh_var_name "_sq_" b.C.exp_seq_pos.start_pos.Lexing.pos_lnum));
														  C.exp_catch_body = (seq_elim b.C.exp_seq_exp2);
														  C.exp_catch_pos = b.C.exp_seq_pos});
								C.exp_try_pos = b.C.exp_seq_pos })
				else C.Seq {b with C.exp_seq_exp1 = seq_elim b.C.exp_seq_exp1 ;
							 C.exp_seq_exp2 = seq_elim b.C.exp_seq_exp2 ;}
  | C.This _ -> e
  | C.Time _ -> e
  | C.Try b ->  C.Try {b with  
				C.exp_try_body = seq_elim b.C.exp_try_body;
				C.exp_catch_clause = 
					let c = C.get_catch_of_exp b.C.exp_catch_clause in
					C.Catch {c with C.exp_catch_body = (seq_elim c.C.exp_catch_body)};}
  | C.Unit _ -> e 
  | C.Unfold _ -> e
  | C.Var _ -> e
  | C.VarDecl _ -> e
  | C.While b -> C.While {b with Cast.exp_while_body = seq_elim b.Cast.exp_while_body}
   
(*transform labels into exceptions, remove the finally clause,
should also check that 
*)
let rec while_labelling (e:I.exp):I.exp = 
		let label_breaks lb e :I.exp = 		
			I.map_exp e (fun c-> match c with 
			   | I.Block _ -> None
			   | I.While _ -> Some c
			   | I.Break b -> 
				    let ty = I.Const_flow (match b.I.exp_break_jump_label with | I.NoJumpLabel -> "brk_"^lb | I.JumpLabel l-> "brk_"^l) in
					Some (I.mkRaise ty false None false b.I.exp_break_path_id b.I.exp_break_pos)
			   | I.Continue b -> 
					let ty = I.Const_flow (match b.I.exp_continue_jump_label with | I.NoJumpLabel -> "cnt_"^lb | I.JumpLabel l-> "cnt_"^l) in
					Some (I.mkRaise ty false None false b.I.exp_continue_path_id b.I.exp_continue_pos )
			   | _ -> None) in
		let need_break_continue_x lb ne non_generated_label :bool = 
			if not (non_generated_label) then 
			 I.fold_exp ne (fun c-> match c with 
				| I.While _ -> Some false
				| I.Break {I.exp_break_jump_label=b}
				| I.Continue {I.exp_continue_jump_label=b}-> Some (b=I.NoJumpLabel) 
				| _ -> None) (fun c-> List.exists (fun c-> c) c) false 
			else 
			 I.fold_exp ne  (fun c-> match c with 
				| I.Block {I.exp_block_jump_label=b; I.exp_block_pos = pos}
				| I.While {I.exp_while_jump_label=b; I.exp_while_pos = pos}-> (match b with
									| I.NoJumpLabel -> None 
									| I.JumpLabel l -> if (String.compare l lb) ==0 then Gen.report_error pos("label"^l^" is duplicated")
										else None)			 
				| I.Break {I.exp_break_jump_label=b}
				| I.Continue {I.exp_continue_jump_label=b}-> 
					Some (match b with 
							 |I.JumpLabel l ->  (String.compare lb l)==0
							 |I.NoJumpLabel -> false)
				| _ -> None) (fun c-> List.exists (fun c-> c) c) false  in
		let  need_break_continue lb ne non_generated_label :bool = 
			Debug.no_2 "need_break_continue" string_of_bool Iprinter.string_of_exp string_of_bool 
			(fun _ _-> need_break_continue_x lb ne non_generated_label) non_generated_label ne in
	I.map_exp e (fun c-> match c with 
		| I.Break b ->
			let ty = I.Const_flow (match b.I.exp_break_jump_label with 
					| I.NoJumpLabel -> Gen.report_error b.I.exp_break_pos "there is no loop/block to break out of"
					| I.JumpLabel l-> l) in
			Some (I.mkRaise ty false None false b.I.exp_break_path_id b.I.exp_break_pos)
		| I.Continue b ->  
			let ty = I.Const_flow (match b.I.exp_continue_jump_label with 
					| I.NoJumpLabel -> Gen.report_error b.I.exp_continue_pos "there is no loop to continue"
					| I.JumpLabel l-> l) in
			Some (I.mkRaise ty false None false b.I.exp_continue_path_id b.I.exp_continue_pos)
		| I.Block b-> None 
			(*let pos = b.I.exp_block_pos in
			let nl,b_rez = match b.I.exp_block_jump_label with
					| I.NoJumpLabel -> ((fresh_label pos),false)
					| I.JumpLabel l -> (l ,true)in
			if (need_break_continue nl b.I.exp_block_body b_rez) then
				let ne = while_labelling (label_breaks nl b.I.exp_block_body) in
				let (nb,nc) = ("brk_"^nl,"cnt_"^nl) in
				let _  = exlist # add_edge nb brk_top in
				let _  = exlist # add_edge nc cont_top in
				let nl = fresh_branch_point_id "" in
				let nl2 = fresh_branch_point_id "" in
				let nit= I.mkTry ne [I.mkCatch None nc None (I.Label((nl,1),I.Empty pos)) pos] [] nl pos in
				Some (I.mkTry nit [I.mkCatch None nb None (I.Label((nl2,1),I.Empty pos)) pos] [] nl2 pos)
			else None*)
		| I.While b -> 
				let pos = b.I.exp_while_pos in
				let nl,b_rez = match b.I.exp_while_jump_label with
						| I.NoJumpLabel -> ((fresh_label pos),false)
						| I.JumpLabel l -> (l,true) in
				let (nb,nc) = ("brk_"^nl,"cnt_"^nl) in
				if (need_break_continue nl b.I.exp_while_body b_rez) then				
						 let ne  = while_labelling (label_breaks nl b.I.exp_while_body) in
						 let _  = exlist # add_edge nb brk_top in
						 let _  = exlist # add_edge nc cont_top in 
						 let nl1 = fresh_branch_point_id "" in
						 let nl2 = fresh_branch_point_id "" in
						 let continue_try = I.mkTry ne [I.mkCatch None None nc None (I.Label ((nl1,1),I.Empty pos)) pos] [] nl1 pos in	
						 let break_try = I.mkTry (I.This {I.exp_this_pos = pos}) [ I.mkCatch None None nb None (I.Label ((nl2,1),I.Empty pos)) pos] [] nl2 pos in
						 Some (I.While {b with I.exp_while_body = continue_try;I.exp_while_wrappings= Some (break_try,nb)})
				else Some (I.While {b with I.exp_while_body = while_labelling (label_breaks nl b.I.exp_while_body);I.exp_while_wrappings= None})
			
		| I.Try b ->
					let pos = b.I.exp_try_pos in
					if (List.length b.I.exp_finally_clause)==0 then None
					else 
						let ob = I.mkTry ( while_labelling b.I.exp_try_block) (List.map while_labelling b.I.exp_catch_clauses) [] b.I.exp_try_path_id pos in
						let l_catch = List.map (fun c-> 
								let c = I.get_finally_of_exp c in
								let f_body = while_labelling c.I.exp_finally_body in
								let new_name = fresh_var_name "fi" b.I.exp_try_pos.start_pos.Lexing.pos_lnum in
								let new_flow_var_name = fresh_var_name "flv" b.I.exp_try_pos.start_pos.Lexing.pos_lnum in
								let new_raise = I.mkRaise (I.Var_flow new_flow_var_name) false  (Some (I.mkVar new_name pos)) true  None pos in
								let catch_body = I.mkBlock (I.mkSeq f_body new_raise pos) I.NoJumpLabel [] pos in
								I.mkCatch (Some new_name) None c_flow (Some new_flow_var_name) catch_body pos
								) b.I.exp_finally_clause in
						Some (I.mkTry ob l_catch [] None pos)
		|_ -> None)
	
and needs_ret e = I.fold_exp e (fun c-> match c with | I.Return _ -> Some true | _ -> None) (List.exists (fun c-> c)) false 
	
and while_return e ret_type = I.map_exp e (fun c-> match c with 
		| I.While b -> 
			let needs_ret = needs_ret b.I.exp_while_body in 
			if needs_ret then
				let new_body = I.map_exp b.I.exp_while_body (fun c -> match c with | I.Return b-> 
					Some (I.mkRaise (I.Const_flow loop_ret_flow) true b.I.exp_return_val false b.I.exp_return_path_id b.I.exp_return_pos) | _ -> None) in
				let b = {b with I.exp_while_body = new_body} in
				let pos = b.I.exp_while_pos in
				let nl2 = fresh_branch_point_id "" in
				let vn = fresh_name () in
				let return  = I.Return { I.exp_return_val = Some (I.Var { I.exp_var_name= vn; I.exp_var_pos = pos}); I.exp_return_path_id = nl2; I.exp_return_pos = pos} in
				let catch = I.mkCatch (Some vn) (Some ret_type) loop_ret_flow None return pos in
				Some (I.mkTry (I.While b) [catch] [] nl2 pos)
			else Some c
		|_ -> None)
   
and prepare_labels_x (fct: I.proc_decl): I.proc_decl = 
  let rec syntax_err_breaks e in_loop l_lbl = 
		let f_args (in_loop,l_lbl) e = match e with 
			| I.While b -> (true, match b.I.exp_while_jump_label with I.NoJumpLabel -> l_lbl | I.JumpLabel l -> l::l_lbl) 
			| _ -> (in_loop,l_lbl) in
		let f (in_loop,l_lbl) e = match e with 
			| I.Block b -> if (b.I.exp_block_jump_label<> I.NoJumpLabel) then Gen.report_error b.I.exp_block_pos "blocks should be unlabeled"
						 else None
			| I.Continue {I.exp_continue_jump_label = l1; I.exp_continue_pos = pos} 
			| I.Break {I.exp_break_jump_label = l1; I.exp_break_pos = pos} -> 
				if not in_loop then Gen.report_error  pos "break/continue statements are allowed only within loops"
				else (match l1 with 
						| I.NoJumpLabel-> None
						| I.JumpLabel l -> 
								if not (List.exists (fun c-> String.compare c l ==0) l_lbl) then Gen.report_error pos ("undefined label "^l)
							else None)
			| _ -> None in
		  I.iter_exp_args e (in_loop,l_lbl) f f_args in
  match fct.I.proc_body with
	| None -> fct
	| Some e-> (syntax_err_breaks e false []; {fct with I.proc_body = Some (while_labelling (while_return e fct.I.proc_return))})

and prepare_labels (fct: I.proc_decl): I.proc_decl =
  let pr = Iprinter.string_of_proc_decl in
  Debug.no_1 "prepare_labels" pr pr prepare_labels_x fct 

and substitute_seq (fct: C.proc_decl): C.proc_decl = match fct.C.proc_body with
	| None -> fct
	| Some e-> {fct with C.proc_body = Some (seq_elim e)}

let trans_logical_vars lvars =
  List.map (fun (id,_,_)-> CP.SpecVar(lvars.I.exp_var_decl_type, id, Unprimed)) lvars.I.exp_var_decl_decls
  
(*HIP*)
let rec trans_prog (prog4 : I.prog_decl) (*(iprims : I.prog_decl)*): C.prog_decl =
  (* let _ = print_string ("--> input prog4 = \n"^(Iprinter.string_of_program prog4)^"\n") in *)
  (* print_string "trans_prog\n"; *)
  let _ = (exlist # add_edge "Object" "") in
  let _ = (exlist # add_edge "String" "Object") in
  let _ = (exlist # add_edge raisable_class "Object") in
  let _ = I.inbuilt_build_exc_hierarchy () in (* for inbuilt control flows *)
  (* let _ = (exlist # add_edge error_flow "Object") in *)
  (* let _ = I.build_exc_hierarchy false iprims in (\* Errors - defined in prelude.ss*\) *)
  let prog4 = I.add_bar_inits prog4 in
  let prog4 = if not (!do_infer_inc) then prog4 else
    try
      let id_spec_from_file = Infer.get_spec_from_file prog4 in
      let ids, specs = List.split id_spec_from_file in
      {prog4 with I.prog_proc_decls =
          let new_proc, others = List.partition (fun x -> List.mem x.I.proc_name ids) prog4.I.prog_proc_decls in
          let new_proc = 
            List.map (fun proc ->
              try 
                let spec = List.assoc proc.I.proc_name id_spec_from_file in
                {proc with I.proc_static_specs = spec}
              with Not_found -> proc
            ) new_proc
          in
          others @ new_proc
      }
    with _ -> prog4
  in
  let _ = I.build_exc_hierarchy true prog4 in  (* Exceptions - defined by users *)
  (* let prog3 = *)
  (*         { prog4 with I.prog_data_decls = iprims.I.prog_data_decls @ prog4.I.prog_data_decls; *)
  (*                      I.prog_proc_decls = iprims.I.prog_proc_decls @ prog4.I.prog_proc_decls; *)
  (*         } *)
  (* in *)
  (*let _ = exlist # compute_hierarchy in*)
  (* let _ = print_endline (exlist # string_of ) in *)
  let prog3 = prog4 in
  let prog2 = { prog3 with I.prog_data_decls =
          ({I.data_name = raisable_class;I.data_fields = [];I.data_parent_name = "Object";I.data_invs = [];I.data_methods = []})
          ::({I.data_name = error_flow;I.data_fields = [];I.data_parent_name = "Object";I.data_invs = [];I.data_methods = []})
          :: prog3.I.prog_data_decls;} in
  (* let _ = print_endline (exlist # string_of ) in *)
  (* let _ = I.find_empty_static_specs prog2 in *)
  let prog2 = I.add_normalize_lemmas prog2 in
  let prog1 = { prog2 with
	  I.prog_proc_decls = List.map prepare_labels prog2.I.prog_proc_decls;
	  I.prog_data_decls = List.map (fun c-> {c with I.data_methods = List.map prepare_labels c.I.data_methods;}) prog2.I.prog_data_decls; } in
  let _ = exlist # compute_hierarchy in	  
  (* let _ = print_endline (Exc.string_of_exc_list (3)) in *)
  (* let _ = I.find_empty_static_specs prog1 in *)
  let prog0 = { prog1 with
      I.prog_data_decls = I.remove_dup_obj prog1.I.prog_data_decls;} in

  (* let _ = print_string ("--> input \n"^(Iprinter.string_of_program prog0)^"\n") in *)
  (* let _ = I.find_empty_static_specs prog0 in *)
  let _ = I.build_hierarchy prog0 in
  (* let _ = print_string "trans_prog :: I.build_hierarchy PASSED\n" in *)
  let check_overridding = Chk.overridding_correct prog0 in
  let check_field_dup = Chk.no_field_duplication prog0 in
  let check_method_dup = Chk.no_method_duplication prog0 in
  let check_field_hiding = Chk.no_field_hiding prog0 in
  if check_field_dup && (check_method_dup && (check_overridding && check_field_hiding))
  then
    ( begin
      (* let _ = print_flush (Exc.string_of_exc_list (10)) in *)
	  (* exlist # compute_hierarchy; *)
      (* let _ = print_endline (Exc.string_of_exc_list (11)) in *)
	  let prims,prim_rels = gen_primitives prog0 in
      (* let prim_rel_ids = List.map (fun rd -> (RelT,rd.I.rel_name)) prim_rels in *)
   let prims = List.map (fun p -> {p with I.proc_is_main = false}) prims in 
	  (* let prims,prim_rels = ([],[]) in *)
	  let prog = { (prog0) with I.prog_proc_decls = prims @ prog0.I.prog_proc_decls;
		  (* AN HOA : adjoint the program with primitive relations *)
		  I.prog_rel_decls = prim_rels @ prog0.I.prog_rel_decls;
		  (* I.prog_rel_ids = prim_rel_ids @ prog0.I.prog_rel_ids; *)
      } in
      (set_mingled_name prog;
      let all_names =(List.map (fun p -> p.I.proc_mingled_name) prog0.I.prog_proc_decls) @
        (List.map (fun ddef -> ddef.I.data_name) prog0.I.prog_data_decls) @
            (List.map (fun vdef -> vdef.I.view_name) prog0.I.prog_view_decls)(*@
			(List.map (fun bdef -> bdef.I.barrier_name) prog0.I.prog_barrier_decls)*) in
      let dups = Gen.BList.find_dups_eq (=) all_names in
      (* let _ = I.find_empty_static_specs prog in *)
      if not (Gen.is_empty dups) then
		(print_string ("duplicated top-level name(s): " ^((String.concat ", " dups) ^ "\n")); failwith "Error detected - astsimp")
      else (
		  let prog = case_normalize_program prog in

		  let prog = if !infer_slicing then slicing_label_inference_program prog else prog in

		  (* let _ = print_string ("\ntrans_prog: Iast.prog_decl: " ^ (Iprinter.string_of_program prog) ^ "\n") in *)
		  
          (* let _ =  print_endline " after case normalize" in *)
          (* let _ = I.find_empty_static_specs prog in *)
		  let tmp_views = order_views prog.I.prog_view_decls in
		  let _ = Iast.set_check_fixpt prog.I.prog_data_decls tmp_views in
		  let cviews = List.map (trans_view prog) tmp_views in
		  (* let _ = print_string "trans_prog :: trans_view PASSED\n" in *)
		  let crels = List.map (trans_rel prog) prog.I.prog_rel_decls in (* An Hoa *)
          let _ = prog.I.prog_rel_ids <- List.map (fun rd -> (RelT,rd.I.rel_name)) prog.I.prog_rel_decls in
          let chps = List.map (trans_hp prog) prog.I.prog_hp_decls in 
           let _ = prog.I.prog_hp_ids <- List.map (fun rd -> (HpT,rd.I.hp_name)) prog.I.prog_hp_decls in
		  let caxms = List.map (trans_axiom prog) prog.I.prog_axiom_decls in (* [4/10/2011] An Hoa *)
		  (* let _ = print_string "trans_prog :: trans_rel PASSED\n" in *)
		  let cdata =  List.map (trans_data prog) prog.I.prog_data_decls in
		  (* let _ = print_string "trans_prog :: trans_data PASSED\n" in *)
		  (* let _ = print_endline ("trans_prog :: trans_data PASSED :: procs = " ^ (Iprinter.string_of_proc_decl_list prog.I.prog_proc_decls)) in *)
		  let cprocs1 = List.map (trans_proc prog) prog.I.prog_proc_decls in
		  (* let _ = print_string "trans_prog :: trans_proc PASSED\n" in *)
		  let cprocs = !loop_procs @ cprocs1 in
		  let (l2r_coers, r2l_coers) = trans_coercions prog in
		  let log_vars = List.concat (List.map (trans_logical_vars) prog.I.prog_logical_var_decls) in 
		  let bdecls = List.map (trans_bdecl prog) prog.I.prog_barrier_decls in
		  let cprog = {
			  C.prog_data_decls = cdata;
			  C.prog_view_decls = cviews;
			  C.prog_barrier_decls = bdecls;
			  C.prog_logical_vars = log_vars;
			  C.prog_rel_decls = crels; (* An Hoa *)
              C.prog_hp_decls = chps;
			  C.prog_axiom_decls = caxms; (* [4/10/2011] An Hoa *)
			  (*C.old_proc_decls = cprocs;*)
			  C.new_proc_decls = C.create_proc_decls_hashtbl cprocs;
			  C.prog_left_coercions = l2r_coers;
			  C.prog_right_coercions = r2l_coers;} in
	    let cprog1 = { cprog with			
			  (* C.old_proc_decls = List.map substitute_seq cprog.C.old_proc_decls; *)
        C.new_proc_decls = C.proc_decls_map substitute_seq cprog.C.new_proc_decls; 
			  C.prog_data_decls = List.map (fun c-> {c with C.data_methods = List.map substitute_seq c.C.data_methods;}) cprog.C.prog_data_decls; } in  
          (ignore (List.map (fun vdef -> compute_view_x_formula cprog vdef !Globals.n_xpure) cviews);
          ignore (List.map (fun vdef -> set_materialized_prop vdef) cviews);
          ignore (C.build_hierarchy cprog1);
          let cprog1 = fill_base_case cprog1 in
          let cprog2 = sat_warnings cprog1 in   
		  let cprog2 = Solver.normalize_perm_prog cprog2 in
          let cprog3 = if (!Globals.enable_case_inference or !Globals.allow_pred_spec) then pred_prune_inference cprog2 else cprog2 in
		  (*let cprog3 = normalize_fracs cprog3 in*)
          let _ = List.map (check_barrier_wf cprog3) cprog3.C.prog_barrier_decls in   
          (*let cprog4 = (add_pre_to_cprog cprog3) in*)
        (* Termination: Mark recursive calls and call order of function
         * Normalize the term specification with call number and implicit
         * phase variable *)
	      let c = (mark_rec_and_call_order cprog3) in
        let c = 
          if not !Globals.dis_term_chk 
          then Cast.add_term_nums_prog c 
          else c 
        in
        let c = (add_pre_to_cprog c) in
        (* let _ = print_endline (exlist # string_of) in *)
        (* let _ = exlist # sort in *)
	      (* let _ = if !Globals.print_core then print_string (Cprinter.string_of_program c) else () in *)
		   c)))
	end)
  else failwith "Error detected"

(* and trans_prog (prog : I.prog_decl) : C.prog_decl = *)
(*   Debug.loop_1_no "trans_prog" (fun _ -> "?") (fun _ -> "?") trans_prog_x prog *)

(* Replaced to use new_proc_decls *)
(*  
and add_pre_to_cprog cprog = 
  {cprog with C.old_proc_decls = List.map (fun c -> 
      let ns = add_pre(*_debug*) cprog c.Cast.proc_static_specs in
      let _ = c.Cast.proc_stk_of_static_specs # push ns in
      c
	  (* {c with  Cast.proc_static_specs_with_pre = add_pre(\*_debug*\) cprog c.Cast.proc_static_specs; *)
    (*     (\*Cast.proc_dynamic_specs = add_pre cprog c.Cast.proc_dynamic_specs;*\)} *)
  ) cprog.C.old_proc_decls;}	
*)

and add_pre_to_cprog cprog = 
  { cprog with C.new_proc_decls = C.proc_decls_map (fun c -> 
    let ns = add_pre cprog c.C.proc_static_specs in
    let _ = c.C.proc_stk_of_static_specs # push ns in
    c
  ) cprog.C.new_proc_decls; }	

and sat_warnings cprog = 
  let warn n discard = 
    print_string ("the view body for "^n^" contains unsat branch(es) :"^(List.fold_left (fun a c-> a^"\n   "^(Cprinter.string_of_formula c)) "" discard)^"\n") in
  
  let trim_unsat (f:CF.formula):(CF.formula* CF.formula list) =  
    let goods,unsat_list = Solver.find_unsat cprog f in
    let nf = List.fold_left ( fun a c -> CF.mkOr a c no_pos) (CF.mkFalse (CF.mkTrueFlow ()) no_pos) goods in
    (nf,unsat_list) in
	
  let trim_unsat_l f = 
    let r1,r2 = List.split (List.map (fun (c1,c2)-> 
        let r1,r2 = trim_unsat c1 in
        ((r1,c2),r2)) f) in
    (r1,(List.concat r2)) in
  
  let n_pred_list = List.map (fun c->       
      let nf,unsat_list =  trim_unsat_l c.Cast.view_un_struc_formula in      
      if ((List.length unsat_list)> 0) then warn c.Cast.view_name unsat_list else ();            
	  let test f = match f with
		| CF.EBase b -> (match b.CF.formula_struc_continuation with
			| None -> List.map (fun d-> CF.EBase {b with CF.formula_struc_base = d}) (fst (Solver.find_unsat cprog b.CF.formula_struc_base)) 
			| _ -> [f])
		| _ -> [f] in
      let ncf = match c.Cast.view_formula with 
		| CF.EList b-> CF.EList (List.concat (List.map (fun (l,c)-> List.map (fun c-> (l,c)) (test c)) b))
		| _ -> (match test c.Cast.view_formula with 
					| x::[] -> x
					| _ as l-> CF.EList (List.map (fun c-> (empty_spec_label_def,c)) l)) in
(*		List.fold_left (fun a c-> match (snd c) with
        | CF.EBase b -> if ((List.length b.CF.formula_ext_continuation)>0) then c::a
          else 
            let goods, unsat_list = Solver.find_unsat cprog b.CF.formula_ext_base in 
            (List.map (fun d-> (fst c, CF.EBase {b with CF.formula_ext_base = d})) goods) @ a 
        |  _ -> c::a) [] c.Cast.view_formula in      *)
      {c with Cast.view_un_struc_formula = nf; Cast.view_formula = ncf}    
  ) cprog.Cast.prog_view_decls in  
  {cprog with Cast.prog_view_decls = n_pred_list;}
      
      
and trans_data (prog : I.prog_decl) (ddef : I.data_decl) : C.data_decl =
  (* Update the list of undefined data types *)
  (** 
	  * An Hoa [22/08/2011] : translate field with inline consideration.
  **)
  let trans_field ((t, c), pos, il) =
    ((trans_type prog t pos), c)
  in
  (* let _ = print_endline ("[trans_data] translate data type { " ^ ddef.I.data_name ^ " }") in
	 let temp = expand_inline_fields ddef.I.data_fields in
	 let _ = print_endline "[trans_data] expand inline fields result :" in
	 let _ = print_endline (Iprinter.string_of_decl_list temp "\n") in *)
  let res = {
      C.data_name = ddef.I.data_name;
      C.data_fields = List.map trans_field (I.expand_inline_fields prog.I.prog_data_decls ddef.I.data_fields);
      C.data_parent_name = ddef.I.data_parent_name;
      C.data_methods = List.map (trans_proc prog) ddef.I.data_methods;
      C.data_invs = [];
  } in
  (* let _ = print_endline ("[trans_data] output = " ^ (Cprinter.string_of_data_decl res)) in *)
  res


and compute_view_x_formula (prog : C.prog_decl) (vdef : C.view_decl) (n : int) =
  Debug.no_3 "compute_view_x_formula"
      Cprinter.string_of_program Cprinter.string_of_view_decl string_of_int 
      (fun x -> "")
      compute_view_x_formula_x prog vdef n
	  
and compute_view_x_formula_x (prog : C.prog_decl) (vdef : C.view_decl) (n : int) =
  (if n > 0 then
      (let pos = CF.pos_of_struc_formula vdef.C.view_formula in

	   if !do_slicing && !multi_provers then
		 let rec trans_formula_to_memo = function
		   | CF.Or ({ CF.formula_or_f1 = f1; CF.formula_or_f2 = f2 }) ->
			 let mpf1 = trans_formula_to_memo f1 in
			 let mpf2 = trans_formula_to_memo f2 in
			 mkOr_mems mpf1 mpf2
		   | CF.Base ({ CF.formula_base_pure = p }) -> p
		   | CF.Exists ({ CF.formula_exists_pure = p }) -> p
		 in

		 let rec trans_exists_to_base f = match f with
		   | CF.Or o ->
			 let ({ CF.formula_or_f1 = f1; CF.formula_or_f2 = f2 }) = o in
			 let nf1 = trans_exists_to_base f1 in
			 let nf2 = trans_exists_to_base f2 in
			 CF.Or { o with CF.formula_or_f1 = nf1; CF.formula_or_f2 = nf2 }
		   | CF.Base _ -> f
		   | CF.Exists ({ CF.formula_exists_qvars = qvars; CF.formula_exists_pure = p; CF.formula_exists_pos = pos }) ->
			 let np = memo_pure_push_exists_lhs qvars p in (* Not push Exists on linking vars at LHS *)
			 CF.formula_of_mix_formula np pos
		 in 

		 let (sxform', saddr_vars', sms) = Solver.xpure_symbolic_slicing prog (C.formula_of_unstruc_view_f vdef) in
		 let sxform = trans_exists_to_base sxform' in
		 
		 let addr_vars = CP.remove_dups_svl saddr_vars' in
		 let formula = CF.formula_of_mix_formula vdef.C.view_user_inv pos in
		 let ctx = CF.build_context (CF.true_ctx ( CF.mkTrueFlow ()) Lab2_List.unlabelled pos) sxform pos in
		 let (rs, _) = Solver.heap_entail_init prog false (CF.SuccCtx [ ctx ]) formula pos in
		 let _ = if not(CF.isFailCtx rs)
           then
			 let pxform = trans_formula_to_memo sxform in
			 (vdef.C.view_x_formula <- pxform;
              vdef.C.view_addr_vars <- addr_vars;
              vdef.C.view_baga <- (match sms.CF.mem_formula_mset with | [] -> [] | h::_ -> h) ;
              compute_view_x_formula prog vdef (n - 1))
           else report_error pos "view formula does not entail supplied invariant\n" in ()
	   else
		 let (xform', addr_vars', ms) = Solver.xpure_symbolic prog (C.formula_of_unstruc_view_f vdef) in	 
		 let addr_vars = CP.remove_dups_svl addr_vars' in
		 let xform = MCP.simpl_memo_pure_formula Solver.simpl_b_formula Solver.simpl_pure_formula xform' (TP.simplify_a 10) in
		 let formula1 = CF.formula_of_mix_formula xform pos in
		 let ctx = CF.build_context (CF.true_ctx ( CF.mkTrueFlow ()) Lab2_List.unlabelled pos) formula1 pos in
		 let formula = CF.formula_of_mix_formula vdef.C.view_user_inv pos in
		 let (rs, _) = Solver.heap_entail_init prog false (CF.SuccCtx [ ctx ]) formula pos in
		 let _ = if not(CF.isFailCtx rs) then
		  (vdef.C.view_x_formula <- xform;
		   vdef.C.view_addr_vars <- addr_vars;
		   vdef.C.view_baga <- (match ms.CF.mem_formula_mset with | [] -> [] | h::_ -> h) ;
		   compute_view_x_formula_x prog vdef (n - 1))
		  else report_error pos "view formula does not entail supplied invariant\n" in ()
    )
  else ();
  if !Globals.print_x_inv && (n = 0)
  then
    (print_string ("\ncomputed invariant for view: " ^ vdef.C.view_name ^"\n" ^(Cprinter.string_of_mix_formula vdef.C.view_x_formula) ^"\n");
    print_string ("addr_vars: " ^(String.concat ", "(List.map CP.name_of_spec_var vdef.C.view_addr_vars))^ "\n\n"))
  else ())

(* TODO WN : this is not doing anything *)
and fill_view_param_types (vdef : I.view_decl) =
  if (String.length vdef.I.view_data_name) = 0 then report_error no_pos ("fill_view_param_types error!")
  else ()

and find_pred_by_self vdef data_name = vdef.I.view_pt_by_self 
  (* Gen.BList.difference_eq (=) vdef.I.view_pt_by_self [data_name] *)

and trans_view (prog : I.prog_decl) (vdef : I.view_decl) : C.view_decl =
  let pr = Iprinter.string_of_view_decl in
  let pr_r = Cprinter.string_of_view_decl in
  Debug.no_1 "trans_view" pr pr_r  (fun _ -> trans_view_x prog vdef) vdef

and trans_view_x (prog : I.prog_decl) (vdef : I.view_decl) : C.view_decl =
  let stab = H.create 103 in
  let view_formula1 = vdef.I.view_formula in
  let _ = IF.has_top_flow_struc view_formula1 in
  (*let recs = rec_grp prog in*)
  let data_name = if (String.length vdef.I.view_data_name) = 0  then  I.incr_fixpt_view  prog.I.prog_data_decls prog.I.prog_view_decls
  else vdef.I.view_data_name in
  (vdef.I.view_data_name <- data_name;
  let vtv = vdef.I.view_typed_vars in
  List.iter (fun (t,c) -> 
      if t==UNK 
      then () 
      else H.add stab c {sv_info_kind=t; id=fresh_int() }) vtv ;
  H.add stab self { sv_info_kind = (Named data_name);id = fresh_int () };
  (* let _ = vdef.I.view_typed_vars <- [] in (\* removing the typed arguments *\) *)
  let cf = trans_I2C_struc_formula_x prog true (self :: vdef.I.view_vars) vdef.I.view_formula stab false in
  let inv_lock = vdef.I.view_inv_lock in
  let inv_lock = 
    (match inv_lock with
      | None -> None
      | Some f -> 
          let new_f = trans_formula prog true (self :: vdef.I.view_vars) true f stab false in
          Some new_f)
  in
  let cf = CF.mark_derv_self vdef.I.view_name cf in 
  let inv = vdef.I.view_invariant in
  let _ = gather_type_info_pure prog inv stab in
  let pf = trans_pure_formula inv stab in
  (* Thai : pf - user given invariant in core form *) 
  let pf = Cpure.arith_simplify 1 pf in
  let cf_fv = List.map CP.name_of_spec_var (CF.struc_fv cf) in
  let inv_lock_fv = match inv_lock with
    | None -> []
    | Some f -> List.map CP.name_of_spec_var (CF.fv f)
  in
  let pf_fv = List.map CP.name_of_spec_var (CP.fv pf) in

  if (List.mem res_name cf_fv) || (List.mem res_name pf_fv) || (List.mem res_name inv_lock_fv)  then
    report_error (IF.pos_of_struc_formula view_formula1) "res is not allowed in view definition or invariant"
  else(
      let pos = IF.pos_of_struc_formula view_formula1 in
      let view_sv_vars = List.map (fun c-> trans_var (c,Unprimed) stab pos) vdef.I.view_vars in
       let self_c_var = Cpure.SpecVar ((Named data_name), self, Unprimed) in
      let _ = 
        let vs1 = (CF.struc_fv cf) in
        let vs2 = (self_c_var::view_sv_vars) in
        let ffv = Gen.BList.difference_eq (CP.eq_spec_var) vs1 vs2 in
        (*filter out holes (#) *)
        let ffv = List.filter (fun v -> not (CP.is_hole_spec_var v)) ffv in
        if (ffv!=[]) then report_error no_pos ("error 1: free variables "^(Cprinter.string_of_spec_var_list ffv)^" in view def "^vdef.I.view_name^" ") in
      let typed_vars = List.map ( fun (Cpure.SpecVar (c1,c2,c3))-> (c1,c2)) view_sv_vars in
      let _ = vdef.I.view_typed_vars <- typed_vars in
      let mvars = [] in
      let cf = CF.label_view cf in
      let n_un_str =  CF.get_view_branches cf in   
      let rec f_tr_base f = 
        let mf f h fl pos = if (CF.is_complex_heap h) then (CF.mkFalse fl pos)  else f in
        match f with
          | CF.Base b -> mf f b.CF.formula_base_heap b.CF.formula_base_flow b.CF.formula_base_pos
          | CF.Exists b -> mf f b.CF.formula_exists_heap b.CF.formula_exists_flow b.CF.formula_exists_pos
          | CF.Or b -> CF.mkOr (f_tr_base b.CF.formula_or_f1) (f_tr_base b.CF.formula_or_f2) no_pos in
      let rbc = List.fold_left (fun a (c,l)-> 
          let fc = f_tr_base c in
          if (CF.isAnyConstFalse fc) then a 
          else match a with 
            | Some f1  -> Some (CF.mkOr f1 fc no_pos)
            | None -> Some fc) None n_un_str in
      (* TODO : This has to be generalised to mutual-recursion *)
      let ir = is_view_recursive vdef.I.view_name in
      let sf = find_pred_by_self vdef data_name in
      let cf = CF.struc_formula_set_lhs_case false cf in
      (* Thai : we can compute better pure inv named new_pf here that 
         should be stronger than pf *)
	  let new_pf = (*Fixcalc.compute_inv vdef.I.view_name view_sv_vars n_un_str*) pf in
      let memo_pf_P = MCP.memoise_add_pure_P (MCP.mkMTrue pos) new_pf in
      let memo_pf_N = MCP.memoise_add_pure_N (MCP.mkMTrue pos) new_pf in
      let cvdef ={
          C.view_name = vdef.I.view_name;
          C.view_vars = view_sv_vars;
          C.view_uni_vars = [];
          C.view_labels = vdef.I.view_labels;
          C.view_modes = vdef.I.view_modes;
          C.view_partially_bound_vars = [];
          C.view_materialized_vars = mvars;
          C.view_data_name = data_name;
          C.view_formula = cf;
          C.view_x_formula = memo_pf_P;
          C.view_addr_vars = [];
          C.view_baga = [];
          C.view_complex_inv = None;
          C.view_user_inv = memo_pf_N;
          C.view_inv_lock = inv_lock;
          C.view_un_struc_formula = n_un_str;
          C.view_base_case = None;
          C.view_is_rec = ir;
          C.view_pt_by_self = sf;
          C.view_case_vars = Gen.BList.intersect_eq (=) view_sv_vars (CF.guard_vars cf);
          C.view_raw_base_case = rbc;
          C.view_prune_branches = [];
          C.view_prune_conditions = [];
          C.view_prune_conditions_baga = [];
          C.view_prune_invariants = []} in
      (Debug.devel_zprint (lazy ("\n" ^ (Cprinter.string_of_view_decl cvdef))) (CF.pos_of_struc_formula cf);
      cvdef)
  )
  )

and fill_one_base_case prog vd = Debug.no_1 "fill_one_base_case" Cprinter.string_of_view_decl Cprinter.string_of_view_decl (fun vd -> fill_one_base_case_x prog vd) vd
	 
and fill_one_base_case_x prog vd = 
  {vd with C.view_base_case = compute_base_case prog vd.C.view_un_struc_formula (Cpure.SpecVar ((Named vd.C.view_data_name), self, Unprimed) ::vd.C.view_vars)}
      
and  fill_base_case prog =  {prog with C.prog_view_decls = List.map (fill_one_base_case prog) prog.C.prog_view_decls }    
  
(* An Hoa : trans_rel *)
and trans_rel (prog : I.prog_decl) (rdef : I.rel_decl) : C.rel_decl =
  let pos = IP.pos_of_formula rdef.I.rel_formula in
  let rel_sv_vars = List.map (fun (var_type, var_name) -> CP.SpecVar (trans_type prog var_type pos, var_name, Unprimed)) rdef.I.rel_typed_vars in
  let stab = H.create 103 in
  let _ = List.map (fun (var_type, var_name) -> H.add stab var_name { sv_info_kind = (trans_type prog var_type pos);id = fresh_int () };) rdef.I.rel_typed_vars in
  (* Need to collect the type information before translating the formula *)
  let _ = gather_type_info_pure prog rdef.I.rel_formula stab in
  let crf = trans_pure_formula rdef.I.rel_formula stab in
  {C.rel_name = rdef.I.rel_name; 
  C.rel_vars = rel_sv_vars;
  C.rel_formula = crf; }

and trans_hp (prog : I.prog_decl) (hpdef : I.hp_decl) : C.hp_decl =
  let pos = IF.pos_of_formula hpdef.I.hp_formula in
  let hp_sv_vars = List.map (fun (var_type, var_name) -> CP.SpecVar (trans_type prog var_type pos, var_name, Unprimed)) hpdef.I.hp_typed_vars in
  let stab = H.create 103 in
  let _ = List.map (fun (var_type, var_name) -> H.add stab var_name { sv_info_kind = (trans_type prog var_type pos);id = fresh_int () };) hpdef.I.hp_typed_vars in
  (* Need to collect the type information before translating the formula *)
  let _ = gather_type_info_formula prog hpdef.I.hp_formula stab false in
  let crf = trans_formula  prog false [] false hpdef.I.hp_formula stab false in
  {C.hp_name = hpdef.I.hp_name; 
   C.hp_vars = hp_sv_vars;
   C.hp_formula = crf; }

and trans_axiom (prog : I.prog_decl) (adef : I.axiom_decl) : C.axiom_decl =
  let pr1 adef = Iprinter.string_of_axiom_decl_list [adef] in
  let pr2 adef = Cprinter.string_of_axiom_decl_list [adef] in
  Debug.no_1 "trans_axiom" pr1 pr2 (fun x -> trans_axiom_x prog adef) adef

(**
   * An Hoa : translate an axiom 
*)
and trans_axiom_x (prog : I.prog_decl) (adef : I.axiom_decl) : C.axiom_decl =
  (* Collect types of variables in the formula *)
  let stab = H.create 103 in
  let _ = gather_type_info_pure prog adef.I.axiom_hypothesis stab in
  let _ = gather_type_info_pure prog adef.I.axiom_conclusion stab in
  (* Translate the hypothesis and conclusion *)
  let chyp = trans_pure_formula adef.I.axiom_hypothesis stab in
  let ccln = trans_pure_formula adef.I.axiom_conclusion stab in
  (* let _ = Smtsolver.add_axiom_def (Smtsolver.AxmDefn (chyp,ccln)) in *)
  { 	C.axiom_hypothesis = chyp;
  C.axiom_conclusion = ccln; }
      (* END : trans_axiom *) 

and rec_grp prog :ident list =
  let r = List.map (fun c-> (c.Iast.view_name, (IF.view_node_types_struc c.Iast.view_formula))) prog.Iast.prog_view_decls in	
  let sccs = List.fold_left (fun a (c1,c2)-> if (List.mem c1 c2) then c1::a else a) [] r in
  let rec trans_cl (l:ident list):ident list =
    let int_l = List.fold_left (fun a (c1,c2)-> if (List.exists (fun c-> List.mem c l) c2) then c1::a else a) l r in
    let int_l = Gen.BList.remove_dups_eq (=) int_l in
    if (List.length int_l)=(List.length l) then int_l
    else trans_cl int_l in
  let recs = trans_cl sccs in
  let recs = Gen.BList.difference_eq (=) recs (List.map (fun c-> c.Iast.data_name)prog.Iast.prog_data_decls) in
  recs
 
and compute_base_case prog cf vars = 
  let pr1 x = Cprinter.string_of_list_formula (fst (List.split x)) in
  let pr2 = Cprinter.string_of_spec_var_list in
  let pr3 = pr_option (fun (p, _) -> Cprinter.string_of_pure_formula p) in
  Debug.no_2 "compute_base_case" pr1 pr2 pr3 (fun _ _ -> compute_base_case_x prog cf vars) cf vars

and compute_base_case_x prog cf vars = (*flatten_base_case cf s self_c_var *)
  let xpuring f = 
    let (xform', _ , _) = Solver.xpure_symbolic prog f in
    let xform = simpl_memo_pure_formula Solver.simpl_b_formula Solver.simpl_pure_formula xform' (TP.simplify_a 10) in
    ([],[fold_mem_lst (CP.mkTrue no_pos) true true xform]) in
  let rec part f = match f with
    | CF.Or b -> 
          let (c1,c2) = part b.CF.formula_or_f1 in
          let (d1,d2) = part b.CF.formula_or_f2 in
          (c1@d1,c2@d2)
    | CF.Base b -> 
          if (CF.is_complex_heap b.CF.formula_base_heap) then xpuring f          
          else ([b.CF.formula_base_pure],[])
    | CF.Exists e -> 
          if (CF.is_complex_heap e.CF.formula_exists_heap) then xpuring f
          else 
            let l1,qv = e.CF.formula_exists_pure, e.CF.formula_exists_qvars in
           ([MCP.memo_pure_push_exists qv l1],[]) in
  let sim,co = List.split(List.map (fun (c,_)-> part c) cf) in
  let sim,co = List.concat sim, List.concat co in
  if (sim==[]) then None 
  else
    let guards = List.map (fold_mem_lst (CP.mkTrue no_pos) true true) sim in
	let cases = sim in
    let cases = List.fold_left mkOr_mems (mkMFalse no_pos) cases in  
    let bcg = List.fold_left (fun a p -> a@(CP.split_conjunctions (TP.simplify_a (-1) p))) [] guards in
    let bcg = Gen.BList.remove_dups_eq (CP.equalFormula_f CP.eq_spec_var) bcg in
    let one_bc = List.fold_left (fun a c -> CP.mkOr a c None no_pos) (CP.mkFalse no_pos) guards in
    let bc_impl c = let r,_,_ = TP.imply_sub_no one_bc c "0" false None in r in
    let sat_subno  = ref 0 in
    let bcg = List.filter (fun c->(not (CP.isConstTrue c))&& (bc_impl c)&& List.for_all 
		(fun d-> not (TP.is_sat_sub_no (CP.mkAnd c d no_pos) sat_subno)) co ) bcg in
    match bcg with
      | []-> None
      | _ -> Some (CP.disj_of_list bcg no_pos,cases)
            

and set_materialized_prop cdef =
  let args = (CP.SpecVar (Named "", self, Unprimed))::cdef.C.view_vars in
  let mvars = find_materialized_prop args (C.formula_of_unstruc_view_f cdef) in
  (cdef.C.view_materialized_vars <- mvars; cdef)
      
and find_m_prop_heap eq_f h = 
  let pr = Cprinter.string_of_h_formula in
  let prr x = string_of_int (List.length x) in
  Debug.no_1 "find_m_prop_heap" pr prr (fun _ -> find_m_prop_heap_x eq_f h) h
      
and find_m_prop_heap_x eq_f h = match h with
  | CF.DataNode h ->
        let l = eq_f h.CF.h_formula_data_node in
        List.map (fun v -> C.mk_mater_prop v true []) l 
  | CF.ViewNode h -> 
        let l = eq_f h.CF.h_formula_view_node in
        List.map (fun v -> C.mk_mater_prop v true [ h.CF.h_formula_view_name]) l 
  | CF.Star h -> (find_m_prop_heap_x eq_f h.CF.h_formula_star_h1)@(find_m_prop_heap_x eq_f h.CF.h_formula_star_h2)
  | CF.Conj h -> (find_m_prop_heap_x eq_f h.CF.h_formula_conj_h1)@(find_m_prop_heap_x eq_f h.CF.h_formula_conj_h2)
  | CF.Phase h -> (find_m_prop_heap_x eq_f h.CF.h_formula_phase_rd)@(find_m_prop_heap_x eq_f h.CF.h_formula_phase_rw)  
  | CF.Hole _ 
  | CF.HTrue 
  | CF.HFalse 
  | CF.HEmp -> []

and param_alias_sets p params = 
  let eqns = ptr_equations_with_null p in
  let asets = Context.alias_nth 10 eqns in
  let aset_get x = x:: (Context.get_aset asets x) in
  List.map (fun c-> ( aset_get c,c)) params
      
and find_materialized_prop params (f0 : CF.formula) : C.mater_property list = 
  let f_l = CF.list_of_disjuncts f0 in
  let is_member (aset :(CP.spec_var list * CP.spec_var)list) v = 
    let l = List.filter (fun (l,_) -> List.exists (CP.eq_spec_var v) l) aset in
    snd (List.split l) in
  let find_m_one f = match f with
    | CF.Base b ->    
          let has = param_alias_sets b.CF.formula_base_pure params in
          find_m_prop_heap (is_member has) b.CF.formula_base_heap
    | CF.Exists b->
          let has = param_alias_sets b.CF.formula_exists_pure params in
          find_m_prop_heap (is_member has) b.CF.formula_exists_heap      
    | _ -> Error.report_error 
          {Error.error_loc = no_pos; Error.error_text = "find_materialized_prop: unexpected disjunction"} in
  let lm = List.map find_m_one f_l in
  let rec elim_dups l = match l with
    | [] -> []
    | x::[] -> l
    | x::y::t -> 
          if (C.mater_prop_cmp x y) ==0 then
            elim_dups ((C.merge_mater_props x y) ::t)
          else x:: (elim_dups (y::t)) in
  let lm = List.map (fun c -> elim_dups (List.sort C.mater_prop_cmp c)) lm in
  let to_partial l = List.map (fun c-> {c with C.mater_full_flag = false}) l in
  let rec merge_mater_lists l1 l2 = match l1,l2 with 
    | [], _ -> to_partial l2
    | _ , [] -> to_partial l1 
    | x::t1,y::t2 -> 
          let r = C.mater_prop_cmp x y in 
          if r<0 then {x with C.mater_full_flag = false} ::(merge_mater_lists t1 l2)
          else if r>0 then {y with C.mater_full_flag = false}:: (merge_mater_lists l1 t2)
          else (C.merge_mater_props x y)::(merge_mater_lists t1 t2) in
  if  (List.length lm ==0) then []
  else 
    List.fold_left (fun a c -> merge_mater_lists a c)(List.hd lm) (List.tl lm)
        
(*
  and set_materialized_vars prog cdef =
  let mvars =
  find_materialized_vars prog cdef.C.view_vars (*cdef.C.view_formula*) (C.formula_of_unstruc_view_f cdef)
  in
  (cdef.C.view_materialized_vars <- mvars; cdef)

  and find_materialized_vars_x prog params (f0 : CF.formula) : CP.spec_var list =
  let tmp0 = find_mvars prog params f0 in
  let all_mvars = ref tmp0 in
  let ef = ref f0 in
  let quit_loop = ref false
  in
  (while not !quit_loop do 
  ef := Solver.expand_all_preds prog !ef false;		
  (let tmp1 = find_mvars prog params !ef in
  let tmp2 = Gen.BList.remove_dups_eq CP.eq_spec_var (tmp1 @ !all_mvars) in
  let tmp3 = Gen.BList.difference_eq CP.eq_spec_var tmp2 !all_mvars
  in if Gen.is_empty tmp3 then quit_loop := true else all_mvars := tmp3)
  done;
  !all_mvars)

  and find_materialized_vars prog params (f0 : CF.formula) : CP.spec_var list =
  let pr1 = Cprinter.string_of_spec_var_list in 
  let pr2 = Cprinter.string_of_formula in 
  Debug.no_2 "find_materialized_vars" pr1 pr2 pr1 (fun _ _ -> find_materialized_vars_x prog params (f0 : CF.formula)) params f0


  and find_mvars prog (params : CP.spec_var list) (f0 : CF.formula) :
  CP.spec_var list =
  match f0 with
  | CF.Or { CF.formula_or_f1 = f1; CF.formula_or_f2 = f2 } ->
  let mvars1 = find_mvars prog params f1 in
  let mvars2 = find_mvars prog params f2 in
  let mvars = Gen.BList.remove_dups_eq CP.eq_spec_var (mvars1 @ mvars2) in
  let tmp = CP.intersect mvars params in 
  tmp
  | CF.Base { CF.formula_base_heap = hf; CF.formula_base_pure = pf } ->
  let mvars = find_mvars_heap prog params hf pf in
  let tmp = CP.intersect mvars params in 
  tmp
  | CF.Exists
  {
  CF.formula_exists_qvars = qvars;
  CF.formula_exists_heap = hf;
  CF.formula_exists_pure = pf
  } ->
  let mvars1 = find_mvars_heap prog params hf pf in
  let mvars = Gen.BList.difference_eq CP.eq_spec_var mvars1 qvars in
  let tmp = CP.intersect mvars params in 
  tmp

  and find_mvars_heap prog params hf pf : CP.spec_var list =
  match hf with
  | CF.HTrue | CF.HFalse -> []
  | _ ->
  let eqns = MCP.ptr_equations_with_null pf in
  let asets = Context.alias eqns in
  let self_aset =
  Context.get_aset asets (CP.SpecVar (Named "", self, Unprimed))
  in self_aset
*)
and all_paths_return (e0 : I.exp) : bool =
  match e0 with
	| I.ArrayAt _ -> false (* An Hoa *)
    | I.Assert _ -> false
    | I.Assign _ -> false
	| I.Barrier _ -> false
    | I.Binary _ -> false
    | I.Bind e -> all_paths_return e.I.exp_bind_body
    | I.Block e -> all_paths_return e.I.exp_block_body
    | I.BoolLit _ -> false
    | I.Break _ -> false
    | I.CallNRecv _ -> false
    | I.CallRecv _ -> false
    | I.Cast _ -> false
    | I.Catch b-> all_paths_return b.I.exp_catch_body
    | I.Cond e ->
	      (all_paths_return e.I.exp_cond_then_arm) &&
              (all_paths_return e.I.exp_cond_else_arm)
    | I.ConstDecl _ -> false
    | I.Continue _ -> false
    | I.Debug _ -> false
    | I.Dprint _ -> false
    | I.Empty _ -> false
    | I.FloatLit _ -> false
    | I.Finally b-> all_paths_return b.I.exp_finally_body
    | I.IntLit _ -> false
    | I.Java _ -> false
    | I.Label (_,e)-> all_paths_return e
    | I.Member _ -> false
	| I.ArrayAlloc _ -> false (* An Hoa *)
    | I.New _ -> false
    | I.Null _ -> false
    | I.Return _ -> true
    | I.Seq e ->(all_paths_return e.I.exp_seq_exp1) || (all_paths_return e.I.exp_seq_exp2)
    | I.This _ -> false
    | I.Time _ -> false
    | I.Unary _ -> false
    | I.Var _ -> false
    | I.VarDecl _ -> false
    | I.While _ -> false
    | I.Unfold _ -> false
    | I.Raise _ -> true
    | I.Try e -> (all_paths_return e.I.exp_try_block) || (List.fold_left (fun a b-> a && (all_paths_return b)) true e.I.exp_catch_clauses)
          || match e.I.exp_finally_clause with 
            | [] -> false
            | h::t -> (all_paths_return h)

and check_return (proc : I.proc_decl) : bool =
  match proc.I.proc_body with
    | None -> true
    | Some e ->
	      if
            (not (I.are_same_type I.void_type proc.I.proc_return)) &&
                (not (all_paths_return e))
	      then false
	      else true
and set_pre_flow f = 
  let pr = Cprinter.string_of_struc_formula in
  Debug.no_1 "set_pre_flow" pr pr set_pre_flow_x f

and set_pre_flow_x f = 
  let nf = {CF.formula_flow_interval = !norm_flow_int; CF.formula_flow_link =None} in
  let rec helper f0 = match f0 with
    | CF.EBase b-> CF.EBase {b with
		  CF.formula_struc_base = CF.set_flow_in_formula_override nf b.CF.formula_struc_base;
		  CF.formula_struc_continuation = map_opt set_pre_flow_x b.CF.formula_struc_continuation}
    | CF.ECase b-> CF.ECase {b with CF.formula_case_branches = map_l_snd helper b.CF.formula_case_branches;}
    | CF.EAssume (b1,b2,b3)-> CF.EAssume (b1,b2,b3)
    | CF.EInfer b -> CF.EInfer {b with CF.formula_inf_continuation = helper b.CF.formula_inf_continuation}
	| CF.EList b -> CF.EList (map_l_snd helper b) 
	| CF.EOr b -> CF.EOr {b with CF.formula_struc_or_f1 = helper b.CF.formula_struc_or_f1; CF.formula_struc_or_f2 = helper b.CF.formula_struc_or_f2;} in
	helper f
	

and check_valid_flows (f:IF.struc_formula) = 
  let rec check_valid_flows_f f = match f with
    | IF.Base b -> if ((is_false_flow (exlist # get_hash b.IF.formula_base_flow))&&
		  ((String.compare b.IF.formula_base_flow false_flow)<>0))then 
	    Error.report_error {Error.error_loc = b.IF.formula_base_pos;Error.error_text = "undefined flow type "^b.IF.formula_base_flow;}
    | IF.Exists b -> if (is_false_flow (exlist # get_hash b.IF.formula_exists_flow))&&
	    ((String.compare b.IF.formula_exists_flow false_flow)<>0)then 
	      Error.report_error {Error.error_loc = b.IF.formula_exists_pos;Error.error_text = "undefined flow type "^b.IF.formula_exists_flow;}
    | IF.Or b-> (check_valid_flows_f b.IF.formula_or_f1);(check_valid_flows_f b.IF.formula_or_f2)
  in
  let rec helper f0 = match f0 with
    | IF.EBase b-> 
		check_valid_flows_f b.IF.formula_struc_base; 
		(match b.IF.formula_struc_continuation with | None -> () | Some l-> helper l)
    | IF.ECase b-> (List.iter (fun d-> check_valid_flows (snd d)) b.IF.formula_case_branches)
    | IF.EAssume (b,_)-> check_valid_flows_f b
    | IF.EInfer b -> helper b.IF.formula_inf_continuation
	| IF.EList b -> List.iter (fun c-> helper(snd c)) b
	| IF.EOr b -> helper b.IF.formula_struc_or_f1; helper b.IF.formula_struc_or_f2 in
	helper f
     
and trans_proc (prog : I.prog_decl) (proc : I.proc_decl) : C.proc_decl =
  (*let pr  x = add_str (x.I.proc_name^" Spec") Iprinter.string_of_struc_formula x.I.proc_static_specs in
  let pr2 x = add_str (x.C.proc_name^" Spec") Cprinter.string_of_struc_formula x.C.proc_static_specs in
  *)let pr  = Iprinter.string_of_proc_decl in
  let pr2 = Cprinter.string_of_proc_decl 5 in
     Debug.no_1 "trans_proc" pr pr2 (trans_proc_x prog) proc
	 
and trans_proc_x (prog : I.prog_decl) (proc : I.proc_decl) : C.proc_decl =
  let dup_names = Gen.BList.find_one_dup_eq (fun a1 a2 -> a1.I.param_name = a2.I.param_name) proc.I.proc_args in
  if not (Gen.is_empty dup_names) then
    (let p = List.hd dup_names in
    Err.report_error{
        Err.error_loc = p.I.param_loc;
        Err.error_text = "parameter " ^ (p.I.param_name ^ " is duplicated");})
  else if not (check_return proc) then
    Err.report_error {
        Err.error_loc = proc.I.proc_loc;
        Err.error_text = "not all paths of " ^ (proc.I.proc_name ^ " contain a return"); }
  else
    (E.push_scope ();
    (let all_args = 
      if Gen.is_some proc.I.proc_data_decl then
        (let cdef = Gen.unsome proc.I.proc_data_decl in
        let this_arg ={
            I.param_type = Named cdef.I.data_name;
            I.param_name = this;
            I.param_mod = I.NoMod;
            I.param_loc = proc.I.proc_loc;} in 
        this_arg :: proc.I.proc_args)
      else proc.I.proc_args in
    let p2v (p : I.param) = {
        E.var_name = p.I.param_name;
        E.var_alpha = p.I.param_name;
        E.var_type = p.I.param_type; } in
    let vinfos = List.map p2v all_args in
    let _ = List.map (fun v -> E.add v.E.var_name (E.VarInfo v)) vinfos in
    let cret_type = trans_type prog proc.I.proc_return proc.I.proc_loc in
    let free_vars = List.map (fun p -> p.I.param_name) all_args in
    let stab = H.create 103 in
    let add_param p = H.add stab p.I.param_name {
        sv_info_kind =  (trans_type prog p.I.param_type p.I.param_loc);
        id = fresh_int () } in
    (ignore (List.map add_param all_args);
	let _ = H.add stab res_name { sv_info_kind = cret_type;id = fresh_int () } in
	let _ = H.add stab eres_name { sv_info_kind = UNK ;id = fresh_int () } in
  (* Termination: Add info of logical vars *)
  let add_logical (CP.SpecVar (t, i, _)) = H.add stab i { 
    sv_info_kind = t; 
    id = fresh_int () } in
  let log_vars = List.concat (List.map (trans_logical_vars) prog.I.prog_logical_var_decls) in 
  (ignore (List.map add_logical log_vars));

	let _ = check_valid_flows proc.I.proc_static_specs in
	let _ = check_valid_flows proc.I.proc_dynamic_specs in
    (* let _ = print_endline ("trans_proc: "^ proc.I.proc_name ^": before set_pre_flow: specs = " ^ (Iprinter.string_of_struc_formula (proc.I.proc_static_specs@proc.I.proc_dynamic_specs))) in *)
	let static_specs_list = set_pre_flow (trans_I2C_struc_formula prog true free_vars proc.I.proc_static_specs stab true) in
	(* let _ = print_string "trans_proc :: set_pre_flow PASSED 1\n" in *)
	let dynamic_specs_list = set_pre_flow (trans_I2C_struc_formula prog true free_vars proc.I.proc_dynamic_specs stab true) in
  (* Termination: Normalize the specification 
   * with the default termination information
   * Primitive functions: Term[] 
   * User-defined functions: MayLoop *)
  let is_primitive = not (proc.I.proc_is_main) in
  let static_specs_list = CF.norm_struc_with_lexvar is_primitive static_specs_list in
  let dynamic_specs_list = CF.norm_struc_with_lexvar is_primitive dynamic_specs_list in
  
	let exc_list = (List.map (exlist # get_hash) proc.I.proc_exceptions) in
	let r_int = exlist # get_hash abnormal_flow in
    (*annotated may and must error in specs*)
    (* let t_int = exlist # get_hash top_flow in *)
    (* let e_int = exlist # get_hash error_flow in *)
    (* let exc_list = exc_list@[t_int;e_int] in *)
	(if (List.exists is_false_flow exc_list)|| (List.exists (fun c-> not (CF.subsume_flow r_int c)) exc_list) then
	  Error.report_error {Err.error_loc = proc.I.proc_loc;Err.error_text =" can not throw an instance of a non throwable class"}
	else ()) ;
	let _ = Cast.check_proper_return cret_type exc_list dynamic_specs_list in 
	let _ = Cast.check_proper_return cret_type exc_list static_specs_list in 
	(* let _ = print_string "trans_proc :: Cast.check_proper_return PASSED \n" in *)
    (* let _ = print_endline "WN : removing result here" in *)
	let _ = H.remove stab res_name in
	let body =match proc.I.proc_body with
	  | None -> None
	  | Some e -> (* let _ = print_string ("trans_proc :: Translate body " ^ Iprinter.string_of_exp e ^ "\n") in *) Some (fst (trans_exp prog proc e)) in
	(* let _ = print_string "trans_proc :: proc body translated PASSED \n" in *)
	let args = List.map (fun p -> ((trans_type prog p.I.param_type p.I.param_loc), (p.I.param_name))) proc.I.proc_args in
	(** An Hoa : compute the important variables **)
	let ftypes, fnames = List.split args in
	(* fsvars are the spec vars corresponding to the parameters *)
	let imp_vars = List.map2 (fun t -> fun v -> CP.SpecVar (t, v, Unprimed)) ftypes fnames in
(*	let _ = print_string "Function parameters : " in                    *)
(*	let _ = print_endline (Cprinter.string_of_spec_var_list imp_vars) in*)
	(** An Hoa : end **)
	let by_names_tmp = List.filter (fun p -> p.I.param_mod = I.RefMod) proc.I.proc_args in
	let new_pt p = trans_type prog p.I.param_type p.I.param_loc in
	let by_names = List.map (fun p -> CP.SpecVar (new_pt p, p.I.param_name, Unprimed)) by_names_tmp in
	let static_specs_list  = CF.plug_ref_vars by_names static_specs_list in
	let dynamic_specs_list = CF.plug_ref_vars by_names dynamic_specs_list in
    (*=============================*)
	let by_val_tmp = List.filter (fun p -> p.I.param_mod = I.NoMod) proc.I.proc_args in
	let new_pt p = trans_type prog p.I.param_type p.I.param_loc in
    (*pass-by-value parameters*)
	let by_val = List.map (fun p -> CP.SpecVar (new_pt p, p.I.param_name, Unprimed)) by_val_tmp in
    (*check and add VPERM when need*)
    let static_specs_list = 
      if (!Globals.ann_vp) then
        CF.norm_struc_vperm static_specs_list by_names by_val
      else
        static_specs_list
    in
    let dynamic_specs_list = 
      if (!Globals.ann_vp) then
        CF.norm_struc_vperm dynamic_specs_list by_names by_val
      else
        dynamic_specs_list
    in
    (*=============================*)
	let final_static_specs_list = if CF.isConstDTrue static_specs_list then Cast.mkEAssume_norm proc.I.proc_loc else static_specs_list in
	(** An Hoa : print out final_static_specs_list for inspection **)
	(* let _ = print_string "Static spec list : " in *)
(*	let _ = print_endline (Cprinter.string_of_struc_formula final_static_specs_list) in*)
	let imp_spec_vars = collect_important_vars_in_spec final_static_specs_list in
	let imp_vars = List.append imp_vars imp_spec_vars in
	let imp_vars = List.append imp_vars [CP.mkRes cret_type] in (* The res variable is also important! *)
	(* let _ = print_string "Important variables found: " in *)
(*	let _ = print_endline (Cprinter.string_of_spec_var_list imp_vars) in*)
	(** An Hoa : end **)
	let final_dynamic_specs_list = dynamic_specs_list in
    (* TODO: is below being computed multiple times? *)
    let args2 = args@(prog.I.prog_rel_ids) in
    let _ = 
      let cmp x (_,y) = (String.compare (CP.name_of_spec_var x) y) == 0 in
      
      let log_vars = List.concat (List.map (trans_logical_vars) prog.I.prog_logical_var_decls) in 
      let struc_fv = CP.diff_svl (CF.struc_fv_infer final_static_specs_list) log_vars in
      let ffv = Gen.BList.difference_eq cmp (*(CF.struc_fv_infer final_static_specs_list)*) struc_fv ((cret_type,res_name)::(Named raisable_class,eres_name)::args2) in
    if (ffv!=[]) then 
      Error.report_error { 
          Err.error_loc = no_pos; 
          Err.error_text = "error 3: free variables "^(Cprinter.string_of_spec_var_list ffv)^" in proc "^proc.I.proc_name^" "} in
	  let cproc ={
          C.proc_name = proc.I.proc_mingled_name;
          C.proc_args = args;
          C.proc_return = trans_type prog proc.I.proc_return proc.I.proc_loc;
		  C.proc_important_vars =  imp_vars(*(Gen.Basic.remove_dups (proc.I.proc_important_vars @imp_vars))*); (* An Hoa *)
          C.proc_static_specs = final_static_specs_list;
          C.proc_dynamic_specs = final_dynamic_specs_list;
          (* C.proc_static_specs_with_pre =  []; *)
          C.proc_stk_of_static_specs = new Gen.stack (* _noexc Cprinter.string_of_struc_formula (=) *);
          C.proc_by_name_params = by_names;
          C.proc_body = body;
          C.proc_logical_vars = [];
          C.proc_call_order = 0;
          C.proc_is_main = proc.I.proc_is_main;
          C.proc_is_recursive = false;
          C.proc_file = proc.I.proc_file;
          C.proc_loc = proc.I.proc_loc;} in 
	  (E.pop_scope (); cproc))))

(** An Hoa : collect important variables in the specification
	Important variables are the ones that appears in the
	post-condition. Those variables are necessary in order
	to prove the final correctness. **)
and collect_important_vars_in_spec (spec : CF.struc_formula) : (CP.spec_var list) =
  (** An Hoa : Internal function to collect important variables in the an ext_formula **)	
  let rec helper f = match f with
	  | CF.ECase b -> List.fold_left (fun x y -> List.append x (collect_important_vars_in_spec (snd y))) [] b.CF.formula_case_branches 
	  | CF.EBase b -> b.CF.formula_struc_implicit_inst
  	  | CF.EAssume (vars,fa,_) -> []
      | CF.EInfer _ -> []
	  | CF.EList b -> fold_l_snd helper b 
	  | CF.EOr b-> (helper b.CF.formula_struc_or_f1)@(helper b.CF.formula_struc_or_f2) in
  helper spec
  
      (** An Hoa : end collect_important_vars_in_spec **)
	  
(* transform coercion lemma from iast to cast *)
and trans_coercions (prog : I.prog_decl) :
      ((C.coercion_decl list) * (C.coercion_decl list)) =
  let tmp =
    List.map (fun coer -> trans_one_coercion prog coer)
        prog.I.prog_coercion_decls in
  let (tmp1, tmp2) = List.split tmp in
  let tmp3 = List.concat tmp1 in let tmp4 = List.concat tmp2 in (tmp3, tmp4)

and trans_one_coercion (prog : I.prog_decl) (coer : I.coercion_decl) :
      ((C.coercion_decl list) * (C.coercion_decl list)) =
  let pr x =  Iprinter.string_of_coerc_decl x in
  let pr2 (r1,r2) = pr_list Cprinter.string_of_coercion (r1@r2) in
  Debug.no_1 "trans_one_coercion" pr pr2 (fun _ -> trans_one_coercion_x prog coer) coer

(* let pr x = "?" in *)
(* let pr2 (r1,r2) = pr_list Cprinter.string_of_coercion (r1@r2) in *)
(* Debug.no_1 "trans_one_coercion" pr pr2 (fun _ -> trans_one_coercion_x prog coer) coer *)

(* TODO : add lemma name to self node to avoid cycle*)
and trans_one_coercion_x (prog : I.prog_decl) (coer : I.coercion_decl) :
      ((C.coercion_decl list) * (C.coercion_decl list)) =
  let stab = H.create 103 in
  let _ = gather_type_info_formula prog coer.I.coercion_head stab false in
  let _ = gather_type_info_formula prog coer.I.coercion_body stab false in
  let c_lhs = trans_formula prog false [ self ] false coer.I.coercion_head stab false in
  let c_lhs = CF.add_origs_to_node self c_lhs [coer.I.coercion_name] in
  let lhs_fnames0 = List.map CP.name_of_spec_var (CF.fv c_lhs) in (* free vars in the LHS *)
  let compute_univ () =
    let h, p, _, _,_ = CF.split_components c_lhs in
    let pvars =mfv p in
    let hvars = CF.h_fv h in
    let univ_vars = Gen.BList.difference_eq CP.eq_spec_var pvars hvars in 
    Gen.BList.remove_dups_eq CP.eq_spec_var univ_vars in
  let univ_vars = compute_univ () in
  let lhs_fnames = Gen.BList.difference_eq (=) lhs_fnames0 (List.map CP.name_of_spec_var univ_vars) in
  let c_rhs = trans_formula prog (Gen.is_empty univ_vars) ((* self :: *) lhs_fnames) false coer.I.coercion_body stab false in
  (*LDK: TODO: check for interraction with lemma proving*)
  (*pass lhs_heap into add_origs *)
  let lhs_heap ,_,_, _,_  = CF.split_components c_lhs in
  let lhs_view_name = match lhs_heap with
    | CF.ViewNode vn -> vn.CF.h_formula_view_name
    | CF.DataNode dn -> dn.CF.h_formula_data_name
    | _ -> 
          (*LDK: expecting complex LHS*)
          let hs = CF.split_star_conjunctions lhs_heap in
          if ( (List.length hs) > 0) then
            let head = List.hd hs in
            match head with
              | CF.ViewNode vn -> vn.CF.h_formula_view_name
              | CF.DataNode dn -> dn.CF.h_formula_data_name
              | _ -> 
                    let _ = print_string "[astsimp] Warning: lhs head node of a coercion is neither a view node nor a data node \n" in 
                    ""
          else
            let _ = print_string "[astsimp] Warning: lhs of a coercion is neither simple or complex\n" in 
            ""
  in
  (*LDK: In the body of a coercions, there may be multiple nodes with
    a same name with self => only add [coercion_name] to origins of the
    first node*)
  let  coercion_lhs_type = (CF.type_of_formula c_lhs) in
  let c_rhs = match (coercion_lhs_type) with
    | CF.Simple -> CF.add_origs_to_first_node self lhs_view_name c_rhs [coer.I.coercion_name]
    | CF.Complex -> c_rhs
  in
  (* c_body_norm is used only for proving l2r part of a lemma (left & equiv lemmas) *)
  let h = List.map (fun c-> (c,Unprimed)) lhs_fnames0 in
  let p = List.map (fun c-> (c,Primed)) lhs_fnames0 in
  let wf,_ = case_normalize_struc_formula prog h p (IF.formula_to_struc_formula coer.I.coercion_body) false true [] in
  let quant = true in
  let cs_body_norm = trans_I2C_struc_formula prog quant (* fv_names *) lhs_fnames0 wf stab false in
  (* c_head_norm is used only for proving r2l part of a lemma (right & equiv lemmas) *)
  let (qvars, form) = IF.split_quantifiers coer.I.coercion_head in 
  let c_hd0, c_guard0, c_fl0, c_a0 = IF.split_components form in
  (* remove the guard from the normalized head as it will be later added to the body of the right lemma *)
  let new_head =  IF.mkExists qvars c_hd0 (IP.mkTrue no_pos) c_fl0 [] no_pos in
  let guard_fnames = List.map (fun (id, _) -> id ) (IP.fv c_guard0) in
  let rhs_fnames = List.map CP.name_of_spec_var (CF.fv c_rhs) in
  let fnames = Gen.BList.remove_dups_eq (=) (guard_fnames@rhs_fnames) in
  let h = List.map (fun c-> (c,Unprimed)) fnames in
  let p = List.map (fun c-> (c,Primed)) fnames in
  let wf,_ = case_normalize_struc_formula prog h p (IF.formula_to_struc_formula new_head) false true [] in
  let quant = true in
  let cs_head_norm = trans_I2C_struc_formula prog quant (* fv_names  *) fnames  wf stab false in
  let c_head_norm = CF.struc_to_formula cs_head_norm in
  (* free vars in RHS but not LHS *)
  let ex_vars = Gen.BList.remove_dups_eq CP.eq_spec_var 
    (List.filter (fun v -> not(List.mem (CP.name_of_spec_var v) lhs_fnames0) ) (CF.fv c_rhs)) in 
  (* wrap exists for RHS - no implicit instantiation*)
  let c_rhs = CF.push_exists ex_vars c_rhs in
  let lhs_name = find_view_name c_lhs self (IF.pos_of_formula coer.I.coercion_head) in
  let rhs_name =
    try find_view_name c_rhs self (IF.pos_of_formula coer.I.coercion_body)
    with | _ -> "" in
  if lhs_name = "" then
    Error.report_error
        {
            Err.error_loc = IF.pos_of_formula coer.I.coercion_head;
            Err.error_text = "root pointer of node on LHS must be self";
        }
  else
    (  
        let args = CF.fv_simple_formula c_lhs in 
        let m_vars = find_materialized_prop args c_rhs in
        let c_coer ={ C.coercion_type = coer.I.coercion_type;
        C.coercion_name = coer.I.coercion_name;
        C.coercion_head = c_lhs;
        C.coercion_head_norm = c_head_norm;
        C.coercion_body = c_rhs;
        C.coercion_body_norm = cs_body_norm;
        C.coercion_impl_vars = []; (* ex_vars; *)
        C.coercion_univ_vars = univ_vars;
        C.coercion_head_view = lhs_name;
        C.coercion_body_view = rhs_name;
        C.coercion_mater_vars = m_vars;
        C.coercion_case = (Cast.case_of_coercion c_lhs c_rhs)} in
        let change_univ c = match c.C.coercion_univ_vars with
            (* move LHS guard to RHS regardless of universal lemma *)
          | v -> 
                let c_hd, c_guard ,c_fl ,c_t, c_a = CF.split_components c.C.coercion_head in
                let new_body = CF.normalize 1 c.C.coercion_body (CF.formula_of_mix_formula c_guard no_pos) no_pos in
                let new_body = CF.push_exists c.C.coercion_univ_vars new_body in
                {c with
                    C.coercion_type = Iast.Right;
                    C.coercion_head = CF.mkBase c_hd (mkMTrue no_pos) c_t c_fl c_a no_pos;
                    (* C.coercion_head_norm = new_head_norm; *)
                    C.coercion_body = new_body;
                    C.coercion_univ_vars = [];} in
        match coer.I.coercion_type with
          | I.Left -> 
                let c_coer = {c_coer with 
                    C.coercion_head = CF.set_lhs_case c_coer.C.coercion_head true;
                    C.coercion_body = CF.set_lhs_case c_coer.C.coercion_body false}
                in
                ([ c_coer ], [])
          | I.Equiv -> 
                let c_coer = {c_coer with 
                    C.coercion_head = CF.set_lhs_case c_coer.C.coercion_head true; 
                    C.coercion_body = CF.set_lhs_case c_coer.C.coercion_body false}
                in
                let c_coer1 = {c_coer with 
                    C.coercion_head = CF.set_lhs_case c_coer.C.coercion_head false;
                    C.coercion_body = CF.set_lhs_case c_coer.C.coercion_body true}
                in
                ([ {c_coer with C.coercion_type = I.Left} ], [change_univ c_coer1]) (*??? try*)
          | I.Right -> 
                let c_coer = {c_coer with 
                    C.coercion_head = CF.set_lhs_case c_coer.C.coercion_head false;
                    C.coercion_body = CF.set_lhs_case c_coer.C.coercion_body true}
                in
                ([], [ change_univ c_coer]))

(* match coer.I.coercion_type with *)
(*   | I.Left -> ([ c_coer ], []) *)
(*   | I.Equiv -> ([ {c_coer with C.coercion_type = I.Left} ], [change_univ c_coer]) *)
(*   | I.Right -> ([], [ change_univ c_coer])) *)

and find_view_name (f0 : CF.formula) (v : ident) pos =
  Debug.no_2 "find_view_name"  (fun x->x) Cprinter.string_of_formula (fun x->x)
      (fun _ _ -> find_view_name_x f0 v pos) v f0 
      
and find_view_name_x (f0 : CF.formula) (v : ident) pos =
  match f0 with
    | CF.Base {
          CF.formula_base_heap = h;
          CF.formula_base_pure = _;
          CF.formula_base_pos = _ } 
    | CF.Exists {
		  CF.formula_exists_qvars = _;
		  CF.formula_exists_heap = h;
		  CF.formula_exists_pure = _;
          CF.formula_exists_pos = _ } ->
	      let rec find_view_heap h0 =
            (match h0 with
              | CF.Star
		              {
		                  CF.h_formula_star_h1 = h1;
		                  CF.h_formula_star_h2 = h2;
		                  CF.h_formula_star_pos = _
		              } 
              | CF.Conj
		              {
		                  CF.h_formula_conj_h1 = h1;
		                  CF.h_formula_conj_h2 = h2;
		                  CF.h_formula_conj_pos = _
		              } 
              | CF.Phase
		              {
		                  CF.h_formula_phase_rd = h1;
		                  CF.h_formula_phase_rw = h2;
		                  CF.h_formula_phase_pos = _
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
                        (*LDK: allow 2 views of a same name*)
                        if (name1=name2)
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
		                  CF.h_formula_data_perm = _; (*LDK*)
		                  CF.h_formula_data_arguments = _;
		                  CF.h_formula_data_pos = _
		              } ->
		            if (CP.name_of_spec_var p) = v
		            then c
                      (*Err.report_error
                        {
                        Err.error_loc = pos;
                        Err.error_text = v ^ " must point to a view";
                        }*)
		            else ""
              | CF.ViewNode
		              {
		                  CF.h_formula_view_node = p;
		                  CF.h_formula_view_name = c;
		                  CF.h_formula_view_perm = _; (*LDK*)
		                  CF.h_formula_view_arguments = _;
		                  CF.h_formula_view_pos = _
		              } -> if (CP.name_of_spec_var p) = v then c else ""
              | CF.HTrue | CF.HFalse | CF.HEmp | CF.Hole _ -> "")
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
  Debug.no_1 "trans_exp"
      Iprinter.string_of_exp
      (pr_pair Cprinter.string_of_exp string_of_typ) 
      (fun _ -> trans_exp_x prog proc ie) ie 

and trans_exp_x (prog : I.prog_decl) (proc : I.proc_decl) (ie : I.exp) :
      trans_exp_type =
  (* let _ = print_endline ("[trans_exp] input = { " ^ (Iprinter.string_of_exp ie) ^ " }") in *)
  let rec helper ie =
    match ie with
      | I.Label (pid, e)-> 
            let e1,t1 = (helper e) in
            (C.Label {C.exp_label_type = t1; C.exp_label_path_id = pid; C.exp_label_exp = e1;},t1)
      | I.Unfold { I.exp_unfold_var = (v, p); I.exp_unfold_pos = pos } ->
            ((C.Unfold {
                C.exp_unfold_var = CP.SpecVar (Named "", v, p);
                C.exp_unfold_pos = pos;
            }), C.void_type)
	            (* An Hoa MARKED *)
	  | I.ArrayAt { I.exp_arrayat_array_base = a; 
	    I.exp_arrayat_index = index;
	    I.exp_arrayat_pos = pos } ->
	  	    let r = List.length index in
		    let new_e = I.CallNRecv {
			    I.exp_call_nrecv_method = array_access_call ^ (string_of_int r) ^ "d"; (* Update call *)					(* TODO CHECK IF THE ORDER IS CORRECT! IT MIGHT BE IN REVERSE ORDER *)
                I.exp_call_nrecv_lock = None;
			    I.exp_call_nrecv_arguments = a :: index;
			    I.exp_call_nrecv_path_id = None; (* No path_id is necessary because there is only one path *)
			    I.exp_call_nrecv_pos = pos;} in 
	        helper new_e
                (*(try
                  let vinfo_tmp = E.look_up a in (* look up the array variable *)
	              let ci,_ = helper i in (* translate the index exp *)
                  match vinfo_tmp with
                  | E.VarInfo vi ->
                  let ct = trans_type prog vi.E.var_type pos in
	              begin match ct with
	              | CP.Array et -> ((C.ArrayAt {
	              C.exp_arrayat_type = et;
	              C.exp_arrayat_array_base = a;
	              C.exp_arrayat_index = ci;
	              C.exp_arrayat_pos = pos; }),et)
	              | _ -> Err.report_error { Err.error_loc = pos; Err.error_text = a ^ " is not an array variable"; }
	              end 
                  | _ -> Err.report_error { Err.error_loc = pos; Err.error_text = a ^ " is not an array variable"; }
                  with | Not_found -> Err.report_error { Err.error_loc = pos; Err.error_text = a ^ " is not defined"; })*)
	            (* An Hoa END *)
      | I.Assert{
            I.exp_assert_asserted_formula = assert_f_o;
            I.exp_assert_assumed_formula = assume_f_o;
            I.exp_assert_path_id = pi;
            I.exp_assert_pos = pos} ->
            let tmp_names = E.visible_names () in
            let all_names =
              List.map (fun (t, n) -> ((trans_type prog t pos), n)) tmp_names in
            let free_vars = List.map snd all_names in
            let stab = H.create 19
            in
            (ignore
                (List.map (fun (t, n) -> H.add stab n { sv_info_kind = t;id = fresh_int () })
                    all_names);
            let assert_cf_o =
              (match assert_f_o with
                | Some f -> Some (trans_I2C_struc_formula prog false free_vars (fst f) stab false (*(Cpure.Void) [])*) )
                | None -> None) in
            let assume_cf_o =
              (match assume_f_o with
                | None -> None
                | Some f -> Some (trans_formula prog false free_vars true f stab false)) in
            let assert_e =
              C.Assert
                  {
                      C.exp_assert_asserted_formula = assert_cf_o;
                      C.exp_assert_assumed_formula = assume_cf_o;
                      C.exp_assert_path_id = pi;
                      C.exp_assert_pos = pos;
                  } in 
            (assert_e, C.void_type))
      | I.Assign	{
            I.exp_assign_op = aop;
            I.exp_assign_lhs = lhs;
            I.exp_assign_rhs = rhs;
            I.exp_assign_path_id = pid;
            I.exp_assign_pos = pos_a	} ->
			(* An Hoa : WORKING *)
		    (* let _ = print_endline ("[trans_exp] assignment input = { " ^ Iprinter.string_of_exp lhs ^ " , " ^ Iprinter.string_of_exp rhs ^ " }") in *)
			(* An Hoa : pre-process the inline field access *)
			let is_member_exp e = match e with | I.Member _ -> true | _ -> false in
			(* [Internal] function to expand an expression with a list of field access *)
			let rec produce_member_exps base fseqs = match base with
			  | I.Member{	I.exp_member_base = base_e;
				I.exp_member_fields = fs;
				I.exp_member_path_id = pid;
				I.exp_member_pos = pos } ->
					List.map (fun x -> I.Member {	I.exp_member_base = base_e;
					I.exp_member_fields = List.append fs [x];
					I.exp_member_path_id = pid;
					I.exp_member_pos = pos}) fseqs
			  | I.Var _ -> List.map (fun x -> I.Member {I.exp_member_base = base;
				I.exp_member_fields = [x];
				I.exp_member_path_id = pid;
				I.exp_member_pos = no_pos }) fseqs 
			  | _ -> failwith "produce_member_exps: unexpected pattern"
			in (* compute the list of field accesses that {lhs = rhs} should be expanded into *)
			let expand_field_list = 
			  if (is_member_exp lhs) then
				match lhs with
				  | I.Member {
						I.exp_member_base = bl;
						I.exp_member_fields = fl;
						I.exp_member_path_id = pidl;
						I.exp_member_pos = posl } ->
						let _,lhst = helper bl in
						let fs,remf,remt = compact_field_access_sequence prog lhst fl in
						if (remf = "") then [] 
						else I.look_up_all_fields prog (match remt with
						  | Named c -> I.look_up_data_def_raw prog.I.prog_data_decls c
						  | _ -> failwith "ERror!")
				  | _ -> failwith "expand_field_list: unexpected pattern"
			  else if (is_member_exp rhs) then
				match rhs with
				  | I.Member {
						I.exp_member_base = br;
						I.exp_member_fields = fr;
						I.exp_member_path_id = pidr;
						I.exp_member_pos = posr } ->
						let _,rhst = helper br in
						let fs,remf,remt = compact_field_access_sequence prog rhst fr in
						if (remf = "") then []
						else I.look_up_all_fields prog (match remt with
						  | Named c -> I.look_up_data_def_raw prog.I.prog_data_decls c
						  | _ -> failwith "ERror!")
				  | _ -> failwith "expand_field_list: unexpected pattern"
			  else []
			in 
			let expand_field_list = List.map I.get_field_name expand_field_list in
			if (expand_field_list != []) then (* inline type --> expand into a sequence *)
			  (* let _ = print_endline ("[trans_exp] expand the inline field of lhs and rhs { " ^ String.concat " , " expand_field_list ^ " }") in *)
			  let lhss = produce_member_exps lhs expand_field_list in
			  let rhss = produce_member_exps rhs expand_field_list in
			  let assignments = List.map2 (fun x y -> I.Assign {
				  I.exp_assign_op = aop;
				  I.exp_assign_lhs = x;
				  I.exp_assign_rhs = y;
				  I.exp_assign_path_id = pid;
				  I.exp_assign_pos = pos_a }) lhss rhss in
			  let expanded_exp = List.fold_left (fun x y -> I.Seq {
				  I.exp_seq_exp1 = x;
				  I.exp_seq_exp2 = y;
				  I.exp_seq_pos = pos_a }) 
				(I.Empty no_pos) assignments in
			  helper expanded_exp
			else (* An Hoa : end of additional pre-processing, continue as usual *)
              (match aop with
                | I.OpAssign ->
                      (match lhs with
                        | I.Var { I.exp_var_name = v0; I.exp_var_pos = pos } -> 
                              let (ce1, te1) = trans_exp prog proc lhs in
						      (* let _ = print_string ("trans_exp :: lhs = " ^ Cprinter.string_of_exp ce1 ^ "\n") in *)
                              let (ce2, te2) = trans_exp prog proc rhs in
						      (* let _ = print_string ("trans_exp :: rhs = " ^ Cprinter.string_of_exp ce2 ^ "\n") in *)
                              if not (sub_type te2 te1) then  Err.report_error {
                                  Err.error_loc = pos;
                                  Err.error_text = "OpAssign : lhs and rhs do not match";  }
                              else
                                (let v = C.get_var ce1 in
                                let assign_e = C.Assign{
                                    C.exp_assign_lhs = v;
                                    C.exp_assign_rhs = ce2;
                                    C.exp_assign_pos = pos;} in
                                if C.is_var ce1 then
	                              (* let vsv = CP.SpecVar (te1, v, Primed) in
                                  let _ = proc.I.proc_important_vars <- proc.I.proc_important_vars @ [vsv] in*)
                                  (assign_e, C.void_type)
                                else
                                  (let seq_e = C.Seq{
                                      C.exp_seq_type = C.void_type;
                                      C.exp_seq_exp1 = ce1;
                                      C.exp_seq_exp2 = assign_e;
                                      C.exp_seq_pos = pos;} in (seq_e, C.void_type)))
								    (* AN HOA MARKED : THE CASE LHS IS AN ARRAY ACCESS IS SIMILAR TO VARIABLE & BINARY - WE NEED TO CONVERT THIS INTO A FUNCTION *)
								    (* (Iast) a[i] = v    ===>     (Iast) a = update___(a,i,v);   ===>   (Cast) Scall {a = update___(a,i,v)} *)
					    | I.ArrayAt { I.exp_arrayat_array_base = a; I.exp_arrayat_index = index; I.exp_arrayat_pos = pos_lhs } ->
						      (* Array variable *)
						      (* let new_lhs = I.Var { I.exp_var_name = a; I.exp_var_pos = pos_lhs } in *)
						      let r = List.length index in
						      let new_rhs = I.CallNRecv {
			                      I.exp_call_nrecv_method = array_update_call ^ (string_of_int r) ^ "d"; (* Update call *)
							      (* TODO CHECK IF THE ORDER IS CORRECT! IT MIGHT BE IN REVERSE ORDER *)
                                  I.exp_call_nrecv_lock = None;
			                      I.exp_call_nrecv_arguments = rhs :: a :: index;
			                      I.exp_call_nrecv_path_id = pid;
			                      I.exp_call_nrecv_pos = I.get_exp_pos rhs; } in 
						      let new_e = I.Assign {
							      I.exp_assign_op = I.OpAssign;
		   					      I.exp_assign_lhs = a; (* new_lhs; *)
							      I.exp_assign_rhs = new_rhs;
							      I.exp_assign_path_id = pid;
							      I.exp_assign_pos = pos_a; } in
			                  helper new_e
							      (* let (ce1, te1) = helper lhs in
	                                 let (ce2, te2) = helper rhs in
								     if not (sub_type te2 te1) then  Err.report_error {
                                     Err.error_loc = pos;
                                     Err.error_text = "lhs and rhs do not match";  }
                         	 	     else
								     (C.ArrayMod { C.exp_arraymod_lhs = (C.arrayat_of_exp ce1); C.exp_arraymod_rhs = ce2; C.exp_arraymod_pos = pos; }, C.void_type) *)
							      (* AN HOA END *)
                        | I.Member {
                              I.exp_member_base = base_e;
                              I.exp_member_fields = fs;
                              I.exp_member_path_id = pid;
                              I.exp_member_pos = pos } ->
							  (* An Hoa : fix this case with inline field access *)
							  let _,lhst = helper base_e in
							  let fs,remf,_ = compact_field_access_sequence prog lhst fs in
							  if not (remf = "") then
								failwith "[trans_exp] expect non inline field access"
							  else
							    (* An Hoa : end *)
                                let (rhs_c, rhs_t) = helper rhs in
                                let (fn, new_var) =
                                  (match rhs_c with
                                    | C.Var { C.exp_var_name = v } -> (v, false)
                                    | _ -> 
                                          let fn = (fresh_ty_var_name (rhs_t) pos.start_pos.Lexing.pos_lnum) in (fn, true)) in
                                let fn_var = C.Var {
                                    C.exp_var_type = rhs_t;
                                    C.exp_var_name = fn;
                                    C.exp_var_pos = pos;
                                } in
                                let (tmp_e, tmp_t) =
			                      flatten_to_bind prog proc base_e (List.rev fs) (Some fn_var) pid Mutable false pos 
			                    in
			                    
                                let fn_decl = if new_var then C.VarDecl {
                                    C.exp_var_decl_type = rhs_t;
                                    C.exp_var_decl_name = fn;
                                    C.exp_var_decl_pos = pos;}
                                else C.Unit pos in
                                let init_fn = if new_var then 
                                  C.Assign{
                                      C.exp_assign_lhs = fn;
                                      C.exp_assign_rhs = rhs_c;
                                      C.exp_assign_pos = pos; }
                                else C.Unit pos in
                                let seq1 = C.mkSeq tmp_t init_fn tmp_e pos in
                                let seq2 = C.mkSeq tmp_t fn_decl seq1 pos in
                                if new_var then
                                  ((C.Block {
                                      C.exp_block_type = tmp_t;
                                      C.exp_block_body = seq2;
                                      C.exp_block_local_vars = [ (rhs_t, fn) ];
                                      C.exp_block_pos = pos;}), tmp_t)
                                else (seq2, tmp_t)
                        | _ -> Err.report_error { Err.error_loc = pos_a; Err.error_text = "lhs is not an lvalue"; }
                      )
                | _ ->
                      let bop = bin_op_of_assign_op aop in
                      let new_rhs = I.Binary {
                          I.exp_binary_op = bop;
                          I.exp_binary_oper1 = lhs;
                          I.exp_binary_oper2 = rhs;
                          I.exp_binary_path_id = pid;
                          I.exp_binary_pos = pos_a;} in
                      let new_assign = I.Assign {
                          I.exp_assign_op = I.OpAssign;
                          I.exp_assign_lhs = lhs;
                          I.exp_assign_rhs = new_rhs;
                          I.exp_assign_path_id = pid;
                          I.exp_assign_pos = pos_a; } in helper new_assign
              )
	  | I.Barrier {I.exp_barrier_recv=v; I.exp_barrier_pos = pos} -> 
            (try
              match E.look_up v with
                | E.VarInfo vi ->
                      let ct = trans_type prog vi.E.var_type pos in
					  if ct=barrierT then 
                      ((C.Barrier {
                          C.exp_barrier_recv = (ct,vi.E.var_alpha);
                          C.exp_barrier_pos = pos; }), ct)
					  else Err.report_error { Err.error_loc = pos; Err.error_text = v ^ " is not a barrier"; }
                | _ -> Err.report_error { Err.error_loc = pos; Err.error_text = v ^ " is not a barrier"; }
            with | Not_found ->Err.report_error { Err.error_loc = pos; Err.error_text = v ^ " is not defined"; })
      | I.Binary {
            I.exp_binary_op = b_op;
            I.exp_binary_oper1 = e1;
            I.exp_binary_oper2 = e2;
            I.exp_binary_path_id = pid;
            I.exp_binary_pos = pos} ->
            if (I.is_null e1) || (I.is_null e2) then
              (let (e1_prim, e2_prim) = if I.is_null e2 then (e1, e2) else (e2, e1) in
              let new_op = match b_op with
                | I.OpEq -> I.OpIsNull
                | I.OpNeq -> I.OpIsNotNull
                | _ -> Err.report_error{ Err.error_loc = pos; Err.error_text = "null can only be used with == or !=";} in
              let b_call = get_binop_call new_op in
              let new_e = I.CallNRecv {
                  I.exp_call_nrecv_method = b_call;
                  I.exp_call_nrecv_lock = None;
                  I.exp_call_nrecv_arguments = [ e1_prim ];
                  I.exp_call_nrecv_path_id = pid (*stub_branch_point_id ("primitive "^b_call)*);
                  I.exp_call_nrecv_pos = pos;}in 
              helper new_e)
            else
              (let b_call = get_binop_call b_op in
              let new_e = I.CallNRecv {
                  I.exp_call_nrecv_method = b_call;
                  I.exp_call_nrecv_lock = None;
                  I.exp_call_nrecv_arguments = [ e1; e2 ];
                  I.exp_call_nrecv_path_id = pid (*stub_branch_point_id ("primitive "^b_call)*);
                  I.exp_call_nrecv_pos = pos; } in 
              helper new_e)
      | I.Bind {
            I.exp_bind_bound_var = v;
            I.exp_bind_fields = vs;
            I.exp_bind_body = e;
            I.exp_bind_pos = pos;
            I.exp_bind_path_id = pid;} ->
            (try
              let vinfo_tmp = E.look_up v in
              match vinfo_tmp with
                | E.VarInfo vi ->
                      (match vi.E.var_type with
                        | Named c -> 
                              let ddef = I.look_up_data_def pos prog.I.prog_data_decls c in
                              if ( != ) (List.length vs) (List.length ddef.I.data_fields) then
                                Err.report_error { Err.error_loc = pos; Err.error_text = "bind " ^ (v ^ ": different number of variables");}
                              else
                                (E.push_scope ();
                                (let _ = List.map2 
                                  (fun vi ti -> let alpha = E.alpha_name vi in
                                  E.add vi (E.VarInfo{
                                      E.var_name = vi;
                                      E.var_alpha = alpha;
                                      E.var_type = ti;})) 
                                  vs
								  (* An Hoa [22/08/2011] : Convert hard code of data fields typ extraction into *)
                                  (List.map I.get_field_typ ddef.I.data_fields) in
                                let vs_types = List.map (fun fld -> trans_type prog (I.get_field_typ fld) (I.get_field_pos fld)) ddef.I.data_fields in
                                let vt = trans_type prog vi.E.var_type pos in
                                let (ce, te) = helper e in
                                let _ = E.pop_scope ()in
                                ((C.Bind {
                                    C.exp_bind_type = te;
                                    C.exp_bind_bound_var = (vt, v);
                                    C.exp_bind_fields = List.combine vs_types vs;
                                    C.exp_bind_body = ce;
                                    C.exp_bind_imm = Mutable; (* can it be true? *)
                                    C.exp_bind_read_only = false; (*conservative. May use read/write analysis to figure out*)
				                    C.exp_bind_pos = pos;
                                    C.exp_bind_path_id = pid; }), te)))
                        | Array _ -> Err.report_error { Err.error_loc = pos; Err.error_text = v ^ " is not a data type";}
                        | _ -> Err.report_error { Err.error_loc = pos; Err.error_text = v ^ " is not a data type"; }
                      )
                | _ -> Err.report_error { Err.error_loc = pos; Err.error_text = v ^ " is not a data type"; }
            with | Not_found -> Err.report_error { Err.error_loc = pos; Err.error_text = v ^ " is not defined"; })
      | I.Block { I.exp_block_body = e; I.exp_block_pos = pos } ->
            (E.push_scope ();
            let (ce, te) = helper e in
            let tmp_local_vars = E.names_on_top () in
            let local_vars = List.map (fun (t, n) -> ((trans_type prog t pos), n)) tmp_local_vars in
            (E.pop_scope (); ((C.Block {
                C.exp_block_type = te;
                C.exp_block_body = ce;
                C.exp_block_local_vars = local_vars;
                C.exp_block_pos = pos; }), te))
            )
      | I.BoolLit { I.exp_bool_lit_val = b; I.exp_bool_lit_pos = pos } ->
            ((C.BConst { C.exp_bconst_val = b; C.exp_bconst_pos = pos; }), C.bool_type)
      | I.CallRecv {
            I.exp_call_recv_receiver = recv;
            I.exp_call_recv_method = mn;
            I.exp_call_recv_arguments = args;
            I.exp_call_recv_path_id = pi;
            I.exp_call_recv_pos = pos } ->
            let (crecv, crecv_t) = helper recv in
            let (recv_ident, recv_init, new_recv_ident) =
              (match crecv with
                | C.Var { C.exp_var_name = v } -> (v, (C.Unit pos), false)
                | _ ->
                      let fname = (fresh_ty_var_name (crecv_t) (pos.start_pos.Lexing.pos_lnum)) in
                      let fdecl = C.VarDecl {
                          C.exp_var_decl_type = crecv_t;
                          C.exp_var_decl_name = fname;
                          C.exp_var_decl_pos = pos;} in
                      let finit = C.Assign {
                          C.exp_assign_lhs = fname;
                          C.exp_assign_rhs = crecv;
                          C.exp_assign_pos = pos; } in
                      let seq = C.mkSeq C.void_type fdecl finit pos in (fname, seq, true)) in
            let tmp = List.map (helper) args in
            let (cargs, cts) = List.split tmp in
            let mingled_mn = C.mingle_name mn cts in
            let class_name = string_of_typ crecv_t in
            (try
              let cdef = I.look_up_data_def pos prog.I.prog_data_decls class_name in
              let all_methods = I.look_up_all_methods prog cdef in
              let pdef = I.look_up_proc_def_mingled_name all_methods mingled_mn in
              if ( != ) (List.length args) (List.length pdef.I.proc_args) then
                Err.report_error{ Err.error_loc = pos; Err.error_text = "number of arguments does not match"; }
              else
                (let parg_types = List.map (fun p -> trans_type prog p.I.param_type p.I.param_loc) pdef.I.proc_args in
                if List.exists2 (fun t1 t2 -> not (sub_type t1 t2)) cts parg_types then
                  Err.report_error{ Err.error_loc = pos;Err.error_text = "argument types do not match";}
                else
                  (let ret_ct = trans_type prog pdef.I.proc_return pdef.I.proc_loc in
                  let positions = List.map I.get_exp_pos args in
                  let (local_vars, init_seq, arg_vars) = trans_args (Gen.combine3 cargs cts positions) in
                  let call_e = C.ICall{
                      C.exp_icall_type = ret_ct;
                      C.exp_icall_receiver = recv_ident;
                      C.exp_icall_receiver_type = crecv_t;
                      C.exp_icall_method_name = mingled_mn;
                      C.exp_icall_arguments = arg_vars;
                      (* Termination: Default value - 
                       * it will be set later in trans_prog
                       * by mark_rec_and_call_order *)
                      C.exp_icall_is_rec = false;                       
                      C.exp_icall_path_id = pi;
                      C.exp_icall_pos = pos;} in
                  let seq1 = C.mkSeq ret_ct init_seq call_e pos in
                  let seq2 = C.mkSeq ret_ct recv_init seq1 pos in
                  let blk =C.Block{
                      C.exp_block_type = ret_ct;
                      C.exp_block_body = seq2;
                      C.exp_block_local_vars = (if new_recv_ident then [ (crecv_t, recv_ident) ] else []) @ local_vars;
                      C.exp_block_pos = pos;} in 
                  (blk, ret_ct)))
            with | Not_found -> Err.report_error { Err.error_loc = pos; Err.error_text = "procedure " ^ (mingled_mn ^ " is not found");}
		    )
      | I.CallNRecv {
            I.exp_call_nrecv_method = mn;
            I.exp_call_nrecv_lock = lock;
            I.exp_call_nrecv_arguments = args;
            I.exp_call_nrecv_path_id = pi;
            I.exp_call_nrecv_pos = pos } ->
		    (* let _ = print_string "trans_exp :: case CallNRecv\n" in*)
            let tmp = List.map (helper) args in
            let (cargs, cts) = List.split tmp in
            let mingled_mn = C.mingle_name mn cts in (* signature of the function *)
            let this_recv = 
              if Gen.is_some proc.I.proc_data_decl then
                (let cdef = Gen.unsome proc.I.proc_data_decl in
                let tmp1 = I.look_up_all_methods prog cdef in
                let tmp2 =List.exists (fun p -> p.I.proc_mingled_name = mingled_mn) tmp1 in tmp2)
              else false in
            if this_recv then (let call_recv = I.CallRecv {
                I.exp_call_recv_receiver = I.This { I.exp_this_pos = pos; };
                I.exp_call_recv_method = mingled_mn;
                I.exp_call_recv_arguments = args;
                I.exp_call_recv_path_id = pi;
                I.exp_call_recv_pos = pos; } in helper call_recv)
            else if (mn=Globals.fork_name) then
              (*============================*)
              (*========== FORK >>>=========*)
              (*============================*)
              (*fork is a generic functions. Its arguments can vary*)
              (*fork has at least a method name*)
              (if (List.length args <1) then
                Err.report_error { Err.error_loc = pos; Err.error_text = "fork has less then 1 argument: method name"; }
              else
                let method_name_exp = List.hd args in (*forked method name*)
                let method_name = match method_name_exp with
                  | I.Var { I.exp_var_name = v; I.exp_var_pos = pos } -> v
                  | _ -> 
                      Err.report_error { Err.error_loc = pos; Err.error_text = ("fork:" ^ "expecting the first argument as a var: a method name"); }
                in
                let method_args = (List.tl args) in (*forked method args*)
                let tmp = List.map (helper) method_args in
                let (cargs, cts) = List.split tmp in
                let mingled_forked_mn = C.mingle_name method_name cts in (* signature of the function *)
                try(
                    let pdef = I.look_up_proc_def_mingled_name prog.I.prog_proc_decls mingled_forked_mn in
                    if ( != ) (List.length method_args) (List.length pdef.I.proc_args) then
                      Err.report_error { Err.error_loc = pos; Err.error_text = ("fork:" ^ mingled_forked_mn ^ "number of arguments does not match"); }
                    else
                      (let parg_types = List.map (fun p -> trans_type prog p.I.param_type p.I.param_loc) pdef.I.proc_args in
                       if List.exists2 (fun t1 t2 -> not (sub_type t1 t2)) cts parg_types then
                         Err.report_error { Err.error_loc = pos; Err.error_text = "argument types do not match"; }
                       else if Inliner.is_inlined mn then (let inlined_exp = Inliner.inline prog pdef ie in helper inlined_exp)
                       else 
                         (let ret_ct  = Globals.thread_typ in (*return a thread _type*) 
                          let positions = List.map I.get_exp_pos method_args in
                          let (local_vars, init_seq, arg_vars) = trans_args (Gen.combine3 cargs cts positions) in
                          let call_e = C.SCall {
                              C.exp_scall_type = ret_ct;
                              C.exp_scall_method_name = mingled_mn;
                              C.exp_scall_lock = lock;
                              C.exp_scall_arguments = mingled_forked_mn::arg_vars;
					          C.exp_scall_is_rec = false; (* default value - it will be set later in trans_prog *)
                              C.exp_scall_pos = pos;
                              C.exp_scall_path_id = pi; } in
                          let seq_1 = C.mkSeq ret_ct init_seq call_e pos in
                          ((C.Block {
                              C.exp_block_type = ret_ct;
                              C.exp_block_body = seq_1;
                              C.exp_block_local_vars = local_vars;
                              C.exp_block_pos = pos; }),ret_ct))))
                    with | Not_found -> Err.report_error { Err.error_loc = pos; Err.error_text = "trans_exp :: case CallNRecv :: forked procedure " ^ (mingled_forked_mn ^ " is not found");})
            (*======== <<<<FORK ==========*)
            else if (mn=Globals.init_name) 
                  || (mn=Globals.finalize_name) 
                  || (mn=Globals.acquire_name)
                  || (mn=Globals.release_name) then
              (*=====================================*)
              (*========== INIT/FINALIZE >>>=========*)
              (*=====================================*)
              (*INIT/FINALIZE is a generic functions. Its arguments can vary*)
              (*it has at least a lock as its argument*)
              (*the rest are ghost arguments*)
              (if (List.length args <1) then
                    Err.report_error { Err.error_loc = pos; Err.error_text = "init/finalize has less then 1 argument: lock"; }
               else 
               (try 
                    let pdef = I.look_up_proc_def_raw prog.I.prog_proc_decls mn in
                    (*CHECK a matched LOCK EXISTS*)
                    let _ = match lock with
                      | None ->
                          Err.report_error { Err.error_loc = pos; Err.error_text = ("trans_exp :: CallNRecv :: init/finalize requires an associated lock");}
                      | Some v ->
                          (try
                              let vdef = I.look_up_view_def_raw prog.I.prog_view_decls v in
                              let n1 = List.length args in
                              let n2 = List.length (vdef.I.view_vars) in
                              if (n1-1) != n2 then
                                Err.report_error { Err.error_loc = pos; Err.error_text = ("trans_exp :: CallNRecv :: init/finalize :: number of args in " ^ (vdef.I.view_name) ^ " not match");}
                           with | Not_found -> Err.report_error { Err.error_loc = pos; Err.error_text = ("trans_exp :: CallNRecv :: init/finalize requires an associated lock");})
                    in
                    let ret_ct = trans_type prog pdef.I.proc_return pdef.I.proc_loc in
                    let positions = List.map I.get_exp_pos args in
                    let (local_vars, init_seq, arg_vars) = trans_args (Gen.combine3 cargs cts positions) in
                    let call_e = C.SCall {
                        C.exp_scall_type = ret_ct;
                        C.exp_scall_method_name = mingled_mn;
                        C.exp_scall_lock = lock;
                        C.exp_scall_arguments = arg_vars;
					    C.exp_scall_is_rec = false; (* default value - it will be set later in trans_prog *)
                        C.exp_scall_pos = pos;
                        C.exp_scall_path_id = pi; } in
                    let seq_1 = C.mkSeq ret_ct init_seq call_e pos in
                    ((C.Block {
                        C.exp_block_type = ret_ct;
                        C.exp_block_body = seq_1;
                        C.exp_block_local_vars = local_vars;
                        C.exp_block_pos = pos; }),ret_ct)
                with | Not_found -> Err.report_error { Err.error_loc = pos; Err.error_text = "trans_exp :: case CallNRecv :: procedure " ^ (mingled_mn ^ " is not found");}))
            (*======== <<<<INIT ==========*)
            else (try 
              let pdef = I.look_up_proc_def_mingled_name prog.I.prog_proc_decls mingled_mn in
              if ( != ) (List.length args) (List.length pdef.I.proc_args) then
                Err.report_error { Err.error_loc = pos; Err.error_text = "number of arguments does not match"; }
              else if (mn=Globals.join_name) &&  ((List.length args) != 1) then
                (*This check may be redundant*)
                (*============================*)
                (*========== JOIN >>>=========*)
                (*===========================*)
                (*join is a special function. Its arguments are fixed to only 1*)
                Err.report_error { Err.error_loc = pos; Err.error_text = "join has other than one argument"; }
              (*======== <<<<JOIN ==========*)
              else
                (let parg_types = List.map (fun p -> trans_type prog p.I.param_type p.I.param_loc) pdef.I.proc_args in
                if List.exists2 (fun t1 t2 -> not (sub_type t1 t2)) cts parg_types then
                  Err.report_error { Err.error_loc = pos; Err.error_text = "argument types do not match"; }
                else if Inliner.is_inlined mn then (let inlined_exp = Inliner.inline prog pdef ie in helper inlined_exp)
                else 
                  (let ret_ct = trans_type prog pdef.I.proc_return pdef.I.proc_loc in
                  let positions = List.map I.get_exp_pos args in
                  let (local_vars, init_seq, arg_vars) = trans_args (Gen.combine3 cargs cts positions) in
                  let call_e = C.SCall {
                      C.exp_scall_type = ret_ct;
                      C.exp_scall_method_name = mingled_mn;
                      C.exp_scall_lock = lock;
                      C.exp_scall_arguments = arg_vars;
                      (* Termination: Default value - 
                       * it will be set later in trans_prog
                       * by mark_rec_and_call_order *)
                      C.exp_scall_is_rec = false; 
                      C.exp_scall_pos = pos;
                      C.exp_scall_path_id = pi; } in
                  let seq_1 = C.mkSeq ret_ct init_seq call_e pos in
                  ((C.Block {
                      C.exp_block_type = ret_ct;
                      C.exp_block_body = seq_1;
                      C.exp_block_local_vars = local_vars;
                      C.exp_block_pos = pos; }),ret_ct)))
            with | Not_found -> Err.report_error { Err.error_loc = pos; Err.error_text = "trans_exp :: case CallNRecv :: procedure " ^ (mingled_mn ^ " is not found");})
      | I.Catch { I.exp_catch_var = cv;
	    I.exp_catch_flow_type = cvt;
	    I.exp_catch_flow_var = cfv;
	    I.exp_catch_body = cb;	
		I.exp_catch_alt_var_type = alt_cvt ;
	    I.exp_catch_pos = pos}->	
            if not (exlist # sub_type_obj cvt c_flow) then Err.report_error { Err.error_loc = pos; 
		    Err.error_text = "can not catch a not raisable object" }
            else begin
		      match cv with
		        | Some x ->
			          if (String.compare cvt c_flow)=0 then  begin
			            E.push_scope();
			            let new_bd, ct2 = helper cb in
			            E.pop_scope();
			            ( C.Catch{C.exp_catch_flow_type = (exlist # get_hash c_flow);
			            C.exp_catch_flow_var = cfv;
			            C.exp_catch_var = Some (Void,x);
			            C.exp_catch_body = new_bd;																					   
			            C.exp_catch_pos = pos;},ct2) end
			          else begin
						let cvt_rev = match alt_cvt with | None -> Named cvt | Some t -> t in
			            E.push_scope();
			            let alpha = E.alpha_name x in
			            E.add x (E.VarInfo {E.var_name = x; E.var_alpha = alpha; E.var_type = cvt_rev});
			            (*let _ = print_string ("\n rrr1 -> \n"^Iprinter.string_of_exp cb^"\n") in*)
			            let new_bd, ct2 = helper cb in
				        (*let _ = print_string ("\n rrr2 -> \n") in*)
			            let ct = if (exlist # sub_type_obj cvt raisable_class) then trans_type prog (Named cvt) pos else Named cvt in
				        E.pop_scope();
				        let r = C.Catch {C.exp_catch_flow_type = (match ct with 
						  | Named ot-> (exlist # get_hash ot) 
						  | _->  Error.report_error { Error.error_loc = pos; Error.error_text = "malfunction, catch translation error"});
					    C.exp_catch_flow_var = cfv;
					    C.exp_catch_var = Some (ct,alpha);
					    C.exp_catch_body = new_bd;																					   
					    C.exp_catch_pos = pos;
					    } in (r,ct2) end
		        | None ->  
			          E.push_scope();
			          let new_bd, ct2 = helper cb in
			          E.pop_scope();
			          (C.Catch{	C.exp_catch_flow_type = exlist # get_hash cvt;
					  C.exp_catch_flow_var = cfv;
					  C.exp_catch_var = None;
					  C.exp_catch_body = new_bd;																					   
					  C.exp_catch_pos = pos;},ct2)
	        end
	  | I.Cond {
            I.exp_cond_condition = e1;
            I.exp_cond_then_arm = e2;
            I.exp_cond_else_arm = e3;
            I.exp_cond_path_id = pi;
            I.exp_cond_pos = pos } ->
		    (* let _ = print_string ("trans_exp :: cond = " ^ Iprinter.string_of_exp e1 ^ " then branch = " ^ Iprinter.string_of_exp e2 ^ " else branch = " ^ Iprinter.string_of_exp e3 ^ "\n") in *) 
            let (ce1, te1) = helper e1 in
            if not (CP.are_same_types te1 C.bool_type) then
              Err.report_error { Error.error_loc = pos; Error.error_text = "conditional expression is not bool";}
            else
              (let (ce2', te2) = helper e2 in
              let (ce3', te3) = helper e3 in
              let ce2 = insert_dummy_vars ce2' pos in
              let ce3 = insert_dummy_vars ce3' pos in
              match ce1 with
                | C.Var { C.exp_var_type = _; C.exp_var_name = v; C.exp_var_pos = _} ->
                      ((C.Cond{
                          C.exp_cond_type = te2;
                          C.exp_cond_condition = v;
                          C.exp_cond_then_arm = ce2;
                          C.exp_cond_else_arm = ce3;
                          C.exp_cond_pos = pos;
                          C.exp_cond_path_id = pi; }), te2)
                | _ ->
                      let e_pos = Iast.get_exp_pos e1 in
                      let fn = (fresh_var_name "bool" e_pos.start_pos.Lexing.pos_lnum) in
                      let vd = C.VarDecl {
                          C.exp_var_decl_type = C.bool_type;
                          C.exp_var_decl_name = fn;
                          C.exp_var_decl_pos = e_pos; } in
                      let init_e = C.Assign {
                          C.exp_assign_lhs = fn;
                          C.exp_assign_rhs = ce1;
                          C.exp_assign_pos = e_pos;} in
                      let cond_e = C.Cond {
                          C.exp_cond_type = te2;
                          C.exp_cond_condition = fn;
                          C.exp_cond_then_arm = ce2;
                          C.exp_cond_else_arm = ce3;
                          C.exp_cond_pos = pos;
                          C.exp_cond_path_id = pi; } in
                      let tmp_e1 = C.Seq {
                          C.exp_seq_type = te2;
                          C.exp_seq_exp1 = init_e;
                          C.exp_seq_exp2 = cond_e;
                          C.exp_seq_pos = e_pos; } in
                      let tmp_e2 = C.Seq {
                          C.exp_seq_type = te2;
                          C.exp_seq_exp1 = vd;
                          C.exp_seq_exp2 = tmp_e1;
                          C.exp_seq_pos = pos; } in (tmp_e2, te2))
      | I.Debug { I.exp_debug_flag = flag; I.exp_debug_pos = pos } -> ((C.Debug { C.exp_debug_flag = flag; C.exp_debug_pos = pos; }), C. void_type)
      | I.Time (b,s,p) -> (C.Time (b,s,p), C. void_type)
      | I.Dprint { I.exp_dprint_string = str; I.exp_dprint_pos = pos } ->
            let tmp_visib_names = E.visible_names () in
            let tmp_visib_names = List.filter (fun v -> I.is_named_type (fst v)) tmp_visib_names in
            let visib_names = List.map snd tmp_visib_names in
            let ce = C.Dprint {
                C.exp_dprint_string = str;
                C.exp_dprint_visible_names = visib_names;
                C.exp_dprint_pos = pos; } in (ce, C.void_type)
      | I.Empty pos -> ((C.Unit pos), C.void_type)
      | I.IntLit { I.exp_int_lit_val = i; I.exp_int_lit_pos = pos } ->
            ((C.IConst { C.exp_iconst_val = i; C.exp_iconst_pos = pos; }), C.int_type)
      | I.Java { I.exp_java_code = jcode; I.exp_java_pos = pos } ->
            ((C.Java { C.exp_java_code = jcode; C.exp_java_pos = pos; }), C.void_type)
      | I.Member {
            I.exp_member_base = e;
            I.exp_member_fields = fs;
            I.exp_member_path_id = pid;
            I.exp_member_pos = pos } -> 
           	(* An Hoa : compact the field access sequence *)
			let et = snd (helper e) in
			let fs,rem,_ = compact_field_access_sequence prog et fs in
			if not (rem = "") then
			  failwith ("[trans_exp] expect non-inline field access but still got { " ^ rem ^ " }")
			else
              (* ... = o.f => read_only = true *)
              let r = 
	            if (!Globals.allow_imm) then
	              flatten_to_bind prog proc e (List.rev fs) None pid Lend true pos (* ok to have it lend instead of Imm? *)
	            else
	              flatten_to_bind prog proc e (List.rev fs) None pid Mutable true pos
	          in
              (* let _ = print_string ("after: "^(Cprinter.string_of_exp (fst r))) in *)
              r
		          (** An Hoa : Translate the new int[x] into core language.
		              Currently only work with 1D array of integer i.e. et = "int"
		              and dims = [x] for a single expression x.		
		              TODO COMPLETE 
		          *)
	  | I.ArrayAlloc {
            I.exp_aalloc_etype_name = et;
            I.exp_aalloc_dimensions = dims;
            I.exp_aalloc_pos = pos } ->
			(* simply translate "new int[n]" into "aalloc___(n)" *)
			let newie = I.CallNRecv {
				I.exp_call_nrecv_method = array_allocate_call;
                I.exp_call_nrecv_lock = None;
				I.exp_call_nrecv_arguments = [List.hd dims];
				I.exp_call_nrecv_path_id = None;
				I.exp_call_nrecv_pos = pos; }
			in helper newie
      | I.New {
            I.exp_new_class_name = c;
            I.exp_new_arguments = args;
            I.exp_new_pos = pos } ->
            let data_def = I.look_up_data_def pos prog.I.prog_data_decls c in
            let all_fields = I.look_up_all_fields prog data_def in
            let field_types = List.map I.get_field_typ all_fields in
            let nargs = List.length args in
            if ( != ) nargs (List.length field_types) then
              Err.report_error{ Err.error_loc = pos; Err.error_text = "number of arguments does not match";}
            else
              (let tmp = List.map (helper) args in
              let (cargs, cts) = List.split tmp in
              let parg_types = List.map (fun ft -> trans_type prog ft pos) field_types in
              if List.exists2 (fun t1 t2 -> not (sub_type t1 t2)) cts parg_types then
                Err.report_error { Err.error_loc = pos; Err.error_text = "argument types do not match";}
              else ( let positions = Gen.repeat pos nargs in
              let (local_vars, init_seq, arg_vars) = trans_args (Gen.combine3 cargs cts positions) in
              let new_e = C.New {
                  C.exp_new_class_name = c;
                  C.exp_new_parent_name = data_def.I.data_parent_name;
                  C.exp_new_arguments = List.combine parg_types arg_vars;
                  C.exp_new_pos = pos;} in
              let new_t = Named c in
              let seq_e = C.mkSeq new_t init_seq new_e pos in
              ((C.Block {
                  C.exp_block_type = new_t;
                  C.exp_block_body = seq_e;
                  C.exp_block_local_vars = local_vars;
                  C.exp_block_pos = pos; }),new_t)))
      | I.Null pos -> ((C.Null pos), (Named ""))
      | I.Return {
            I.exp_return_val = oe;
            I.exp_return_path_id = pi;
            I.exp_return_pos = pos} ->  begin
          let cret_type = trans_type prog proc.I.proc_return proc.I.proc_loc in
          match oe with
            | None -> 
                  if CP.are_same_types cret_type C.void_type then
                    (C.Sharp ({ C.exp_sharp_type = C.void_type;
                    C.exp_sharp_flow_type = C.Sharp_ct 
                            {CF.formula_flow_interval = !ret_flow_int ; CF.formula_flow_link = None};
                    C.exp_sharp_val = Cast.Sharp_no_val;
                    C.exp_sharp_unpack = false;
                    C.exp_sharp_path_id = pi;
                    C.exp_sharp_pos = pos}), C.void_type)
                  else
                    Err.report_error { Err.error_loc = proc.I.proc_loc; 
                    Err.error_text = "return statement for procedures with non-void return type need a value" }
            | Some e -> 
                  let e_pos = Iast.get_exp_pos e in
                  let ce, ct = helper e in
                  if sub_type ct cret_type then
                    let fn = (fresh_ty_var_name (ct) e_pos.start_pos.Lexing.pos_lnum) in
                    let vd = C.VarDecl { 
                        C.exp_var_decl_type = ct;
                        C.exp_var_decl_name = fn;
                        C.exp_var_decl_pos = e_pos;} in
                    let init_e = C.Assign { 
                        C.exp_assign_lhs = fn;
                        C.exp_assign_rhs = ce;
                        C.exp_assign_pos = e_pos;} in
                    let shar = C.Sharp ({
                        C.exp_sharp_type = C.void_type;
                        C.exp_sharp_flow_type = C.Sharp_ct {CF.formula_flow_interval = !ret_flow_int ; CF.formula_flow_link = None};
                        C.exp_sharp_unpack = false;
                        C.exp_sharp_val = Cast.Sharp_var (ct,fn);
                        C.exp_sharp_path_id = pi;
                        C.exp_sharp_pos = pos}) in
                    let tmp_e1 = C.Seq { 
                        C.exp_seq_type = C.void_type;
                        C.exp_seq_exp1 = init_e;
                        C.exp_seq_exp2 = shar;
                        C.exp_seq_pos = e_pos;} in
                    let tmp_e2 = C.Seq { 
                        C.exp_seq_type = C.void_type;
                        C.exp_seq_exp1 = vd;
                        C.exp_seq_exp2 = tmp_e1;
                        C.exp_seq_pos = e_pos;} in 
                    (tmp_e2, C.void_type)
                  else
                    Err.report_error { Err.error_loc = proc.I.proc_loc; Err.error_text = "return type doesn't match" }
        end
      | I.Seq { I.exp_seq_exp1 = e1; I.exp_seq_exp2 = e2; I.exp_seq_pos = pos }->
            let (ce1', te1) = trans_exp prog proc e1 in
            let (ce2, te2) = trans_exp prog proc e2 in
            let ce1 = insert_dummy_vars ce1' pos in
            ((C.Seq {
                C.exp_seq_type = te2;
                C.exp_seq_exp1 = ce1;
                C.exp_seq_exp2 = ce2;
                C.exp_seq_pos = pos; }), te2)
      | I.This { I.exp_this_pos = pos } ->
            if Gen.is_some proc.I.proc_data_decl then
              (let cdef = Gen.unsome proc.I.proc_data_decl in
              let ct = Named cdef.I.data_name in 
              ((C.This { C.exp_this_type = ct; C.exp_this_pos = pos; }), ct))
            else
              Err.report_error { Err.error_loc = pos; Err.error_text = "\"this\" can only be used in members of a class";}
      | I.Unary {I.exp_unary_op = u_op; I.exp_unary_exp = e; I.exp_unary_path_id = pid; I.exp_unary_pos = pos;} ->
            (*let pi = stub_branch_point_id "fresh_unary_call" in*)
            (match u_op with
              | I.OpNot ->
                    let u_call = "not___" in
                    let call_e = I.CallNRecv {
                        I.exp_call_nrecv_method = u_call;
                        I.exp_call_nrecv_lock = None;
                        I.exp_call_nrecv_arguments = [ e ];
                        I.exp_call_nrecv_path_id = pid;
                        I.exp_call_nrecv_pos = pos;} in helper call_e
              | I.OpPostInc ->
                    let fn = (fresh_var_name "int" pos.start_pos.Lexing.pos_lnum) in
                    let fn_decl = I.VarDecl{
                        I.exp_var_decl_type = I.int_type;
                        I.exp_var_decl_decls = [ (fn, (Some e), pos) ];
                        I.exp_var_decl_pos = pos; } in
                    let add1_e = I.Binary {
                        I.exp_binary_op = I.OpPlus;
                        I.exp_binary_oper1 = e;
                        I.exp_binary_oper2 = I.IntLit { I.exp_int_lit_val = 1; I.exp_int_lit_pos = pos; };
                        I.exp_binary_path_id = pid;
                        I.exp_binary_pos = pos; } in
                    let assign_e = I.Assign {
                        I.exp_assign_op = I.OpAssign;
                        I.exp_assign_lhs = e;
                        I.exp_assign_rhs = add1_e;
                        I.exp_assign_path_id = None;
                        I.exp_assign_pos = pos; } in
                    let seq1 = I.Seq {
                        I.exp_seq_exp1 = assign_e;
                        I.exp_seq_exp2 = I.Var { I.exp_var_name = fn; I.exp_var_pos = pos; };
                        I.exp_seq_pos = pos; } in
                    let seq2 = I.Seq {
                        I.exp_seq_exp1 = fn_decl;
                        I.exp_seq_exp2 = seq1;
                        I.exp_seq_pos = pos; } in
                    helper (I.Block { I.exp_block_local_vars = [];I.exp_block_body = seq2; I.exp_block_jump_label = I.NoJumpLabel; I.exp_block_pos = pos;})
              | I.OpPostDec -> 
                    let fn = (fresh_var_name "int" pos.start_pos.Lexing.pos_lnum) in
                    let fn_decl = I.VarDecl {
                        I.exp_var_decl_type = I.int_type;
                        I.exp_var_decl_decls = [ (fn, (Some e), pos) ];
                        I.exp_var_decl_pos = pos; } in
                    let sub1_e = I.Binary {
                        I.exp_binary_op = I.OpMinus;
                        I.exp_binary_oper1 = e;
                        I.exp_binary_oper2 = I.IntLit { I.exp_int_lit_val = 1; I.exp_int_lit_pos = pos; };
                        I.exp_binary_path_id = pid;
                        I.exp_binary_pos = pos;} in
                    let assign_e = I.Assign {
                        I.exp_assign_op = I.OpAssign;
                        I.exp_assign_lhs = e;
                        I.exp_assign_rhs = sub1_e;
                        I.exp_assign_path_id = None;
                        I.exp_assign_pos = pos; } in
                    let seq1 = I.Seq {
                        I.exp_seq_exp1 = assign_e;
                        I.exp_seq_exp2 = I.Var { I.exp_var_name = fn; I.exp_var_pos = pos; };
                        I.exp_seq_pos = pos; } in
                    let seq2 = I.Seq {
                        I.exp_seq_exp1 = fn_decl;
                        I.exp_seq_exp2 = seq1;
                        I.exp_seq_pos = pos; } in
                    helper (I.Block { I.exp_block_local_vars = [];I.exp_block_body = seq2;I.exp_block_jump_label = I.NoJumpLabel;  I.exp_block_pos = pos;})
              | I.OpPreInc ->
                    let add1_e = I.Binary {
                        I.exp_binary_op = I.OpPlus;
                        I.exp_binary_oper1 = e;
                        I.exp_binary_oper2 = I.IntLit { I.exp_int_lit_val = 1; I.exp_int_lit_pos = pos; };
                        I.exp_binary_path_id = pid;
                        I.exp_binary_pos = pos; } in
                    let assign_e = I.Assign {
                        I.exp_assign_op = I.OpAssign;
                        I.exp_assign_lhs = e;
                        I.exp_assign_rhs = add1_e;
                        I.exp_assign_path_id = None;
                        I.exp_assign_pos = pos; } in
                    let seq = I.Seq {
                        I.exp_seq_exp1 = assign_e;
                        I.exp_seq_exp2 = e;
                        I.exp_seq_pos = pos;} in
                    helper (I.Block { I.exp_block_local_vars = [];I.exp_block_body = seq;I.exp_block_jump_label = I.NoJumpLabel;  I.exp_block_pos = pos;})
              | I.OpPreDec ->
                    let sub1_e = I.Binary {
                        I.exp_binary_op = I.OpMinus;
                        I.exp_binary_oper1 = e;
                        I.exp_binary_oper2 = I.IntLit { I.exp_int_lit_val = 1; I.exp_int_lit_pos = pos; };
                        I.exp_binary_path_id = pid;
                        I.exp_binary_pos = pos; } in
                    let assign_e = I.Assign {
                        I.exp_assign_op = I.OpAssign;
                        I.exp_assign_lhs = e;
                        I.exp_assign_rhs = sub1_e;
                        I.exp_assign_path_id = None;
                        I.exp_assign_pos = pos; } in
                    let seq = I.Seq {
                        I.exp_seq_exp1 = assign_e;
                        I.exp_seq_exp2 = e;
                        I.exp_seq_pos = pos; } in
                    helper (I.Block { exp_block_local_vars = [];I.exp_block_body = seq;I.exp_block_jump_label = I.NoJumpLabel;  I.exp_block_pos = pos;})
              | _ -> failwith "u_op not supported yet")
      | I.Var { I.exp_var_name = v; I.exp_var_pos = pos } ->
            (try
              let vinfo_tmp = E.look_up v in
              match vinfo_tmp with
                | E.VarInfo vi ->
                      let ct = trans_type prog vi.E.var_type pos in
                      (*let _ = print_string ("llok bf: "^v^" after: "^vi.E.var_alpha^"\n") in*)
                      ((C.Var {
                          C.exp_var_type = ct;
                          C.exp_var_name = vi.E.var_alpha;
                          C.exp_var_pos = pos; }), ct)
                | E.ConstInfo ci ->
                      let ct = trans_type prog ci.E.const_type pos in ((ci.E.const_value), ct)
                | E.EnumInfo ei ->
                      let ct = trans_type prog ei.E.enum_type pos in
                      ((C.IConst {
                          C.exp_iconst_val = ei.E.enum_value;
                          C.exp_iconst_pos = pos; }), ct)
            with | Not_found ->
                  let proc_idents = 
                    let fun0 (proc: I.proc_decl) : ident = proc.I.proc_name in
                    List.map fun0 prog.I.prog_proc_decls
                  in
                  if (List.mem v proc_idents) then
                    (*procedure as an argument*)
                    (* let _ = print_endline ("trans_exp: before trans_typ") in *)
                    let ct = trans_type prog proc_typ pos in
                    (* let _ = print_endline ("trans_exp: after trans_typ") in *)
                    ((C.Var {
                        C.exp_var_type = ct;
                        C.exp_var_name = v;
                        C.exp_var_pos = pos; }), ct)
                  else
                    Err.report_error { Err.error_loc = pos; Err.error_text = v ^ " is not defined"; })
      | I.VarDecl {
            I.exp_var_decl_type = t;
            I.exp_var_decl_decls = decls;
            I.exp_var_decl_pos = tpos } ->
            let ct = trans_type prog t tpos in
            let rec helper2 ds = (match ds with
              | [ (v, oe, pos) ] ->
                    if E.name_clash v then
                      Err.report_error{Err.error_loc = pos;Err.error_text = v ^ " is already declared";}
                    else (let alpha = E.alpha_name v in
                    (E.add v (E.VarInfo{
                        E.var_name = v;
                        E.var_alpha = alpha;
                        E.var_type = t; });
                    let init_val = match oe with
                      | Some e ->
                            let (tmp_e, tmp_t) = helper e in
                            if sub_type tmp_t ct then tmp_e
                            else Err.report_error {
                                Err.error_loc = pos;
                                Err.error_text = "initializer doesn't match variable type";}
                      | None -> default_value ct pos in
                    let init_e = C.Assign {
                        C.exp_assign_lhs = alpha;
                        C.exp_assign_rhs = init_val;
                        C.exp_assign_pos = pos; } in
                    let var_decl = C.VarDecl {
                        C.exp_var_decl_type = ct;
                        C.exp_var_decl_name = alpha;
                        C.exp_var_decl_pos = pos; } in
                    match oe with 
                      | None -> 
                            (* WN : no automatic intialization!! *)
                            var_decl
                      | Some _ -> 
                            C.Seq {
                                C.exp_seq_type = C.void_type;
                                C.exp_seq_exp1 = var_decl;
                                C.exp_seq_exp2 = init_e;
                                C.exp_seq_pos = pos; }
                    ))
              | (v, oe, pos) :: rest ->
                    let crest = helper2 rest in
                    let ce = helper2 [ (v, oe, pos) ] in
                    C.Seq {
                        C.exp_seq_type = C.void_type;
                        C.exp_seq_exp1 = ce;
                        C.exp_seq_exp2 = crest;
                        C.exp_seq_pos = pos;}
              | [] -> failwith "trans_exp: VarDecl has an empty declaration list") in 
            ((helper2 decls), C.void_type)
      | I.While{
            I.exp_while_condition = cond;
            I.exp_while_body = body;
            I.exp_while_specs = prepost;
            I.exp_while_wrappings = wrap;
            I.exp_while_path_id = pi;
            I.exp_while_pos = pos } ->
            let tvars = E.visible_names () in
            let tvars = Gen.BList.remove_dups_eq (=) tvars in
            let w_args = List.map (fun tv -> I.Var { I.exp_var_name = snd tv; I.exp_var_pos = pos; }) tvars in
            let fn3 = fresh_name () in  
            let w_name = fn3 ^ ("_" ^ (Gen.replace_path_sep_with_uscore
                (Gen.replace_dot_with_uscore (string_of_loc pos)))) in
			let prepost = match wrap with 
				| None -> prepost
				| Some _ -> IF.add_post_for_flow (I.get_breaks body) prepost in
            let w_body_1 = body in
            let w_body_2 = I.Block {
                I.exp_block_jump_label = I.NoJumpLabel; 
                I.exp_block_body = I.Seq{
                    I.exp_seq_exp1 = w_body_1;                     
                    I.exp_seq_exp2 = I.CallNRecv {
                        I.exp_call_nrecv_method = w_name;
                        I.exp_call_nrecv_lock = None;
                        I.exp_call_nrecv_arguments = w_args;
                        I.exp_call_nrecv_pos = pos;
                        I.exp_call_nrecv_path_id = pi; };
                    I.exp_seq_pos = pos; };
                I.exp_block_local_vars = [];
                I.exp_block_pos = pos;} in
            let w_body = I.Block {
                I.exp_block_jump_label = I.NoJumpLabel; 
                I.exp_block_body = I.Cond {
                    I.exp_cond_condition = cond;
                    I.exp_cond_then_arm = w_body_2;
                    I.exp_cond_else_arm = I.Empty pos;
                    I.exp_cond_pos = pos;
                    I.exp_cond_path_id = pi;};
                I.exp_block_local_vars = [];
                I.exp_block_pos = pos;} in
            let w_formal_args = List.map (fun tv ->{
                I.param_type = fst tv;
                I.param_name = snd tv;
                I.param_mod = I.RefMod;
                I.param_loc = pos; }) tvars in
            let w_proc ={
                I.proc_name = w_name;
                I.proc_mingled_name = mingle_name_enum prog w_name (List.map fst tvars);
                I.proc_data_decl = proc.I.proc_data_decl;
                I.proc_constructor = false;
                I.proc_args = w_formal_args;
                I.proc_return = I.void_type;
               (* I.proc_important_vars= [];*)
                I.proc_static_specs = prepost;
                I.proc_exceptions = [brk_top]; (*should be ok, other wise while will have a throws set and this does not seem ergonomic*)
                I.proc_dynamic_specs = IF.mkEFalseF ();
                I.proc_body = Some w_body;
                I.proc_is_main = proc.I.proc_is_main;
                I.proc_file = proc.I.proc_file;
                I.proc_loc = pos; } in
            let temp_call =  I.CallNRecv {
                I.exp_call_nrecv_method = w_name;
                I.exp_call_nrecv_lock = None;
                I.exp_call_nrecv_arguments = w_args;
                I.exp_call_nrecv_pos = pos;
                I.exp_call_nrecv_path_id = pi; } in
            let w_call = match wrap with
              | None -> temp_call
              | Some (e,_) -> (*let e,et = helper e in*)
                    match e with
                      | I.Try b -> I.Try{b with I.exp_try_block  = temp_call}
                      | _ ->  Err.report_error { Err.error_loc = pos; Err.error_text = "Translation of loop break wrapping failed";} in
			let w_proc = case_normalize_proc prog w_proc in
            let new_prog = { (prog) with I.prog_proc_decls = w_proc :: prog.I.prog_proc_decls; } in
            let (iw_call, _) = trans_exp new_prog w_proc w_call in
            let cw_proc = trans_proc new_prog w_proc in 
            (loop_procs := cw_proc :: !loop_procs; (iw_call, C.void_type))
      | Iast.FloatLit {I.exp_float_lit_val = fval; I.exp_float_lit_pos = pos} -> 
            (C.FConst {C.exp_fconst_val = fval; C.exp_fconst_pos = pos}, C.float_type)
      | Iast.Finally b ->  Err.report_error { Err.error_loc = b.I.exp_finally_pos; Err.error_text = "Translation of finally failed";} 
      | Iast.ConstDecl _ -> failwith (Iprinter.string_of_exp ie)
      | Iast.Cast _ -> failwith (Iprinter.string_of_exp ie)
      | Iast.Break _ -> failwith (Iprinter.string_of_exp ie)
      | Iast.Continue _ -> failwith (Iprinter.string_of_exp ie)
      | I.Raise ({ 
            I.exp_raise_type = ot;
            I.exp_raise_val = oe;
			I.exp_raise_use_type = use_type;
            I.exp_raise_from_final = ff;
            I.exp_raise_path_id = pi;
            I.exp_raise_pos = pos })->
            (*let _ = print_string ("\n trt : "^(string_of_bool ff)^"\n") in*)
            let r = match oe with
              | Some oe ->  
                    if ff then 
                      (C.Sharp({C.exp_sharp_type = C.void_type;
                      C.exp_sharp_unpack = false;
                      C.exp_sharp_flow_type = (
                          match ot with 
                            | I.Const_flow c -> (C.Sharp_ct 
                                  {CF.formula_flow_interval = (exlist # get_hash c); CF.formula_flow_link = None})
                            | I.Var_flow c -> (C.Sharp_id c));
                      C.exp_sharp_val = Cast.Sharp_flow 
                              (match oe with	
                                | I.Var ve -> ve.I.exp_var_name
                                | _ -> Err.report_error { Err.error_loc = pos; 
                                  Err.error_text = "translation error, raise from finally raises"^ (Iprinter.string_of_exp oe)});
                      C.exp_sharp_pos = pos;
                      C.exp_sharp_path_id = pi;}), C.void_type)
                    else
                      let e_pos = Iast.get_exp_pos oe in
                      let ce, ct = helper oe in						
                      if exlist # sub_type_obj (string_of_typ ct) raisable_class then 							 
                        let fn = (fresh_ty_var_name (ct) pos.start_pos.Lexing.pos_lnum) in
                        let vd = C.VarDecl { C.exp_var_decl_type = ct;
                        C.exp_var_decl_name = fn;
                        C.exp_var_decl_pos = e_pos;} in
                        let init_e = C.Assign { C.exp_assign_lhs = fn;
                        C.exp_assign_rhs = ce;
                        C.exp_assign_pos = e_pos;} in
                        let shar = C.Sharp ({	
                            C.exp_sharp_type = C.void_type;
                            C.exp_sharp_flow_type = C.Sharp_ct (
								if use_type then 
									match ot with
										| I.Const_flow fl -> {CF.formula_flow_interval = (exlist # get_hash fl); CF.formula_flow_link = None}
										| _ -> Error.report_error {Error.error_loc = pos; Error.error_text = ("expecting constant flow")}
									else  match ct with 
										| Named v_t ->  {CF.formula_flow_interval = (exlist # get_hash v_t); CF.formula_flow_link = None}
										| _ -> Error.report_error {Error.error_loc = pos; Error.error_text = ("malfunction, primitive thrown type ")} );
                            C.exp_sharp_unpack = false;
                            C.exp_sharp_val = Cast.Sharp_var (ct,fn);
                            C.exp_sharp_path_id = pi;
                            C.exp_sharp_pos = pos }) in
                        let tmp_e1 = C.Seq { C.exp_seq_type = C.void_type;
                        C.exp_seq_exp1 = init_e;
                        C.exp_seq_exp2 = shar;
                        C.exp_seq_pos = pos;} in
                        let tmp_e2 = C.Seq { C.exp_seq_type = C.void_type;
                        C.exp_seq_exp1 = vd;
                        C.exp_seq_exp2 = tmp_e1;
                        C.exp_seq_pos = pos;} in 
                        (tmp_e2, Void)
                      else Err.report_error { Err.error_loc = pos; 
                      Err.error_text = "can not raise a not raisable object" }
              | None -> (
                    C.Sharp({C.exp_sharp_type = C.void_type;
                    C.exp_sharp_unpack = false;
                    C.exp_sharp_flow_type = (
                        match ot with 
                          | I.Const_flow c -> (C.Sharp_ct 
                                {CF.formula_flow_interval = (exlist # get_hash c); CF.formula_flow_link = None})
                          | I.Var_flow c -> (C.Sharp_id c));
                    C.exp_sharp_val = Cast.Sharp_no_val;
                    C.exp_sharp_pos = pos;
                    C.exp_sharp_path_id = pi;}), C.void_type) in r				
      | Iast.Try {  
            I.exp_try_block = body;
            I.exp_try_path_id = pid;
            I.exp_catch_clauses = cl_list;
            I.exp_finally_clause = fl_list;
            I.exp_try_pos = pos}-> 
            let pid = match pid with | None -> fresh_strict_branch_point_id "" | Some s -> s in
            if ((List.length fl_list)>0) then
              Err.report_error { Err.error_loc = pos; Err.error_text = "translation failed, i still found a finally clause" }
            else
              let new_clauses = List.map (fun c-> fst(helper c)) cl_list in
              let new_body , ct1 = helper body in
              (match (List.length cl_list) with
                | 0 -> (new_body,ct1)
                | 1 -> (C.Try({ C.exp_try_type = ct1;
                  C.exp_try_path_id = pid;
                  C.exp_try_body = new_body;
                  C.exp_catch_clause = (List.hd new_clauses) ;
                  C.exp_try_pos = pos}),C.void_type)
                | _ -> let r1 = List.fold_left (fun a c ->
                      let c = C.get_catch_of_exp c in
                      let fl_var = fresh_var_name "fl" pos.start_pos.Lexing.pos_lnum in
                      C.Try({ C.exp_try_type = ct1;
                      C.exp_try_body = a;
                      C.exp_try_path_id = fresh_strict_branch_point_id "";
                      C.exp_try_pos = pos;
                      C.exp_catch_clause =
                              C.Catch ({ c with C.exp_catch_body =
                                      C.Try({C.exp_try_type = Void;
                                      C.exp_try_path_id = fresh_strict_branch_point_id "";
                                      C.exp_try_body = c.C.exp_catch_body;
                                      C.exp_try_pos = c.C.exp_catch_pos;		   
                                      C.exp_catch_clause = C.Catch{
                                          C.exp_catch_flow_type = exlist # get_hash c_flow;
                                          C.exp_catch_flow_var = Some fl_var;
                                          C.exp_catch_var = None;
                                          C.exp_catch_body = C.Sharp({
                                              C.exp_sharp_type = (Void);
                                              C.exp_sharp_flow_type = C.Sharp_ct 
                                                  {CF.formula_flow_interval = !spec_flow_int; CF.formula_flow_link = Some fl_var};
                                              C.exp_sharp_val = Cast.Sharp_no_val;
                                              C.exp_sharp_unpack = false;
                                              C.exp_sharp_pos = pos;
                                              C.exp_sharp_path_id =None (* c.C.exp_catch_path_id*);
                                          });
                                          C.exp_catch_pos = pos;
                                          (*C.exp_catch_path_id = c.C.exp_catch_path_id;*)
                                      };
                                      });
                              });
                      })
                  ) new_body new_clauses in
		          let r = C.Try({C.exp_try_type = (match r1 with | C.Try t -> t.C.exp_try_type | _ -> Err.report_error { Err.error_loc = pos; Err.error_text = "translation failed, compacting case's failed" });
				  C.exp_try_body = r1;
				  C.exp_try_path_id = pid;
				  C.exp_catch_clause = C.Catch{
				      C.exp_catch_flow_type = !spec_flow_int;
				      C.exp_catch_flow_var = None (*Some (fresh_var_name "fl" pos.start_pos.Lexing.pos_lnum)*);
				      C.exp_catch_var = None;
				      C.exp_catch_body = C.Sharp({
						  C.exp_sharp_type = (Void);
						  C.exp_sharp_flow_type = C.Sharp_ct 
							  {CF.formula_flow_interval = !spec_flow_int; CF.formula_flow_link = None};
						  C.exp_sharp_val = Cast.Sharp_no_val;
						  C.exp_sharp_unpack = true;
						  C.exp_sharp_pos = pos;
						  C.exp_sharp_path_id = None (*stub_branch_point_id "_spec_catch"*);
					  });
				      C.exp_catch_pos = pos;};
				  C.exp_try_pos = pos};) in
		          (r, C.void_type)
	          )
	              (*  
                      and translate_catch prog proc pos c :C.exp_catch = match c with 
                      | { I.exp_catch_var = cv;
                      I.exp_catch_flow_type = cvt;
                      I.exp_catch_flow_var = cfv;
                      I.exp_catch_body = cb;	
                      I.exp_catch_pos = pos}->	
                      if not (Exc.exc_sub_type cvt c_flow) then Err.report_error { Err.error_loc = pos; 
		              Err.error_text = "can not catch a not raisable object" }
                      else begin
	                  match cv with
	                  | Some x ->
	                  if (String.compare cvt c_flow)=0 then  begin
		              E.push_scope();
		              let new_bd, ct2 = helper cb in
		              E.pop_scope();
		              {C.exp_catch_flow_type = (Exc.get_hash_of_exc c_flow);
		              C.exp_catch_flow_var = cfv;
		              C.exp_catch_var = Some (Void,x);
		              C.exp_catch_body = new_bd;																					   
		              C.exp_catch_pos = pos;} end
	                  else begin
		              E.push_scope();
		              let alpha = E.alpha_name x in
		              E.add x (E.VarInfo {E.var_name = x; E.var_alpha = alpha; E.var_type = (I.Named cvt)});
		          (*let _ = print_string ("\n rrr1 -> \n"^Iprinter.string_of_exp cb^"\n") in*)
		              let new_bd, ct2 = helper cb in
		          (*let _ = print_string ("\n rrr2 -> \n") in*)
		              let ct = if (Exc.exc_sub_type cvt raisable_class) then trans_type prog (I.Named cvt) pos else Named cvt in
		              E.pop_scope();
		              let r = {C.exp_catch_flow_type = (match ct with 
					  | Named ot-> (Exc.get_hash_of_exc ot) 
					  | _->  Error.report_error { Error.error_loc = pos; Error.error_text = "malfunction, catch translation error"});
			          C.exp_catch_flow_var = cfv;
			          C.exp_catch_var = Some (ct,alpha);
			          C.exp_catch_body = new_bd;																					   
			          C.exp_catch_pos = pos;
			          } in r end
	                  | None ->  
	                  E.push_scope();
	                  let new_bd, ct2 = helper cb in
		              E.pop_scope();
		              {	C.exp_catch_flow_type = Exc.get_hash_of_exc cvt;
			          C.exp_catch_flow_var = cfv;
			          C.exp_catch_var = None;
			          C.exp_catch_body = new_bd;																					   
			          C.exp_catch_pos = pos;}
                      end
	              (*| _ -> Err.report_error { Err.error_loc = pos; Err.error_text = "translation failed, catch clause got mistranslated" }*)
	              *)
   in helper ie

and default_value (t :typ) pos : C.exp =
  match t with
    | Int -> C.IConst { C.exp_iconst_val = 0; C.exp_iconst_pos = pos; }
    | Bool ->
	      C.BConst { C.exp_bconst_val = false; C.exp_bconst_pos = pos; }
    | Float ->
	      C.FConst { C.exp_fconst_val = 0.0; C.exp_fconst_pos = pos; }
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
    | HpT ->
          failwith "default_value: HpT can only be used for constraints"
    | Named c -> C.Null pos
	| Tree_sh ->  failwith
              "default_value: tree_sh in variable declaration should have been rejected"
	| Array (t, d) ->
		  C.EmptyArray { C.exp_emparray_type = t; 
		  C.exp_emparray_dim = d; 
		  C.exp_emparray_pos = pos}

and sub_type_x (t1 : typ) (t2 : typ) =
  let it1 = trans_type_back t1 in
  let it2 = trans_type_back t2 in I.sub_type it1 it2

and sub_type (t1 : typ) (t2 : typ) =
  let pr = string_of_typ in
  Debug.no_2 "sub_type" pr pr string_of_bool sub_type_x t1 t2 

(* TODO WN : NEED to re-check this function *)
and trans_type (prog : I.prog_decl) (t : typ) (pos : loc) : typ =
  match t with
    | Named c ->
	      (try
            let _ = I.look_up_data_def_raw prog.I.prog_data_decls c
            in Named c
	      with
	        | Not_found ->
                  (try
		            let _ = I.look_up_enum_def_raw prog.I.prog_enum_decls c
		            in Int
		          with
		            | Not_found -> (* An Hoa : cannot find the type, just keep the name. *)
						 (* if !inter then*)
							Err.report_error
			                    {
			                        Err.error_loc = pos;
			                        Err.error_text = c ^ " is neither data nor enum type";
			                    }
						  (*else let _ = report_warning pos ("Type " ^ c ^ " is not yet defined!") in
						  let _ = undef_data_types := (c, pos) :: !undef_data_types in
						  Named c (* Store this temporarily *)*)
				  ))
    | Array (et, r) -> Array (trans_type prog et pos, r) (* An Hoa *)
    | p -> p

and flatten_to_bind_debug prog proc b r rhs_o pid imm pos =
  Debug.no_2 "flatten_to_bind " 
      (Iprinter.string_of_exp) 
      (fun x -> match x with
        | Some x1 -> (Cprinter.string_of_exp x1) | None -> "")
      (fun _ -> "?")
      (fun b rhs_o -> flatten_to_bind prog proc b r rhs_o pid imm pos) b rhs_o

(**
   * An Hoa : compact field access by combining inline fields. For example, given
   * data pair { int x; int y; }
   * data quad { inline pair p1; pair p2; }
   * Suppose that q is of type quad.
   * The member access q.p1.x expression is parsed as Member { base = q, fields = [p1,x] }
   * We need to compact it to Member { base = q, fields = [p1.x] } because after expansion,
   * "p1.x" is a field of q. So q.p2.x is still Member { base = q, fields = [p2,x] }
**)
and compact_field_access_sequence prog root_type field_seq =
  (* let _ = print_endline ("[compact_field_access_sequence] input = { " ^ (string_of_typ root_type) ^ " ; { " ^ (String.concat " ; " field_seq) ^ " } }") in *)
  (* [Internal] Folding function: 
   * cfsq = current folding sequence; cf = accumulated field
   * ct = current type; fn = field name
   * Output : next state of (cfsq,cf,ct)
   *)
  let fold_function (cfsq,cf,ct) fn = 
	let f = I.get_field_from_typ prog.I.prog_data_decls ct fn in
	let ncf = cf ^ (if cf = "" then "" else ".") ^ fn in
	let nct = I.get_field_typ f in
	if (I.is_inline_field f) then
	  (cfsq,ncf,nct)
	else
	  (List.append cfsq [ncf],"",nct) in
  let res = List.fold_left fold_function ([],"",root_type) field_seq in
  (* let _ = print_endline ("[compact_field_access_sequence] output = { " ^ (String.concat " ; " res) ^ " }") in *)
  res

and flatten_to_bind prog proc (base : I.exp) (rev_fs : ident list)
      (rhs_o : C.exp option) (pid:control_path_id) (imm : heap_ann) (read_only : bool) pos =
  match rev_fs with
    | f :: rest ->
          let (cbase, base_t) = flatten_to_bind prog proc base rest None pid imm read_only pos in
          let (fn, new_var) =
            (match cbase with
              | C.Var { C.exp_var_name = v } -> (v, false)
              | _ -> let fn2 = (fresh_ty_var_name (base_t) pos.start_pos.Lexing.pos_lnum) in (fn2, true)) in
          let fn_decl = if new_var then
            C.VarDecl {
                C.exp_var_decl_type = base_t;
                C.exp_var_decl_name = fn;
                C.exp_var_decl_pos = pos; }
          else C.Unit pos in
          let init_fn = if new_var then
            C.Assign {
                C.exp_assign_lhs = fn;
                C.exp_assign_rhs = cbase;
                C.exp_assign_pos = pos; }
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
                    let (tmp, new_rest) = gen_names fn rest in
                    if (snd f) = fn then ((Some (fst f, fresh_fn)), (fresh_fn :: new_rest))
                    else (tmp, (fresh_fn :: new_rest))) in
          let all_fields = I.look_up_all_fields prog ddef in
          let field_types = List.map (fun f -> trans_type prog (I.get_field_typ f) pos) all_fields in
          let (tmp1, fresh_names) = gen_names f (List.map I.get_field_typed_id all_fields) in
          if not (Gen.is_some tmp1) then
            Err.report_error {
                Err.error_loc = pos;
                Err.error_text = "field " ^ (f ^ " is not accessible");}
          else
            (let (vt, fresh_v) = Gen.unsome tmp1 in
            let ct = trans_type prog vt pos in
            let (bind_body, bind_type) = match rhs_o with
              | None -> ((C.Var {
                    C.exp_var_type = ct;
                    C.exp_var_name = fresh_v;
                    C.exp_var_pos = pos; }), ct)
              | Some rhs_e ->
                    let rhs_t = C.type_of_exp rhs_e in
                    if (Gen.is_some rhs_t) && (sub_type (Gen.unsome rhs_t) ct) then
                      ((C.Assign {
                          C.exp_assign_lhs = fresh_v;
                          C.exp_assign_rhs = rhs_e;
                          C.exp_assign_pos = pos;}), C.void_type)
                    else Err.report_error {
                        Err.error_loc = pos;
                        Err.error_text = "lhs and rhs do not match"; } in
            let bind_e = C.Bind {
                C.exp_bind_type = bind_type;
                C.exp_bind_bound_var = ((Named dname), fn);
                C.exp_bind_fields = List.combine field_types fresh_names;
                C.exp_bind_body = bind_body;
		        C.exp_bind_imm = imm;
                C.exp_bind_read_only = read_only;
                C.exp_bind_pos = pos;
                C.exp_bind_path_id = pid;} in
            let seq1 = C.mkSeq bind_type init_fn bind_e pos in
            let seq2 = C.mkSeq bind_type fn_decl seq1 pos in
            if new_var then
              ((C.Block {
                  C.exp_block_type = bind_type;
                  C.exp_block_body = seq2;
		          C.exp_block_local_vars = [ (base_t, fn) ];
                  C.exp_block_pos = pos;}),bind_type)
            else (seq2, bind_type))
    | [] -> trans_exp prog proc base
and convert_to_bind prog (v : ident) (dname : ident) (fs : ident list)
      (rhs : C.exp option) pid imm read_only pos : trans_exp_type =
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
              List.map (fun f -> trans_type prog (I.get_field_typ f) pos)
                  ddef.I.data_fields in
            let (tmp1, fresh_names) =
              gen_names f (List.map I.get_field_typed_id ddef.I.data_fields)
            in
            if not (Gen.is_some tmp1)
            then
              Err.report_error
		          {
                      Err.error_loc = pos;
                      Err.error_text = "can't follow field " ^ f;
		          }
            else
              (let (vt, fresh_v) = Gen.unsome tmp1 in
		      let ct = trans_type prog vt pos in
		      let (bind_body, bind_type) =
                if Gen.is_empty rest
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
                            (Gen.is_some rhs_t) &&
				                (sub_type (Gen.unsome rhs_t) ct)
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
                  convert_to_bind prog fresh_v (string_of_typ vt) rest rhs pid imm read_only
                      pos
		      in
              ((C.Bind
                  {
			          C.exp_bind_type = bind_type;
			          C.exp_bind_bound_var = ((Named dname), v);
			          C.exp_bind_fields =
                          List.combine field_types fresh_names;
			          C.exp_bind_body = bind_body;
			          C.exp_bind_path_id = pid;
					  C.exp_bind_imm = imm;
                      C.exp_bind_read_only = read_only;
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

and trans_type_back (te : typ) : typ =
  match te with 
    | Named n -> Named n 
    | Array (t, d) -> Array (trans_type_back t, d) (* An Hoa *) 
    | p -> p 

and trans_args (args : (C.exp * typ * loc) list) :
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
		          let fn = fresh_ty_var_name (at) pos.start_pos.Lexing.pos_lnum in
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

and get_type_name_for_mingling (prog : I.prog_decl) (t : typ) : ident =
  match t with
    | Named c ->
	      (try let _ = I.look_up_enum_def_raw prog.I.prog_enum_decls c in "int"
	      with | Not_found -> c)
    |t -> string_of_typ t

and mingle_name_enum prog (m : ident) (targs : typ list) =
  let param_tnames =
    String.concat "~" (List.map (get_type_name_for_mingling prog) targs)
  in m ^ ("$" ^ param_tnames)

and set_mingled_name (prog : I.prog_decl) =
  let rec helper1 (pdecls : I.proc_decl list) =
    match pdecls with
      | pdef :: rest ->
            let ptypes = List.map (fun p -> p.I.param_type) pdef.I.proc_args in
            (pdef.I.proc_mingled_name <-
                mingle_name_enum prog pdef.I.proc_name ptypes;
            helper1 rest)
      | [] -> () in
  let rec helper2 (cdecls : I.data_decl list) =
    match cdecls with
      | cdef :: rest -> (helper1 cdef.I.data_methods; helper2 rest)
      | [] -> ()
  in (helper1 prog.I.prog_proc_decls; helper2 prog.I.prog_data_decls)

and insert_dummy_vars (ce : C.exp) (pos : loc) : C.exp =
  match ce with
    | C.Seq{
          C.exp_seq_type = t;
          C.exp_seq_exp1 = ce1;
          C.exp_seq_exp2 = ce2;
          C.exp_seq_pos = pos
      } ->
          let new_ce2 = insert_dummy_vars ce2 pos in
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
	        | Some t -> if CP.are_same_types t C.void_type then ce
              else
		        (let fn = fresh_ty_var_name (t) pos.start_pos.Lexing.pos_lnum in
		        let fn_decl = C.VarDecl {
                    C.exp_var_decl_type = t;
                    C.exp_var_decl_name = fn;
                    C.exp_var_decl_pos = pos; } in
		        let assign_e = C.Assign {
                    C.exp_assign_lhs = fn;
                    C.exp_assign_rhs = ce;
                    C.exp_assign_pos = pos; } in
		        let local_vars = [ (t, fn) ] in
		        let seq = C.Seq {
                    C.exp_seq_type = C.void_type;
                    C.exp_seq_exp1 = fn_decl;
                    C.exp_seq_exp2 = assign_e;
                    C.exp_seq_pos = pos;} in
		        let block_e = C.Block {
                    C.exp_block_type = C.void_type;
                    C.exp_block_body = seq;
                    C.exp_block_local_vars = local_vars;
                    C.exp_block_pos = pos; }
		        in block_e))

and case_coverage (instant:Cpure.spec_var list)(f:CF.struc_formula): bool =
  Debug.no_2 "case_coverage" (Gen.BList.string_of_f Cpure.string_of_spec_var_type)  
      Cprinter.string_of_struc_formula string_of_bool
      case_coverage_x instant f

and case_coverage_x (instant:Cpure.spec_var list)(f:CF.struc_formula): bool =
  let sat_subno  = ref 0 in
  let rec struc_case_coverage (instant:Cpure.spec_var list)(f1:CF.struc_formula):bool = match f1 with
    | CF.EAssume b ->  true
    | CF.EBase b -> (match b.CF.formula_struc_continuation with 
		| None -> true
		| Some l -> case_coverage_x (instant@ b.CF.formula_struc_explicit_inst@ b.CF.formula_struc_implicit_inst@ b.CF.formula_struc_exists) l)
    | CF.ECase b -> 
	      let r1,r2 = List.split b.CF.formula_case_branches in
	      let all = List.fold_left (fun a c->(Cpure.mkOr a c None no_pos) ) (Cpure.mkFalse b.CF.formula_case_pos) r1  in
		  (** An Hoa Temporary Printing **)
		  (* let _ = print_endline ("An Hoa : all = " ^ (Cprinter.string_of_pure_formula all)) in*)
	      let _ = if not(Gen.BList.subset_eq (=) (Cpure.fv all) instant) then 
	        let _ = print_string (
	            (List.fold_left (fun a c1-> a^" "^ (Cprinter.string_of_spec_var c1)) "\nall:" (Cpure.fv all))^"\n"^
	                (List.fold_left (fun a c1-> a^" "^ (Cprinter.string_of_spec_var c1)) "instant:" instant)^"\n")in			
	        Error.report_error {  Err.error_loc = b.CF.formula_case_pos;
            Err.error_text = "all guard free vars must be instantiated";} in
	      let _ = 
	        let sat = Tpdispatcher.is_sat_sub_no (Cpure.Not (all,None,no_pos)) sat_subno in
	        if sat then 
              let s = (Cprinter.string_of_struc_formula f) in
              Error.report_error {  Err.error_loc = b.CF.formula_case_pos;
              Err.error_text = "the guards don't cover the whole domain for : "^s^"\n";} 	in
	      
	      let rec p_check (p:Cpure.formula list):bool = match p with
	        | [] -> false 
	        | p1::p2 -> if (List.fold_left (fun a c-> a ||(Tpdispatcher.is_sat_sub_no (Cpure.mkAnd p1 c no_pos) sat_subno)) false p2 ) then true else p_check p2 in
	      
	      let _ = if (p_check r1) then 
            Error.report_error {  Err.error_loc = b.CF.formula_case_pos;
            Err.error_text = "the guards are not disjoint : "^(Cprinter.string_of_struc_formula f)^"\n";} in
	      let _ = List.map (case_coverage_x instant) r2 in true
    | CF.EInfer b -> struc_case_coverage instant b.CF.formula_inf_continuation
	| CF.EOr b -> (struc_case_coverage instant b.CF.formula_struc_or_f1)&&(struc_case_coverage instant b.CF.formula_struc_or_f2)
	| CF.EList b -> List.for_all (fun c-> struc_case_coverage instant(snd c)) b in
  struc_case_coverage instant f

and trans_var_nth i p stab pos =
  let pr = pr_var_prime in
  Debug.no_1_num i "trans_var" pr Cprinter.string_of_spec_var (fun _ -> trans_var_x p stab pos) p

and trans_var p stab pos =
  let pr = pr_var_prime in
  Debug.no_1 "trans_var" pr Cprinter.string_of_spec_var (fun _ -> trans_var_x p stab pos) p

(* TODO WN : need to test how type checking handle # vars *)
and trans_var_x (ve, pe) stab pos =
  (* An Hoa [23/08/2011] Variables with "#" should not be considered.*)
  (* if (ve.[0] = '#') then  *)
  (*   CP.SpecVar (UNK,"#",Unprimed) *)
  if (is_dont_care_var ve) then 
	CP.SpecVar (UNK,ve,Unprimed)
  else (* An Hoa : END *)
	try
      let ve_info = H.find stab ve
      in
      (match ve_info.sv_info_kind with
        | UNK ->
              Err.report_error
                  {
                      Err.error_loc = pos;
                      Err.error_text = "couldn't infer type for " ^ ve^(match pe with |Unprimed->""|Primed -> "'")^" in "^(string_of_stab stab)^"\n";
                  }
        | t -> CP.SpecVar (t, ve, pe)

      )
    with Not_found ->   
        Err.report_error
            {
                Err.error_loc = pos;
                Err.error_text = "type table does not contain an entry for " ^ ve^(match pe with |Unprimed->""|Primed -> "'")^" in "^(string_of_stab stab)^"\n, could it be an unused var?\n";
            }			
            
and trans_var_safe (ve, pe) et stab pos =
  (* An Hoa [23/08/2011] Variables with "#" should not be considered.*)
  (* if (ve.[0] = '#') then   CP.SpecVar (UNK,"#",Unprimed) *)
  if (is_dont_care_var ve) then 
	CP.SpecVar (UNK,ve,Unprimed)
  else (* An Hoa : END *)
	try
      let ve_info = H.find stab ve
      in
      (match ve_info.sv_info_kind with
        | UNK -> CP.SpecVar (et, ve, pe)
        | t -> CP.SpecVar (t, ve, pe)

      )
    with Not_found ->   
        CP.SpecVar (et, ve, pe)

and add_pre_x (prog :C.prog_decl) (f:CF.struc_formula):CF.struc_formula = 
  let rec helper (pf:Cpure.formula) (f:CF.struc_formula): CF.struc_formula = match f with
	| CF.ECase b -> CF.ECase{b with CF.formula_case_branches =  List.map (fun (c1,c2)->(c1,(helper (Cpure.mkAnd c1 pf no_pos) c2))) b.CF.formula_case_branches;}
	| CF.EBase b ->
	          let xpure_pre2_prim = Solver.xpure_consumed_pre prog b.CF.formula_struc_base in
	          let new_pf = Cpure.mkAnd pf (Cpure.mkExists b.CF.formula_struc_exists xpure_pre2_prim None no_pos) no_pos in
	          CF.EBase{b with CF.formula_struc_continuation = map_opt (helper new_pf) b.CF.formula_struc_continuation;}
	| CF.EAssume (ref_vars, bf,y) -> CF.EAssume (ref_vars, (CF.normalize 2 bf (CF.formula_of_pure_N pf no_pos) no_pos),y)
	| CF.EInfer b -> CF.EInfer {b with CF.formula_inf_continuation = helper pf b.CF.formula_inf_continuation;}
	| CF.EList b -> CF.EList (map_l_snd (helper pf) b)
	| CF.EOr b-> CF.EOr {b with CF.formula_struc_or_f1 = helper pf b.CF.formula_struc_or_f1; CF.formula_struc_or_f2 = helper pf b.CF.formula_struc_or_f2;} in
  helper (Cpure.mkTrue no_pos) f
         
and add_pre prog f =
  let pr = Cprinter.string_of_struc_formula in
  Debug.no_1 "add_pre"  pr pr (add_pre_x prog) f 
      
and trans_I2C_struc_formula (prog : I.prog_decl) (quantify : bool) (fvars : ident list) (f0 : IF.struc_formula) stab (sp:bool): CF.struc_formula = 
  let prb = string_of_bool in
  Debug.no_eff_5 "trans_I2C_struc_formula" [true] string_of_stab prb prb Cprinter.str_ident_list 
      (add_str "Input Struc:" Iprinter.string_of_struc_formula) 
      (add_str "Output Struc:" Cprinter.string_of_struc_formula)
      (fun _ _ _ _ _ -> trans_I2C_struc_formula_x prog quantify fvars f0 stab sp) stab (* type table *) quantify (* quantified flag *) sp 
      fvars (* free vars *) f0 (*struc formula *)

      
and trans_I2C_struc_formula_x (prog : I.prog_decl) (quantify : bool) (fvars : ident list)
      (f0 : IF.struc_formula) stab (sp:bool): CF.struc_formula = 
  let rec trans_struc_formula (fvars : ident list) stab (f0 : IF.struc_formula) :CF.struc_formula = match f0 with
      | IF.EAssume (b,y)->	(*add res, self*)
            CF.EAssume ([], trans_formula prog true (self::res_name::eres_name::fvars) false b stab true, y)
      | IF.ECase b-> 	
            CF.ECase {
                CF.formula_case_exists = [];
                CF.formula_case_branches = List.map (fun (c1,c2)-> (Cpure.arith_simplify 2 (trans_pure_formula c1 stab),
                trans_struc_formula fvars stab c2)) b.IF.formula_case_branches;          
                CF.formula_case_pos = b.IF.formula_case_pos}			
      | IF.EBase b-> 			
			let nc = map_opt (trans_struc_formula (fvars @ (fst (List.split(IF.heap_fv b.IF.formula_struc_base)))) stab)
				b.IF.formula_struc_continuation in
            let nb = trans_formula prog quantify fvars false b.IF.formula_struc_base stab false in
            let ex_inst = List.map (fun c-> trans_var_safe c UNK stab b.IF.formula_struc_pos) b.IF.formula_struc_explicit_inst in
            let ext_impl = List.map (fun c-> trans_var_safe c UNK stab b.IF.formula_struc_pos) b.IF.formula_struc_implicit_inst in
            let ext_exis = List.map (fun c-> trans_var_safe c UNK stab b.IF.formula_struc_pos) b.IF.formula_struc_exists in
            CF.EBase {
                CF.formula_struc_explicit_inst = ex_inst;
                CF.formula_struc_implicit_inst = ext_impl;
                CF.formula_struc_exists = ext_exis;
                CF.formula_struc_base = nb;
                CF.formula_struc_continuation = nc;
                CF.formula_struc_pos = b.IF.formula_struc_pos}
      | IF.EInfer b -> 
            (* TODO : check iv - fvars = {} *)
            let pos = b.IF.formula_inf_pos in
            let ivs = b.IF.formula_inf_vars in
            let ct = trans_struc_formula fvars stab b.IF.formula_inf_continuation in
            let new_ivs = List.map (fun (i,p) -> 
                let v=get_spec_var_ident stab i p in
                match v with
                  | CP.SpecVar(t,id,pr) ->
                        if t==UNK then
                          try
                            let _ = I.look_up_rel_def_raw prog.I.prog_rel_decls id in
                            CP.SpecVar(RelT,id,pr)
                          with _ -> 
                            try
                              let _ = I.look_up_func_def_raw prog.I.prog_func_decls id in
                              CP.SpecVar(RelT,id,pr)
                            with _ ->
                                try
                                    let _ = I.look_up_hp_def_raw prog.I.prog_hp_decls id in
                                    CP.SpecVar(HpT,id,pr)
                                with _ -> v
                        else v
            ) ivs in
            (* TODO : any warning below should be fixed *)
            let ivs_unk = List.filter (fun v -> (CP.type_of_spec_var v)==UNK) new_ivs in
            if ivs_unk!=[] then 
              begin
                let s = (Cprinter.string_of_spec_var_list ivs_unk) in
                print_endline ("WARNING (must fix): Vars from"^s^"has type UNK")
              end;
            if ivs_unk!=[] then
              Err.report_error { Err.error_loc = pos;
              Err.error_text = ("infer vars with unknown type "^(Cprinter.string_of_spec_var_list ivs_unk)) }
             else
        CF.EInfer {
        CF.formula_inf_post = b.IF.formula_inf_post;
        CF.formula_inf_xpost = b.IF.formula_inf_xpost;
        CF.formula_inf_transpec = b.IF.formula_inf_transpec;
        CF.formula_inf_vars = new_ivs;
        CF.formula_inf_continuation = ct;
        CF.formula_inf_pos = pos}
	| IF.EList b -> CF.mkEList (map_l_snd (trans_struc_formula fvars stab) b) 
	| IF.EOr b -> CF.EOr {
			CF.formula_struc_or_f1 = trans_struc_formula fvars stab b.IF.formula_struc_or_f1;
			CF.formula_struc_or_f2 = trans_struc_formula fvars stab b.IF.formula_struc_or_f2;
			CF.formula_struc_or_pos = b.IF.formula_struc_or_pos;}in
   
  (* let _ = collect_type_info_struc_f prog f0 stab in	 *)
  let _ = gather_type_info_struc_f prog f0 stab in
  let r = trans_struc_formula fvars stab f0 in
  let cfvhp1 = List.map (fun c-> trans_var_safe (c,Primed) UNK stab (IF.pos_of_struc_formula f0)) fvars in
  let cfvhp2 = List.map (fun sv -> match sv with | CP.SpecVar (t,v,_) -> CP.SpecVar(t,v,Unprimed)) cfvhp1 in
  (* let cfvhp2 = List.map (fun c-> trans_var_safe (c,Unprimed) stab (IF.pos_of_struc_formula f0)) fvars in *)
  let cfvhp = cfvhp1@cfvhp2 in
  let _ = case_coverage cfvhp r in
  let tmp_vars  =  (CF.struc_post_fv r) in 
  let post_fv = List.map CP.name_of_spec_var tmp_vars in
  let pre_fv = List.map CP.name_of_spec_var (Gen.BList.difference_eq (=) (CF.struc_fv r) tmp_vars) in
  let r = if ((List.mem self pre_fv) || (List.mem self post_fv))&&sp then
    Err.report_error { Err.error_loc = CF.pos_of_struc_formula r; Err.error_text ="self is not allowed in pre/postcondition";}
  else if List.mem res_name pre_fv then
    Err.report_error{ Err.error_loc = CF.pos_of_struc_formula r; Err.error_text = "res is not allowed in precondition";}
  else r  in
  let _ = type_store_clean_up r stab in
  r

and trans_formula (prog : I.prog_decl) (quantify : bool) (fvars : ident list) sep_collect
      (f0 : IF.formula) stab (clean_res:bool) : CF.formula =
  let prb = string_of_bool in
  Debug.no_eff_5 "trans_formula" [true] string_of_stab 
      (add_str "quantify" prb) 
      (add_str "cleanres" prb) Cprinter.str_ident_list Iprinter.string_of_formula Cprinter.string_of_formula 
      (fun _ _ _ _ _ -> trans_formula_x (prog : I.prog_decl) (quantify : bool) (fvars : ident list) sep_collect
          (f0 : IF.formula) stab (clean_res:bool)) stab quantify clean_res fvars f0

and trans_formula_x (prog : I.prog_decl) (quantify : bool) (fvars : ident list) sep_collect (f0 : IF.formula) stab (clean_res:bool) : CF.formula =
  let helper_one_formula (f:IF.one_formula)  =
    if sep_collect then (gather_type_info_pure prog f.IF.formula_pure stab; gather_type_info_heap prog f.IF.formula_heap stab) else () in
  let rec helper f0 =
    match f0 with
      | IF.Or b-> CF.mkOr (helper b.IF.formula_or_f1) (helper b.IF.formula_or_f2) b.IF.formula_or_pos
      | IF.Base {
            IF.formula_base_heap = h;
            IF.formula_base_pure = p;
            IF.formula_base_flow = fl;
            IF.formula_base_and = a;
            IF.formula_base_pos = pos} ->(
            let rl = res_retrieve stab clean_res fl in
            let _ = if sep_collect then  (gather_type_info_pure prog p stab; gather_type_info_heap prog h stab) else () in 					
            let _ = List.map helper_one_formula a in
            let ch = linearize_formula prog f0 stab in					
            (*let ch1 = linearize_formula prog false [] f0 stab in*)
            let _ = 
              if sep_collect then (
                  if quantify then
                    (let tmp_stab = H.create 103 in
                    (Gen.HashUti.copy_keys fvars stab tmp_stab;
                    H.clear stab;
                    Gen.HashUti.copy_keys fvars tmp_stab stab;))
                  else ()) 
              else () in 
            (res_replace stab rl clean_res fl);ch)
      | IF.Exists	{
            IF.formula_exists_qvars = qvars;
            IF.formula_exists_heap = h;
            IF.formula_exists_pure = p;
            IF.formula_exists_flow = fl;
            IF.formula_exists_and = a;
            IF.formula_exists_pos = pos} -> (
            let rl = res_retrieve stab clean_res fl in
            let _ = if sep_collect then (gather_type_info_pure prog p stab;
            gather_type_info_heap prog h stab) else () in 
            let _ = List.map helper_one_formula a in
            let f1 = IF.Base {
                IF.formula_base_heap = h;
                IF.formula_base_pure = p;
                IF.formula_base_flow = fl;
                IF.formula_base_and = a;
                IF.formula_base_pos = pos; } in
            (* let _ = print_endline ("trans_formula: Exists: before linearize:" *)
            (*                        ^ " ### stab = " ^ (string_of_stab stab )) in *)
            let ch = linearize_formula prog f1 stab in
            let qsvars = List.map (fun qv -> trans_var qv stab pos) qvars in
            let ch = CF.push_exists qsvars ch in
            let _ = if sep_collect then
              (if quantify then
                (let tmp_stab = H.create 103 in
                let fvars = (List.map fst qvars) @ fvars in
		        (Gen.HashUti.copy_keys fvars stab tmp_stab;
		        H.clear stab;
		        Gen.HashUti.copy_keys fvars tmp_stab stab;))
		      else ())
            else () in
	        (res_replace stab rl clean_res fl);ch) 
  in (* An Hoa : Add measure to combine partial heaps into a single heap *)
  let cf = helper f0 in
  (*TO CHECK: temporarily disabled*) 
  (* let cf = CF.merge_partial_heaps cf in (\*ENABLE THIS for partial fields*\) *)
   cf

and linearize_formula (prog : I.prog_decl)  (f0 : IF.formula)(stab : spec_var_table) =
  let pr1 prog = "prog" in
  Debug.no_3 "linearize_formula" pr1 Iprinter.string_of_formula string_of_stab Cprinter.string_of_formula linearize_formula_x prog f0 stab

and linearize_formula_x (prog : I.prog_decl)  (f0 : IF.formula)(stab : spec_var_table) =
  let rec match_exp (hargs : (IP.exp * Label_only.spec_label) list) pos : (CP.spec_var list) =
    match hargs with
      | (e, _) :: rest ->
            let e_hvars = match e with
              | IP.Var ((ve, pe), pos_e) -> trans_var_safe (ve, pe) UNK stab pos_e
              | _ -> report_error (IF.pos_of_formula f0)("malfunction with float out exp: "^(Iprinter.string_of_formula f0))in
            let rest_hvars = match_exp rest pos in
            let hvars = e_hvars :: rest_hvars in
	        hvars
      | [] -> [] in
  let rec linearize_heap (f : IF.h_formula) pos : ( CF.h_formula * CF.t_formula) = 
    let res = 
      match f with
        | IF.HeapNode2 h2 -> report_error (IF.pos_of_formula f0) "malfunction with convert to heap node"
        | IF.HeapNode{
              IF.h_formula_heap_node = (v, p);
              IF.h_formula_heap_name = c;
	          IF.h_formula_heap_derv = dr;
	          IF.h_formula_heap_imm = imm;
	          IF.h_formula_heap_perm = perm; (*LDK*)
              IF.h_formula_heap_arguments = exps;
              IF.h_formula_heap_full = full;
              IF.h_formula_heap_pos = pos;
              IF.h_formula_heap_label = pi;} ->
			  (* An Hoa : Handle field access *)
			  (* ASSUMPTIONS detected: exps ARE ALL VARIABLES i.e. I.Var AFTER float_out_exp PRE-PROCESSING! *)
			  if (c = Parser.generic_pointer_type_name || String.contains v '.') then
				let tokens = Str.split (Str.regexp "\\.") v in
				let field_access_seq = List.filter (fun x -> I.is_not_data_type_identifier prog.I.prog_data_decls x) tokens in
				let field_access_seq = List.tl field_access_seq in (* get rid of the root pointer as well *)
				let rootptr = List.hd tokens in
				let rpsi = H.find stab rootptr in
				let rootptr_type = rpsi.sv_info_kind in
				let rootptr_type_name = match rootptr_type with | Named c -> c | _ -> failwith ("[linearize_heap] " ^ rootptr ^ " must be a pointer.") in
				let rootptr, p = let rl = String.length rootptr in
				if rootptr.[rl-1] = '\'' then
				  (String.sub rootptr 0 (rl - 1), Primed)
				else
				  (rootptr, Unprimed) in 
				let field_offset = I.compute_field_seq_offset prog.I.prog_data_decls rootptr_type_name field_access_seq in
				let num_ptrs = I.get_typ_size prog.I.prog_data_decls rootptr_type in
				(* An Hoa : The rest are copied from the original code with modification to account for the holes *)
				let labels = List.map (fun _ -> Label_only.empty_spec_label) exps in
				let hvars = match_exp (List.combine exps labels) pos in
				(* [Internal] Create a list [x,x+1,...,x+n-1] *)
				let rec first_naturals n x = 
				  if n = 0 then [] 
				  else x :: (first_naturals (n-1) (x+1)) in
				(* [Internal] Extends hvars with holes and collect the list of holes! *)
				let rec extend_and_collect_holes vs offset num_ptrs =
				  let temp = first_naturals num_ptrs 0 in
				  let numargs = List.length vs in
				  let holes = List.fold_left (fun l i -> let d = i - offset in
				  if (d < 0 || d >= numargs) then List.append l [i] else l)
					[] temp	in
				  let newvs = List.map (fun i -> if (List.mem i holes) then 
					CP.SpecVar (UNK,"#",Unprimed) 
				  else List.nth vs (i - offset)) temp in
				  (newvs,holes) in
				(* [Internal] End of function <extend_and_collect_holes> *)
				let hvars, holes = extend_and_collect_holes hvars field_offset num_ptrs in
                (*TO CHECK: for correctness*)
                (*LDK: linearize perm permission as a spec var*)
                let permvar = (match perm with
                  | None -> None
                  | Some f -> 
                        let perms = [f] in
                        let permlabels = List.map (fun _ -> Label_only.empty_spec_label) perms in
                        let permvars = match_exp (List.combine perms permlabels) pos in
                        Some (List.nth permvars 0) )
                in
				let result_heap = CF.DataNode {
					CF.h_formula_data_node = CP.SpecVar (rootptr_type,rootptr,p);
					CF.h_formula_data_name = rootptr_type_name;
		            CF.h_formula_data_derv = dr;
					CF.h_formula_data_imm = Immutable.iformula_ann_to_cformula_ann imm;
		            CF.h_formula_data_perm = permvar; (*??? TO CHECK: temporarily*)
                    CF.h_formula_data_origins = []; (*??? temporarily*)
		            CF.h_formula_data_original = true; (*??? temporarily*)
					CF.h_formula_data_arguments = hvars;
					CF.h_formula_data_holes = holes;
					CF.h_formula_data_label = pi;
					CF.h_formula_data_remaining_branches = None;
					CF.h_formula_data_pruning_conditions = [];
					CF.h_formula_data_pos = pos; } in
				(result_heap, CF.TypeTrue)
			  else (* Not a field access, proceed with the original code *)
                (try
                  let vdef = I.look_up_view_def_raw prog.I.prog_view_decls c in
                  let labels = vdef.I.view_labels in
                  let hvars = match_exp (List.combine exps labels) pos in
                  let c0 =
                    if vdef.I.view_data_name = "" then 
                      (fill_view_param_types vdef;
                      vdef.I.view_data_name)
                    else vdef.I.view_data_name in
                  let new_v = CP.SpecVar (Named c0, v, p) in
                  (*LDK: linearize perm permission as a spec var*)
                  let permvar = (match perm with
                    | None -> None
                    | Some f -> 
                          let perms = f :: [] in
                          let permlabels = List.map (fun _ -> Label_only.empty_spec_label) perms in
                          let permvars = match_exp (List.combine perms permlabels) pos in
                          Some (List.nth permvars 0) )
                  in
                  let new_h = CF.ViewNode {
                      CF.h_formula_view_node = new_v;
                      CF.h_formula_view_name = c;
		              CF.h_formula_view_derv = dr;
		              CF.h_formula_view_imm = Immutable.iformula_ann_to_cformula_ann imm;
		              CF.h_formula_view_perm = permvar; (*LDK: TO CHECK*)
                      CF.h_formula_view_arguments = hvars;
                      CF.h_formula_view_modes = vdef.I.view_modes;
                      CF.h_formula_view_coercible = true;
                      CF.h_formula_view_origins = [];
		              CF.h_formula_view_original = true;
		              (* CF.h_formula_view_orig_fold_num = !num_self_fold_search; *)
		              CF.h_formula_view_lhs_case = true;
		              CF.h_formula_view_unfold_num = 0;
                      CF.h_formula_view_label = pi;
                      CF.h_formula_view_pruning_conditions = [];
                      CF.h_formula_view_remaining_branches = None;
                      CF.h_formula_view_pos = pos;}
                  in (new_h, CF.TypeTrue)
                with
                  | Not_found ->
                        let labels = List.map (fun _ -> Label_only.empty_spec_label) exps in
                        let hvars = match_exp (List.combine exps labels) pos in
                        let new_v = CP.SpecVar (Named c, v, p) in
						(* An Hoa : find the holes here! *)
						let rec collect_holes vars n = match vars with
						  | [] -> []
						  | x::t -> let th = collect_holes t (n+1) in 
							(match x with 
							  | CP.SpecVar (_,vn,_) -> if (vn.[0] = '#') then n::th else th ) in
                        (*LDK: linearize perm permission as a spec var*)
                        let permvar = match perm with 
                          | None -> None
                          | Some f -> 
                                let perms = f :: [] in
                                let permlabels = List.map (fun _ -> Label_only.empty_spec_label) perms in
                                let permvars = match_exp (List.combine perms permlabels) pos in
                                Some (List.nth permvars 0) 
						in
						let holes = collect_holes hvars 0 in
                        let new_h = CF.DataNode {
                            CF.h_formula_data_node = new_v;
                            CF.h_formula_data_name = c;
		                    CF.h_formula_data_derv = dr;
		                    CF.h_formula_data_imm = Immutable.iformula_ann_to_cformula_ann imm;
		                    CF.h_formula_data_perm = permvar; (*LDK*)
                            CF.h_formula_data_origins = [];
		                    CF.h_formula_data_original = true;
		                    CF.h_formula_data_arguments = hvars;
							CF.h_formula_data_holes = holes; (* An Hoa : Set the hole *)
                            CF.h_formula_data_label = pi;
                            CF.h_formula_data_remaining_branches = None;
                            CF.h_formula_data_pruning_conditions = [];
                            CF.h_formula_data_pos = pos;} 
                        in ( new_h, CF.TypeTrue))
        | IF.Star {
              IF.h_formula_star_h1 = f1;
              IF.h_formula_star_h2 = f2;
              IF.h_formula_star_pos = pos
          } ->
              let (lf1, type1) = linearize_heap f1 pos in
              let (lf2, type2) = linearize_heap f2 pos in
              let tmp_h = CF.mkStarH lf1 lf2 pos in
              let tmp_type = CF.mkAndType type1 type2 in 
	          (tmp_h, tmp_type)
        | IF.Phase
                {
                    IF.h_formula_phase_rd = f1;
                    IF.h_formula_phase_rw = f2;
                    IF.h_formula_phase_pos = pos
                } ->
              let (lf1, type1) = linearize_heap f1 pos in
              let (lf2, type2) = linearize_heap f2 pos in
              let tmp_h = CF.mkPhaseH lf1 lf2 pos in
              let tmp_type = CF.mkAndType type1 type2 in 
	          (tmp_h, tmp_type)
        | IF.Conj
                {
                    IF.h_formula_conj_h1 = f1;
                    IF.h_formula_conj_h2 = f2;
                    IF.h_formula_conj_pos = pos
                } ->
              let (lf1, type1) = linearize_heap f1 pos in
              let (lf2, type2) = linearize_heap f2 pos in
              let tmp_h = CF.mkConjH lf1 lf2 pos in
              let tmp_type = CF.mkAndType type1 type2 in 
	          (tmp_h, tmp_type)
        | IF.HRel (r, args, pos) ->    
          let nv = trans_var_safe (r,Unprimed) HpT stab pos in
    	  (* Match types of arguments with relation signature *)
		  let cpargs = trans_pure_exp_list args stab in
		   (CF.HRel (nv, cpargs, pos), CF.TypeTrue)
        | IF.HTrue ->  (CF.HTrue, CF.TypeTrue)
        | IF.HFalse -> (CF.HFalse, CF.TypeFalse) 
        | IF.HEmp -> (CF.HEmp, CF.TypeTrue) in 
    res

  in
  let linearize_one_formula_x f pos = 
    let h = f.IF.formula_heap in
    let p = f.IF.formula_pure in
    let id = f.IF.formula_thread in
    let pos = f.IF.formula_pos in
    let (new_h, type_f) = linearize_heap h pos in
    let new_p = trans_pure_formula p stab in
    let new_p = Cpure.arith_simplify 5 new_p in
    let mix_p = (MCP.memoise_add_pure_N (MCP.mkMTrue pos) new_p) in
    let id_var = (match id with
      | None -> 
          (*May be redundant*)
          (*this lookup should be done when float_out_thread*)
          (*Here, try it the second chance*)
          (*look for an thread id*)
          let thread_var = Cpure.SpecVar (Globals.thread_typ, Globals.thread_name,Globals.Unprimed) in
          (*find all spec_var which is equal to "thread"*)
          let vv = MCP.find_closure_mix_formula thread_var mix_p in 
          let vv1 = Gen.BList.difference_eq CP.eq_spec_var vv [thread_var] in
          if (vv1==[]) then Error.report_error {Error.error_loc = pos;Error.error_text = "linearize_one_formula: could not find thread id"}
          else List.hd vv1
      | Some (ve,pe) -> (trans_var (ve, pe) stab pos))
    in
    let new_f = { CF.formula_heap = new_h;
                  CF.formula_pure = mix_p;
                  CF.formula_thread = id_var;
                  CF.formula_ref_vars = [];
                  CF.formula_label = None;
                  CF.formula_pos = pos} in
    (new_f,type_f)
  in
  let linearize_one_formula f pos =
    let pr (a,b) = Cprinter.string_of_one_formula a in
    Debug.no_1 "linearize_one_formula" 
        Iprinter.string_of_one_formula pr
        (fun _ -> linearize_one_formula_x f pos) f
  in
  let linearize_base base pos =
    let h = base.IF.formula_base_heap in
    let p = base.IF.formula_base_pure in
    let fl = base.IF.formula_base_flow in
    let a = base.IF.formula_base_and in
    let pos = base.IF.formula_base_pos in
    let (new_h, type_f) = linearize_heap h pos in
    let new_p = trans_pure_formula p stab in
    let new_p = Cpure.arith_simplify 5 new_p in
    let new_fl = trans_flow_formula fl pos in

    let new_a,_ = List.split (List.map (fun f -> linearize_one_formula f pos) a) in
    (new_h, new_p, type_f, new_fl, new_a) in
  match f0 with
    | IF.Or {
          IF.formula_or_f1 = f1;
          IF.formula_or_f2 = f2;
          IF.formula_or_pos = pos } ->
          let lf1 = linearize_formula prog f1 stab in
          let lf2 = linearize_formula prog f2 stab in
          let result = CF.mkOr lf1 lf2 pos in result
    | IF.Base base ->
          let pos = base.IF.formula_base_pos in
          let nh,np,nt,nfl, na = (linearize_base base pos) in
          let np = (memoise_add_pure_N (mkMTrue pos) np)  in
          CF.mkBase nh np nt nfl na pos
    | IF.Exists {
          IF.formula_exists_heap = h; 
          IF.formula_exists_pure = p;
          IF.formula_exists_flow = fl;
          IF.formula_exists_qvars = qvars;
          IF.formula_exists_and = a;
          IF.formula_exists_pos = pos} ->
          let base ={
              IF.formula_base_heap = h;
              IF.formula_base_pure = p;
              IF.formula_base_flow = fl;
              IF.formula_base_and = a;
              IF.formula_base_pos = pos;
          } in 
	      let nh,np,nt,nfl,na = linearize_base base pos in
          let np = memoise_add_pure_N (mkMTrue pos) np in
	      CF.mkExists (List.map (fun c-> trans_var_safe c UNK stab pos) qvars) nh np nt nfl na pos 
	          

and trans_flow_formula (f0:IF.flow_formula) pos : CF.flow_formula = 
  { CF.formula_flow_interval = exlist #  get_hash f0;
  CF.formula_flow_link = None} 

and check_dfrac_wf e1 e2 pos = if (CP.has_e_tscons e1)||(CP.has_e_tscons e2) then
	match e1,e2 with 
	| CP.Var _ , CP.Var _ 
	| CP.Var _, CP.Tsconst _
    | CP.Tsconst _, CP.Var _
	| CP.Tsconst _, CP.Tsconst _ -> ()
	| CP.Add (e1,e2,_), CP.Var _ 
	| CP.Var _ , CP.Add (e1,e2,_)-> 
		(match e1,e2 with 
			  | CP.Var _, CP.Var _
			  | CP.Var _, CP.Tsconst _
			  | CP.Tsconst _, CP.Var _
			  | CP.Tsconst _, CP.Tsconst _ -> ()
			  | _,_ -> report_error pos ("distinct shares can appear only in expressions of the form a=a or a+a=a where a=v|c "^(Cprinter.string_of_formula_exp e1)^" = "^(Cprinter.string_of_formula_exp e1)))
	| _ -> report_error pos ("distinct shares can appear only in expressions of the form a=a or a+a=a where a=v|c "^(Cprinter.string_of_formula_exp e1)^" = "^(Cprinter.string_of_formula_exp e1))
  else ()
  
and trans_pure_formula (f0 : IP.formula) stab : CP.formula =
  match f0 with
    | IP.BForm (bf,lbl) -> CP.BForm (trans_pure_b_formula bf stab , lbl) 
    | IP.And (f1, f2, pos) ->
          let pf1 = trans_pure_formula f1 stab in
          let pf2 = trans_pure_formula f2 stab in CP.mkAnd pf1 pf2 pos
	| IP.AndList b -> CP.mkAndList (map_l_snd (fun c-> trans_pure_formula c stab) b)
    | IP.Or (f1, f2,lbl, pos) ->
          let pf1 = trans_pure_formula f1 stab in
          let pf2 = trans_pure_formula f2 stab in CP.mkOr pf1 pf2 lbl pos
    | IP.Not (f, lbl, pos) -> let pf = trans_pure_formula f stab in CP.mkNot pf lbl pos
    | IP.Forall ((v, p), f, lbl, pos) ->
          let pf = trans_pure_formula f stab in
          let v_type = Cpure.type_of_spec_var (trans_var (v,Unprimed) stab pos) in
          let sv = CP.SpecVar (v_type, v, p) in CP.mkForall [ sv ] pf lbl pos
    | IP.Exists ((v, p), f, lbl, pos) ->
          let pf = trans_pure_formula f stab in
          let sv = trans_var (v,p) stab pos in
	      CP.mkExists [ sv ] pf lbl pos
			  
and trans_pure_b_formula (b0 : IP.b_formula) stab : CP.b_formula =
  Debug.no_1 "trans_pure_b_formula" (Iprinter.string_of_b_formula) (Cprinter.string_of_b_formula) (fun b -> trans_pure_b_formula_x b stab) b0 			
	  
and trans_pure_b_formula_x (b0 : IP.b_formula) stab : CP.b_formula =
  let (pf, sl) = b0 in
  let npf =  match pf with
    | IP.BConst (b, pos) -> CP.BConst (b, pos)
    | IP.BVar ((v, p), pos) -> CP.BVar (CP.SpecVar (C.bool_type, v, p), pos)
    | IP.LexVar (t_ann, ls1, ls2, pos) ->
          let cle = List.map (fun e -> trans_pure_exp e stab) ls1 in
          let clt = List.map (fun e -> trans_pure_exp e stab) ls2 in
          CP.LexVar {
					  CP.lex_ann = t_ann;
						CP.lex_exp = cle;
						CP.lex_tmp = clt;
						CP.lex_loc = pos; }
    | IP.Lt (e1, e2, pos) ->
          let pe1 = trans_pure_exp e1 stab in
          let pe2 = trans_pure_exp e2 stab in CP.mkLt pe1 pe2 pos
    | IP.Lte (e1, e2, pos) ->
          let pe1 = trans_pure_exp e1 stab in
          let pe2 = trans_pure_exp e2 stab in CP.mkLte pe1 pe2 pos
    | IP.SubAnn (e1, e2, pos) ->
          let pe1 = trans_pure_exp e1 stab in
          let pe2 = trans_pure_exp e2 stab in CP.SubAnn(pe1,pe2,pos)
    | IP.Gt (e1, e2, pos) ->
          let pe1 = trans_pure_exp e1 stab in
          let pe2 = trans_pure_exp e2 stab in CP.mkGt pe1 pe2 pos
    | IP.Gte (e1, e2, pos) ->
          let pe1 = trans_pure_exp e1 stab in
          let pe2 = trans_pure_exp e2 stab in CP.mkGte pe1 pe2 pos
    | IP.Eq (e1, e2, pos) ->
          let pe1 = trans_pure_exp e1 stab in
          let pe2 = trans_pure_exp e2 stab in 
		  (check_dfrac_wf pe1 pe2 pos; CP.mkEq pe1 pe2 pos)
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
          let pe = trans_pure_exp e stab in CP.BagIn ((trans_var (v,p) stab pos), pe, pos)
    | IP.BagNotIn ((v, p), e, pos) ->
          let pe = trans_pure_exp e stab in
          CP.BagNotIn ((trans_var (v,p) stab pos), pe, pos)
    | IP.BagSub (e1, e2, pos) ->
          let pe1 = trans_pure_exp e1 stab in
          let pe2 = trans_pure_exp e2 stab in CP.BagSub (pe1, pe2, pos)
    | IP.BagMax ((v1, p1), (v2, p2), pos) ->
          CP.BagMax (CP.SpecVar (C.int_type, v1, p1),CP.SpecVar (C.bag_type, v2, p2), pos)
    | IP.BagMin ((v1, p1), (v2, p2), pos) ->
          CP.BagMin (CP.SpecVar (C.int_type, v1, p1), CP.SpecVar (C.bag_type, v2, p2), pos)
    | IP.VarPerm (ct,ls,pos) ->
        let func (v,p) =
	      CP.SpecVar (UNK,v,p) (*TO CHECK: ignore type info*)
        in
        let ls1 = List.map func ls in
        (* let ls1 = List.map (fun (v,p) -> trans_var (v,p) stab pos) ls in *)
        (* let ls1 = List.map (fun v -> trans_var (v,Unprimed) stab pos) ls in *)
        CP.VarPerm (ct,ls1,pos)
    | IP.ListIn (e1, e2, pos) ->
          let pe1 = trans_pure_exp e1 stab in
          let pe2 = trans_pure_exp e2 stab in CP.ListIn (pe1, pe2, pos)
    | IP.ListNotIn (e1, e2, pos) ->
          let pe1 = trans_pure_exp e1 stab in
          let pe2 = trans_pure_exp e2 stab in CP.ListNotIn (pe1, pe2, pos)
    | IP.ListAllN (e1, e2, pos) ->
          let pe1 = trans_pure_exp e1 stab in
          let pe2 = trans_pure_exp e2 stab in CP.ListAllN (pe1, pe2, pos)
    | IP.ListPerm (e1, e2, pos) ->
          let pe1 = trans_pure_exp e1 stab in
          let pe2 = trans_pure_exp e2 stab in CP.ListPerm (pe1, pe2, pos)
    | IP.RelForm (r, args, pos) ->    
          let nv = trans_var_safe (r,Unprimed) RelT stab pos in
    	  (* Match types of arguments with relation signature *)
		  let cpargs = trans_pure_exp_list args stab in
		  CP.RelForm (nv, cpargs, pos) (* An Hoa : Translate IP.RelForm to CP.RelForm *)
  in
  match sl with
	| None -> (npf, None)
	| Some (il,lbl,el) -> let nel = trans_pure_exp_list el stab in (npf, Some (il,lbl,nel))
                                                                       
and trans_pure_exp (e0 : IP.exp) stab : CP.exp =
  Debug.no_1 "trans_pure_exp" 
  (Iprinter.string_of_formula_exp)
  (Cprinter.string_of_formula_exp) 
  (fun e -> trans_pure_exp_x e stab) e0 
      
and trans_pure_exp_x (e0 : IP.exp) stab : CP.exp =
  match e0 with
    | IP.Null pos -> CP.Null pos
	| IP.Tsconst (t,pos) -> CP.Tsconst (t,pos)
    | IP.AConst(a,pos) -> CP.AConst(a,pos)
    | IP.Var ((v, p), pos) -> 
          CP.Var ((trans_var (v,p) stab pos),pos)
    | IP.Ann_Exp (e, t) -> trans_pure_exp e stab
    | IP.IConst (c, pos) -> CP.IConst (c, pos)
    | IP.FConst (c, pos) -> CP.FConst (c, pos)
    | IP.Add (e1, e2, pos) -> CP.Add (trans_pure_exp e1 stab, trans_pure_exp e2 stab, pos)
    | IP.Subtract (e1, e2, pos) -> CP.Subtract (trans_pure_exp e1 stab, trans_pure_exp e2 stab, pos)
    | IP.Mult (e1, e2, pos) -> CP.Mult (trans_pure_exp e1 stab, trans_pure_exp e2 stab, pos)
    | IP.Div (e1, e2, pos) -> CP.Div (trans_pure_exp e1 stab, trans_pure_exp e2 stab, pos)
    | IP.Max (e1, e2, pos) -> CP.Max (trans_pure_exp e1 stab, trans_pure_exp e2 stab, pos)
    | IP.Min (e1, e2, pos) -> CP.Min (trans_pure_exp e1 stab, trans_pure_exp e2 stab, pos)
    | IP.Bag (elist, pos) -> CP.Bag (trans_pure_exp_list elist stab, pos)
    | IP.BagUnion (elist, pos) -> CP.BagUnion (trans_pure_exp_list elist stab, pos)
    | IP.BagIntersect (elist, pos) -> CP.BagIntersect (trans_pure_exp_list elist stab, pos)
    | IP.BagDiff (e1, e2, pos) -> CP.BagDiff (trans_pure_exp e1 stab, trans_pure_exp e2 stab, pos)
    | IP.List (elist, pos) -> CP.List (trans_pure_exp_list elist stab, pos)
    | IP.ListAppend (elist, pos) -> CP.ListAppend (trans_pure_exp_list elist stab, pos)
    | IP.ListCons (e1, e2, pos) -> CP.ListCons (trans_pure_exp e1 stab, trans_pure_exp e2 stab, pos)
    | IP.ListHead (e, pos) -> CP.ListHead (trans_pure_exp e stab, pos)
    | IP.ListTail (e, pos) -> CP.ListTail (trans_pure_exp e stab, pos)
    | IP.ListLength (e, pos) -> CP.ListLength (trans_pure_exp e stab, pos)
    | IP.ListReverse (e, pos) -> CP.ListReverse (trans_pure_exp e stab, pos)
    | IP.Func (id, es, pos) ->
		  let es = List.map (fun e -> trans_pure_exp e stab) es in
		  CP.Func (CP.SpecVar (RelT, id, Unprimed), es, pos)
    | IP.ArrayAt ((a, p), ind, pos) ->
		  let cpind = List.map (fun i -> trans_pure_exp i stab) ind in
		  let dim = List.length ind in (* currently only support int type array *)
		  CP.ArrayAt (CP.SpecVar ((Array (C.int_type, dim)), a, p), cpind, pos)

and trans_pure_exp_list (elist : IP.exp list) stab : CP.exp list =
  match elist with
    | [] -> []
    | e :: rest -> (trans_pure_exp e stab) :: (trans_pure_exp_list rest stab)


and dim_unify d1 d2 = if (d1 = d2) then Some d1 else None

and must_unify (k1 : typ) (k2 : typ) stab pos : typ  =
  let pr = string_of_typ in
  Debug.no_2 "must_unify" pr pr pr (fun _ _ -> must_unify_x k1 k2 stab pos) k1 k2

and must_unify_x (k1 : typ) (k2 : typ) stab pos : typ  =
  let k = unify_type k1 k2 stab in
  match k with
    | Some r -> r
    | None -> report_error pos ("UNIFICATION ERROR : at location "^(string_of_full_loc pos)
      ^" types "^(string_of_typ (get_type_entire stab k1))
      ^" and "^(string_of_typ (get_type_entire stab k2))^" are inconsistent")

and must_unify_expect (k1 : typ) (k2 : typ) stab pos : typ  =
  let pr = string_of_typ in
  Debug.no_2 "must_unify_expect" pr pr pr (fun _ _ -> must_unify_expect_x k1 k2 stab pos) k1 k2

and must_unify_expect_x (k1 : typ) (k2 : typ) stab pos : typ  =
  let k = unify_expect k1 k2 stab in
  match k with
    | Some r -> r
    | None -> report_error pos ("TYPE ERROR : 1.1 Found "
      ^(string_of_typ (get_type_entire stab k1))
      ^" but expecting "^(string_of_typ (get_type_entire  stab k2)))

and unify_type (k1 : spec_var_kind) (k2 : spec_var_kind) stab :
      spec_var_kind option =
  let pr = string_of_spec_var_kind in
  let pr2 = pr_option pr in
  Debug.no_2 "unify_type" pr pr pr2 (fun _ _ -> unify_type_x k1 k2 stab) k1 k2

and unify_type_x (k1 : spec_var_kind) (k2 : spec_var_kind) stab : spec_var_kind option =
  unify_type_modify true k1 k2 stab

and unify_type_modify (modify_flag:bool) (k1 : spec_var_kind) (k2 : spec_var_kind) stab : spec_var_kind option =
  let rec repl_stab i k = repl_tvar_in unify modify_flag stab i k 
  and unify k1 k2 =
    match k1,k2 with
      | UNK, _ -> Some k2
      | _, UNK -> Some k1
      | Int, NUM -> Some Int (* HACK here : give refined type *)
      | Float, NUM -> Some Float (* give refined type *)
      | NUM, Int -> Some Int
      | NUM, Float -> Some Float
      | Int, Float -> Some Float (*LDK: support floating point*)
      | Float, Int -> Some Float (*LDK*)
	  | Tree_sh, Tree_sh -> Some Tree_sh
      | t1, t2  -> 
            if sub_type t1 t2 then Some k2  (* found t1, but expecting t2 *)
            else if sub_type t2 t1 then Some k1
            else 
              begin
                match t1,t2 with
                    (* | TVar i1,TVar i2 -> ? *)
                  | TVar i1,_ -> repl_stab i1 k2
                  | _,TVar i2 -> repl_stab i2 k1
                  | BagT x1,BagT x2 -> (match (unify x1 x2) with
                      | Some t -> Some (BagT t)
                      | None -> None)
                  | List x1,List x2 -> (match (unify x1 x2) with
                      | Some t -> Some (List t)
                      | None -> None)
                  | Array (x1,d1),Array (x2,d2) -> 
                        (match (dim_unify d1 d2), (unify x1 x2) with
                          | Some d, Some t  -> Some (Array (t,d))
                          | _,_ -> None)
                  | _,_ -> None
              end
  in unify k1 k2

(* k2 is expected type *)
and unify_expect (k1 : spec_var_kind) (k2 : spec_var_kind) stab : spec_var_kind option =
  unify_expect_modify true k1 k2 stab

and must_unify_expect_test k1 k2 pos = 
  let k = unify_expect_modify false k1 k2 !type_table  in
  match k with
    | Some r -> r
    | None -> report_error pos ("TYPE ERROR : 1.2 Found "
      ^(string_of_typ (k1))
      ^" but expecting "^(string_of_typ (k2)))

and must_unify_expect_test_2 k1 k2 k3 pos = 
  let k = unify_expect_modify false k1 k2 !type_table  in
  match k with
    | Some r -> r
    | None -> must_unify_expect_test k1 k3 pos 
	   	  
and subtype_expect_test _ _ = true

and unify_expect_modify (modify_flag:bool) (k1 : spec_var_kind) (k2 : spec_var_kind) stab : spec_var_kind option =
  let pr = string_of_typ in
  Debug.no_2 "unify_expect_modify" pr pr (pr_option pr) (fun _ _ -> unify_expect_modify_x modify_flag k1 k2 stab) k1 k2

(* k2 is expected type *)
and unify_expect_modify_x (modify_flag:bool) (k1 : spec_var_kind) (k2 : spec_var_kind) stab : spec_var_kind option =
  let bal_unify k1 k2 = unify_type_modify modify_flag k1 k2 stab in
  let repl_stab i k = repl_tvar_in bal_unify modify_flag stab i k in
  let rec unify k1 k2 =
    match k1,k2 with
      | UNK, _ -> Some k2
      | _, UNK -> Some k1
      | Int, NUM -> Some Int (* give refined type *)
      | Float, NUM -> Some Float (* give refined type *)
      | Int , Float -> Some Float (*LDK*)
      | Float , Int -> Some Float (*LDK*)
      | t1, t2  -> 
            if sub_type t1 t2 then Some k2  (* found t1, but expecting t2 *)
              (* else if sub_type t2 t1 then Some k1 *)
            else 
              begin
                match t1,t2 with
                    (* | TVar i1,TVar i2 -> ? *)
                  | TVar i1,_ -> repl_stab i1 k2
                  | _,TVar i2 -> repl_stab i2 k1
                  | BagT x1,BagT x2 -> (match (unify x1 x2) with
                      | Some t -> Some (BagT t)
                      | None -> None)
                  | List x1,List x2 -> (match (unify x1 x2) with
                      | Some t -> Some (List t)
                      | None -> None)
                  | Array (x1,d1),Array (x2,d2) -> 
                        (match (dim_unify d1 d2), (unify x1 x2) with
                          | Some d, Some t  -> Some (Array (t,d))
                          | _,_ -> None)
                  | _,_ -> None
              end
  in unify k1 k2

(* val fold : ('a -> 'b -> 'c -> 'c) -> ('a, 'b) t -> 'c -> 'c *)

and repl_tvar_in unify flag stab i k =
  Debug.no_eff_4 "repl_tvar_in" [false;false;false;true]
      string_of_bool string_of_int string_of_typ string_of_stab (pr_option string_of_typ)
      (fun _ _ _ _ -> repl_tvar_in_x unify flag stab i k) flag i k stab 

(* TODO : should TVar j be updated to point to i *)
and repl_tvar_in_x unify flag stab i k =
  let test x = let i2 = x.id in 
  match k with 
    | TVar j -> i2=i || i2=j 
    | _ -> i2=i in
  let new_k = match k with 
    | TVar _ -> UNK
    | _ -> k in
  let res_t = Hashtbl.fold (fun v en et -> 
      match et with
        | None -> et
        | Some t1 -> begin
            if not(test en) then et
            else match en.sv_info_kind with
              | TVar _ -> et
              | t -> (unify t t1)
          end) stab (Some new_k) in
  match res_t with 
    | None -> None
    | Some ut ->
          let ut = if ut==UNK then k else ut in
          (* TVar i --> ut *)
          if flag then 
            begin
              Hashtbl.iter (fun v en -> 
                  if test en then en.sv_info_kind <- ut
                  else en.sv_info_kind <- subs_tvar_in_typ en.sv_info_kind i ut
              ) stab
            end
          ; (Some ut) 

and unify_var_kind_x (k1 : spec_var_kind) (k2 : spec_var_kind) :
      spec_var_kind option =
  unify_type k1 k2 !type_table
   
	  
and unify_var_kind (k1 : spec_var_kind) (k2 : spec_var_kind) =
  let pr = string_of_spec_var_kind in
  let pr2 x = match x with 
    | None -> "None"
    | Some v -> "Some "^(pr v) in
  Debug.no_2 "unify_var_kind" pr pr pr2 unify_var_kind_x k1 k2

and get_var_kind (var : ident) (stab : spec_var_table) =
  try let r = H.find stab var in r.sv_info_kind with | Not_found -> UNK

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


and gather_type_info_var (var : ident) stab (ex_t : typ) pos : typ =
  let pr = string_of_typ in
  Debug.no_eff_3 "gather_type_info_var" [false;true] (fun x -> ("ident: "^x)) string_of_stab pr pr 
      (fun _ _ _ -> gather_type_info_var_x var stab ex_t pos) var stab ex_t


and get_spec_var_ident stab (var : ident) p =
      try
        let k = H.find stab var in
               CP.SpecVar(k.sv_info_kind,var,p)
      with 
        | Not_found -> CP.SpecVar(UNK,var,p)
 

and gather_type_info_var_x (var : ident) stab (ex_t : spec_var_kind) pos : spec_var_kind =
  begin
    if (is_dont_care_var var) 
    then UNK (* for vars such as _ and # *)
    else
      try
        let k = H.find stab var in
        (* if ex_t==UNK then k.sv_info_kind *)
        (* else *)
        (let tmp = must_unify(* _expect *)  k.sv_info_kind ex_t stab pos in
        (k.sv_info_kind <- tmp); tmp)
      with 
        | Not_found -> 
              (* if ex_t==UNK then UNK *)
              (* else *)
              let vk = fresh_proc_var_kind stab ex_t in
              (H.add stab var vk; vk.sv_info_kind
              )
        | ex -> report_error pos ("gather_type_info_var : unexpected exception"^(Printexc.to_string ex))
  end

and fresh_proc_var_kind stab et = 
  let r = match et with
    | TVar i -> { sv_info_kind = et; id = i}
          (* | NUM -> fresh_tvar_rec stab *)
    | _ -> { sv_info_kind = et; id = fresh_int ()} in
  r

(* should create entry in stab *)
and fresh_tvar_rec stab = 
  let i = fresh_int() in
  let key = "TVar__"^(string_of_int i) in
  let t2 = TVar i in
  let en={ sv_info_kind = t2; id = i} in
  (Hashtbl.add stab key en); en

and fresh_tvar stab = 
  let en = fresh_tvar_rec stab in
  en.sv_info_kind

and update_tvar stab i t = 
  let key = "TVar__"^(string_of_int i) in
  try 
    let en = Hashtbl.find stab key in
    en.sv_info_kind <- t
  with _ -> report_error no_pos ("Type Var "^key^" cannot be found in stab")

and get_type_entire stab t =
  let rec helper t = match t with
    | TVar j -> get_type stab j
    | BagT et -> BagT (helper et)
    | List et -> List (helper et)
    | Array (et,d) -> Array (helper et,d)
    | _ -> t
  in helper t
         
and get_type stab i = 
  let key = "TVar__"^(string_of_int i) in
  ( try 
    let en = Hashtbl.find stab key in
    en.sv_info_kind 
  with _ -> report_error no_pos ("UNEXPECTED : Type Var "^key^" cannot be found in stab"))

and gather_type_info_exp a0 stab et =
  Debug.no_eff_3 "gather_type_info_exp" [false;true] 
      Iprinter.string_of_formula_exp string_of_stab string_of_typ
      string_of_typ gather_type_info_exp_x a0 stab et

and gather_type_info_exp_x a0 stab et =
  match a0 with
    | IP.Null pos -> 
          let t = null_type in
          must_unify_expect t et stab pos
    | IP.Ann_Exp (e,t) -> 
          (* TODO WN : check if t<:et *)
          gather_type_info_exp_x e stab t
    | IP.Var ((sv, sp), pos) -> 
          let t = gather_type_info_var sv stab et pos
          in t
    | IP.Tsconst (_,pos) ->
		  let t = Tree_sh in
          let _ = must_unify_expect t et stab pos in
          t
    | IP.AConst (_,pos) -> 
          let t = I.ann_type in
          let _ = must_unify_expect t et stab pos in
          t
    | IP.IConst (_,pos) -> 
          let t = I.int_type in
          let _ = must_unify_expect t et stab pos in
          t
    | IP.FConst (_,pos) -> 
          let t = I.float_type in
          let _ = must_unify_expect t et stab pos in
          t
    | IP.Add (a1, a2, pos) -> 
		  let _ = must_unify_expect_test_2 et NUM Tree_sh pos in (* UNK, Int, Float, NUm, Tvar *)
          let new_et = fresh_tvar stab in
	      let t1 = gather_type_info_exp_x a1 stab new_et in (* tvar, Int, Float *)
	      let t2 = gather_type_info_exp_x a2 stab new_et in
          let t1 = must_unify_expect t1 et stab pos in
          let t2 = must_unify_expect t2 t1 stab pos in
          t2
	| IP.Subtract (a1, a2, pos) | IP.Max (a1, a2, pos) | IP.Min (a1, a2, pos) 
    | IP.Mult (a1, a2, pos) -> (* Num t: t -> t -> t *)
          let _ = must_unify_expect_test et NUM pos in (* UNK, Int, Float, NUm, Tvar *)
          let new_et = fresh_tvar stab in
	      let t1 = gather_type_info_exp_x a1 stab new_et in (* tvar, Int, Float *)
	      let t2 = gather_type_info_exp_x a2 stab new_et in
          let t1 = must_unify_expect t1 et stab pos in
          let t2 = must_unify_expect t2 t1 stab pos in
          t2
    | IP.Div (a1, a2, pos) -> (* Num t: t -> t -> t *)
          let _ = must_unify_expect_test et NUM pos in (* UNK, Int, Float, NUm, Tvar *)
          let new_et = fresh_tvar stab in
	      let t1 = gather_type_info_exp_x a1 stab new_et in (* tvar, Int, Float *)
	      let t2 = gather_type_info_exp_x a2 stab new_et in
          let t1 = must_unify_expect t1 et stab pos in
          let t2 = must_unify_expect t2 t1 stab pos in
          t2
    | IP.BagDiff (a1,a2,pos) ->
          let el_t = fresh_tvar stab in
          let new_et = must_unify_expect_test (BagT el_t) et pos in 
	      let t1 = gather_type_info_exp_x a1 stab new_et in 
	      let t2 = gather_type_info_exp_x a2 stab new_et in
          must_unify t1 t2 stab pos  
    | IP.BagIntersect (es,pos) | IP.BagUnion (es,pos) ->
          let el_t = fresh_tvar stab in
          let new_et = must_unify_expect_test (BagT el_t) et pos in 
	      let ts = List.map (fun e -> gather_type_info_exp_x e stab new_et) es in
          List.fold_left (fun e a -> must_unify a e stab pos) new_et ts
    | IP.Bag (es,pos) ->
          let el_t = fresh_tvar stab in
          let t = List.fold_left (fun e a -> gather_type_info_exp_x a stab e) el_t es in
          BagT t
    | IP.Func (id, es, pos) -> 
          let t = I.int_type in
          let _ = must_unify_expect t et stab pos in
          t
    | IP.ArrayAt ((a,p),idx,pos) -> (* t[] -> int -> t *)
          (* An Hoa : Assert that the variable (a,p) must be of type expected_type Array *)
		  (* and hence, accessing the element at position i, we get the value of expected_type *)
		  (* Furthermore, the expression of the index must be of type integer. *)
		  let dim = List.length idx in
          let new_et = Array (et, dim) in
          let lt = gather_type_info_var a stab new_et pos in
          let _ = List.map (fun i -> gather_type_info_exp_x i stab Int) idx in
          (match lt with
            | Array (r,_) -> r
            | _ ->  failwith ("gather_type_info_exp: expecting type Array of dimension " ^ (string_of_int dim) ^ " but given " ^ (string_of_typ lt)))
		      (* let a_exp_type = match et with *)
		      (*   | UNK -> UNK *)
		      (*   | t -> Array (t, None) *)
		      (* in *)
		      (* collect_type_info_var a stab a_exp_type pos; *)
		      (* collect_type_info_arith i stab (C.int_type) *)
    | IP.ListTail (a,pos)  | IP.ListReverse (a,pos) -> (* List t -> List t  *)
          let fv = fresh_tvar stab in
          let lt = List fv in
          let new_et = must_unify lt et stab pos in
          let lt = gather_type_info_exp_x a stab new_et in
          lt
    | IP.ListAppend (es,pos) -> (* [List t] -> List t *)
          let fv = fresh_tvar stab in
          let lt = List fv in
          let new_et = must_unify lt et stab pos in
          let rs = List.fold_left (fun e l -> gather_type_info_exp_x l stab e) new_et es  in
          rs
    | IP.ListHead (a, pos) ->  (* List t -> t*)
          let fv = fresh_tvar stab in
          let new_et = List fv in
          let lt = gather_type_info_exp_x a stab new_et in
          let rs = must_unify lt (List et) stab pos in
          (match rs with
            | List r -> r
            | _ ->  failwith ("gather_type_info_exp: expecting List type but obtained "^(string_of_typ lt)))
    | IP.ListCons (e,es,pos) -> (* t -> List t -> List t *)
          let fv = fresh_tvar stab in
          let e1 = gather_type_info_exp_x e stab fv in
          let lt = List e1 in
          let new_et = must_unify lt et stab pos in
          let lt = gather_type_info_exp_x es stab new_et in
          lt
    | IP.List (es,pos) -> (* a,..,a -> List a *)
          let fv = fresh_tvar stab in
          let r = List.fold_left (fun e l -> gather_type_info_exp_x l stab e) fv es  in
          let lt = List r in
          let r = must_unify lt et stab pos in
          r
    | IP.ListLength (a, pos) -> (* List t -> Int *)
          let fv = fresh_tvar stab in
          let new_et = List fv in
          let r = must_unify Int et stab pos in
          let _ = gather_type_info_exp_x a stab new_et in
          r
              
and gather_type_info_pure_x prog (p0 : IP.formula) (stab : spec_var_table) : unit =
  match p0 with
    | IP.BForm (b,_) -> gather_type_info_b_formula prog b stab
    | IP.And (p1, p2, pos) | IP.Or (p1, p2, _, pos) ->
          (gather_type_info_pure prog p1 stab; gather_type_info_pure prog p2 stab)
	| IP.AndList b -> List.iter (fun (_,c)-> gather_type_info_pure prog c stab) b
    | IP.Not (p1, _, pos) -> gather_type_info_pure_x prog p1 stab 
    | IP.Forall ((qv, qp), qf, _,pos) | IP.Exists ((qv, qp), qf, _,pos) ->
	      if (H.mem stab qv) then
            if !check_shallow_var
	        then
              Err.report_error
                  {
                      Err.error_loc = pos;
                      Err.error_text = qv ^ " shadows outer name";
                  }
            else gather_type_info_pure_x prog qf stab
	      else 
            begin
              let new_et = fresh_tvar stab in
              let vk = fresh_proc_var_kind stab new_et in
              H.add stab qv vk; gather_type_info_pure prog qf stab
            end

and gather_type_info_pure prog (p0 : IP.formula) (stab : spec_var_table) : unit =
  Debug.no_eff_2 "gather_type_info_pure" [false;true]  (Iprinter.string_of_pure_formula) string_of_stab (fun _ -> "()")
      (gather_type_info_pure_x prog) p0 stab


(* An Hoa : add argument prog *)
(* and collect_type_info_pure prog (p0 : IP.formula) (stab : spec_var_table) : unit = *)
(*   Debug.no_eff_2 "collect_type_info_pure" [false;true]  *)
(*       (Iprinter.string_of_pure_formula) string_of_stab (fun _ -> "()") *)
(*       (collect_type_info_pure_x prog) p0 stab *)

(* and collect_type_info_pure_x prog (p0 : IP.formula) (stab : spec_var_table) : unit = *)
(*   match p0 with *)
(*     | IP.BForm (b,_) -> collect_type_info_b_formula prog b stab *)
(*     | IP.And (p1, p2, pos) | IP.Or (p1, p2, _, pos) -> *)
(*           (collect_type_info_pure_x prog p1 stab; collect_type_info_pure_x prog p2 stab) *)
(*     | IP.Not (p1, _, pos) -> collect_type_info_pure_x prog p1 stab  *)
(*     | IP.Forall ((qv, qp), qf, _,pos) | IP.Exists ((qv, qp), qf, _,pos) -> *)
(* 	      if (H.mem stab qv) && !check_shallow_var *)
(* 	      then *)
(*             Err.report_error *)
(*                 { *)
(*                     Err.error_loc = pos; *)
(*                     Err.error_text = qv ^ " shadows outer name"; *)
(*                 } *)
(* 	      else collect_type_info_pure prog qf stab *)


(* and collect_type_info_b_formula prog b0 stab = *)
(*   Debug.no_eff_2 "collect_type_info_b_formula" [false;true] (Iprinter.string_of_b_formula) string_of_stab (fun _ -> "()") *)
(*       (collect_type_info_b_formula_x prog) b0 stab *)

(* and collect_type_info_b_formula_x prog b0 stab = *)
(*   let (pf,_) = b0 in *)
(*   match pf with *)
(*     | IP.BConst _ -> () *)
(*     | IP.BVar ((bv, bp), pos) -> *)
(* 	      collect_type_info_var bv stab (C.bool_type) pos *)
(*     | IP.Lt (a1, a2, pos) | IP.Lte (a1, a2, pos) | IP.Gt (a1, a2, pos) | *)
(* 	          IP.Gte (a1, a2, pos) -> *)
(*           let t1 = guess_type_of_exp_arith a1 stab in *)
(*           let t2 = guess_type_of_exp_arith a2 stab in *)
(*           begin *)
(*             match t1, t2 with *)
(*               | UNK, _ -> *)
(* 		            (collect_type_info_arith a1 stab t2; collect_type_info_arith a2 stab t2) *)
(*               | _, UNK -> *)
(* 		            (collect_type_info_arith a1 stab t1; collect_type_info_arith a2 stab t1) *)
(*               | _,_ -> (match unify_type t1 t2 stab with *)
(*                   | Some t -> (collect_type_info_arith a1 stab t; collect_type_info_arith a2 stab t) *)
(*                   | None -> report_error pos "Unable to unify arithmetic types") *)
(*                     (\* | _ -> *\) *)
(* 		            (\*       (\\* TODO: check for type consistency - equality of t1 & t2 not captured *\\) *\) *)
(* 		            (\*       (collect_type_info_arith a1 stab t1; collect_type_info_arith a2 stab t2) *\) *)
(*           end *)
(*     | IP.EqMin (a1, a2, a3, pos) | IP.EqMax (a1, a2, a3, pos) -> *)
(* 	      let t1 = guess_type_of_exp_arith a1 stab in *)
(* 	      let t2 = guess_type_of_exp_arith a2 stab in *)
(* 	      let t3 = guess_type_of_exp_arith a3 stab in *)
(* 	      let helper typ =  *)
(*             (collect_type_info_arith a1 stab typ; *)
(*             collect_type_info_arith a2 stab typ; *)
(*             collect_type_info_arith a3 stab typ) *)
(* 	      in begin *)
(*             (\* TODO : what about two knowns and one unknown ? *\) *)
(*             if (t1==UNK) then *)
(*               if (t2==UNK) then *)
(*                 helper t3 *)
(*               else helper t2 *)
(*             else helper t1 *)
(*               (\* match t1, t2, t3 with *\) *)
(*               (\*   | _, UNK, UNK -> helper t1 *\) *)
(*               (\*   | , Known _, Unknown -> helper t2 *\) *)
(*               (\*   | Unknown, Unknown, Known _ -> helper t3 *\) *)
(*               (\*   | _ -> helper Unknown *\) *)
(* 	      end *)
(*     | IP.BagIn ((v, p), e, pos) -> *)
(* 	      (collect_type_info_var v stab (C.int_type) pos; *)
(* 	      collect_type_info_bag e stab) *)
(*     | IP.BagNotIn ((v, p), e, pos) -> *)
(* 	      (collect_type_info_var v stab (C.int_type) pos; *)
(* 	      collect_type_info_bag e stab) *)
(*     | IP.BagSub (e1, e2, pos) -> *)
(* 	      (collect_type_info_bag e1 stab; collect_type_info_bag e2 stab) *)
(*     | IP.BagMax ((v1, p1), (v2, p2), pos) -> *)
(* 	      (collect_type_info_var v1 stab (C.int_type) pos; *)
(* 	      collect_type_info_var v2 stab (C.bag_type) pos) *)
(*     | IP.BagMin ((v1, p1), (v2, p2), pos) -> *)
(* 	      (collect_type_info_var v1 stab (C.int_type) pos; *)
(* 	      collect_type_info_var v2 stab (C.bag_type) pos) *)
(*     | IP.ListIn (e1, e2, pos) -> *)
(*           (collect_type_info_arith e1 stab UNK; *)
(*           collect_type_info_list e2 stab) *)
(*     | IP.ListNotIn (e1, e2, pos) -> *)
(*           (collect_type_info_arith e1 stab UNK ; *)
(*           collect_type_info_list e2 stab) *)
(*     | IP.ListAllN (e1, e2, pos) -> *)
(*           (collect_type_info_arith e1 stab UNK; *)
(*           collect_type_info_list e2 stab) *)
(*     | IP.ListPerm (e1, e2, pos) -> *)
(*           (collect_type_info_list e1 stab; *)
(*           collect_type_info_list e2 stab) *)
(* 		      (\* An Hoa : TODO IMPLEMENT IMMEDIATELY *\)			 *)
(* 	| IP.RelForm (r, args, pos) -> *)
(* 		  (try  *)
(* 		  	(\* let _ = print_endline ("collect_type_info_b_formula_x : fail with " ^ r) in *)
(* 		  	let _ = print_endline (String.concat " ; " (List.map Iprinter.string_of_formula_exp args)) in *\) *)
(* 			let rdef = I.look_up_rel_def_raw prog.I.prog_rel_decls r in *)
(* 			let args_ctypes = List.map (fun (t,n) -> trans_type prog t pos) rdef.I.rel_typed_vars in *)
(* 			let args_exp_types = List.map (fun t -> (t)) args_ctypes in *)
(* 			let _ = List.map2 (fun x y -> collect_type_info_arith x stab y) args args_exp_types in () *)
(* 		  with *)
(* 			| Not_found -> ()) *)
(* 		      (\* An Hoa *\) *)
(*     | IP.Eq (a1, a2, pos) | IP.Neq (a1, a2, pos) -> *)
(* 	      let _ =  *)
(* 	        if (IP.is_var a1) && (IP.is_var a2) *)
(* 	        then *)
(*               (let va1 = IP.name_of_var a1 in *)
(*               let va2 = IP.name_of_var a2 in *)
(*               let k1 = get_var_kind va1 stab in *)
(*               let k2 = get_var_kind va2 stab in *)
(*               let r = unify_var_kind k1 k2 in *)
(* 	          (\*let _ = print_string ("\n equality: "^va1^" "^va2^" "^(string_of_var_kind k1)^"  "^(string_of_var_kind k2)^" "^ *)
(* 		        (match r with | None -> "" |Some r -> (string_of_var_kind r))^"\n") in*\) *)
(*               match r with *)
(* 		        | Some k -> *)
(* 		              set_var_kind2 va1 va2 k stab  *)
(* 		                  (\*let r = set_var_kind va1 k stab in H.replace stab va2 r*\) *)
(* 		        | None -> *)
(* 		              (print_stab stab; *)
(*                       Err.report_error *)
(* 			              { *)
(* 			                  Err.error_loc = pos; *)
(* 			                  Err.error_text = *)
(* 			                      "type-mismatch in equation (1): " ^ *)
(*                                       (Iprinter.string_of_b_formula b0); *)
(* 			              })) *)
(* 	        else *)
(*               if (IP.is_var a1) || (IP.is_var a2) *)
(*               then *)
(*                 (let (a1', a2') = if IP.is_var a1 then (a1, a2) else (a2, a1) in *)
(*                 let va1' = IP.name_of_var a1' in *)
(*                 let k1 = get_var_kind va1' stab in *)
(*                 let (k2, _) = *)
(*                   if IP.is_null a2' *)
(*                   then *)
(*                     (((Named "")), *)
(*                     (collect_type_info_pointer a1' ((Named "")) stab)) *)
(*                   else *)
(*                     if IP.is_bag a2' *)
(*                     then ((C.bag_type), (collect_type_info_bag a2' stab)) *)
(* 			        else if IP.is_list a2' *)
(*                     then ((C.list_type), (collect_type_info_list a2' stab)) *)
(*                     else   begin *)
(*                       let typ = guess_type_of_exp_arith a2' stab in *)
(*                       let a2_typ = if typ = UNK then k1 else typ in *)
(* 			          (a2_typ, collect_type_info_arith a2' stab a2_typ) *)
(*                     end *)
(*                 in *)
(*                 let r = unify_var_kind k1 k2 *)
(*                 in *)
(*                 match r with *)
(*                   | Some k -> ignore (set_var_kind va1' k stab) *)
(*                   | None -> *)
(*                         Err.report_error *)
(*                             { *)
(*                                 Err.error_loc = pos; *)
(*                                 Err.error_text = *)
(*                                     "type-mismatch in equation (2): " ^ *)
(*                                         (Iprinter.string_of_b_formula b0); *)
(*                             }) *)
(*               else *)
(*                 if (IP.is_null a1) && (IP.is_null a2) *)
(*                 then () *)
(*                 else *)
(*                   if (not (IP.is_null a1)) && (not (IP.is_null a2)) *)
(*                   then *)
(*                     if (IP.is_bag a1) && (IP.is_bag a2) *)
(*                     then *)
(*                       (collect_type_info_bag a1 stab; *)
(*                       collect_type_info_bag a2 stab) *)
(*                     else if (IP.is_list a1) && (IP.is_list a2) *)
(*                     then *)
(*                       (collect_type_info_list a1 stab; *)
(*                       collect_type_info_list a2 stab) *)
(*                     else *)
(*                       (collect_type_info_arith a1 stab UNK; *)
(*                       collect_type_info_arith a2 stab UNK) *)
(*                   else *)
(* 		            Err.report_error *)
(*                         { *)
(*                             Err.error_loc = pos; *)
(*                             Err.error_text = *)
(* 			                    "type-mismatch in equation (3): " ^ *)
(* 			                        (Iprinter.string_of_b_formula b0); *)
(*                         } in *)
(* 	      (\*let _ = print_string ("\n new stab: "^(string_of_stab stab)^"\n") in *\)() *)
	  
and gather_type_info_b_formula prog b0 stab =
  Debug.no_eff_2 "gather_type_info_b_formula" [false;true] 
      Iprinter.string_of_b_formula string_of_stab (fun _ -> "()")
      (fun _ _ -> gather_type_info_b_formula_x prog b0 stab) b0 stab 
      
and gather_type_info_b_formula_x prog b0 stab =
  let (pf,_) = b0 in
  match pf with
    | IP.BConst _ -> ()
    | IP.BVar ((bv, bp), pos) ->
	      let _ = gather_type_info_var bv stab (C.bool_type) pos in
          ()
    | IP.SubAnn(a1,a2,pos) ->
	      let _ = gather_type_info_exp a1 stab (Cpure.ann_type) in
	      let _ = gather_type_info_exp a2 stab (Cpure.ann_type) in
          ()
    | IP.LexVar(t_ann, ls1, ls2, pos) ->
	      let _ = List.map (fun e -> gather_type_info_exp e stab (Int)) ls1 in
	      let _ = List.map (fun e -> gather_type_info_exp e stab (Int)) ls2 in
        ()
    | IP.Lt (a1, a2, pos) | IP.Lte (a1, a2, pos) | IP.Gt (a1, a2, pos) |
	          IP.Gte (a1, a2, pos) ->
          let new_et = fresh_tvar stab in
	      let t1 = gather_type_info_exp a1 stab new_et in (* tvar, Int, Float *)
	      let t2 = gather_type_info_exp a2 stab new_et in
          let t1 = must_unify_expect t1 NUM stab pos in
          let t2 = must_unify_expect t2 NUM stab pos in
          let _ = must_unify t1 t2 stab pos  in (* UNK, Int, Float, TVar *) 
          ()
    | IP.EqMin (a1, a2, a3, pos) | IP.EqMax (a1, a2, a3, pos) ->
          let new_et = fresh_tvar stab in
	      let t1 = gather_type_info_exp a1 stab new_et in (* tvar, Int, Float *)
	      let t2 = gather_type_info_exp a2 stab new_et in
	      let t3 = gather_type_info_exp a3 stab new_et in (* tvar, Int, Float *)
          let t1 = must_unify_expect t1 NUM stab pos in
          let t2 = must_unify_expect t2 NUM stab pos in
          let t3 = must_unify_expect t3 NUM stab pos in
          let t = must_unify t1 t2 stab pos  in (* UNK, Int, Float, TVar *) 
          let _ = must_unify t t3 stab pos  in (* UNK, Int, Float, TVar *) 
          ()
    | IP.BagIn ((v, p), e, pos) | IP.BagNotIn ((v, p), e, pos) ->  (* v in e *)
          let new_et = fresh_tvar stab in
          let t1 = gather_type_info_exp e stab (BagT new_et) in
          let t2 = gather_type_info_var v stab new_et pos in
          let _ = must_unify t1 (BagT t2) stab pos in
          ()
    | IP.BagSub (e1, e2, pos) ->
          let new_et = fresh_tvar stab in
          let t1 = gather_type_info_exp e1 stab (BagT new_et) in
          let t2 = gather_type_info_exp e2 stab (BagT new_et) in
          let _ = must_unify t1 t2 stab pos in
          ()
    | IP.Eq (a1, a2, pos) | IP.Neq (a1, a2, pos) ->
          let new_et = fresh_tvar stab in
	      let t1 = gather_type_info_exp a1 stab new_et in (* tvar, Int, Float *)
	      let t2 = gather_type_info_exp a2 stab new_et in
          let _ = must_unify t1 t2 stab pos  in (* UNK, Int, Float, TVar *)
          ()
    | IP.BagMax ((v1, p1), (v2, p2), pos) 
    | IP.BagMin ((v1, p1), (v2, p2), pos) -> (* V1=BagMin(V2) *)
          let et = fresh_tvar stab in
	      let t1 = gather_type_info_var v1 stab et pos in
          let t = must_unify t1 NUM stab pos  in
	      let _ = gather_type_info_var v2 stab (BagT t) pos in
          ()
    | IP.VarPerm _ -> () (*TO CHECK: no type info*)
    | IP.ListIn (e1, e2, pos) | IP.ListNotIn (e1, e2, pos)  | IP.ListAllN (e1, e2, pos) ->
          let new_et = fresh_tvar stab in
          let t1 = gather_type_info_exp e2 stab (List new_et) in
          let t2 = gather_type_info_exp e1 stab new_et in
          let _ = must_unify t1 (List t2) stab pos in
          ()
    | IP.ListPerm (e1, e2, pos) ->
          let el_t = fresh_tvar stab in
          let new_et = List el_t in
	      let t1 = gather_type_info_exp_x e1 stab new_et in 
	      let t2 = gather_type_info_exp_x e2 stab new_et in
          let _ = must_unify t1 t2 stab pos in
          ()
	| IP.RelForm (r, args, pos) ->
 		  (try
		    let rdef = I.look_up_rel_def_raw prog.I.prog_rel_decls r in
		    let args_ctypes = List.map (fun (t,n) -> trans_type prog t pos) rdef.I.rel_typed_vars in
		    let args_exp_types = List.map (fun t -> (t)) args_ctypes in
            let _ = gather_type_info_var r stab RelT in
		    let _ = List.map2 (fun x y -> gather_type_info_exp x stab y) args args_exp_types in ()
		  with
		    | Not_found ->    failwith ("gather_type_info_b_formula: relation "^r^" cannot be found")
            | _ -> print_endline ("gather_type_info_b_formula: relation " ^ r)
          )

    

(* An Hoa *)

and guess_type_of_exp_arith a0 stab =
  match a0 with
    | IP.Null _ -> UNK
    | IP.Var ((sv, sp), pos) ->
	      begin
            try
              let info = Hashtbl.find stab sv in
              info.sv_info_kind
            with Not_found -> UNK
	      end
    | IP.Add (e1, e2, pos) | IP.Subtract (e1, e2, pos) | IP.Mult (e1, e2, pos)
    | IP.Max (e1, e2, pos) | IP.Min (e1, e2, pos) | IP.Div (e1, e2, pos) ->
	      let t1 = guess_type_of_exp_arith e1 stab in
	      let t2 = guess_type_of_exp_arith e2 stab in
	      begin
            match t1, t2 with
              | _, UNK -> t1
              | UNK, _ -> t2
              | Float, Float -> t1
              | Int, Int -> t1
              | Int, Float | Float, Int  -> 
		            Err.report_error
		                {
                            Err.error_loc = pos;
                            Err.error_text = "int<>float: type-mismatch in expression: " ^ (Iprinter.string_of_formula_exp a0);
		                }
              | _ -> UNK
	      end
	          (* | IP.Div _ -> Known (Float) *)
    | IP.IConst _ -> Int
    | IP.FConst _ -> Float
    | IP.Ann_Exp (_,t) -> t
    | _ -> UNK

(* and collect_type_info_arith a0 stab expected_type = *)
(*   match a0 with *)
(*     | IP.Null pos -> *)
(* 	      Err.report_error *)
(*               { *)
(*                   Err.error_loc = pos; *)
(*                   Err.error_text = "null is not allowed in arithmetic term"; *)
(*               } *)
(*     | IP.Var ((sv, sp), pos) -> collect_type_info_var sv stab expected_type pos; *)
(*     | IP.IConst _ -> () *)
(*     | IP.FConst _ -> () *)
(*     | IP.Add (a1, a2, pos) | IP.Subtract (a1, a2, pos) | IP.Max (a1, a2, pos) | *)
(* 	          IP.Min (a1, a2, pos) -> *)
(* 	      (collect_type_info_arith a1 stab expected_type; collect_type_info_arith a2 stab expected_type) *)
(*     | IP.Mult (a1, a2, pos) | IP.Div (a1, a2, pos) -> *)
(* 	      (collect_type_info_arith a1 stab expected_type; collect_type_info_arith a2 stab expected_type) *)
(*     | IP.ListHead (a, pos) *)
(*     | IP.ListLength (a, pos) -> (collect_type_info_list a stab) *)
(*     | IP.BagDiff _ | IP.BagIntersect _ | IP.BagUnion _ | IP.Bag _ -> *)
(*           failwith "collect_type_info_arith: encountered bag constraint 1" *)
(*     | IP.ListTail _ | IP.ListReverse _ | IP.ListAppend _ | IP.ListCons _ | IP.List _ -> *)
(*           failwith "collect_type_info_arith: encountered list constraint" *)
(*     | IP.ArrayAt ((a,p),idx,pos) ->  *)
(*           (\* An Hoa : Assert that the variable (a,p) must be of type expected_type Array*\) *)
(* 		  (\* and hence, accessing the element at position i, we get the value of expected_type*\) *)
(* 		  (\* Furthermore, the expression of the index must be of type integer.*\) *)
(* 		  let a_exp_type = match expected_type with *)
(* 			| UNK -> UNK *)
(* 			| t -> Array (t, List.length idx) *)
(* 		  in *)
(* 		  collect_type_info_var a stab a_exp_type pos; *)
(* 		  let _ = List.map (fun i -> collect_type_info_arith i stab (C.int_type)) idx in () *)

(* and collect_type_info_bag_content a0 stab = *)
(*   Debug.no_eff_2 "collect_type_info_bag_content" [false;true] (Iprinter.string_of_formula_exp) string_of_stab (fun _ -> "?") *)
(*       collect_type_info_bag_content_x a0 stab *)

(* and collect_type_info_bag_content_x a0 stab = *)
(*   match a0 with *)
(*     | IP.Null pos -> *)
(* 	      Err.report_error *)
(*               { *)
(*                   Err.error_loc = pos; *)
(*                   Err.error_text = "null is not allowed in arithmetic term"; *)
(*               } *)
(*     | IP.Var ((sv, sp), pos) -> collect_type_info_var sv stab UNK pos *)
(*     | IP.IConst _ -> () *)
(*     | IP.FConst _ -> () *)
(*     | IP.Add (a1, a2, pos) | IP.Subtract (a1, a2, pos) | IP.Max (a1, a2, pos) | *)
(* 	          IP.Min (a1, a2, pos) -> *)
(*           (collect_type_info_arith a1 stab UNK; collect_type_info_arith a2 stab UNK) *)
(*     | IP.Mult (a1, a2, pos) | IP.Div (a1, a2, pos) -> *)
(* 	      (collect_type_info_arith a1 stab UNK; collect_type_info_arith a2 stab UNK) *)
(*     | IP.BagDiff _ | IP.BagIntersect _ | IP.BagUnion _ | IP.Bag _ -> *)
(* 	      failwith "collect_type_info_arith: encountered bag constraint 2" *)
(*     | IP.ListHead (a, pos) | IP.ListLength (a, pos) -> (collect_type_info_list a stab) *)
(*     | IP.ListTail _ | IP.ListReverse _ | IP.ListAppend _ | IP.ListCons _ | IP.List _ -> *)
(*           failwith "collect_type_info_bag_content: encountered list constraint" *)
(*     | IP.ArrayAt _ ->  *)
(*           (\* An Hoa *\) *)
(*           failwith "collect_type_info_bag_content: encountered array access"  *)

(* and coll_type_info_bag_content a0 stab : prim_type = *)
(*   match a0 with *)
(*     | IP.Null pos -> *)
(* 	      Err.report_error *)
(*               { *)
(*                   Err.error_loc = pos; *)
(*                   Err.error_text = "null is not allowed in arithmetic term"; *)
(*               } *)
(*     | IP.Var ((sv, sp), pos) -> collect_type_info_var sv stab UNK pos *)
(*     | IP.IConst _ -> () *)
(*     | IP.FConst _ -> () *)
(*     | IP.Add (a1, a2, pos) | IP.Subtract (a1, a2, pos) | IP.Max (a1, a2, pos) | *)
(* 	          IP.Min (a1, a2, pos) -> *)
(*           (collect_type_info_arith a1 stab UNK; collect_type_info_arith a2 stab UNK) *)
(*     | IP.Mult (a1, a2, pos) | IP.Div (a1, a2, pos) -> *)
(* 	      (collect_type_info_arith a1 stab UNK; collect_type_info_arith a2 stab UNK) *)
(*     | IP.BagDiff _ | IP.BagIntersect _ | IP.BagUnion _ | IP.Bag _ -> *)
(* 	      failwith "collect_type_info_arith: encountered bag constraint" *)
(*     | IP.ListHead (a, pos) | IP.ListLength (a, pos) -> (collect_type_info_list a stab) *)
(*     | IP.ListTail _ | IP.ListReverse _ | IP.ListAppend _ | IP.ListCons _ | IP.List _ -> *)
(*           failwith "collect_type_info_bag_content: encountered list constraint" *)
(*     | IP.ArrayAt _ ->  *)
(*           (\* An Hoa *\) *)
(*           failwith "collect_type_info_bag_content: encountered array access"  *)

(* and collect_type_info_bag (e0 : IP.exp) stab = *)
(*   Debug.no_eff_2 "collect_type_info_bag" [false;true] (Iprinter.string_of_formula_exp) string_of_stab (fun _ -> "()") *)
(*       (fun _ _ -> collect_type_info_bag_x e0 stab) e0 stab *)

(* and collect_type_info_bag_x (e0 : IP.exp) stab = *)
(*   let rec helper e0 = *)
(*     match e0 with *)
(*       | IP.Var ((sv, sp), pos) -> *)
(* 	        collect_type_info_var sv stab (C.bag_type) pos *)
(*       | IP.Bag ((a :: rest), pos) -> *)
(* 	        (collect_type_info_bag_content a stab; *)
(* 	        helper  (IP.Bag (rest, pos)) ) *)
(*       | IP.Bag ([], pos) -> () *)
(*       | IP.BagUnion ((a :: rest), pos) -> *)
(* 	        (helper a; *)
(* 	        helper (IP.BagUnion (rest, pos))) *)
(*       | IP.BagUnion ([], pos) -> () *)
(*       | IP.BagIntersect ((a :: rest), pos) -> *)
(* 	        (helper a; *)
(* 	        helper (IP.BagIntersect (rest, pos))) *)
(*       | IP.BagIntersect ([], pos) -> () *)
(*       | IP.BagDiff (a1, a2, pos) -> *)
(* 	        (helper a1; helper a2) *)
(*       | IP.Min _ | IP.Max _  *)
(*       | IP.Mult _ | IP.Div _ | IP.Subtract _ | IP.Add _  *)
(*       | IP.IConst _ | IP.FConst _ | IP.Null _ -> *)
(* 	        failwith "collect_type_info_bag: encountered arithmetic constraint" *)
(*       | IP.ListHead _ | IP.ListTail _ | IP.ListLength _ | IP.ListReverse _ | IP.ListAppend _ | IP.ListCons _ | IP.List _ -> *)
(*             failwith "collect_type_info_bag: encountered list constraint" *)
(*       | IP.ArrayAt _ -> *)
(*             (\* An Hoa *\) *)
(*             failwith "collect_type_info_bag: encountered array constraint!"  *)
(*   in helper e0 *)

(* and collect_type_info_list (e0 : IP.exp) stab = *)
(*   match e0 with *)
(*     | IP.Var ((sv, sp), pos) -> *)
(*           collect_type_info_var sv stab (C.list_type) pos *)
(*     | IP.List ((a :: rest), pos) -> *)
(*           (collect_type_info_bag_content a stab; *)
(*           collect_type_info_list (IP.List (rest, pos)) stab) *)
(*     | IP.List ([], pos) -> () *)
(*     | IP.ListAppend ((a :: rest), pos) -> *)
(*           (collect_type_info_list a stab; *)
(*           collect_type_info_list (IP.ListAppend (rest, pos)) stab) *)
(*     | IP.ListAppend ([], pos) -> () *)
(*     | IP.ListCons (a1, a2, pos) ->  *)
(*           (collect_type_info_arith a1 stab UNK; *)
(* 	      collect_type_info_list a2 stab) *)
(*     | IP.ListTail (a, pos) -> *)
(*           (collect_type_info_list a stab) *)
(*     | IP.ListReverse (a, pos) -> *)
(*           (collect_type_info_list a stab) *)
(*     | IP.Min _ | IP.Max _ | IP.Mult _ | IP.FConst _ | IP.Div _ | IP.Subtract _ | IP.Add _ | IP.IConst _ *)
(*     | IP.Null _ | IP.ListHead _ | IP.ListLength _ -> *)
(*           failwith "collect_type_info_list: encountered arithmetic constraint" *)
(*     | IP.BagDiff _ | IP.BagIntersect _ | IP.BagUnion _ | IP.Bag _ -> *)
(*           failwith "collect_type_info_list: encountered bag constraint 3" *)
(*     | IP.ArrayAt _ -> *)
(*           (\* An Hoa *\) *)
(*           failwith "collect_type_info_list: encountered array access"  *)

(* and collect_type_info_pointer (e0 : IP.exp) (k : spec_var_kind) stab = *)
(*   match e0 with *)
(*     | IP.Null _ -> () *)
(*     | IP.Var ((sv, sp), pos) -> collect_type_info_var sv stab k pos *)
(*     | _ -> *)
(* 	      Err.report_error *)
(*               { *)
(*                   Err.error_loc = IP.pos_of_exp e0; *)
(*                   Err.error_text = "arithmetic is not allowed in pointer term"; *)
(*               } *)

and gather_type_info_pointer (e0 : IP.exp) (k : spec_var_kind) stab : typ =
  match e0 with
    | IP.Null _ -> null_type
    | IP.Var ((sv, sp), pos) -> gather_type_info_var sv stab k pos
    | _ ->
	      Err.report_error
              {
                  Err.error_loc = IP.pos_of_exp e0;
                  Err.error_text = "arithmetic is not allowed in pointer term";
              }


(* AN HOA : TODO CHECK *)
(* and collect_type_info_formula prog f0 stab filter_res =  *)
(*   (\* let _ = print_string ("collecting types for:\n"^(Iprinter.string_of_formula f0)^"\n") in  *)
(*      let _ = print_string ("stab: " ^ (string_of_stab stab) ^ "\n") in *\) *)
(*   let helper pure branches heap =  *)
(*     ( *)
(*         collect_type_info_heap prog heap stab; *)
(*         collect_type_info_pure prog pure stab; *)
(*         ignore (List.map (fun (c1,c2) -> collect_type_info_pure prog c2 stab) branches) *)
(*     )	in *)
(*   match f0 with *)
(*     | IF.Or b-> ( collect_type_info_formula prog b.IF.formula_or_f1 stab filter_res; *)
(* 	  collect_type_info_formula prog b.IF.formula_or_f2 stab filter_res) *)
(*     | IF.Exists b ->  *)
(* 	      let rl = CF.res_retrieve stab filter_res b.IF.formula_exists_flow in *)
(* 	      (helper b.IF.formula_exists_pure b.IF.formula_exists_branches b.IF.formula_exists_heap);	 *)
(* 	      (CF.res_replace stab rl filter_res b.IF.formula_exists_flow)  *)
(*     | IF.Base b -> *)
(* 	      let rl = CF.res_retrieve stab filter_res b.IF.formula_base_flow in *)
(* 	      (helper b.IF.formula_base_pure b.IF.formula_base_branches b.IF.formula_base_heap); *)
(* 	      (CF.res_replace stab rl filter_res b.IF.formula_base_flow) *)

and gather_type_info_formula prog f0 stab filter_res = 
  Debug.no_eff_3 "gather_type_info_formula"
      [false;true]
      (Iprinter.string_of_formula) string_of_stab 
      string_of_bool (fun x -> "()")
      (fun _ _ _ -> gather_type_info_formula_x prog f0 stab filter_res)
      f0 stab filter_res

and gather_type_info_one_formula prog (f : IF.one_formula) stab filter_res =
  (
      (match f.IF.formula_thread with
        | None -> ()
        | Some (v,pr) -> let _ = gather_type_info_var v stab thread_typ f.IF.formula_pos in () );
      gather_type_info_heap prog f.IF.formula_heap stab;
      gather_type_info_pure prog f.IF.formula_pure stab
  )

and gather_type_info_formula_x prog f0 stab filter_res = 
  let helper pure heap = gather_type_info_heap prog heap stab; gather_type_info_pure prog pure stab in
  match f0 with
    | IF.Or b-> ( gather_type_info_formula_x prog b.IF.formula_or_f1 stab filter_res;
	  gather_type_info_formula_x prog b.IF.formula_or_f2 stab filter_res)
    | IF.Exists b -> 
	      let rl = res_retrieve stab filter_res b.IF.formula_exists_flow in
          let _ = List.map (fun f -> gather_type_info_one_formula prog f stab filter_res) b.IF.formula_exists_and in
	      (helper b.IF.formula_exists_pure b.IF.formula_exists_heap);	
	      (res_replace stab rl filter_res b.IF.formula_exists_flow) 
    | IF.Base b ->
	      let rl = res_retrieve stab filter_res b.IF.formula_base_flow in
          let _ = List.map (fun f -> gather_type_info_one_formula prog f stab filter_res) b.IF.formula_base_and in
	      (helper b.IF.formula_base_pure b.IF.formula_base_heap);
	      (res_replace stab rl filter_res b.IF.formula_base_flow) 

and type_store_clean_up (f:CF.struc_formula) stab = () (*if stab to big,  -> get list of quantified vars, remove them from stab*)
  
and gather_type_info_struc_f prog (f0:IF.struc_formula) stab =
  Debug.no_eff_2 "gather_type_info_struc_f" [false;true]
      Iprinter.string_of_struc_formula string_of_stab (fun _ -> "()")
      (fun _ _ -> gather_type_info_struc_f_x prog f0 stab) f0 stab 

and gather_type_info_struc_f_x prog (f0:IF.struc_formula) stab = 
  let rec inner_collector (f0:IF.struc_formula) =  match f0 with
      | IF.EAssume (b,_)-> let _ = gather_type_info_formula prog b stab true in ()
      | IF.ECase b ->  List.iter (fun (c1,c2)->
			let _ = gather_type_info_pure prog c1 stab in
			inner_collector c2) b.IF.formula_case_branches
      | IF.EBase b ->  let _ = gather_type_info_formula prog b.IF.formula_struc_base stab false in
	    let _ = match b.IF.formula_struc_continuation with | None -> () | Some l -> inner_collector l in ()								
      | IF.EInfer b -> let _ = inner_collector b.IF.formula_inf_continuation in ()
	  | IF.EList b -> List.iter (fun (_,c)-> inner_collector c) b
	  | IF.EOr b -> inner_collector b.IF.formula_struc_or_f1;inner_collector b.IF.formula_struc_or_f2 in
  begin
    inner_collector f0;
    (* TODO WN : to remove check_shallow_var *)
    (* TODO WN : to avoid double parsing *)
    (* re-collect type info, don't check for shadowing outer var this time *)
    (* check_shallow_var := false; *)
    (* inner_collector f0; *)
    (* check_shallow_var := true *)
  end
      

and try_unify_data_type_args prog c ddef v ies stab pos =
  (* An Hoa : problem detected - have to expand the inline fields as well, fix in look_up_all_fields. *)
  let _ = gather_type_info_var v stab ((Named c)) pos in
  let fields = I.look_up_all_fields prog ddef
  in 
  (try 
    let f _ arg ((ty,_),_,_) = 
      (let _ = gather_type_info_exp arg stab ty in ())
    in (List.fold_left2 f () ies fields)
  with | Invalid_argument _ ->
	  Err.report_error
		  {
              Err.error_loc = pos;
              Err.error_text =
                  "number of arguments for data " ^
				      c ^ " does not match"^(pr_list (fun c->c)(List.map Iprinter.string_of_formula_exp ies));
		  }
  )


(* ident, args, table *)
and try_unify_view_type_args prog c vdef v ies stab pos =
  let dname = vdef.I.view_data_name in
  let _ =  (if not (dname = "")
  then let _ = gather_type_info_var v stab ( (Named dname)) pos in ()
  else ()) 
  in
  let _ = if (String.length vdef.I.view_data_name) = 0  then fill_view_param_types vdef in
  let vt = vdef.I.view_typed_vars in
  let rec helper exps tvars =
    match (exps, tvars) with
      | ([], []) -> []
      | (e :: rest1, t :: rest2) ->
			let tmp = helper rest1 rest2
			in
            (match e with
			  | IP.Var ((v, p), pos) -> 
                    let ty = fst t in (ty, v) :: tmp
			  | _ -> tmp)
      | _ ->
			Err.report_error
                {
                    Err.error_loc = pos;
                    Err.error_text =
				        "number of arguments for view " ^
				            (c ^ " does not match");
                } in
  let tmp_r = helper ies vt in
  let (vt_u,tmp_r) = List.partition (fun (ty,_) -> ty==UNK) tmp_r in
  if (Gen.is_empty vt_u)
  then
    let _ = (List.map (fun (t, n) -> gather_type_info_var n stab (t) pos) tmp_r) in
    ()
  else begin
    (* below seems wrong to unify against previous var names *)
    (try 
      let _ = (List.map (fun (t, n) -> gather_type_info_var n stab (t) pos) tmp_r) in
      let f _ arg lhs_v = 
        (let et = get_var_kind lhs_v stab  in 
        let new_t = gather_type_info_exp arg stab et in
        let _ = set_var_kind lhs_v new_t stab in () ) 
      in (List.fold_left2 f () ies vdef.I.view_vars)
    with | Invalid_argument _ -> report_error pos ("number of arguments for view " ^ c ^ " does not match")
    )
  end


and gather_type_info_heap prog (h0 : IF.h_formula) stab =
  Debug.no_eff_2 "gather_type_info_heap" [false;true]
      Iprinter.string_of_h_formula string_of_stab (fun _ -> "()")
      (fun _ _ -> gather_type_info_heap_x prog h0 stab) h0 stab 

and gather_type_info_heap_x prog (h0 : IF.h_formula) stab =
  match h0 with
    | IF.Star
	        {
                IF.h_formula_star_h1 = h1;
                IF.h_formula_star_h2 = h2;
                IF.h_formula_star_pos = pos
	        } 
    | IF.Conj
	        {
                IF.h_formula_conj_h1 = h1;
                IF.h_formula_conj_h2 = h2;
                IF.h_formula_conj_pos = pos
	        } 
    | IF.Phase
	        {
                IF.h_formula_phase_rd = h1;
                IF.h_formula_phase_rw = h2;
                IF.h_formula_phase_pos = pos
	        } ->
	      (gather_type_info_heap_x prog h1 stab;
	      gather_type_info_heap_x prog h2 stab)
    | IF.HeapNode2 h2 ->
	      let h = node2_to_node prog h2 in
	      let fh = IF.HeapNode h in gather_type_info_heap_x prog fh stab
    | IF.HeapNode
	        {
                IF.h_formula_heap_node = (v, p); (* ident, primed *)
                IF.h_formula_heap_arguments = ies; (* arguments *)
                IF.h_formula_heap_perm = perm;
                IF.h_formula_heap_name = c; (* data/pred name *)
                IF.h_formula_heap_imm = ann; (* data/pred name *)
                IF.h_formula_heap_pos = pos
	        } ->
          Debug.trace_hprint (add_str "view" Iprinter.string_of_h_formula) h0 no_pos;
          let ft = cperm_typ () in
          let gather_type_info_ann c stab = match c with
            | IF.ConstAnn _ -> ()
            | IF.PolyAnn ((i,_),_) -> ignore(gather_type_info_var i stab AnnT pos) in
          let gather_type_info_perm p stab = match p with
            | None -> ()
            | Some e -> let _ = gather_type_info_exp e stab ft in () in
          let _ = gather_type_info_perm perm stab in
          let _ = gather_type_info_ann ann stab in
		  (* let _ = print_endline ("[gather_type_info_heap_x] input formula = " ^ Iprinter.string_of_h_formula h0) in *)
		  (* An Hoa : Deal with the generic pointer! *)
		  if (c = Parser.generic_pointer_type_name) then 
			(* Assumptions:
			 * (i)  ies to contain a single argument, namely the value of the pointer
			 * (ii) the head of the heap node is of form "V[.TypeOfV].FieldAccess"
			 *      where [.TypeOfV] is optional type of V. If it is present, it is
			 *      the type of V pointer. Otherwise, we try to find this information
			 *      based on its fields.
			 * (iii) Temporarily assume that only one field; the case of inline fields
			 *      will be dealt with later.
			 *)
			(* Step 1: Extract the main variable i.e. the root of the pointer *)
			(* let _ = print_endline ("[gather_type_info_heap_x] heap pointer = " ^ v) in *)
			let tokens = Str.split (Str.regexp "\\.") v in
			(* let _ = print_endline ("[gather_type_info_heap_x] tokens = {" ^ (String.concat "," tokens) ^ "}") in *)
			let rootptr = List.hd tokens in
			(* Step 2: Determine the type of [rootptr] and the field by looking 
			 * up the current state of stab & information supplied by the user.
			 *)
			let s = List.nth tokens 1 in
			let type_found,type_rootptr = try (* looking up in the list of data types *)
			  (* Good user provides type for [rootptr] ==> done! *)
			  let ddef = I.look_up_data_def_raw prog.I.prog_data_decls s in 
			  (* let _ = print_endline ("[gather_type_info_heap_x] root pointer type = " ^ ddef.I.data_name) in *)
			  (true, Named ddef.I.data_name)
			with 
			  | Not_found -> (false,UNK) (* Lazy user ==> perform type reasoning! *) in
			(* After this, if type_found = false then we know that 
			 * s is a name of field of some data type
			 *)
			let type_found,type_rootptr = if type_found then (type_found,type_rootptr)
			else try (* looking up in the collected types table for [rootptr] *)
			  let vi = H.find stab rootptr in
			  match vi.sv_info_kind with
				| UNK -> (false,UNK)
				| _ -> (true,vi.sv_info_kind) (* type of [rootptr] is known ==> done! *)
			with
			  | Not_found -> (false,UNK) in
			let type_found,type_rootptr = if type_found then (type_found,type_rootptr)
			else (* inferring the type from the name of the field *)
			  let dts = I.look_up_types_containing_field prog.I.prog_data_decls s in
			  if (List.length dts = 1) then
				(* the field uniquely determines the data type ==> done! *)
				(* let _ = print_endline ("[gather_type_info_heap_x] Only type " ^ (List.hd dts) ^ " has field " ^ s) in *)
				(true,Named (List.hd dts))
			  else
				(false,UNK) in
			(* Step 3: Collect the remaining type information *)
			if type_found then
			  (* Know the type of rootptr ==> Know the type of the field *)
			  let _ = H.add stab rootptr { sv_info_kind = type_rootptr; id = 0 } in
			  (* Filter out user type indication, List.tl to remove the root as well *)
			  let field_access_seq = List.tl (List.filter (fun x -> I.is_not_data_type_identifier prog.I.prog_data_decls x) tokens) in
			  (* Get the type of the field which is the type of the pointer *)
			  let ptr_type = I.get_type_of_field_seq prog.I.prog_data_decls type_rootptr field_access_seq in
			  (* let _ = print_endline ("[gather_type_info_heap_x] pointer type found = " ^ (string_of_typ ptr_type)) in *)
			  let _ = gather_type_info_exp (List.hd ies) stab ptr_type in ()
			else ()
		  else (* End dealing with generic ptr, continue what the original system did *)
	        let _ = 
              (try
                let vdef = I.look_up_view_def_raw prog.I.prog_view_decls c in
                (*let ss = pr_list (pr_pair string_of_typ pr_id) vdef.I.view_typed_vars in*)
	            (* let _ = print_string ("\n searching for: "^(\* c^ *\)" got: "^vdef.I.view_data_name^"-"^vdef.I.view_name^" types:"^ss^"\n") in *)
                try_unify_view_type_args prog c vdef v ies stab pos 
              with
                | Not_found ->
		              (try
                        let ddef = I.look_up_data_def_raw prog.I.prog_data_decls c in
                        let _ = try_unify_data_type_args prog c ddef v ies stab pos in ()
		              with
		                | Not_found ->
			                  (*let _ = print_string (Iprinter.string_of_program prog) in*)
			                  Err.report_error
			                      {
			                          Err.error_loc = pos;
			                          Err.error_text = c ^ " is neither 2 a data nor view name";
			                      })) in ()
    | IF.HRel (r, args, pos) ->
        (try
		    let hpdef = I.look_up_hp_def_raw prog.I.prog_hp_decls r in
		    let args_ctypes = List.map (fun (t,n) -> trans_type prog t pos) hpdef.I.hp_typed_vars in
		    let args_exp_types = List.map (fun t -> (t)) args_ctypes in
            let _ = gather_type_info_var r stab HpT in
		    let _ = List.map2 (fun x y -> gather_type_info_exp x stab y) args args_exp_types in ()
		  with
		    | Not_found ->    failwith ("gather_type_info_heap: relation "^r^" cannot be found")
            | _ -> print_endline ("gather_type_info_heap: relation " ^ r)
          )

    | IF.HTrue | IF.HFalse | IF.HEmp -> ()

and get_spec_var_stab (v : ident) stab pos =
  try
    let v_info = H.find stab v
    in
    match v_info.sv_info_kind with
	  | UNK ->
            Err.report_error
                { Err.error_loc = pos; Err.error_text = v ^ " is undefined"; }
	  | t -> let sv = CP.SpecVar (t, v, Unprimed) in sv
  with
    | Not_found ->
	      Err.report_error
              { Err.error_loc = pos; Err.error_text = v ^ " is undefined"; }

and get_spec_var_stab_infer (v : ident) fvs pos =
  let pr_sv = Cprinter.string_of_spec_var in
  Debug.no_2 "get_spec_var_stab_infer" 
      pr_id (pr_list pr_sv) pr_sv
      (fun _ _ -> get_spec_var_stab_infer_x v fvs pos) v fvs

and get_spec_var_stab_infer_x (v : ident) fvs pos =
  let get_var_type v fv_list: (typ * bool) = 
    let res_list = CP.remove_dups_svl (List.filter (fun c -> v = CP.name_of_spec_var c) fv_list) in
    match res_list with
	  | [] -> (Void,false)
	  | [sv] -> (CP.type_of_spec_var sv,true)
	  | _ -> Err.report_error { Err.error_loc = pos; Err.error_text = "could not find a coherent "^v^" type"}
  in
  let vtyp, check = get_var_type v fvs in
  if check = false
  then Err.report_error { Err.error_loc = pos; Err.error_text = v ^ " is not found in both sides"; }
  else
    match vtyp with
      | UNK -> Err.report_error { Err.error_loc = pos; Err.error_text = v ^ " is undefined"; }
      | t -> CP.SpecVar (t, v, Unprimed)

and get_spec_var_stab_infer_with_prime (v, p) fvs pos =
  let get_var_type v fv_list: (typ * bool) = 
    let res_list = CP.remove_dups_svl (List.filter 
      (fun c -> v = CP.name_of_spec_var c & p = CP.primed_of_spec_var c) fv_list) in
    match res_list with
      | [] -> (Void,false)
      | [sv] -> (CP.type_of_spec_var sv,true)
      | _ -> Err.report_error { Err.error_loc = pos; Err.error_text = "could not find a coherent "^v^" type"}
  in
  let vtyp, check = get_var_type v fvs in
  if check = false
  then Err.report_error { Err.error_loc = pos; Err.error_text = v ^ " is not found in both sides"; }
  else
    match vtyp with
      | UNK -> Err.report_error { Err.error_loc = pos; Err.error_text = v ^ " is undefined"; }
      | t -> CP.SpecVar (t, v, Unprimed)

and string_of_spec_var_kind (k : spec_var_kind) =
  string_of_typ k
      (* match k with | UNK -> "Unk" | Known t -> (string_of_typ t)^" " *)


and print_stab (stab : spec_var_table) =
  let p k i =
    print_string
        (k ^ (" --> " ^ ((string_of_spec_var_kind i.sv_info_kind) ^ "\n")))
  in (print_string "\n"; H.iter p stab; print_string "\n")

and case_normalize_pure_formula hp b f = f

(*moved the liniarization to case_normalize_renamed_formula*)
and case_normalize_renamed_formula prog (avail_vars:(ident*primed) list) posib_expl (f:IF.formula): IF.formula* ((ident*primed)list) * ((ident*primed)list) =
  let pr = (pr_list (fun (i,p) -> i)) in
  let pr_out (f,h,expl) = 
    ("\n ### f = " ^ (Iprinter.string_of_formula f)
     ^"\n ### h = " ^ (pr h)
     ^"\n ### expl = " ^ (pr expl)) 
  in 
  Debug.no_3 "case_normalize_renamed_formula" 
      pr pr Iprinter.string_of_formula pr_out
      (fun _ _ _ -> case_normalize_renamed_formula_x prog avail_vars posib_expl f) avail_vars posib_expl f

(*moved the liniarization to case_normalize_renamed_formula*)
and case_normalize_renamed_formula_x prog (avail_vars:(ident*primed) list) posib_expl (f:IF.formula):
      IF.formula* ((ident*primed)list) * ((ident*primed)list) = 
  (*existential wrapping and other magic tricks, avail_vars -> program variables, function arguments...*)
  (*returns the new formula, used variables and vars to be explicitly instantiated*)
  let rec match_exp (used_names : (ident*primed) list) (hargs : (IP.exp * Label_only.spec_label) list) pos :
        ((ident*primed) list) * ((ident*primed) list) * ((ident*primed) list) * IP.formula = 
    match hargs with
      | (e, label) :: rest ->
            let new_used_names, e_hvars, e_evars, e_link = match e with
              | IP.Var (v, pos_e) ->
                    (try
                      if (List.mem v avail_vars) || (List.mem v used_names) then(*existential wrapping and liniarization*)
                        let fresh_v = (Ipure.fresh_old_name (fst v)),Unprimed in
                        let link_f = IP.mkEqExp (IP.Var (fresh_v,pos_e)) e pos_e in
                        (used_names, [ fresh_v ], [ fresh_v ], if Lab_List.is_unlabelled label then link_f else IP.mkAndList [label, link_f])
                      else
                        ((v :: used_names), [ v ], [],IP.mkTrue pos_e)
                    with
                      | Not_found -> Err.report_error{ Err.error_loc = pos_e; Err.error_text = (fst v) ^ " is undefined"; })
              | _ -> Err.report_error { Err.error_loc = (IF.pos_of_formula f); Err.error_text = "malfunction with float out exp in normalizing"; } in
            let rest_used_names, rest_hvars, rest_evars, rest_link = match_exp new_used_names rest pos in
            let hvars = e_hvars @ rest_hvars in
            let evars = e_evars @ rest_evars in
            let link_f = IP.mkAnd e_link rest_link pos in
            (rest_used_names, hvars, evars, link_f)
      | [] -> (used_names, [], [], IP.mkTrue pos) in

  let rec flatten f = match f with
    | IF.HTrue -> [IF.HTrue]
    | IF.HFalse -> []
    | IF.HEmp -> []
    | IF.Conj
	        {  IF.h_formula_conj_h1 = f1;
	        IF.h_formula_conj_h2 = f2;
	        IF.h_formula_conj_pos = pos
	        } 
    | IF.Phase
	        {   IF.h_formula_phase_rd = f1;
	        IF.h_formula_phase_rw = f2;
	        IF.h_formula_phase_pos = pos
	        } 
        -> (flatten f1)@(flatten f2)
    | _ -> [f]
  in
  let rec imm_heap (f : IF.h_formula): IF.h_formula = match f with
    | IF.Star
	        {	  IF.h_formula_star_h1 = f1;
	        IF.h_formula_star_h2 = f2;
	        IF.h_formula_star_pos = pos
	        } ->
          IF.mkStar (imm_heap f1) (imm_heap f2) pos 
    | IF.Conj
	        {
	            IF.h_formula_conj_h1 = f1;
	            IF.h_formula_conj_h2 = f2;
	            IF.h_formula_conj_pos = pos
	        } 
    | IF.Phase
	        {
	            IF.h_formula_phase_rd = f1;
	            IF.h_formula_phase_rw = f2;
	            IF.h_formula_phase_pos = pos
	        } ->
	      imm_heap_2 f1 f2
    | _ ->  f
  and imm_heap_2 (f1 : IF.h_formula) (f2 : IF.h_formula) =
    let ls = flatten f1 in
    let r = imm_heap f2 in
    List.fold_right (fun a r -> IF.mkPhase a r no_pos) ls r
  in
  
  let rec linearize_heap (used_names:((ident*primed) list)) (f : IF.h_formula): ((ident*primed) list) * ((ident*primed) list) * IF.h_formula * Ipure.formula =
    match f with
      | IF.HeapNode2 b -> report_error b.IF.h_formula_heap2_pos "malfunction: heap node 2 still present"
      | IF.HeapNode b ->
	        let pos = b.IF.h_formula_heap_pos in
	        let labels = try
	          let vdef = I.look_up_view_def_raw prog.I.prog_view_decls b.IF.h_formula_heap_name in
	          vdef.I.view_labels
	        with
	          | Not_found ->List.map (fun _ -> Label_only.empty_spec_label) b.IF.h_formula_heap_arguments in	
	        let _ = if (List.length b.IF.h_formula_heap_arguments) != (List.length labels) then
	          report_error pos ("predicate "^b.IF.h_formula_heap_name^" does not have the correct number of arguments")
	        in
            let perm_labels,perm_var = 
              match b.IF.h_formula_heap_perm with
                | None -> [],[]
                | Some f -> [Label_only.empty_spec_label], [f]
            in
	        let new_used_names, hvars, evars, link_f = match_exp used_names (List.combine (perm_var@b.IF.h_formula_heap_arguments) (perm_labels@labels)) pos in
	        let hvars = List.map (fun c-> Ipure.Var (c,pos)) hvars in
            (*split perm if any*)
            let perm_var,hvars = match b.IF.h_formula_heap_perm with
              | Some _ -> (Some (List.hd hvars), List.tl hvars)
              | None -> (None,hvars)
            in
	        let new_h = IF.HeapNode{ b with 
                IF.h_formula_heap_arguments = hvars;
                IF.h_formula_heap_perm = perm_var;}
	        in (new_used_names, evars, new_h, link_f)
      | IF.Star
	          {
	              IF.h_formula_star_h1 = f1;
	              IF.h_formula_star_h2 = f2;
	              IF.h_formula_star_pos = pos
	          } ->
	        let new_used_names1, qv1, lf1, link1 = linearize_heap used_names f1 in
	        let new_used_names2, qv2, lf2, link2 = linearize_heap new_used_names1 f2 in
	        let tmp_h = IF.mkStar lf1 lf2 pos in
	        let tmp_link = IP.mkAnd link1 link2 pos in
	        (new_used_names2, (qv1 @ qv2), tmp_h, tmp_link)

      | IF.Conj
	          {
	              IF.h_formula_conj_h1 = f1;
	              IF.h_formula_conj_h2 = f2;
	              IF.h_formula_conj_pos = pos
	          } ->
	        let new_used_names1, qv1, lf1, link1 = linearize_heap used_names f1 in
	        let new_used_names2, qv2, lf2, link2 = linearize_heap new_used_names1 f2 in
	        let tmp_h = IF.mkConj lf1 lf2 pos in
	        let tmp_link = IP.mkAnd link1 link2 pos in
	        (new_used_names2, (qv1 @ qv2), tmp_h, tmp_link)
      | IF.Phase
	          {
	              IF.h_formula_phase_rd = f1;
	              IF.h_formula_phase_rw = f2;
	              IF.h_formula_phase_pos = pos
	          } ->
	        let new_used_names1, qv1, lf1, link1 = linearize_heap used_names f1 in
	        let new_used_names2, qv2, lf2, link2 = linearize_heap new_used_names1 f2 in
	        let tmp_h = IF.mkPhase lf1 lf2 pos in
	        let tmp_link = IP.mkAnd link1 link2 pos in
	        (new_used_names2, (qv1 @ qv2), tmp_h, tmp_link)
      | IF.HRel r -> (used_names, [], IF.HRel r ,  IP.mkTrue no_pos)
      | IF.HTrue ->  (used_names, [], IF.HTrue,  IP.mkTrue no_pos)
      | IF.HFalse -> (used_names, [], IF.HFalse, IP.mkTrue no_pos)
      | IF.HEmp -> (used_names, [], IF.HEmp, IP.mkTrue no_pos) in 
	  
  let linearize_heap (used_names:((ident*primed) list)) (f : IF.h_formula):
        (((ident*primed) list) * ((ident*primed) list) * IF.h_formula * Ipure.formula) =
    let (a,b,h,r) = linearize_heap used_names f in
    (a,b,imm_heap h,r)
  in
  let linearize_heap (used_names:((ident*primed) list)) (f : IF.h_formula):
        (((ident*primed) list) * ((ident*primed) list) * IF.h_formula * Ipure.formula) =
    let pr1 = Iprinter.string_of_h_formula in
    let pr2 (_,_,h, p) = (Iprinter.string_of_h_formula h)^"&&$"^(Iprinter.string_of_pure_formula p) in
    let pr0 (vs:((ident*primed) list))= 
      let idents, _ = List.split vs in
      (string_of_ident_list idents) in
    Debug.no_2 "linearize_heap" pr0 pr1 pr2 (fun _ _ -> linearize_heap used_names f) used_names f  in
	
  let rec normalize_base heap cp fl a evs pos : IF.formula* ((ident*primed)list)* ((ident*primed)list) =
    let heap = Immutable.normalize_h_formula heap false in 
    let nu, h_evars, new_h, link_f = linearize_heap [] heap in
    (****processsing formula_*_and***********)
    (*Note: f.formula_thread should appear in f.formula_pure*)
	let func evars (f:IF.one_formula) = normalize_base f.IF.formula_heap  f.IF.formula_pure top_flow [] evars f.IF.formula_pos in
    let tmp_a = List.map (func h_evars) a in
    let rec split3 ls = match ls with
      | [] -> [],[],[]
      | (x1,x2,x3)::xs -> 
          let ls1,ls2,ls3 = split3 xs in
          (x1::ls1,x2::ls2,x3::ls3)
    in
    let new_a, used_vars_a,to_expl_a = split3 tmp_a in
    let rec func2 (fs: (IF.formula * IF.one_formula) list) : ((IF.one_formula list) * ((ident*primed)list)) =
      match fs with
        | [] -> [],[]
        | (f1,f2):: xs ->
            let rs,evars2 = func2 xs in
            let evars1,_ = IF.split_quantifiers f1 in
            let f = IF.one_formula_of_formula f1 in
            let f1 = {f with IF.formula_thread = f2.IF.formula_thread} in
            (f1::rs,evars1@evars2)
    in
    let tmp = List.combine new_a a in
    let new_a, evars_a = func2 tmp in
    let used_vars_a = List.concat used_vars_a in
    let to_expl_a = List.concat to_expl_a in
    let new_p = Ipure.mkAnd cp link_f pos in
    let nu = nu@used_vars_a in
    let posib_expl = Gen.BList.remove_dups_eq (=) (posib_expl@to_expl_a) in
    let tmp_evars, to_expl =
      (let init_evars = Gen.BList.remove_dups_eq (=) (evars_a@h_evars@evs) in
      let to_evars = Gen.BList.difference_eq (=) init_evars posib_expl in
      let to_expl = Gen.BList.intersect_eq (=) init_evars posib_expl in       
      (to_evars,to_expl))in
    let result = IF.mkExists tmp_evars new_h new_p fl new_a pos in
    let used_vars = Gen.BList.difference_eq (=) nu tmp_evars in
    if not (Gen.is_empty tmp_evars)  then 
      Debug.pprint ("linearize_constraint: " ^ ((String.concat ", " (List.map fst tmp_evars)) ^ " are quantified\n")) pos
    else ();
    (result,used_vars,to_expl)  in  
  
  let rec helper (f:IF.formula):IF.formula* ((ident*primed)list)* ((ident*primed)list) = match f with
    | IF.Or b -> 
          let f1,l1,expl1 = (helper b.IF.formula_or_f1) in
          let f2,l2,expl2 = (helper b.IF.formula_or_f2) in
          (IF.Or {b with IF.formula_or_f1 = f1; IF.formula_or_f2 = f2}, 
          Gen.BList.remove_dups_eq (=) (l1@l2),(Gen.BList.remove_dups_eq (=) (expl1@expl2)))
    | IF.Base b -> normalize_base  b.IF.formula_base_heap b.IF.formula_base_pure  b.IF.formula_base_flow  b.IF.formula_base_and [] b.IF.formula_base_pos
    | IF.Exists b-> normalize_base b.IF.formula_exists_heap  b.IF.formula_exists_pure b.IF.formula_exists_flow b.IF.formula_exists_and b.IF.formula_exists_qvars b.IF.formula_exists_pos in
  helper f    

(* AN HOA : TODO CHECK *)
and case_normalize_formula prog (h:(ident*primed) list)(f:IF.formula):IF.formula =
  let pr = Iprinter.string_of_formula in
  Debug.no_1 "case_normalize_formula" pr pr (fun f -> case_normalize_formula_x prog h f) f
	  
	  
and case_normalize_formula_x prog (h:(ident*primed) list)(f:IF.formula):IF.formula = 
  (*called for data invariants and assume formulas ... rename bound, convert_struc2 float out exps from heap struc*)
  let f = convert_heap2 prog f in
  (* let _ = print_string ("case_normalize_formula :: CHECK POINT 0 ==> f = " ^ Iprinter.string_of_formula f ^ "\n") in *)
  let f = IF.float_out_thread f in
  let f = IF.float_out_exps_from_heap f in
  let f = IF.float_out_min_max f in
  let f = IF.rename_bound_vars f in
  let f,_,_ = case_normalize_renamed_formula prog h [] f in
  f
      
and case_normalize_struc_formula  prog (h:(ident*primed) list)(p:(ident*primed) list)(f:IF.struc_formula) allow_primes (lax_implicit:bool)
      strad_vs :IF.struc_formula* ((ident*primed)list) = 	
  let pr0 = pr_list (fun (i,p) -> i) in
  let pr1 = Iprinter.string_of_struc_formula in
  let pr2 (x,_) = pr1 x in
  Debug.no_3_loop "case_normalize_struc_formula" pr0 pr0 pr1 pr2 (fun _ _ _ -> case_normalize_struc_formula_x prog h p f allow_primes lax_implicit strad_vs) h p f
      
and case_normalize_struc_formula_x prog (h:(ident*primed) list)(p:(ident*primed) list)(f:IF.struc_formula) allow_primes (lax_implicit:bool)
      strad_vs :IF.struc_formula* ((ident*primed)list) = 	
  let ilinearize_formula (f:IF.formula)(h:(ident*primed) list): IF.formula = 
    let need_quant = Gen.BList.difference_eq (=) (IF.all_fv f) h in
    let _ = if not (List.for_all(fun (c1,c2)->c2==Unprimed)need_quant) then 
          let vars = List.filter (fun (c1,c2)->c2==Primed) need_quant in
          let msg = "Pass-by-value parameters and local variables can not escape out of scope: " ^ (string_of_primed_ident_list vars) in
          Err.report_error{ 
              Err.error_loc = IF.pos_of_formula f; 
              Err.error_text = msg; } 

        (*   Err.report_error{  *)
        (* Err.error_loc = IF.pos_of_formula f;  *)
        (* Err.error_text = "call-by-value parameters & existential vars should not be primed"; }  *)
    in
    (* let _ = if (List.length need_quant)>0 then  *)
    (*   print_string ("\n warning "^(string_of_loc (IF.pos_of_formula f))^" quantifying: "^(Iprinter.string_of_var_list need_quant)^"\n") in *)
    IF.push_exists need_quant f in
  (* let _ = print_string ("case_normalize_struc_formula :: CHECK POINT 0 ==> f = " ^ Iprinter.string_of_struc_formula f ^ "\n") in *)
  let nf = convert_struc2 prog f in
  (* let _ = print_string ("case_normalize_struc_formula :: CHECK POINT 0.5 ==> f = " ^ Iprinter.string_of_struc_formula f ^ "\n") in *)
  let nf = IF.float_out_thread_struc_formula nf in
  (* let _ = print_string ("case_normalize_struc_formula :: CHECK POINT 1 ==> nf = " ^ Iprinter.string_of_struc_formula nf ^ "\n") in *)
  let nf = IF.float_out_exps_from_heap_struc nf in
  (* let _ = print_string ("case_normalize_struc_formula :: CHECK POINT 2 ==> nf = " ^ Iprinter.string_of_struc_formula nf ^ "\n") in *)
  let nf = IF.float_out_struc_min_max nf in
  (* let _ = print_string ("case_normalize_struc_formula :: CHECK POINT 3 ==> nf = " ^ Iprinter.string_of_struc_formula nf ^ "\n") in *)

  (*let _ = print_string ("\n b rename "^(Iprinter.string_of_struc_formula "" nf))in*)
  let nf = IF.rename_bound_var_struc_formula nf in
  (* let _ = print_string ("\n after ren: "^(Iprinter.string_of_struc_formula  nf)^"\n") in *)
  (*convert anonym to exists*)
  let rec helper (h:(ident*primed) list) strad_vs vars (f0:IF.struc_formula):IF.struc_formula* ((ident*primed)list) = 
	let diff = Gen.BList.difference_eq (=) in
	let rdups = Gen.BList.remove_dups_eq (=) in
	let inters = Gen.BList.intersect_eq (=)  in
    match f0 with
      | IF.EAssume (b,y)-> 
            let onb = convert_anonym_to_exist b in
            let hp = rdups (h@p)in
            let nb,nh,_ = case_normalize_renamed_formula prog hp strad_vs onb in
            let nb = ilinearize_formula nb hp in
            let vars_list = IF.all_fv nb in
            let nb = IF.prune_exists nb vars in (* Remove exists_vars included in infer_vars *) 
	        (IF.EAssume (nb,y),(diff vars_list p)) 
      | IF.ECase b->
            let r1,r2 = List.fold_left (fun (a1,a2)(c1,c2)->
                let r12 = inters (Ipure.fv c1) h in
                let r21,r22 = helper h strad_vs vars c2 in
                (((c1,r21)::a1),r12::r22::a2)
            ) ([],[]) b.IF.formula_case_branches in				
            (IF.ECase {b with IF.formula_case_branches = r1 },rdups (List.concat r2))
      | IF.EBase b->		
            let init_expl = b.IF.formula_struc_explicit_inst in
            let _ = if (List.length (inters h init_expl))>0 then 
              Error.report_error {Error.error_loc = b.IF.formula_struc_pos;
              Error.error_text = "the late instantiation variables collide with the used vars"}
            else true in
            let onb = convert_anonym_to_exist b.IF.formula_struc_base in
            let nb,h3,new_expl = case_normalize_renamed_formula prog h strad_vs onb in
            let all_expl = rdups (new_expl @ init_expl) in
            let new_strad_vs = diff strad_vs new_expl in   
            let all_vars = rdups (h@all_expl) in          
            let posib_impl = diff(IF.heap_fv onb) all_vars in
            let h1prm = rdups (all_vars@posib_impl) in
            let _ = if (not allow_primes)&&(List.length (List.filter (fun (c1,c2)-> c2==Primed) (all_expl@posib_impl)))>0 then
              Error.report_error {Error.error_loc = b.IF.formula_struc_pos; Error.error_text = "should not have prime vars"} else () in
            let _ = if (List.length (inters (all_expl@posib_impl) p))>0 then 	
              Error.report_error {Error.error_loc = b.IF.formula_struc_pos; Error.error_text = "post variables should not appear here"} else () in
            let nc,h2 = match b.IF.formula_struc_continuation with | None-> (None,[]) | Some l-> let r1,r2 = helper h1prm new_strad_vs vars l in (Some r1,r2) in
            let implvar = diff (IF.unbound_heap_fv onb) all_vars in
            let _ = if (List.length (diff implvar (IF.heap_fv onb @ fold_opt IF.struc_hp_fv nc)))>0 then 
              Error.report_error {Error.error_loc = b.IF.formula_struc_pos; Error.error_text = ("malfunction: some implicit vars are not heap_vars\n")} else true in
            (IF.EBase {
                IF.formula_struc_base = nb;
                IF.formula_struc_implicit_inst =implvar;					
                IF.formula_struc_explicit_inst = all_expl;
                IF.formula_struc_exists = [];
                IF.formula_struc_continuation = nc;
                IF.formula_struc_pos = b.IF.formula_struc_pos},rdups (h2@h3))
      | IF.EInfer b -> (* Tricky thing *)
        (IF.EInfer {b with IF.formula_inf_continuation = fst (helper h strad_vs b.IF.formula_inf_vars b.IF.formula_inf_continuation)}, [])
	  | IF.EList b -> 
		let ll1, ll2 = map_l_snd_res (helper h strad_vs vars) b in	  
		(IF.EList ll1, rdups (List.concat ll2))
	  | IF.EOr b-> 
			let f1,l1 = helper h strad_vs vars b.IF.formula_struc_or_f1 in
			let f2,l2 = helper h strad_vs vars b.IF.formula_struc_or_f2 in
			(IF.EOr {b with IF.formula_struc_or_f1 = f1; IF.formula_struc_or_f2 = f2;},rdups (l1@l2))
		in	
  (helper h strad_vs [] nf)
      
and case_normalize_coerc prog (cd: Iast.coercion_decl):Iast.coercion_decl = 
  let nch = case_normalize_formula prog [] cd.Iast.coercion_head in
  let ncb = case_normalize_formula prog [] cd.Iast.coercion_body in
  { Iast.coercion_type = cd.Iast.coercion_type;
  Iast.coercion_name = cd.Iast.coercion_name;
  Iast.coercion_head = nch;
  Iast.coercion_body = ncb;
  Iast.coercion_proof = cd.Iast.coercion_proof}
      
and ren_list_concat (l1:((ident*ident) list)) (l2:((ident*ident) list)):((ident*ident) list) = 
  let fl2 = fst (List.split l2) in
  let nl1 = List.filter (fun (c1,c2)-> not (List.mem c1 fl2)) l1 in (nl1@l2)

and subid (ren:(ident*ident) list) (i:ident) :ident = 
  let nl = List.filter (fun (c1,c2)-> (String.compare c1 i)==0) ren in
  if (List.length nl )> 0 then let _,l2 = List.hd nl in l2
  else i 			
    
and rename_exp (ren:(ident*ident) list) (f:Iast.exp):Iast.exp = 
  
  let rec helper (ren:(ident*ident) list) (f:Iast.exp):Iast.exp =   match f with
    | Iast.Label (pid, b) -> Iast.Label (pid, (helper ren b))
    | Iast.Assert b ->
          let subst_list = 
            List.fold_left(fun a (c1,c2)-> ((c1,Unprimed),(c2,Unprimed))::((c1,Primed),(c2,Primed))::a) [] ren in
          let assert_formula = match b.Iast.exp_assert_asserted_formula with
			| None -> None
			| Some (f1,f2)-> Some (IF.subst_struc subst_list f1,f2) in
          let assume_formula = match b.Iast.exp_assert_assumed_formula with
			| None -> None
			| Some f -> Some (IF.subst subst_list f) in
          (*let r =*) Iast.Assert{
              Iast.exp_assert_asserted_formula = assert_formula;
		      Iast.exp_assert_assumed_formula = assume_formula;
		      Iast.exp_assert_pos = b.Iast.exp_assert_pos;
		      Iast.exp_assert_path_id = b.Iast.exp_assert_path_id} (*in
                                                                     let _ = print_string (" before ren assert: "^(Iprinter.string_of_exp f)^"\n") in 
                                                                     let _ = print_string (" after ren assert: "^(Iprinter.string_of_exp r)^"\n") in 
                                                                     r*)
	| Iast.ArrayAt b->
          Iast.ArrayAt	{  Iast.exp_arrayat_array_base = helper ren b.Iast.exp_arrayat_array_base; (* substitute the new name for array name if it is in ren *)
          Iast.exp_arrayat_index = List.map (helper ren) b.Iast.exp_arrayat_index;
          Iast.exp_arrayat_pos = b.Iast.exp_arrayat_pos}
    | Iast.Assign b->
          Iast.Assign	{  Iast.exp_assign_op = b.Iast.exp_assign_op;
          Iast.exp_assign_lhs = helper ren b.Iast.exp_assign_lhs;
          Iast.exp_assign_rhs = helper ren b.Iast.exp_assign_rhs;
          Iast.exp_assign_path_id = b.Iast.exp_assign_path_id;
          Iast.exp_assign_pos = b.Iast.exp_assign_pos}
	| Iast.Barrier b -> Iast.Barrier{b with Iast.exp_barrier_recv = subid ren b.Iast.exp_barrier_recv}
    | Iast.Binary b->
          Iast.Binary { b with  
              Iast.exp_binary_oper1 = helper ren b.Iast.exp_binary_oper1;
              Iast.exp_binary_oper2 = helper ren b.Iast.exp_binary_oper2;}
    | Iast.Bind b->
          let nren = ren_list_concat ren (List.map (fun c-> (c,Ipure.fresh_old_name c)) b.Iast.exp_bind_fields) in	 
          let new_bound_var = subid ren b.Iast.exp_bind_bound_var in
          Iast.Bind { b with 
              Iast.exp_bind_bound_var = new_bound_var;
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
	| Iast.Catch b-> Iast.Catch {b with
          Iast.exp_catch_flow_var = (match b.Iast.exp_catch_flow_var with | None-> None |Some e-> Some (subid ren e));
          Iast.exp_catch_var = (match b.Iast.exp_catch_var with | None-> None |Some e-> Some (subid ren e));
          Iast.exp_catch_body = helper ren b.Iast.exp_catch_body;}
    | Iast.Cast b -> Iast.Cast{b with Iast.exp_cast_body =  helper ren b.Iast.exp_cast_body}
    | Iast.Cond b -> Iast.Cond {b with 
		  Iast.exp_cond_condition = helper ren b.Iast.exp_cond_condition;
		  Iast.exp_cond_then_arm = helper ren b.Iast.exp_cond_then_arm;
		  Iast.exp_cond_else_arm = helper ren b.Iast.exp_cond_else_arm}	  
	| Iast.Finally b-> Iast.Finally {b with Iast.exp_finally_body = helper ren b.Iast.exp_finally_body}
    | Iast.Member b ->
          Iast.Member {b with 
              Iast.exp_member_base = helper ren b.Iast.exp_member_base;
              Iast.exp_member_fields = List.map (subid ren ) b.Iast.exp_member_fields}
		      (* An Hoa *)
	| Iast.ArrayAlloc b-> 
          Iast.ArrayAlloc {b with Iast.exp_aalloc_dimensions = List.map (helper ren) b.Iast.exp_aalloc_dimensions}
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
    | Iast.While b-> 
          let nw = match b.Iast.exp_while_wrappings with
            | None -> None
            | Some (e,l) -> Some ((rename_exp ren e),l)  in
          Iast.While{
              Iast.exp_while_condition = rename_exp ren b.Iast.exp_while_condition;
              Iast.exp_while_body = rename_exp ren b.Iast.exp_while_body;
              Iast.exp_while_jump_label = b.Iast.exp_while_jump_label;
              Iast.exp_while_f_name = b.Iast.exp_while_f_name;
              Iast.exp_while_wrappings = nw;
              Iast.exp_while_specs = IF.subst_struc (List.fold_left(fun a (c1,c2)-> ((c1,Unprimed),(c2,Unprimed))::((c1,Primed),(c2,Primed))::a) [] ren) b.Iast.exp_while_specs;
              Iast.exp_while_path_id = b.Iast.exp_while_path_id;
              Iast.exp_while_pos = b.Iast.exp_while_pos;}
    | Iast.Time _ ->f
    | Iast.Try b -> 
          Iast.Try { b with
              Iast.exp_try_block = rename_exp ren b.Iast.exp_try_block;
              Iast.exp_catch_clauses = List.map (rename_exp ren) b.Iast.exp_catch_clauses;
              Iast.exp_finally_clause = List.map (rename_exp ren) b.Iast.exp_finally_clause;}
    | Iast.Raise b-> 
          Iast.Raise {b with
              Iast.exp_raise_val = (match b.Iast.exp_raise_val with 
                | None -> None 
                | Some e -> Some (rename_exp ren e));
              Iast.exp_raise_type = (match b.Iast.exp_raise_type with
                | Iast.Const_flow _ -> b.Iast.exp_raise_type
                | Iast.Var_flow vf -> Iast.Var_flow (subid ren vf))} in
  helper ren f 


and case_rename_var_decls (f:Iast.exp) : (Iast.exp * ((ident*ident) list)) =  match f with
  | Iast.Assert _ -> (f,[])
  | Iast.Assign b -> 
        (Iast.Assign{ Iast.exp_assign_op = b.Iast.exp_assign_op;
        Iast.exp_assign_lhs = fst(case_rename_var_decls b.Iast.exp_assign_lhs);
        Iast.exp_assign_rhs = fst(case_rename_var_decls b.Iast.exp_assign_rhs);
        Iast.exp_assign_path_id = b.Iast.exp_assign_path_id;
        Iast.exp_assign_pos = b.Iast.exp_assign_pos},[])
  | Iast.Binary b->
        (Iast.Binary {Iast.exp_binary_op = b.Iast.exp_binary_op;
        Iast.exp_binary_oper1 = fst (case_rename_var_decls b.Iast.exp_binary_oper1);
        Iast.exp_binary_oper2 = fst (case_rename_var_decls b.Iast.exp_binary_oper2);
        Iast.exp_binary_path_id = b.Iast.exp_binary_path_id;
        Iast.exp_binary_pos = b.Iast.exp_binary_pos},[])
  | Iast.Bind b ->
        (Iast.Bind {b with Iast.exp_bind_body = fst (case_rename_var_decls b.Iast.exp_bind_body)},[])  
  | Iast.Block b->
        (Iast.Block { b with Iast.exp_block_body = fst (case_rename_var_decls b.Iast.exp_block_body)},[])
            
  | Iast.Continue _  | Iast.Debug _ | Iast.Dprint _ | Iast.Empty _ 
  | Iast.FloatLit _  | Iast.IntLit _  | Iast.Java _  | Iast.BoolLit _
  | Iast.Null _   | Iast.Unfold _  | Iast.Var _ | Iast.This _  | Iast.Time _
  | Iast.Break _ | Iast.Barrier _ -> (f,[])  
  | Iast.CallNRecv b ->
        let nl = List.map (fun c-> fst (case_rename_var_decls c)) b.Iast.exp_call_nrecv_arguments in
        (Iast.CallNRecv{b with Iast.exp_call_nrecv_arguments = nl },[]) 
  | Iast.CallRecv b->
        let nl = List.map (fun c-> fst (case_rename_var_decls c)) b.Iast.exp_call_recv_arguments in
        (Iast.CallRecv{b with 
            Iast.exp_call_recv_receiver = fst (case_rename_var_decls b.Iast.exp_call_recv_receiver);
            Iast.exp_call_recv_arguments = nl},[])
  | Iast.Cast b->
        (Iast.Cast {b with Iast.exp_cast_body= fst (case_rename_var_decls b.Iast.exp_cast_body)},[])
  | Iast.Catch b->
		let ncv,ren = match b.Iast.exp_catch_var with
          | None -> (None,[])
          | Some e-> 
                let nn = (Ipure.fresh_old_name e) in
                ((Some nn),[(e,nn)])in
        let ncfv,ren = match b.Iast.exp_catch_flow_var with
          | None -> (None,ren)
          | Some e-> 
                let nn = (Ipure.fresh_old_name e) in
                ((Some nn),(e,nn)::ren)in								
        (Iast.Catch{b with 
            Iast.exp_catch_var = ncv ;
            Iast.exp_catch_flow_type = b.Iast.exp_catch_flow_type;
            Iast.exp_catch_flow_var = ncfv;
            Iast.exp_catch_body = fst (case_rename_var_decls (rename_exp ren b.Iast.exp_catch_body));},[])
  | Iast.Cond b->
        let ncond,r = case_rename_var_decls b.Iast.exp_cond_condition in	
        (Iast.Cond {b with 
            Iast.exp_cond_condition= ncond;
            Iast.exp_cond_then_arm= fst (case_rename_var_decls b.Iast.exp_cond_then_arm);
            Iast.exp_cond_else_arm= fst (case_rename_var_decls b.Iast.exp_cond_else_arm);},r)
  | Iast.ConstDecl b->
        let ndecl,nren = List.fold_left (fun (a1,a2) (c1,c2,c3)-> 
            let nn = (Ipure.fresh_old_name c1) in
            let ne,_ = case_rename_var_decls c2 in
            ((nn,ne,c3)::a1,(c1,nn)::a2)) ([],[]) b.Iast.exp_const_decl_decls in
        (Iast.ConstDecl {b with Iast.exp_const_decl_decls = ndecl;},nren)
  | Iast.Finally b -> (Iast.Finally {b with Iast.exp_finally_body = fst(case_rename_var_decls b.Iast.exp_finally_body)},[])
  | Iast.Label (pid,b)-> (Iast.Label (pid, fst (case_rename_var_decls b)),[])
  | Iast.Member b ->
        (Iast.Member {b with Iast.exp_member_base = fst (case_rename_var_decls b.Iast.exp_member_base)},[]) 
  | Iast.ArrayAlloc b->
        let nl = List.map (fun c-> fst (case_rename_var_decls c)) b.Iast.exp_aalloc_dimensions in
        (Iast.ArrayAlloc  {b with Iast.exp_aalloc_dimensions =nl},[])
  | Iast.ArrayAt b -> 
		let new_index = List.map (fun c-> fst (case_rename_var_decls c)) b.Iast.exp_arrayat_index in
        (Iast.ArrayAt { Iast.exp_arrayat_array_base = b.Iast.exp_arrayat_array_base;
        Iast.exp_arrayat_index = new_index;
        Iast.exp_arrayat_pos = b.Iast.exp_arrayat_pos},[])
  | Iast.New b->
        let nl = List.map (fun c-> fst (case_rename_var_decls c)) b.Iast.exp_new_arguments in
        (Iast.New  {b with Iast.exp_new_arguments =nl},[])
  | Iast.Return b -> 
        (Iast.Return {b with Iast.exp_return_val= match b.Iast.exp_return_val with 
          | None -> None 
          | Some f -> Some (fst (case_rename_var_decls f))},[])
  | Iast.Seq b -> 
        let l1,ren = case_rename_var_decls b.Iast.exp_seq_exp1 in
        let l2,ren2 = case_rename_var_decls b.Iast.exp_seq_exp2 in          
        let l2 = rename_exp ren l2 in      
        let aux_ren = (ren_list_concat ren ren2) in
        (Iast.Seq ({ Iast.exp_seq_exp1 = l1; Iast.exp_seq_exp2 = l2; Iast.exp_seq_pos = b.Iast.exp_seq_pos }),aux_ren)
  | Iast.Unary b -> 
        (Iast.Unary {b with Iast.exp_unary_exp = fst (case_rename_var_decls b.Iast.exp_unary_exp)},[])
  | Iast.VarDecl b -> 		
        let ndecl,nren = List.fold_left (fun (a1,a2) (c1,c2,c3)->
            let nn = (Ipure.fresh_old_name c1) in
            let ne = match c2 with
              | None -> None 
              | Some f-> Some (fst (case_rename_var_decls f)) in
            ((nn,ne,c3)::a1,(c1,nn)::a2)) ([],[]) b.Iast.exp_var_decl_decls in
        (Iast.VarDecl {b with Iast.exp_var_decl_decls = ndecl;},nren)		
  | Iast.While b->
        (Iast.While {b with 
            Iast.exp_while_condition= fst (case_rename_var_decls b.Iast.exp_while_condition); 
            Iast.exp_while_body= fst (case_rename_var_decls b.Iast.exp_while_body);},[])
  | Iast.Try b-> 
        let nfl = List.map (fun c-> fst(case_rename_var_decls c)) b.Iast.exp_finally_clause in
        (Iast.Try {b with 
            Iast.exp_try_block = fst (case_rename_var_decls b.Iast.exp_try_block);
            Iast.exp_catch_clauses = List.map (fun c-> fst (case_rename_var_decls c))b.Iast.exp_catch_clauses;
            Iast.exp_finally_clause = nfl;
        },[])
  | Iast.Raise b-> (Iast.Raise {b with 
		Iast.exp_raise_val = match b.Iast.exp_raise_val with
		  | None -> None
		  | Some e -> Some (fst (case_rename_var_decls e))},[])


and err_prim_l_vars s l pos= 
  List.iter (fun (c1,c2)-> match c2 with
    | Primed  -> Error.report_error { 
          Error.error_loc = pos;
          Error.error_text = c1^"' "^s}
    | Unprimed -> () ) l
      
and check_eprim_in_formula s f = match f with
  | IF.Or o -> (check_eprim_in_formula s o.IF.formula_or_f1; check_eprim_in_formula s o.IF.formula_or_f2 )
  | IF.Base b-> ()
  | IF.Exists e-> err_prim_l_vars s e.IF.formula_exists_qvars e.IF.formula_exists_pos
        
and check_eprim_in_struc_formula s f = match f with
    | IF.ECase b-> List.iter (fun (_,c2)-> check_eprim_in_struc_formula s c2) b.IF.formula_case_branches
    | IF.EBase b-> 
          (err_prim_l_vars s b.IF.formula_struc_exists b.IF.formula_struc_pos; 
          check_eprim_in_formula s b.IF.formula_struc_base;
          match b.IF.formula_struc_continuation with | None-> () | Some l-> check_eprim_in_struc_formula s l)
    | IF.EAssume (b,_) -> check_eprim_in_formula " is not a ref param " b
    | IF.EInfer b -> check_eprim_in_struc_formula s b.IF.formula_inf_continuation
	| IF.EList b -> List.iter (fun (_,c)-> check_eprim_in_struc_formula s c) b
	| IF.EOr b -> check_eprim_in_struc_formula s b.IF.formula_struc_or_f1; check_eprim_in_struc_formula s b.IF.formula_struc_or_f2

and case_normalize_exp prog (h: (ident*primed) list) (p: (ident*primed) list)(f:Iast.exp) :
      Iast.exp*((ident*primed) list)*((ident*primed) list) =  match f with
        | Iast.Assert b->
              let asrt_nf,nh = match b.Iast.exp_assert_asserted_formula with
                | None -> (None,h)
                | Some asserted_f -> 
                      let r, _ = case_normalize_struc_formula prog h p (fst asserted_f) true false [] in
                      let _ = check_eprim_in_struc_formula " is not a valid program variable " r in
                      (Some (r,(snd asserted_f)),h) in
              let assm_nf  = match b.Iast.exp_assert_assumed_formula with
                | None-> None 
                | Some f -> 
                      let r = case_normalize_formula prog nh f in 
                      let _ = check_eprim_in_formula " is not a valid program variable " r in
                      Some r in
              let rez_assert = Iast.Assert { Iast.exp_assert_asserted_formula = asrt_nf;
              Iast.exp_assert_assumed_formula = assm_nf;
              Iast.exp_assert_pos = b.Iast.exp_assert_pos;
              Iast.exp_assert_path_id = b.Iast.exp_assert_path_id;} in
              (rez_assert, h, p)
		| Iast.Assign b-> 
              let l1,_,_ = case_normalize_exp prog h p b.Iast.exp_assign_lhs in
              let l2,_,_ = case_normalize_exp prog h p b.Iast.exp_assign_rhs in
              (Iast.Assign{ Iast.exp_assign_op = b.Iast.exp_assign_op;
              Iast.exp_assign_lhs = l1;
              Iast.exp_assign_rhs = l2;
              Iast.exp_assign_path_id = b.Iast.exp_assign_path_id;
              Iast.exp_assign_pos = b.Iast.exp_assign_pos},h,p)
        | Iast.Binary b->
              let l1,_,_ = case_normalize_exp prog h p b.Iast.exp_binary_oper1 in
              let l2,_,_ = case_normalize_exp prog h p b.Iast.exp_binary_oper2 in
              (Iast.Binary {Iast.exp_binary_op = b.Iast.exp_binary_op;
              Iast.exp_binary_oper1 = l1;
              Iast.exp_binary_oper2 = l2;
              Iast.exp_binary_path_id = b.Iast.exp_binary_path_id;
              Iast.exp_binary_pos = b.Iast.exp_binary_pos},h,p)
        | Iast.Bind b ->
              let r,nh,np =   case_normalize_exp prog h p b.Iast.exp_bind_body in
              (Iast.Bind {b with Iast.exp_bind_body =r},h,p)  
        | Iast.Block b->
              let r,_,_ = case_normalize_exp prog h p b.Iast.exp_block_body in
              (Iast.Block { b with Iast.exp_block_body = r},h,p)
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
        | Iast.Time _
        | Iast.Break _
		| Iast.Barrier _ -> (f,h,p)
        | Iast.CallNRecv b ->
              let nl = List.map (fun c-> let r1,_,_ = case_normalize_exp prog h p c in r1) b.Iast.exp_call_nrecv_arguments in
              (Iast.CallNRecv{b with Iast.exp_call_nrecv_arguments = nl },h,p) 
        | Iast.CallRecv b->
              let a1,_,_ = case_normalize_exp prog h p b.Iast.exp_call_recv_receiver in
              let nl = List.map (fun c-> let r1,_,_ = case_normalize_exp prog h p c in r1) b.Iast.exp_call_recv_arguments in
              (Iast.CallRecv{b with 
                  Iast.exp_call_recv_receiver = a1;
                  Iast.exp_call_recv_arguments = nl},h,p)
        | Iast.Cast b->
              let nb,_,_ = case_normalize_exp prog h p b.Iast.exp_cast_body in
              (Iast.Cast {b with Iast.exp_cast_body= nb},h,p)
	    | Iast.Catch b ->
	          let ncv,nh,np = match b.Iast.exp_catch_var with
                | None -> (None,h,p)
                | Some e-> ((Some e),(e,Primed)::h,(e,Primed)::p)in
              let ncfv,nh,np = match b.Iast.exp_catch_flow_var with
                | None -> (None,nh,np)
                | Some e->
                      ((Some e),(e,Primed)::nh,(e,Primed)::np) in	
              let nb,nh,np = case_normalize_exp prog nh np b.Iast.exp_catch_body in									
              (Iast.Catch {b with 
                  Iast.exp_catch_var = ncv ;
                  Iast.exp_catch_flow_type = b.Iast.exp_catch_flow_type;
                  Iast.exp_catch_flow_var = ncfv;
                  Iast.exp_catch_body = nb;},nh,np)
	              
        | Iast.Cond b->
              let ncond,_,_ = case_normalize_exp prog h p b.Iast.exp_cond_condition in	
              let nthen,_,_ = case_normalize_exp prog h p b.Iast.exp_cond_then_arm in
              let nelse,_,_ = case_normalize_exp prog h p b.Iast.exp_cond_else_arm in
              (Iast.Cond {b with 
                  Iast.exp_cond_condition= ncond;
                  Iast.exp_cond_then_arm= nthen;
                  Iast.exp_cond_else_arm= nelse;},h,p)
        | Iast.ConstDecl b->
              let ndecl = List.fold_left (fun a1 (c1,c2,c3)-> 
                  let ne,_,_ = case_normalize_exp prog h p c2 in
                  (c1,ne,c3)::a1) [] b.Iast.exp_const_decl_decls in
              let nvl = List.map (fun (c1,_,_)-> c1) ndecl in
              let nvlprm = List.map (fun c-> (c,Primed)) nvl in
              let nh = nvlprm@h in
              let np = (List.map (fun c->(c,Primed))nvl)@p in
              (Iast.ConstDecl {b with Iast.exp_const_decl_decls = ndecl;},nh,np)
	    | Iast.Finally b-> 
		      let nf,h,p = case_normalize_exp prog h p b.Iast.exp_finally_body in
		      (Iast.Finally {b with Iast.exp_finally_body= nf},h,p)
        | Iast.Label (pid,b)-> 
              let nb,_,_ =  case_normalize_exp prog h p b in 
              (Iast.Label (pid, nb),h,p)
        | Iast.Member b ->
              let nb,_,_ = case_normalize_exp prog h p b.Iast.exp_member_base in
              (Iast.Member {b with Iast.exp_member_base = nb},h,p) 
        | Iast.ArrayAlloc b-> (* An Hoa *)
              let nl = List.map (fun c-> let r1,_,_ = case_normalize_exp prog h p c in r1) b.Iast.exp_aalloc_dimensions in
              (Iast.ArrayAlloc  {b with Iast.exp_aalloc_dimensions =nl},h,p)
		| Iast.ArrayAt b-> 
			  let new_index = List.map (fun c-> let r1,_,_ = case_normalize_exp prog h p c in r1) b.Iast.exp_arrayat_index in
              (Iast.ArrayAt { Iast.exp_arrayat_array_base = b.Iast.exp_arrayat_array_base;
              Iast.exp_arrayat_index = new_index;
              Iast.exp_arrayat_pos = b.Iast.exp_arrayat_pos},h,p)
		| Iast.New b->
              let nl = List.map (fun c-> let r1,_,_ = case_normalize_exp prog h p c in r1) b.Iast.exp_new_arguments in
              (Iast.New  {b with Iast.exp_new_arguments =nl},h,p)
        | Iast.Return b -> 
              (Iast.Return {b with Iast.exp_return_val= match b.Iast.exp_return_val with | None -> None | Some f -> 
                  let r,_,_ = (case_normalize_exp prog h p f) in Some r},h,p)
        | Iast.Seq b -> 
              let l1,nh,np = case_normalize_exp prog h p b.Iast.exp_seq_exp1 in
              let l2 ,nh,np = case_normalize_exp prog nh np b.Iast.exp_seq_exp2 in          
              (Iast.Seq ({ Iast.exp_seq_exp1 = l1; Iast.exp_seq_exp2 = l2; Iast.exp_seq_pos = b.Iast.exp_seq_pos }), nh, np)
        | Iast.Unary b -> 
              let l1,_,_ = case_normalize_exp prog h p b.Iast.exp_unary_exp in
              (Iast.Unary {b with Iast.exp_unary_exp = l1},h,p)
        | Iast.VarDecl b -> 		
              let ndecl = List.fold_left (fun a1 (c1,c2,c3)->
                  let ne = match c2 with
                    | None -> None 
                    | Some f-> let ne,_,_ = case_normalize_exp prog h p f in Some ne in
                  (c1,ne,c3)::a1) [] b.Iast.exp_var_decl_decls in
              let nvl = List.map (fun (c1,_,_)-> c1) ndecl in
              let nvlprm = List.map (fun c-> (c,Primed)) nvl in
              let nh = nvlprm@h in
              let np = (List.map (fun c->(c,Primed))nvl)@p in
              (Iast.VarDecl {b with Iast.exp_var_decl_decls = ndecl;},nh,np)		
        | Iast.While b->
              let nc,nh,np = case_normalize_exp prog h p b.Iast.exp_while_condition in
              let nb,nh,np = case_normalize_exp prog nh np b.Iast.exp_while_body in
              (*let strad = 
                let pr,pst = IF.struc_split_fv b.Iast.exp_while_specs false in
                Gen.BList.intersect_eq (=) pr pst in*)
              (*let ns,_ = case_normalize_struc_formula prog h p b.Iast.exp_while_specs false false strad in*)
              (Iast.While {b with Iast.exp_while_condition=nc; Iast.exp_while_body=nb;(*Iast.exp_while_specs = ns*)},h,p)
        | Iast.Try b-> 
              let nb,nh,np = case_normalize_exp prog h p b.Iast.exp_try_block in
		      let f l =  List.map (fun c-> let nf,_,_ = case_normalize_exp prog nh np c in nf) l in
              (Iast.Try {b with 
                  Iast.exp_try_block = nb;
                  Iast.exp_catch_clauses = f b.Iast.exp_catch_clauses;
                  Iast.exp_finally_clause = f b.Iast.exp_finally_clause;
              },h,p)
        | Iast.Raise b-> (Iast.Raise {b with 
			  Iast.exp_raise_val = (match b.Iast.exp_raise_val with
				| None -> None
				| Some e -> let nc,_,_ = (case_normalize_exp prog h p e) in
				  Some nc)},h,p)

and case_normalize_data prog (f:Iast.data_decl):Iast.data_decl =
  let h = List.map (fun f -> (I.get_field_name f,Unprimed) ) f.Iast.data_fields in  
  {f with Iast.data_invs = List.map (case_normalize_formula prog h) f.Iast.data_invs}

and case_normalize_proc prog (f:Iast.proc_decl):Iast.proc_decl =
  let pr = Iprinter.string_of_proc_decl in
  Debug.no_1 "case_normalize_proc" pr pr
      (fun _ -> case_normalize_proc_x prog f) f

and case_normalize_proc_x prog (f:Iast.proc_decl):Iast.proc_decl = 
  let gl_v_l = List.map (fun c-> List.map (fun (v,_,_)-> (c.I.exp_var_decl_type,v)) c.I.exp_var_decl_decls) prog.I.prog_global_var_decls in
  let gl_v =  List.map (fun (c1,c2)-> {I.param_type = c1; I.param_name = c2; I.param_mod = I.RefMod; I.param_loc = no_pos })(List.concat gl_v_l) in
  let gl_proc_args = gl_v@ f.Iast.proc_args in
  let h = (List.map (fun c1-> (c1.Iast.param_name,Unprimed)) gl_proc_args) in
  let h_prm = (List.map (fun c1-> (c1.Iast.param_name,Primed)) gl_proc_args) in
  let p = (eres_name,Unprimed)::(res_name,Unprimed)::(List.map (fun c1-> (c1.Iast.param_name,Primed)) (List.filter (fun c-> c.Iast.param_mod == Iast.RefMod) gl_proc_args)) in
  let strad_s = 
    let pr,pst = IF.struc_split_fv f.Iast.proc_static_specs false in
    Gen.BList.intersect_eq (=) pr pst in
  let nst,h11 = case_normalize_struc_formula prog h p f.Iast.proc_static_specs false false strad_s in
  let _ = check_eprim_in_struc_formula " is not allowed in precond " nst in 
  let strad_d = 
    let pr,pst = IF.struc_split_fv f.Iast.proc_static_specs false in
    Gen.BList.intersect_eq (=) pr pst in
  let ndn, h12 = case_normalize_struc_formula prog h p f.Iast.proc_dynamic_specs false false strad_d in
  let _ = check_eprim_in_struc_formula "is not allowed in precond " ndn in
  let h1 = Gen.BList.remove_dups_eq (=) (h11@h12) in 
  let h2 = Gen.BList.remove_dups_eq (=) (h@h_prm@(Gen.BList.difference_eq (=) h1 h)@ (IF.struc_free_vars true nst)) in
  let nb = match f.Iast.proc_body with 
      None -> None 
    | Some f->
          let f,_ = case_rename_var_decls f in
          let r,_,_ = (case_normalize_exp prog h2 [(eres_name,Unprimed);(res_name,Unprimed)] f) in
          Some r in
  {f with Iast.proc_static_specs =nst;
      Iast.proc_dynamic_specs = ndn;			
      Iast.proc_body = nb;
  }

and case_normalize_barrier_x prog bd = 
   (*let lv = bd.I.barrier_shared_vars in
   let u = (self,Unprimed)::(List.map (fun (_,c)-> (c,Unprimed)) lv) in
   let p = (self,Primed)::(List.map (fun (_,c)-> (c,Primed)) lv) in*)
   let u = [(self,Unprimed)] in
   let p = [(self,Primed)] in
   let fct f = fst (case_normalize_struc_formula prog u p f false false []) in
  {bd with I.barrier_tr_list = List.map (fun (f,t,sp)-> (f,t,List.map fct sp)) bd.I.barrier_tr_list}
   
and case_normalize_barrier prog bd =    
	let pr_in = Iprinter.string_of_barrier_decl in
	Debug.no_1 "case_normalize_barrier " pr_in pr_in (case_normalize_barrier_x prog) bd
  
   
(* AN HOA : WHAT IS THIS FUNCTION SUPPOSED TO DO ? *)
and case_normalize_program (prog: Iast.prog_decl):Iast.prog_decl =
  Debug.no_1 "case_normalize_program" (Iprinter.string_of_program) (Iprinter.string_of_program) case_normalize_program_x prog
	  
and case_normalize_program_x (prog: Iast.prog_decl):Iast.prog_decl=
  let tmp_views = (* order_views *) prog.I.prog_view_decls in
  (*let _ = print_string ("case_normalize_program: view_b: " ^ (Iprinter.string_of_view_decl_list tmp_views)) in*)
  let tmp_views = List.map (fun c-> 
	  let h = (self,Unprimed)::(eres_name,Unprimed)::(res_name,Unprimed)::(List.map (fun c-> (c,Unprimed)) c.Iast.view_vars ) in
	  let p = (self,Primed)::(eres_name,Primed)::(res_name,Primed)::(List.map (fun c-> (c,Primed)) c.Iast.view_vars ) in
	  let wf,_ = case_normalize_struc_formula prog h p c.Iast.view_formula false false [] in
      let inv_lock = c.Iast.view_inv_lock in
      let inv_lock =
        (match inv_lock with
          | None -> None
          | Some f ->
              let new_f = case_normalize_formula prog p f in (* it has to be p to maintain self in the invariant*)
              Some new_f)
      in
      { c with Iast.view_formula = 	wf; Iast.view_inv_lock = inv_lock}) tmp_views in
  (*let _ = print_string ("case_normalize_program: view_a: " ^ (Iprinter.string_of_view_decl_list tmp_views)) in*)
  let prog = {prog with Iast.prog_view_decls = tmp_views} in
  let cdata = List.map (case_normalize_data prog) prog.I.prog_data_decls in
  let prog = {prog with Iast.prog_data_decls = cdata} in
  let procs1 = List.map (case_normalize_proc prog) prog.I.prog_proc_decls in
  let prog = {prog with Iast.prog_proc_decls = procs1} in
  let coer1 = List.map (case_normalize_coerc prog) prog.Iast.prog_coercion_decls in	 
  { prog with 
      Iast.prog_data_decls = cdata;
      Iast.prog_view_decls = tmp_views;
      Iast.prog_proc_decls = procs1;
      Iast.prog_coercion_decls = coer1;
	  Iast.prog_barrier_decls = List.map (case_normalize_barrier prog) prog.Iast.prog_barrier_decls;
  }

and prune_inv_inference_formula (cp:C.prog_decl) (v_l : CP.spec_var list) 
	  (init_form_lst: (CF.formula*formula_label) list) u_baga u_inv pos:
      ((Cpure.b_formula * (formula_label list)) list)* (C.ba_prun_cond list) *
      ((formula_label list * (Gen.Baga(CP.PtrSV).baga * Cpure.b_formula list) ) list)
      = 
  let pr1 = pr_list (fun (bf,fl) -> Cprinter.string_of_b_formula bf) in
  let pr ls = pr_list (fun (x,_)->Cprinter.string_of_formula x) ls in
  Debug.no_2 "prune_inv_inference_formula" Cprinter.string_of_spec_var_list pr
      (fun (lb,_,r) -> pr1 lb)
      (fun _ _ -> prune_inv_inference_formula_x cp v_l init_form_lst u_baga u_inv pos) v_l init_form_lst

and prune_inv_inference_formula_x (cp:C.prog_decl) (v_l : CP.spec_var list) (init_form_lst: (CF.formula*formula_label) list) u_baga u_inv pos: 
      ((Cpure.b_formula * (formula_label list)) list)* (C.ba_prun_cond list) *
      ((formula_label list * (Gen.Baga(CP.PtrSV).baga * Cpure.b_formula list)) list) = 
  (*print_string ("sent to case inf: "^(Cprinter.string_of_formula init_form)^"\n");*)
  (*aux functions for case inference*)
  let rec get_or_list (f: CF.formula):CF.formula list = match f with
    | CF.Base _
    | CF.Exists _ -> [f]
    | CF.Or o -> (get_or_list o.CF.formula_or_f1)@(get_or_list o.CF.formula_or_f2) in
  
  let rec get_pure_conj_list (f:CP.formula):(CP.formula * (bool*CP.b_formula) list) = match f with
    | CP.BForm (l,_) -> (CP.mkTrue no_pos , [(true,l)])
    | CP.And (f1,f2,_ )-> 
          let l1,l2 = (get_pure_conj_list f1) in
          let r1,r2 = (get_pure_conj_list f2) in
          (CP.mkAnd l1 r1 no_pos, l2@r2)
	| CP.AndList b-> 
		  let l1,l2 = map_l_snd_res get_pure_conj_list b in
		  (CP.mkAndList l1, List.concat l2) 
    | CP.Or _ -> (f,[])
    | CP.Not (nf,_,_) -> (match nf with
        |CP.BForm (l,_) ->(CP.mkTrue no_pos, [(false,l)]) 
        |_ ->(f,[]))
    | CP.Forall (_,ff,_,_) 
    | CP.Exists (_,ff,_,_) -> (f,[]) in
  

  let filter_pure_conj_list pc  =
    let r = List.filter (fun (c1,c2) ->
	    let (pf,_) = c2 in
	    match pf with 
          | CP.Lt _ | CP.Lte _ | CP.Gt _ | CP.Gte _ | CP.Eq _ 
          | CP.Neq _ | CP.BagIn _ | CP.BagNotIn _ | CP.ListIn _ 
          | CP.ListNotIn _ | CP.EqMax _ | CP.EqMin _-> c1 
          | _ -> false ) pc in
    let r = List.map (fun (c1,c2) ->
	    let (pf,il) = c2 in
        if c1 then match pf with
          | CP.Gt (e1,e2,l) -> (CP.Lt (e2,e1,l), il)
          | CP.Gte (e1,e2,l) -> (CP.Lte (e2,e1,l), il)
          | _ -> c2
        else match pf with
          | CP.Lt (e1,e2,l) -> (CP.Lte (e2,e1,l), il)
          | CP.Lte (e1,e2,l) -> (CP.Lt (e2,e1,l), il)
          | CP.Gt (e1,e2,l) -> (CP.Lte (e1,e2,l), il)
          | CP.Gte (e1,e2,l) -> (CP.Lt (e1,e2,l), il)
          | CP.Eq (e1,e2,l) ->  (CP.Neq (e1,e2,l), il)
          | CP.Neq (e1,e2,l) -> (CP.Eq (e1,e2,l), il)
          | CP.BagIn l -> (CP.BagNotIn l, il)
          | CP.BagNotIn l -> (CP.BagIn l, il)
          | CP.ListIn l -> (CP.ListNotIn l, il)
          | CP.ListNotIn l -> (CP.ListIn l, il)
          | _ -> c2) r  in
    let r = List.map (fun c ->
	    let (pf,il) = c in
	    match pf with
          | CP.Eq (e1,e2,l) -> (match e1,e2 with
              | CP.Var _ , CP.BagUnion(l,p) ->  
                    if (List.exists (fun c-> match c with | CP.Bag (l,p)-> (List.length l)>0 | _ -> false )l) then (CP.Neq (e1, CP.Bag ([],p),p), il)
                    else c
              | CP.BagUnion (l,p), CP.Var _ -> 
                    if (List.exists (fun c-> match c with | CP.Bag (l,p)-> (List.length l)>0 | _ -> false )l) then (CP.Neq (e2, CP.Bag ([],p),p), il)
                    else c 
              | CP.Var _ , CP.Bag (l,p) -> if (List.length l)>0 then (CP.Neq (e1, CP.Bag ([],p),p), il) else c
              | CP.Bag (l,p) , CP.Var _ -> if (List.length l)>0 then (CP.Neq (e2, CP.Bag ([],p),p), il) else c
              | _-> c) 
          | _ -> c) r in
    Gen.BList.remove_dups_eq CP.eq_b_formula_no_aset r in

  let filter_pure_conj_list pc =
    let pr1 = pr_list (fun (_,c)-> Cprinter.string_of_b_formula c) in
    let pr2 = pr_list Cprinter.string_of_b_formula in
    Debug.no_1 "filter_pure_conj_list" pr1 pr2 filter_pure_conj_list pc in

  let hull_invs v_l (f:CP.formula):CP.formula list =
    let rec helper acc e_v_l : CP.formula list = match e_v_l with
      | [] ->
            (*let _ = print_string ("\n pures:: "^(Cprinter.string_of_pure_formula (CP.mkExists acc f None no_pos))^"\n") in*)
            [TP.hull (CP.mkExists acc f None no_pos)]
      | h::t -> (helper acc t)@(helper (h::acc) t) in
    helper [] v_l in
  
  let hull_invs v_l (f:CP.formula):CP.formula list =
    let pr2 = Cprinter.string_of_pure_formula in
    let pr3 = pr_list Cprinter.string_of_pure_formula in
    Debug.no_2 "hull_invs" Cprinter.string_of_spec_var_list pr2  pr3 hull_invs v_l f in

  let compute_invariants v_l (pure_list:(formula_label * (CP.baga_sv * CP.b_formula list)) list) : (formula_label list * (CP.baga_sv * CP.b_formula list)) list= 
    let combine_pures (l1:CP.b_formula list) (l2:CP.b_formula list) :CP.b_formula list = 
      let split_neq l = List.partition (fun c1 ->
		  let (pf, il) = c1 in
		  match pf with | CP.Neq _ -> true | _ -> false) l in
      let l1_n, l1r = split_neq l1 in
      let l2_n, l2r = split_neq l2 in
      let to_be_added = Gen.BList.intersect_eq CP.eq_b_formula_no_aset l1_n l2_n in
      let lr = match (List.length l1r),(List.length l2r) with 
        | 0,0 | _,0 | 0,_ -> CP.mkTrue no_pos        
              (* | _,_ -> CP.mkOr  *)
              (* (List.fold_left (fun a c-> CP.mkAnd a (CP.BForm
                 (c,None)) no_pos) (CP.mkTrue no_pos) l1r) *)
              (*     (List.fold_left (fun a c-> CP.mkAnd a (CP.BForm (c,None)) no_pos) (CP.mkTrue no_pos) l2r) None no_pos in *)
              (* Cristian's fixes which seem very slow *)
        | _,_ ->
              let f1r = List.fold_left (fun a c-> CP.mkAnd a (CP.BForm (c,None)) no_pos) (CP.mkTrue no_pos) l1r in
              let f2r = List.fold_left (fun a c-> CP.mkAnd a (CP.BForm (c,None)) no_pos) (CP.mkTrue no_pos) l2r in
              let tpi = fun f1 f2 -> TP.imply f1 f2 "" false None in
              if ((fun (c,_,_)-> c) (tpi f1r f2r)) then f2r
              else if ((fun (c,_,_)-> c) (tpi f2r f1r)) then f1r
              else  CP.mkOr f1r f2r None no_pos in
      (*let _ = print_string ("before hull: "^(Cprinter.string_of_pure_formula lr)^"\n") in*)
      let lr = hull_invs v_l lr in
      (*let _ = print_string ("after hull: "^(String.concat " - " (List.map Cprinter.string_of_pure_formula lr))^"\n") in*)
      let lr = let rec r f = match f with
        | CP.BForm (l, _) -> [l]
        | CP.And (f1,f2,_) -> (r f1)@(r f2)
        | _ -> [] in 
      List.concat (List.map r lr) in  
      to_be_added @ (Gen.BList.remove_dups_eq CP.eq_b_formula_no_aset lr) in      
    let l = List.length pure_list in
    let start = List.map (fun (c1,c2) -> ([c1],c2)) pure_list in
    let all = 
      if (!Globals.enable_strong_invariant) then
        List.fold_left 
            (fun (a1,(b1,a2))(c1,(b2,c2))-> 
                if a1=[] then ([c1],(b2,c2))
                else (c1::a1, (CP.BagaSV.or_baga b1 b2, combine_pures c2 a2))) ([],(CP.BagaSV.mkEmpty,[])) pure_list
      else ((fst (List.split pure_list)),
      (u_baga,List.concat (List.map (fun c->List.map (fun c-> c.memo_formula) c.memo_group_cons)u_inv))) in
    (* Globals.formula_label list * (CP.BagaSV.baga * CP.b_formula list) *)
    (* (formula_label list * (Gen.Baga(P.PtrSV).baga * P.b_formula list)) list *)
    (* let _ = print_endline ("all: "^(Cprinter.string_of_prune_invariants [all])) in *)
    let rec comp i (crt_lst: (formula_label list * (CP.baga_sv * CP.b_formula list))list) (last_lst: (formula_label list * (CP.baga_sv * CP.b_formula list))list) =
      if i>l then [all] (* crt_lst   *)(* in case l=1, we just return one answer; not twice*)
      else
        if i>=l then all :: crt_lst
        else 
          let n_list1 = List.map (
              fun  (c1,(b1,c2)) -> 
                  let h = (List.hd c1) in
                  let rem = List.filter (fun (d1,_)-> 
                      (not (List.exists (fun x-> (fst x)=(fst d1)) c1))&
                          ((fst h)>(fst d1))) pure_list in
                  List.map (fun (d1,(b2,d2))->(d1::c1, (CP.BagaSV.or_baga b1 b2,combine_pures c2 d2))) rem 
          ) last_lst 
          in          
          let n_list = List.concat n_list1 in 
          comp (i+1) (crt_lst@n_list) n_list in        
    let comp i (crt_lst: (formula_label list * (CP.baga_sv * CP.b_formula list))list) (last_lst: (formula_label list * (CP.baga_sv * CP.b_formula list))list) = 
      let pr x = string_of_int (List.length x) in
      Debug.no_3 "comp" string_of_int pr pr pr comp i crt_lst last_lst 
    in
    (comp 2 start start) in

  let compute_invariants v_l (pure_list:(formula_label * (CP.baga_sv * CP.b_formula list)) list) 
        : (formula_label list * (CP.baga_sv * CP.b_formula list)) list= 
    let pr0 = Gen.BList.string_of_f (CP.SV.string_of) in
    let pr x = Gen.BList.string_of_f Cprinter.string_of_b_formula x in
    let pr1 inp = let l= List.map (fun (f,(_,a)) -> (f,a)) inp 
    in  Gen.BList.string_of_f (Gen.string_of_pair (fun x -> (Cprinter.string_of_formula_label) x "") pr ) l in
    let pr2 inp = let l= List.map (fun (f,(_,a)) -> (f,a)) inp 
    in  (string_of_int (List.length inp))^":"^Gen.BList.string_of_f (Gen.string_of_pair (Gen.BList.string_of_f (fun x -> (Cprinter.string_of_formula_label) x "")) pr ) l 
    in
    Debug.no_2 "compute_invariants"  
        pr0 pr1 pr2 compute_invariants v_l pure_list in


  (*
    vl : spec_var list // list or parameters
    allL : formula_label list
    // each formula
    orig_f : formula_label -> formula
    // potential pruning_conds on vl & LSet<allL
    PF = C -> LSet 
    // safe filters
    {c->LS | c->LS in PF & forall L in allL-F, c/\(orig_f f)=false}

    possible_prune_conds :: 
    lst : (formula * label) list
    -> vl:spec_var list
    -> uinv:memo_pure
    -> (f : label -> pure_formula, allL : label list, (b_formula, label list) list)

    safe_prune_conds ::
    lst:(b_formula, label list) list 
    -> f : label -> pure_formula
    -> allL : label list
    -> (b_formula, label list) list 


  *)


  (* this obtains constraint implied by the branches *)
  (* TODO : obtain propagated constraints & keep only stronger constraint *)
  let split_one_branch (vl:CP.spec_var list) (uinvl:CP.b_formula list) ((b0,lbl):(CF.formula * Globals.formula_label)) 
        : CP.formula * (formula_label * CP.spec_var list * CP.b_formula list) =
    let h,p,_,_,_ = CF.split_components b0 in
    let cm,ba = Solver.xpure_heap_symbolic_i cp h 0 in
    let xp = fold_mem_lst (CP.mkTrue no_pos) true true cm in
    let all_p = fold_mem_lst xp true true p in
    let split_p = filter_pure_conj_list (snd (get_pure_conj_list all_p)) in
    let r = List.filter (fun c-> (CP.bfv c)!=[] && Gen.BList.subset_eq CP.eq_spec_var (CP.bfv c) vl) split_p in		  
	(all_p,(lbl,ba,r)) in

  let split_one_branch (vl:CP.spec_var list) (uinvl:CP.b_formula list) (p2:(CF.formula * formula_label)) 
        : CP.formula * (formula_label * CP.spec_var list * CP.b_formula list) =
    let pr = Cprinter.string_of_formula_label_only in
    let pr1 = pr_pair (Cprinter.string_of_formula) pr in
    let pr2 = pr_pair (Cprinter.string_of_pure_formula) (pr_triple pr Cprinter.string_of_spec_var_list (pr_list Cprinter.string_of_b_formula)) in
    Debug.no_1 "split_one_branch" pr1 pr2 (fun _ -> split_one_branch vl uinvl p2) p2
  in

  (* this computes negated b_formula for possible use by other branches *)
  let neg_b_list (lbl:formula_label) (bl:CP.b_formula list) : (formula_label * CP.b_formula) list =
    List.fold_left (fun al c-> 
        match CP.mkNot_b_norm c with
          | None -> al
          | Some e -> (lbl,e)::al) [] bl
  in



  (* collects implied constraint from formula and also from negated b_form from elsewhere *)
  let collect_constr (neg_br:  (formula_label * CP.b_formula) list)
        ((f:CP.formula),((lbl:formula_label),(ba:CP.spec_var list),(pl:CP.b_formula list)))  
        : (formula_label * (CP.spec_var list * CP.b_formula list)) =  
    let n_c = List.fold_left (fun a (l,c)  ->  
        if (eq_formula_label l lbl) then a else 
          let (b,_,_) = TP.imply f (CP.BForm (c,None)) "" false None in
          if b then c::a  else
            a) [] neg_br in
    let r = Gen.BList.remove_dups_eq CP.eq_b_formula_no_aset (pl@n_c) in 
    (lbl,(ba,r)) in 

  let collect_constr split_br
        (x:  ((CP.formula) * ((formula_label) * (CP.spec_var list) * (CP.b_formula list))))
        : (formula_label * (CP.spec_var list * CP.b_formula list)) =
    let pr1 (f,(_,ba,pl)) = pr_pair Cprinter.string_of_pure_formula (pr_list Cprinter.string_of_b_formula) (f,pl) in
    let pr2 (l,(svl,pl)) = pr_pair Cprinter.string_of_spec_var_list (pr_list Cprinter.string_of_b_formula) (svl,pl) in
    Debug.no_1 "collect_constr" pr1 pr2 (fun _ -> collect_constr split_br x) x
  in

  let add_needed_inv uinvl (lbl,(_,rl)) =
	let all_r = CP.join_conjunctions (List.map (fun c-> CP.BForm (c,None)) rl) in
	let uinv2 = List.filter (fun c->
	    let r,_,_ = TP.imply all_r (CP.BForm (c,None)) "" false None in
	    not r) uinvl in
    (lbl, uinv2)
  in

  (* this picks a candidate set of pruning conditions for each branch *)
  let pick_pures (lst:(CF.formula * formula_label) list) (vl:CP.spec_var list) (uinv:memo_pure) : 
        ((formula_label * (CP.spec_var list * CP.b_formula list)) list * ((formula_label * CP.b_formula list) list)
        * ((formula_label * CP.formula) list)) =
	let uinvc = fold_mem_lst (CP.mkTrue no_pos) true true (MemoF uinv) in	 
	let uinvl = filter_pure_conj_list (snd (get_pure_conj_list uinvc)) in
    let split_br = List.map (split_one_branch vl uinvl) lst  in 
    let p_ls = List.map (fun (f,(l,_,_)) ->  (l,f)) split_br in
    let neg_br = List.concat (List.map (fun (_,(lbl,_,bl)) -> neg_b_list lbl bl) split_br) in
    let rlist = List.map (collect_constr neg_br) split_br in  
	(* let uinv2 = List.filter (fun c->  *)
	(*     let r,_,_ = TP.imply all_r (CP.BForm (c,None)) "" false None in *)
	(*     not r) uinvl in *)
    (* let uinv2 = imply_by_all all_r uinvl in *)
    let n_inv = List.map (add_needed_inv uinvl) rlist
    in (rlist,n_inv,p_ls) 
  in

  let pick_pures (lst:(CF.formula * formula_label) list) (vl:CP.spec_var list) (uinv:memo_pure) =
    let pr0 = Gen.BList.string_of_f (CP.SV.string_of) in
    let pr x = Gen.BList.string_of_f Cprinter.string_of_b_formula x in
    let pr_fl x = (Cprinter.string_of_formula_label) x "" in
    let pr1 (inp,_,_) = let l= List.map (fun (f,(_,a)) -> (f,a)) inp
    in Gen.BList.string_of_f (Gen.string_of_pair pr_fl pr ) l in
    let pr2 x= Cprinter.string_of_mix_formula (MemoF x) in
    let pr3 = pr_list (pr_pair Cprinter.string_of_formula pr_fl) in
    Debug.no_3 "pick_pures" pr3 pr0 pr2 pr1 (fun _ _ _ -> pick_pures lst vl uinv) lst vl uinv in

  let sel_prune_conds (ugl:(formula_label * CP.b_formula) list) : ((CP.b_formula * formula_label list) list) =
    let prune_conds = List.fold_left (fun a (f_lbl, constr)->
        let leq,lneq = List.partition (fun (c,_)-> CP.eq_b_formula_no_aset constr c) a in
        let rest_lbls = match (List.length leq) with | 0 -> [] | 1 -> snd (List.hd leq) | _ -> [] in
        (constr,f_lbl::rest_lbls)::lneq) [] ugl in
    let prune_conds = List.filter (fun (c1,c2)-> (List.length init_form_lst)>(List.length c2)) prune_conds in
    prune_conds
  in

  let sel_prune_conds (ugl:(formula_label * CP.b_formula) list) : ((CP.b_formula * formula_label list) list) =
    let pr_fl x = Cprinter.string_of_formula_label x "" in
    let pr1 = pr_list (pr_pair pr_fl (Cprinter.string_of_b_formula)) in
    let pr2 = pr_list (pr_pair (Cprinter.string_of_b_formula) (pr_list pr_fl)) in
    Debug.no_1 "sel_prune_conds" pr1 pr2 sel_prune_conds ugl
  in

  let get_safe_prune_conds (pc:(CP.b_formula * formula_label list) list) (orig_pf:(formula_label * CP.formula) list)
        : (CP.b_formula * formula_label list) list = 
 
    let safe_test bf ls =
      let neg_bf = CP.mkNot_b_norm  bf in
      match neg_bf with
        | None -> false
        | Some bf ->
              begin
                let bf = CP.BForm (bf,None) in
                let remain_ls = Gen.BList.difference_eq (fun (f,_) -> eq_formula_label f) orig_pf ls in
                if remain_ls==[] then false
                else List.for_all
                  (fun (o_l,o_f) ->
                      let new_f = CP.mkAnd o_f bf no_pos
                      in (TP.is_sat new_f "get_safe_prune_conds" false)
                  ) remain_ls
              end
    in
    let safe_test bf ls = 
      let pr1 = Cprinter.string_of_b_formula in
      let pr2 ls = string_of_int (List.length ls) in
      Debug.no_2 "safe_test" pr1 pr2 string_of_bool safe_test bf ls in
    List.filter (fun (b,ls) ->safe_test b ls) pc
  in

  let get_safe_prune_conds (pc:(CP.b_formula * formula_label list) list) (orig_pf:(formula_label * CP.formula) list)
        : (CP.b_formula * formula_label list) list = 
    let pr = pr_list (pr_pair Cprinter.string_of_b_formula (pr_list Cprinter.string_of_formula_label_only)) in
    Debug.no_1 "get_safe_prune_conds" pr pr (fun _ -> get_safe_prune_conds pc orig_pf) pc
  in
  let (guard_list,u_inv_ls,pure_form_ls) = pick_pures init_form_lst v_l u_inv in
  let new_guard_list = List.map (fun (l,(svl,f)) -> let r = List.assoc l u_inv_ls in (l,(svl,f@r))) guard_list in
  let invariant_list = compute_invariants v_l new_guard_list in  
  let norm_inv_list = List.map (fun (c1,(b1,c2))-> (c1,(CP.BagaSV.conj_baga v_l b1,memo_norm_wrapper c2))) invariant_list in
  let ungrouped_g_l = List.concat (List.map (fun (lbl, (_,c_l))-> List.map (fun c-> (lbl,c)) c_l) guard_list) in
  let ungrouped_b_l = 
	let filter_vl l= List.filter (fun c-> List.exists (CP.eq_spec_var c) v_l) l in
	List.map (fun (lbl, (b,_))-> (filter_vl b,lbl)) guard_list in
  let prune_conds = sel_prune_conds ungrouped_g_l in
  let safe_prune_conds = get_safe_prune_conds prune_conds pure_form_ls in
  (safe_prune_conds,ungrouped_b_l, norm_inv_list)
      
(*usefull: disjunct_count, disjunct_list *)

and view_prune_inv_inference cp vd =  
  let pr = Cprinter.string_of_view_decl in
  Debug.no_1 "view_prune_inv_inference" pr pr
      (fun _ -> view_prune_inv_inference_x cp vd) vd

and view_prune_inv_inference_x cp vd =  
  let sf  = CP.SpecVar (Named vd.C.view_data_name, self, Unprimed) in
  let f_branches = CF.get_view_branches  vd.C.view_formula in 
  let branches = snd (List.split f_branches) in
  let u_inv = vd.C.view_user_inv in
  let conds, baga_cond ,invs = prune_inv_inference_formula cp (sf::vd.C.view_vars) f_branches vd.C.view_baga (drop_pf u_inv) no_pos in    
  let c_inv = 
    if (List.length branches)=1 then 
      (* TODO : to compute complex_inv from formula *)
      let mf  = vd.C.view_x_formula in
      let r = filter_complex_inv mf in
      if (isConstMTrue r) then None else Some r
    else None in
  let v' = { vd with  
      C.view_complex_inv =  c_inv ; 
      C.view_prune_branches = branches; 
      C.view_prune_conditions = conds ; 
      C.view_prune_conditions_baga = baga_cond;
      C.view_prune_invariants = invs;} in 
  v'    

and barrier_prune_inv_inference_x cp bd = 
  (*let sf  = CP.SpecVar (Named bd.C.barrier_name, self, Unprimed) in*)
  let f_branches = CF.get_bar_branches  bd.C.barrier_def in 
  let branches = List.map snd f_branches in
  (*let _, baga_cond ,_ = prune_inv_inference_formula cp (sf::bd.C.barrier_shared_vars) f_branches [] [] no_pos in    *)
  let state_conds,perm_conds = 
	(*let state_var = List.hd bd.C.barrier_shared_vars in*)
	let l = CF.get_bar_conds [bd.C.barrier_name] self f_branches in
	let l_state,l_perm = List.fold_left (fun (a1,a2) (c1,c2,c3)-> 
		let a1 = match c1 with | None -> a1 | Some v -> (v,c3)::a1 in
		let a2 = match c2 with | None -> a2 | Some v -> (v,c3)::a2 in
		(a1,a2)) ([],[]) l in
	let rec fix_p_state l= match l with
		| [] -> []
		| (v,lbl)::t-> 
			let l_v,l_nv = List.partition (fun (v2,_)-> v=v2) t in
			(v, lbl:: (snd (List.split l_v)))::(fix_p_state l_nv) in
	let rec fix_perm l= match l with
		| [] -> []
		| (v,lbl)::t-> 
			let l_v,l_nv = List.partition (fun (v2,_)-> Tree_shares.Ts.eq v v2) t in
			(v, lbl:: (snd (List.split l_v)))::(fix_perm l_nv) in		
	fix_p_state l_state, fix_perm l_perm in
  { bd with  
	C.barrier_prune_branches = branches; 
	C.barrier_prune_conditions_state = state_conds;
	C.barrier_prune_conditions_perm = perm_conds;
	C.barrier_prune_conditions = [] ;	
    C.barrier_prune_conditions_baga = [];	
    C.barrier_prune_invariants = [];}
  
and barrier_prune_inv_inference cp bd = 
	let pr = Cprinter.string_of_barrier_decl in
	Debug.no_1 "barrier_prune_inv_inference" pr pr (barrier_prune_inv_inference_x cp) bd


  
  
and coerc_spec prog is_l c = 
  if not !Globals.allow_pred_spec then [c] 
  else 
    let prun_f = Solver.prune_preds prog true  in
    [{c with C.coercion_head = prun_f c.C.coercion_head; C.coercion_body = prun_f c.C.coercion_body}]
  

and pred_prune_inference (cp:C.prog_decl):C.prog_decl = 
  Debug.no_1 "pred_prune_inference" pr_no pr_no pred_prune_inference_x cp 

and pred_prune_inference_x (cp:C.prog_decl):C.prog_decl =      
  Gen.Profiling.push_time "pred_inference";
    let preds = List.map (fun c-> view_prune_inv_inference cp c) cp.C.prog_view_decls in
	let bars = List.map (barrier_prune_inv_inference cp) cp.C.prog_barrier_decls in
    let prog_views_inf = {cp with C.prog_view_decls  = preds;C.prog_barrier_decls = bars} in
    let preds = List.map (fun c-> 
        let unstruc = List.map (fun (c1,c2) ->
            (Solver.prune_preds(*_debug*) prog_views_inf true c1,c2))c.C.view_un_struc_formula in
        {c with 
            C.view_formula =  CF.erase_propagated (Solver.prune_pred_struc prog_views_inf true c.C.view_formula) ;
            C.view_un_struc_formula = unstruc;}) preds in
    let prog_views_pruned = { prog_views_inf with C.prog_view_decls  = preds;} in
	let prune_bar c = { c with 
		 C.barrier_tr_list = List.map (fun (a1,a2,c)-> a1,a2,List.map (Solver.prune_pred_struc prog_views_pruned true) c) c.C.barrier_tr_list;
		 C.barrier_def= CF.erase_propagated (Solver.prune_pred_struc prog_views_pruned true c.C.barrier_def)} in
	let prune_bar c = Debug.no_1 "prune_bar" Cprinter.string_of_barrier_decl Cprinter.string_of_barrier_decl prune_bar c in
	let bars = List.map prune_bar bars in
		 
	let prog_barriers_pruned ={prog_views_pruned with C.prog_barrier_decls = bars} in
    let proc_spec f = 
      let simp_b = not ((String.compare f.C.proc_file "primitives")==0 or (f.C.proc_file="")) in
      {f with 
          C.proc_static_specs= Solver.prune_pred_struc prog_barriers_pruned simp_b f.C.proc_static_specs;
          C.proc_dynamic_specs=  Solver.prune_pred_struc prog_barriers_pruned simp_b f.C.proc_dynamic_specs;
      } in
    let procs = C.proc_decls_map proc_spec prog_barriers_pruned.C.new_proc_decls in 
    let l_coerc = List.concat (List.map (coerc_spec prog_barriers_pruned true) prog_barriers_pruned.C.prog_left_coercions) in
    let r_coerc = List.concat (List.map (coerc_spec prog_barriers_pruned false) prog_barriers_pruned.C.prog_right_coercions) in
    let r = { prog_barriers_pruned with 
          C.new_proc_decls = procs;
          C.prog_left_coercions  = l_coerc;
          C.prog_right_coercions = r_coerc;} in
    Gen.Profiling.pop_time "pred_inference" ;r
   
and pr_proc_call_order p = 
  let n = p.Cast.proc_name in
  let c = p.Cast.proc_call_order in
  pr_pair pr_id string_of_int (n,c)

(* Termination *)			  
(* Recursive call and call order detection *)
(* irf = is_rec_field *)
and mark_rec_and_call_order_x (cp: C.prog_decl) : C.prog_decl =
  let cg = C.callgraph_of_prog cp in
  let scc_list = List.rev (C.IGC.scc_list cg) in
  let cp = mark_recursive_call cp scc_list cg in
  let cp = mark_call_order cp scc_list cg in
  let (prims, mutual_grps) = C.re_proc_mutual (C.sort_proc_decls (C.list_of_procs cp)) in
  Debug.trace_hprint (add_str "mutual scc" (pr_list (pr_list pr_proc_call_order))) mutual_grps no_pos;
  cp

and mark_rec_and_call_order (cp: C.prog_decl) : C.prog_decl =
  let pr p = pr_list (pr_proc_call_order) 
    (List.filter (fun x -> not (x.C.proc_body == None)) (C.list_of_procs p)) in
  Debug.no_1 "mark_rec_and_call_order" pr pr mark_rec_and_call_order_x cp

and mark_recursive_call (cp: C.prog_decl) scc_list cg : C.prog_decl =   irf_traverse_prog cp scc_list


and mark_call_order (cp: C.prog_decl) scc_list cg : C.prog_decl =
  let proc_top, proc_base  = List.partition (fun proc -> proc.C.proc_is_main) (C.list_of_procs cp) in
  let proc_top_names = List.map (fun p -> p.C.proc_name) proc_top in
  let scc_list = List.filter (fun scc -> Gen.BList.overlap_eq (=) scc proc_top_names) scc_list in
  let scc_list = scc_sort scc_list cg in
  let _, scc_list = List.fold_left (fun (index, acc) scc ->
	  (index+1, acc @ [(index, scc)])) (0, []) scc_list in
  let call_hierarchy = List.concat (List.map (fun (i, scc) -> List.map (fun m -> (m,i)) scc) scc_list) in 
  let cal_index name lst = try List.assoc name lst with _ -> 0 in 
   let tbl = C.proc_decls_map (fun p ->  
    { p with C.proc_call_order = cal_index p.C.proc_name call_hierarchy }
  ) cp.C.new_proc_decls in
  { cp with C.new_proc_decls = tbl }

and is_found (cp: C.prog_decl) (pname: Globals.ident) (scc: C.IG.V.t list) : bool =
  List.exists (fun m ->
	  let mn = (C.look_up_proc_def_raw cp.C.new_proc_decls m).C.proc_name in
	mn = pname) scc
			  
and find_scc_group (cp: C.prog_decl) (pname: Globals.ident) (scc_list: C.IG.V.t list list) : (C.IG.V.t list) =
  try List.find (fun scc -> is_found cp pname scc) scc_list
  with _ -> []
	
and neighbors_of_scc (scc: C.IG.V.t list) (scc_list: C.IG.V.t list list) cg : C.IG.V.t list list =
	let neighbors = List.filter (fun m -> not (List.mem m scc)) (C.IGN.list_from_vertices cg scc) in
	let scc_neighbors = List.find_all (fun s -> List.exists (fun m -> List.mem m neighbors) s) scc_list in 
	scc_neighbors
	
and scc_sort (scc_list: C.IG.V.t list list) cg : C.IG.V.t list list =
  let compare_scc scc1 scc2 =
		if (List.mem scc2 (neighbors_of_scc scc1 scc_list cg)) then 1
		else if (List.mem scc1 (neighbors_of_scc scc2 scc_list cg)) then -1
		else 0
  in List.fast_sort (fun s1 s2 -> compare_scc s1 s2) scc_list 

and irf_traverse_prog (cp: C.prog_decl) (scc_list: C.IG.V.t list list) : C.prog_decl = 
  { cp with
    C.new_proc_decls = C.proc_decls_map (fun proc ->
      irf_traverse_proc cp proc (find_scc_group cp proc.C.proc_name scc_list)
    ) cp.C.new_proc_decls;
  }

and irf_traverse_proc (cp: C.prog_decl) (proc: C.proc_decl) (scc: C.IG.V.t list) : C.proc_decl =
  let marked_rec_body, call_list = match proc.C.proc_body with
    | None -> None, []
    | Some b -> 
        let body, cl = irf_traverse_exp cp b scc in
        Some body, cl
  in let is_rec =
    if (List.length scc) > 1 then true (* Mutual recursive function *)
    else List.exists (fun mn -> mn = proc.C.proc_name) call_list
  in { proc with
    C.proc_body = marked_rec_body;
    C.proc_is_recursive = is_rec }

and irf_traverse_exp (cp: C.prog_decl) (exp: C.exp) (scc: C.IG.V.t list) : (C.exp * ident list) =
  match exp with
  | C.Label e -> 
      let ex, il = irf_traverse_exp cp e.C.exp_label_exp scc in
      (C.Label {e with C.exp_label_exp = ex}, il)
  | C.CheckRef _ 
  | C.Java _
  | C.Assert _ -> (exp, [])
  | C.Assign e -> 
      let ex, il = irf_traverse_exp cp e.C.exp_assign_rhs scc in
      (C.Assign {e with C.exp_assign_rhs = ex}, il)
  | C.BConst e -> (exp, [])
  | C.Barrier _ -> (exp,[])
  | C.Bind e -> 
      let ex, il = irf_traverse_exp cp e.C.exp_bind_body scc in
      (C.Bind {e with Cast.exp_bind_body = ex}, il)
  | C.Block e -> 
      let ex, il = irf_traverse_exp cp e.C.exp_block_body scc in
      (C.Block {e with C.exp_block_body = ex}, il)
  | C.Cond e -> 
      let ex1, il1 = irf_traverse_exp cp e.C.exp_cond_then_arm scc in
      let ex2, il2 = irf_traverse_exp cp e.C.exp_cond_else_arm scc in
      (C.Cond {e with
        C.exp_cond_then_arm = ex1; C.exp_cond_else_arm = ex2}, il1@il2)
  | C.Cast e -> 
      let ex, il = irf_traverse_exp cp e.C.exp_cast_body scc in
      (C.Cast {e with C.exp_cast_body = ex}, il)
  | C.Catch e -> 
      let ex, il = irf_traverse_exp cp e.C.exp_catch_body scc in
      (C.Catch {e with C.exp_catch_body = ex}, il)
  | C.Debug _
  | C.Dprint _
  | C.FConst _ 
  | C.IConst _
  | C.New _
  | C.Null _ 
  | C.EmptyArray _ 
  | C.Print _ -> (exp, [])
  | C.Seq e -> 
      let ex1, il1 = irf_traverse_exp cp e.C.exp_seq_exp1 scc in
      let ex2, il2 = irf_traverse_exp cp e.C.exp_seq_exp2 scc in
      (C.Seq {e with
        C.exp_seq_exp1 = ex1; C.exp_seq_exp2 = ex2}, il1@il2)
  | C.This _
  | C.Time _
  | C.Var _
  | C.VarDecl _
  | C.Unfold _
  | C.Unit _ -> (exp, [])
  | C.While e ->
      let ex, il = irf_traverse_exp cp e.C.exp_while_body scc in
      (C.While {e with C.exp_while_body = ex}, il)
  | C.Sharp _ -> (exp, [])
  | C.Try e -> 
      let ex1, il1 = irf_traverse_exp cp e.C.exp_try_body scc in
      let ex2, il2 = irf_traverse_exp cp e.C.exp_catch_clause scc in
      (C.Try {e with
        C.exp_try_body = ex1; C.exp_catch_clause = ex2}, il1@il2)
  | C.ICall e -> 
      (C.ICall {e with C.exp_icall_is_rec = (is_found cp e.C.exp_icall_method_name scc)}, 
      [e.C.exp_icall_method_name])
  | C.SCall e -> 
      (C.SCall {e with C.exp_scall_is_rec = (is_found cp e.C.exp_scall_method_name scc)},
      [e.C.exp_scall_method_name])
		  

and slicing_label_inference_program (prog : I.prog_decl) : I.prog_decl =
  {prog with
	  I.prog_view_decls = List.map (fun v -> slicing_label_inference_view v) prog.I.prog_view_decls;}
      
and slicing_label_inference_view (view : I.view_decl) : I.view_decl =
  let v_inv = IP.break_pure_formula view.I.view_invariant in
  let v_form = IF.break_struc_formula view.I.view_formula in

  let str_inv = pr_list (Iprinter.string_of_b_formula) v_inv in
  let str_form = pr_list (pr_list Iprinter.string_of_b_formula) v_form in

  let _ = print_string ("\nslicing_label_inference_view: inv: " ^ str_inv ^ "\n") in
  let _ = print_string ("\nslicing_label_inference_view: form: " ^ str_form ^ "\n") in

  let lg = List.map (fun v -> trans_view_to_graph v) v_form in

  let str_lg = pr_list (pr_list (pr_list Iprinter.string_of_var)) lg in

  let _ = print_string ("\nslicing_label_inference_view: graph: " ^ str_lg ^ "\n") in

  let _ = List.iter (
	  fun g ->
	      let lv = Gen.BList.remove_dups_eq IP.eq_var (List.concat g) in
	      let lp = fm_main g lv in

	      let str_lp = pr_list (fun (p, cutsize) -> (pr_list (pr_list Iprinter.string_of_var) p) ^ (string_of_int cutsize) ^ "\n") lp in

	      print_string (str_lp)
  ) lg in  
  view

and trans_view_to_graph (lbf : IP.b_formula list) =
  List.fold_left (
	  fun acc bf ->
	      let e = IP.bfv bf in
	      if (List.length e) > 1 then e::acc
	      else acc
  ) [] lbf
	  
(* Fiduccia-Mattheyses algorithm *)
and fm_cut_size g lp =
  let is_cut_edge e lp =
	List.fold_left (
	    fun acc p ->
		    if (acc && Gen.BList.subset_eq IP.eq_var e p) then false
		    else acc
	) true lp in
  List.fold_left (fun acc e -> if (is_cut_edge e lp) then acc + 1 else acc) 0 g

and fm_fs g p v =
  List.fold_left (
	  fun acc e -> if ((Gen.BList.intersect_eq IP.eq_var p e) = [v]) then acc + 1 else acc
  ) 0 g

and fm_te g p v =
  List.fold_left (
	  fun acc e -> if (Gen.BList.subset_eq IP.eq_var p e) then acc + 1 else acc
  ) 0 g

and fm_gain g p v = (fm_fs g p v) - (fm_te g p v)

and fm_constr g lp = true

and fm_find_partition lp v =
  List.find (fun p -> Gen.BList.mem_eq IP.eq_var v p) lp
      
and fm_moving_cell v lp =  
  List.map (
      fun p ->
	      if Gen.BList.mem_eq IP.eq_var v p then
	        Gen.BList.difference_eq IP.eq_var p [v]
	      else p@[v]
  ) lp
      
and fm_choose_moved_cell g lp lv =
  let (unlocked_v, _) = lv in
  List.fold_left (
	  fun acc v ->
	      let (v_id, v_gain) = v in
	      match acc with
	        | None ->
		          let nlp = fm_moving_cell v_id lp in
		          if fm_constr g nlp then Some v else None
	        | Some (a_id, a_gain) ->
		          if v_gain < a_gain then acc
		          else
		            let nlp = fm_moving_cell v_id lp in
		            if fm_constr g nlp then Some v else acc
  ) None unlocked_v
	  
and fm_main g lv =
  let rec helper g lp lv =
	let moved_v = fm_choose_moved_cell g lp lv in
	match moved_v with
	  | None -> [(lp, fm_cut_size g lp)]
	  | Some v ->
		    let (v_id, v_gain) = v in
		    let nlp = fm_moving_cell v_id lp in
		    let nlv =
		      let (unlocked_v, locked_v) = lv in
		      let n_unlocked_v =
			    List.fold_left (
			        fun acc ele ->
				        if ele = v then acc
				        else
				          let (e_id, _) = ele in
				          acc@[(e_id, fm_gain g (fm_find_partition nlp e_id) e_id)]
			    ) [] unlocked_v in
		      let n_locked_v = locked_v @ [v] in
		      (n_unlocked_v, n_locked_v) in
		    [(lp, fm_cut_size g lp)] @ (helper g nlp nlv)
  in

  let (lp1, lp2) = List.partition (fun (v_id, _) -> (String.length v_id) > 1) lv in
  let lp = [lp1] @ [lp2] in
  let unlocked_v = List.map (fun v -> (v, fm_gain g (fm_find_partition lp v) v)) lv in
  helper g lp (unlocked_v, [])


  
  

and check_barrier_wf prog bd = 
	(*aux es *)
  
  (*let rec wrapp_frac_fv f = match f with
    | CF.Or ({CF.formula_or_f1 = f1; CF.formula_or_f2 = f2; CF.formula_or_pos = pos}) ->
         CF.mkOr (wrapp_frac_fv f1) (wrapp_frac_fv f2) pos
    | CF.Base b -> 
        let l = Gen.BList.remove_dups_eq CP.eq_spec_var (MCP.mfv b.CF.formula_base_pure) in
        CF.add_quantifiers l f
    | CF.Exists e -> 
        let l = Gen.BList.remove_dups_eq CP.eq_spec_var (MCP.mfv e.CF.formula_exists_pure) in
        CF.add_quantifiers l f in*)
  let empty_es = CF.empty_es (CF.mkTrueFlow ()) Lab2_List.unlabelled no_pos in
  let rec group_tr l =  match l with
    | [] -> []
    | (hf,ht,hp)::t -> 
      let u,l = List.partition (fun (fl,_,_)-> fl=hf) t in
      let u = hp::(List.map (fun (_,_,c)->c) u) in
      let u = List.map (List.map (fun c-> 
        let pres = List.map fst (CF.split_struc_formula c) in
        List.fold_left (fun a c-> CF.mkOr a c no_pos) (CF.mkFalse (CF.mkFalseFlow) no_pos) pres)) u in 
      (hf,u)::(group_tr l) in
	  
	let f_gen_base st v perm = 
	  let st_v = CP.SpecVar (Int,fresh_name (),Unprimed) in
	  let h = CF.DataNode {
                        CF.h_formula_data_node = CP.SpecVar (Named bd.C.barrier_name, self,Unprimed);
                        CF.h_formula_data_name = bd.C.barrier_name;
                        CF.h_formula_data_imm = CF.ConstAnn Mutable;
                        CF.h_formula_data_perm = Some v;
                        CF.h_formula_data_arguments = st_v::List.tl bd.C.barrier_shared_vars;
                        CF.h_formula_data_label = None; 
                        CF.h_formula_data_remaining_branches = None ;
                        CF.h_formula_data_pruning_conditions = [] ;
						CF.h_formula_data_origins = [] ;
						CF.h_formula_data_original = true;
						CF.h_formula_data_holes =[];
						CF.h_formula_data_derv = false;
                        CF.h_formula_data_pos = no_pos } in
	  let p2 = CP.mkEqVarInt st_v st no_pos in
	  let p = Mcpure.mix_of_pure (CP.mkAnd p2 perm no_pos) in
	  CF.mkExists [v;st_v] h p CF.TypeTrue (CF.mkTrueFlow ()) [] no_pos in
	let f_gen_base st v perm = Debug.no_1 "f_gen_base" Cprinter.string_of_pure_formula Cprinter.string_of_formula (f_gen_base st v) perm in
	let f_gen st = f_gen_base st (CP.fresh_perm_var ()) (CP.mkTrue no_pos) in
	let f_gen_tot st = 
		let v = CP.fresh_perm_var () in
		let pf = CP.mkEq (CP.Var (v,no_pos)) (CP.Tsconst (Tree_shares.Ts.top,no_pos)) no_pos  in
		f_gen_base st v (CP.BForm ((pf,None),None)) in
				
	let one_entail f1 f2 = 
		let ctx = CF.build_context (CF.empty_ctx (CF.mkTrueFlow ()) Lab2_List.unlabelled no_pos) f1 no_pos in
		(*let _ = if !Globals.print_core then print_string ("\n"^(Cprinter.string_of_formula f1)^" |- "^(Cprinter.string_of_formula f2)^"\n") else () in*)
    Gen.Profiling.inc_counter "barrier_proofs";
		let rs1, _ = Solver.heap_entail_init prog false (CF.SuccCtx[ctx]) f2 no_pos in
		CF.transform_list_context (Solver.elim_ante_evars,(fun c->c)) rs1 in
	
	let one_entail f1 f2  = Debug.no_2 "one_entail" Cprinter.string_of_formula Cprinter.string_of_formula Cprinter.string_of_list_context one_entail f1 f2 in
		
	let one_ctx_entail c1 c2 =
    let r = 
      Gen.Profiling.inc_counter "barrier_proofs"; 
	  let c1 = CF.set_context_formula (CF.Ctx empty_es) c1 in
      (*let f2 = (CF.context_to_formula c2) in*)
      (*let _ = print_string ("entail: "^(Cprinter.string_of_list_context c1) ^" \n entails : "^(Cprinter.string_of_formula f2)^"\n") in*)
      (*print_string "cica start\n";*)
      fst (Solver.heap_entail_init prog false (CF.SuccCtx[c1]) (*wrapp_frac_fv*) c2 no_pos) in
    match r with
     | CF.SuccCtx l ->  List.for_all  (fun c-> (CF.isAnyFalseCtx c || CF.ctx_no_heap c)) l
     | CF.FailCtx _ -> ((*print_string "result : failed \n";*) false) in
	(*end auxes*)
	
	let one_ctx_entail c1 c2 = Debug.no_2_loop "one_ctx_entail" Cprinter.string_of_formula Cprinter.string_of_formula string_of_bool one_ctx_entail c1 c2 in
	  	
  let prep_t (fs,ts,fl) = 
    let t_str = "("^(string_of_int fs)^"->"^(string_of_int ts)^")" in
	(*	print_string ("transition: "^t_str^"\n"); flush stdout;*)
	let pres, posts = List.split (List.map (fun f-> match CF.split_struc_formula f with
	  | (p1,p2)::[] -> 
		 (* if Solver1.unsat_base_nth "0" prog (ref 0) p1 then raise  (Err.Malformed_barrier (" unsat pre for transition "^t_str ))
		  else if Solver1.unsat_base_nth "0" prog (ref 0) p2 then raise  (Err.Malformed_barrier (" unsat post for transition  "^t_str))
		  else*) (*checks: each contain a barrier fs in pre and ts in post*)
		   if (CF.isFailCtx (one_entail p1 (f_gen fs))) then raise (Err.Malformed_barrier ("a precondition does not contain a barrier share for transition "^t_str))
		   else if (CF.isFailCtx (one_entail p2 (f_gen ts))) then raise (Err.Malformed_barrier ("a postcondition does not contain a barrier share for transition "^t_str))
		   else (*check precision P * P = false , shold be redundant at this point*)
		   
        let f = (*Solver.normalize_frac_formula prog*) (CF.mkStar p1 p1 CF.Flow_combine no_pos) in
		let f = Solver.normalize_formula_w_coers prog empty_es f prog.C.prog_left_coercions in
        Gen.Profiling.inc_counter "barrier_proofs";
			if Solver.unsat_base_nth "0" prog (ref 0) f then (p1,p2)  
			else raise  (Err.Malformed_barrier "imprecise specification, this should not occur as long as the prev check is correct")
	  | _ -> raise  (Err.Malformed_barrier " disjunctive specification?")) fl) in
	(*the pre sum totals full barrier fs get residue F1*)
	let tot_pre = List.fold_left (fun a c-> CF.mkStar a c CF.Flow_combine no_pos) (CF.mkTrue_nf no_pos) pres in
	let tot_pre = Solver.normalize_formula_w_coers prog empty_es tot_pre prog.C.prog_left_coercions in
    (*let tot_pre = Solver.normalize_frac_formula prog tot_pre in*)
    (*let _ = print_string (Cprinter.string_of_formula tot_pre) in *)
  Gen.Profiling.inc_counter "barrier_proofs";
	if Solver.unsat_base_nth "0" prog (ref 0) tot_pre then raise  (Err.Malformed_barrier (" contradiction in pres for transition "^t_str ))
	else
		let tot_pre_bar = f_gen_tot fs in
		let _ = Debug.devel_zprint (lazy ("check_barriers: whole pre:  "^ (Cprinter.string_of_formula tot_pre))) no_pos in
		let _ = Debug.devel_zprint (lazy ("check_barriers: whole pre barr: "^ (Cprinter.string_of_formula tot_pre_bar))) no_pos in
		let fpre = one_entail tot_pre tot_pre_bar in
		if CF.isFailCtx fpre then  raise  (Err.Malformed_barrier (" preconditions do not contain the entire barrier in transition "^t_str ))
		else (*the post sum totals full barrier ts get residue F2*)
			let tot_post = List.fold_left (fun a c-> CF.mkStar a c CF.Flow_combine no_pos) (CF.mkTrue_nf no_pos) posts in
			let tot_post = Solver.normalize_formula_w_coers prog empty_es tot_post prog.C.prog_left_coercions in
            (*let tot_post = Solver.normalize_frac_formula prog tot_post in*)
			Gen.Profiling.inc_counter "barrier_proofs";
			if Solver.unsat_base_nth "0" prog (ref 0) tot_post then raise (Err.Malformed_barrier (" contradiction in post for transition "^t_str ))
			else 
				let tot_post_bar = f_gen_tot ts in
				let _ = Debug.devel_zprint (lazy ("check_barriers: whole post:  "^ (Cprinter.string_of_formula tot_post))) no_pos in
				let _ = Debug.devel_zprint (lazy ("check_barriers: whole post barr: "^ (Cprinter.string_of_formula tot_post_bar))) no_pos in
				let fpost = one_entail tot_post tot_post_bar in
				if CF.isFailCtx fpost then  raise  (Err.Malformed_barrier (" postconditions do not contain the entire barrier in transition "^t_str ))
				else (*show F1 = F2*)
				let _ = Debug.devel_zprint (lazy ("check_barriers: pre: "^ (Cprinter.string_of_list_context fpre))) no_pos in
				let _ = Debug.devel_zprint (lazy ("check_barriers: post: "^ (Cprinter.string_of_list_context fpost))) no_pos in
				
				
				let fpre,fpost  = 	(*add existential quantif for pure vars that do not appear on the other side*)
					
					let fpost = match fpost with | CF.SuccCtx l -> CF.formula_of_context (List.hd l) | _ ->raise (Err.Malformed_barrier "error in check") in
					let fpre = match fpre with | CF.SuccCtx l -> CF.formula_of_context (List.hd l) | _ ->raise (Err.Malformed_barrier "error in check") in
					let h_fv = List.tl bd.C.barrier_shared_vars in
					let pre_ex  = Gen.BList.difference_eq CP.eq_spec_var  (CF.fv fpre)  h_fv in
					let post_ex = Gen.BList.difference_eq CP.eq_spec_var  (CF.fv fpost) h_fv in
					CF.push_exists pre_ex  fpre,CF.push_exists post_ex  fpost in				
				let r = one_ctx_entail fpre fpost && one_ctx_entail fpost fpre in
				if r then () 
				else  raise (Err.Malformed_barrier (" frames do not match "^t_str )) in
  
  let prep_t f = Debug.no_1 "prep_t" (fun c-> "") (fun c-> "") prep_t f in
  
  let prep_grp (st,l) = 
    let incomp f1 f2 = 
      Gen.Profiling.inc_counter "barrier_proofs";
      (*should be made to use "and" on xpures to detect the contradiction, probably by looking only at the pures after normalization*)
      if  Solver.unsat_base_nth "0" prog (ref 0) (CF.mkStar f1 f2 CF.Flow_combine no_pos) then () 
      else raise (Err.Malformed_barrier (" no contradiction found in preconditions of transitions from "^(string_of_int st)^"  for preconditions: \n f1:   "^
	  (Cprinter.string_of_formula f1)^"\n f2:    "^(Cprinter.string_of_formula f2))) in
	  let rec check_one p1 p2 = List.iter (fun c1 -> List.iter (incomp c1) p1) p2 in 
    let rec helper l = match l with
     | [] -> ()
     | p::r -> helper r ; List.iter (check_one p) r in
    helper l in
   
  let prep_grp f = Debug.no_1 "prep_grp" (fun c-> "") (fun c-> "") prep_grp f in
  
  List.iter prep_t bd.C.barrier_tr_list;
  List.iter prep_grp (group_tr bd.C.barrier_tr_list)
   

				
and trans_bdecl_x prog bd = 
  if Gen.BList.check_dups_eq (fun (c1,c2,_) (d1,d2,_)-> c1=d1 && c2=d2) bd.I.barrier_tr_list then 
	  raise  (Err.Malformed_barrier ("several descriptions for the same transition "))
   else (); 
   (*thread count consistency*)
  List.iter (fun (fs,ts,specl)-> if (List.length specl)<> bd.I.barrier_thc then 	
		raise  (Err.Malformed_barrier (" eroneous thread specification number for transition : "^(string_of_int fs)^"->"^(string_of_int ts))) 
	else ();
	if not (List.for_all (IF.find_barr_node bd.I.barrier_name fs ts)  specl) then 
		raise  (Err.Malformed_barrier (" eroneous thread specification pre/post cond bar states do not match : "^(string_of_int fs)^"->"^(string_of_int ts)))
	else ()) bd.I.barrier_tr_list;
  let stab = H.create 103 in
  H.add stab self { sv_info_kind = (Named bd.I.barrier_name);id = fresh_int () };
  List.iter (fun (t,c)-> H.add stab c {sv_info_kind = t;id = fresh_int ()}) bd.I.barrier_shared_vars ; 
  (*let vl = self::(List.map snd bd.I.barrier_shared_vars) in*)
  let vl = [self] in
  
  let fct f = trans_I2C_struc_formula prog true vl f stab false in
  let l = List.map (fun (f,t,sp)-> (f,t,List.map fct sp)) bd.I.barrier_tr_list in
  let bdef = let fct a l = match l with 
			| CF.EList l -> a@l 
			| _ -> (empty_spec_label_def, l)::a in
		CF.mkEList (List.fold_left (fun a (_,_,l)-> List.fold_left fct a l) [] l) in
  { C.barrier_thc = bd.I.barrier_thc;
	C.barrier_name = bd.I.barrier_name;
	C.barrier_shared_vars = List.map (fun (_,c)-> trans_var (c,Unprimed) stab no_pos) bd.I.barrier_shared_vars;
	C.barrier_tr_list = l;
	C.barrier_def = bdef;
    C.barrier_prune_branches = [];
	C.barrier_prune_conditions = []; 
    C.barrier_prune_conditions_baga = [];
    C.barrier_prune_invariants = [];
	C.barrier_prune_conditions_state = [];
	C.barrier_prune_conditions_perm =[]}
  
and trans_bdecl prog bd =
	let pr_in = Iprinter.string_of_barrier_decl in
	let pr_out c = Cprinter.string_of_barrier_decl c in
	Debug.no_1 "trans_bdecl " pr_in pr_out (trans_bdecl_x prog) bd
  
(*
and normalize_barr_decl cprog p = 
		let nfs = Solver.normalize_frac_struc cprog in
    let l  = List.map (fun (f,t,fl) -> (f,t,List.map nfs fl)) p.C.barrier_tr_list in
		let bd = List.concat (List.map (fun (_,_,l)->List.concat l) l) in
		{ p with C.barrier_tr_list = l; C.barrier_def = bd;}
        
and normalize_fracs cprog  = 
	let nff = Solver.normalize_frac_formula cprog in
	let nfs = Solver.normalize_frac_struc cprog in
	let nfof f = match f with None -> None | Some f-> Some (nff f) in
	let nfos f = match f with None -> None | Some f-> Some (nfs f) in
	let normalize_fracs_pred p = 
		{p with 
			C.view_formula = nfs p.C.view_formula;
			C.view_un_struc_formula = List.map (fun (c1,c2)-> (nff c1,c2)) p.C.view_un_struc_formula;
			C.view_raw_base_case = nfof p.C.view_raw_base_case}in
			
	let rec normalize_fracs_exp e = match e with
		  | C.CheckRef _ | C.Java _ | C.Debug _ | C.Dprint _ | C.FConst _ | C.ICall _ | C.Sharp _
		  | C.IConst _ | C.New _ | C.Null _ | C.EmptyArray _ | C.Print _ | C.VarDecl _ | C.Unfold _ 
		  | C.Barrier_cmd _ | C.BConst _  | C.SCall _ | C.This _ | C.Time _ | C.Var _ | C.Unit _ -> e
		  
		  | C.Label e -> C.Label {e with C.exp_label_exp = normalize_fracs_exp e.C.exp_label_exp}
		  | C.Assert e -> C.Assert {e with  
				C.exp_assert_asserted_formula = nfos e.C.exp_assert_asserted_formula;
				C.exp_assert_assumed_formula = nfof e.C.exp_assert_assumed_formula}
		  | C.Assign e -> C.Assign {e with C.exp_assign_rhs = normalize_fracs_exp e.C.exp_assign_rhs}
		  | C.Bind e -> C.Bind {e with C.exp_bind_body = normalize_fracs_exp e.C.exp_bind_body}
		  | C.Block e -> C.Block {e with C.exp_block_body = normalize_fracs_exp e.C.exp_block_body}
		  | C.Cond e -> C.Cond {e with 
				C.exp_cond_then_arm = normalize_fracs_exp e.C.exp_cond_then_arm;
				C.exp_cond_else_arm = normalize_fracs_exp e.C.exp_cond_else_arm}
		  | C.Cast e -> C.Cast {e with C.exp_cast_body = normalize_fracs_exp e.C.exp_cast_body}
		  | C.Catch e -> C.Catch {e with C.exp_catch_body = normalize_fracs_exp e.C.exp_catch_body}
		  | C.Seq e -> C.Seq {e with
				C.exp_seq_exp1 = normalize_fracs_exp e.C.exp_seq_exp1;
				C.exp_seq_exp2 = normalize_fracs_exp e.C.exp_seq_exp2}
		  | C.While e -> C.While {e with 
				C.exp_while_body = normalize_fracs_exp e.C.exp_while_body;
				C.exp_while_spec = nfs e.C.exp_while_spec;}
		  | C.Try e -> C.Try {e with
				C.exp_try_body = normalize_fracs_exp e.C.exp_try_body;
				C.exp_catch_clause = normalize_fracs_exp e.C.exp_catch_clause} in
			
	let normalize_fracs_proc p = 
	{p with 
		C.proc_static_specs = nfs p.C.proc_static_specs ;
		C.proc_static_specs_with_pre = nfs p.C.proc_static_specs_with_pre;
		C.proc_dynamic_specs = nfs p.C.proc_dynamic_specs ;
		C.proc_body = match p.C.proc_body with | None -> None | Some e -> Some (normalize_fracs_exp e);} in
			
	let normalize_fracs_data p = 
		{p with
			C.data_invs = List.map nff p.C.data_invs;
			C.data_methods = List.map normalize_fracs_proc p.C.data_methods;} in
	
	let normalize_coerc_decl p = 
		{p with
			C.coercion_head = nff p.C.coercion_head;
			C.coercion_body = nff p.C.coercion_body;} in
	
	{ cprog with 
		C.prog_data_decls = List.map normalize_fracs_data cprog.C.prog_data_decls;
		C.prog_view_decls = List.map normalize_fracs_pred cprog.C.prog_view_decls;
		C.prog_proc_decls = List.map normalize_fracs_proc cprog.C.prog_proc_decls;
		C.prog_left_coercions = List.map normalize_coerc_decl cprog.C.prog_left_coercions;
		C.prog_right_coercions = List.map normalize_coerc_decl cprog.C.prog_right_coercions;
		C.prog_barrier_decls = List.map (normalize_barr_decl cprog) cprog.C.prog_barrier_decls;
	}
*)	
