#include "xdebug.cppo"
open VarGen

(* Created 21 Feb 2006 Simplify Iast to Cast *)
open Globals
open Gen.Basic
open Wrapper
open Others
open Exc.GTable
open Printf
open Gen.Basic
open Gen.BList
open Perm
open Mcpure_D
open Mcpure
open Label_only
open Typeinfer
open CvpermUtils
open HipUtil

module C = Cast
module E = Env
module Err = Error
module I = Iast
module IF = Iformula
module IP = Ipure
module CF = Cformula
(* module CFU = Cfutil *)
module CFS = Cfsolver
(* module GV = Globalvars *)
module CP = Cpure
module MCP = Mcpure
module H = Hashtbl
module TP = Tpdispatcher
module Chk = Checks
(* module PRED = Predicate *)
module LO = Label_only.LOne
module LP = CP.Label_Pure
open IastUtil

module IVP = IvpermUtils
module CVP = CvpermUtils

type trans_exp_type =
  (C.exp * typ)

(* let view_args_map = CP.view_args_map *)

let pr_v_decls l = pr_list (fun v -> v.I.view_name) l

let ihp_decl = ref ([]: I.hp_decl list)
(* let strip_exists_pure f = *)
(*   let rec aux f = *)
(*     match f with *)
(*       | CP.Exists (_,f,_,_) -> aux f *)
(*       | _ -> f *)
(*   in let ls=CP.split_conjunction f in *)
(*   let ls = List.map aux ls in *)
(*   CP.join_conjunction ls *)

(* list of scc views that are in mutual-recursion *)
let view_scc : (ident list) list ref = ref []

(* list of views that are recursive *)
let view_rec : (ident list) ref = ref []


(* Add this to adapt to the ret_int problem. Because in string_of_typ in globals, bool will return "boolean", which will cause a lot of trouble.*)
let rec new_string_of_typ (x:typ) : string = match x with
   (* may be based on types used !! *)
  | FORM          -> "Formula"
  | UNK          -> "Unknown"
  | Bool          -> "bool"
  | Float         -> "float"
  | Int           -> "int"
  | INFInt        -> "INFint"
  | Void          -> "void"
  | NUM          -> "NUM"
  | AnnT          -> "AnnT"
  | Tup2 (t1,t2)  -> "tup2("^(string_of_typ t1) ^ "," ^(string_of_typ t2) ^")"
  | BagT t        -> "bag("^(string_of_typ t)^")"
  | TVar t        -> "TVar["^(string_of_int t)^"]"
  | List t        -> "list("^(string_of_typ t)^")"
  | Tree_sh		  -> "Tsh"
  | Bptyp		  -> "Bptyp"
  | RelT a      -> "RelT("^(pr_list string_of_typ a)^")"
  | Pointer t        -> "Pointer{"^(string_of_typ t)^"}"
  | FuncT (t1, t2) -> (string_of_typ t1) ^ "->" ^ (string_of_typ t2)
  | UtT        -> "UtT"
  | HpT        -> "HpT"
  (* | SLTyp -> "SLTyp" *)
  | Named ot -> if ((String.compare ot "") ==0) then "null_type" else ot
  | Array (et, r) -> (* An Hoa *)
	let rec repeat k = if (k <= 0) then "" else "[]" ^ (repeat (k-1)) in
		(string_of_typ et) ^ (repeat r)
;;



(* if no processed, conservatively assume a view is recursive *)
let is_view_recursive (n:ident) = 
  if (!view_scc)==[] then (
      (* report_warning no_pos "view_scc is empty : not processed yet?"; *)
      false)
  else List.mem n !view_rec 

(** An Hoa : List of undefined data types **)
let undef_data_types = ref([] : (string * loc) list)


(** An Hoa : Alias for the Scriptarguments.inter, necessary because this module
            is compiled prior to Scriptarguments.
 **)
let inter_hoa = ref false

(* let op_map = Hashtbl.create 19 *)

(************************************************************
Primitives handling stuff
************************************************************)
(* Add a primitive function update___. Note: it is supposed to be dynamically inserted depending on the available types. *)

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
     (* let () = print_string ("\n primitives: "^prim_str^"\n") in *)
     helper prog.I.prog_data_decls;
     let all_prims = Buffer.contents prim_buffer in
     let prog = 
       (try
           Parser.parse_hip_string "primitives" all_prims 
        with  _ ->
            Error.report_error {Error.error_loc = no_pos;
                                Error.error_text = ("Parsing error in gen_primitives")}
       )
     in
        (* An Hoa : print out the primitive relations parsed -- Problem : no relation parsed! *)
        (* let () = print_endline "Primitive relations : " in *)
        (* let todo_unk = List.map (fun x -> print_endline x.I.rel_name) prog.I.prog_rel_decls in *)
        (* An Hoa : THIS IS NOT THE PLACE THE PRIMITIVES IN prelude.ss IS ADDED! *)

     (* AN HOA : modify to return the list of primitive relations *)
     (prog.I.prog_proc_decls, prog.I.prog_rel_decls))
     (* let input = Lexing.from_string all_prims in *)
     (* input_file_name := "primitives"; *)
     (* let prog = Iparser.program (Ilexer.tokenizer "primitives") input *)
     (* in  *)
     (* (\*let () = print_string ("\n primitives: "^(Iprinter.string_of_program prog)^"\n") in*\) *)
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

let get_binop_call_safe_int (bop : I.bin_op) : ident =
  match bop with
  | I.OpPlus -> "safe_sadd___"
  | _ -> (try Hashtbl.find op_map bop
         with
           | Not_found -> failwith
               ("binary operator " ^ ((Iprinter.string_of_binary_op bop) ^ " is not supported")))
	  
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

module NGComponents = Graph.Components.Make(NG)
  

(***********************************************)
(* 17.04.2008 *)
(* add existential quantifiers for the anonymous vars - those that start with "Anon_" *)
(***********************************************)
let rec

    (* - added 17.04.2008 - checks if the heap formula contains anonymous    *)
    (* vars                                                                  *)
   look_for_anonymous_h_formula (h0 : IF.h_formula) : (ident * primed) list =
  match h0 with
  | IF.Star { IF.h_formula_star_h1 = h1; IF.h_formula_star_h2 = h2 } ->
      let tmp1 = look_for_anonymous_h_formula h1 in
      let tmp2 = look_for_anonymous_h_formula h2 in List.append tmp1 tmp2
  | IF.HeapNode { IF.h_formula_heap_arguments = args;
                  IF.h_formula_heap_name = name;
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

and convert_anonym_to_exist_struc f = match f with
    | IF.ECase b -> IF.ECase {b with IF.formula_case_branches = map_l_snd convert_anonym_to_exist_struc b.IF.formula_case_branches}
    | IF.EBase b -> IF.EBase {b with 
                        IF.formula_struc_base = convert_anonym_to_exist b.IF.formula_struc_base;
                        IF.formula_struc_continuation = map_opt convert_anonym_to_exist_struc b.IF.formula_struc_continuation;}
    | IF.EAssume b -> IF.EAssume {b with 
                        IF.formula_assume_simpl = convert_anonym_to_exist b.IF.formula_assume_simpl;
                        IF.formula_assume_struc = convert_anonym_to_exist_struc b.IF.formula_assume_struc}
    | IF.EInfer b -> IF.EInfer {b with IF.formula_inf_continuation =convert_anonym_to_exist_struc b.IF.formula_inf_continuation}
    | IF.EList b -> IF.EList (map_l_snd convert_anonym_to_exist_struc b)
  
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
        IF.formula_base_vperm = vp;
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
              IF.formula_exists_vperm = vp;
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

(* convert HeapNode2 to HeapNode *)
let rec convert_heap2_heap prog (h0 : IF.h_formula) : IF.h_formula =
  match h0 with
    | IF.Star (({ IF.h_formula_star_h1 = h1; IF.h_formula_star_h2 = h2 } as h))
        -> let tmp1 = convert_heap2_heap prog h1 in
        let tmp2 = convert_heap2_heap prog h2
        in IF.Star { (h) with
            IF.h_formula_star_h1 = tmp1;
            IF.h_formula_star_h2 = tmp2; }
    | IF.StarMinus (({ IF.h_formula_starminus_h1 = h1; IF.h_formula_starminus_h2 = h2 } as h))
        -> let tmp1 = convert_heap2_heap prog h1 in
        let tmp2 = convert_heap2_heap prog h2
        in IF.StarMinus { (h) with
            IF.h_formula_starminus_h1 = tmp1;
            IF.h_formula_starminus_h2 = tmp2; }
    | IF.Conj (({ IF.h_formula_conj_h1 = h1; IF.h_formula_conj_h2 = h2 } as h))
        -> let tmp1 = convert_heap2_heap prog h1 in
        let tmp2 = convert_heap2_heap prog h2
        in IF.Conj { (h) with
            IF.h_formula_conj_h1 = tmp1;
            IF.h_formula_conj_h2 = tmp2; }
    | IF.ConjStar (({ IF.h_formula_conjstar_h1 = h1; IF.h_formula_conjstar_h2 = h2 } as h))
        -> let tmp1 = convert_heap2_heap prog h1 in
        let tmp2 = convert_heap2_heap prog h2
        in IF.ConjStar{ (h) with
            IF.h_formula_conjstar_h1 = tmp1;
            IF.h_formula_conjstar_h2 = tmp2; }
    | IF.ConjConj (({ IF.h_formula_conjconj_h1 = h1; IF.h_formula_conjconj_h2 = h2 } as h))
        -> let tmp1 = convert_heap2_heap prog h1 in
        let tmp2 = convert_heap2_heap prog h2
        in IF.ConjConj { (h) with
            IF.h_formula_conjconj_h1 = tmp1;
            IF.h_formula_conjconj_h2 = tmp2; }
    | IF.Phase (({ IF.h_formula_phase_rd = h1; IF.h_formula_phase_rw = h2 } as h))
        -> let tmp1 = convert_heap2_heap prog h1 in
        let tmp2 = convert_heap2_heap prog h2
        in IF.Phase { (h) with
            IF.h_formula_phase_rd = tmp1;
            IF.h_formula_phase_rw = tmp2; }
    | IF.HeapNode2 h2 -> IF.HeapNode (node2_to_node 1 prog h2)
    | IF.HRel _
    | IF.ThreadNode _
    | IF.HTrue | IF.HFalse | IF.HEmp | IF.HeapNode _ | IF.HVar _ -> h0

and convert_heap2_x prog (f0 : IF.formula) : IF.formula =
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

and convert_heap2 prog (f0:IF.formula):IF.formula =
  let pr = Iprinter.string_of_formula in
  Debug.no_1 "convert_heap2" pr pr (convert_heap2_x prog) f0

and convert_struc2 prog (f0:IF.struc_formula):IF.struc_formula =
  let pr = Iprinter.string_of_struc_formula in
  Debug.no_1 "convert_struc2" pr pr (convert_struc2_x prog) f0

and convert_struc2_x prog (f0:IF.struc_formula):IF.struc_formula = match f0 with
  | IF.EAssume b -> IF.EAssume {b with 
        IF.formula_assume_simpl = convert_heap2 prog b.IF.formula_assume_simpl;
        IF.formula_assume_struc = convert_struc2 prog b.IF.formula_assume_struc;}
  | IF.ECase b -> IF.ECase {b with IF.formula_case_branches = map_l_snd (convert_struc2_x prog) b.IF.formula_case_branches};
  | IF.EBase b -> IF.EBase{b with 
        IF.formula_struc_base = convert_heap2 prog b.IF.formula_struc_base;
        IF.formula_struc_continuation = map_opt (convert_struc2_x prog) b.IF.formula_struc_continuation}
  | IF.EInfer b -> IF.EInfer {b with IF.formula_inf_continuation = convert_struc2_x prog b.IF.formula_inf_continuation}
  | IF.EList b -> IF.EList (map_l_snd (convert_struc2_x prog) b)

let order_views (view_decls0 : I.view_decl list) : I.view_decl list* (ident list list) =
  (* generate pairs (vdef.view_name, v) where v is a view appearing in     *)
  (* vdef                                                                  *)
  let rec gen_name_pairs_heap vname h =
    match h with
      | IF.Star { IF.h_formula_star_h1 = h1; IF.h_formula_star_h2 = h2 }
      | IF.Conj { IF.h_formula_conj_h1 = h1; IF.h_formula_conj_h2 = h2 }
      | IF.ConjStar { IF.h_formula_conjstar_h1 = h1; IF.h_formula_conjstar_h2 = h2 }
      | IF.ConjConj { IF.h_formula_conjconj_h1 = h1; IF.h_formula_conjconj_h2 = h2 }
      | IF.Phase { IF.h_formula_phase_rd = h1; IF.h_formula_phase_rw = h2 } ->
            (gen_name_pairs_heap vname h1) @ (gen_name_pairs_heap vname h2)
      | IF.HeapNode { IF.h_formula_heap_name = c } ->
            (* if c = vname *)
            (* then [] *)
            (* else *)
            (try let todo_unk = I.look_up_view_def_raw 7 view_decls0 c in [ (vname, c) ]
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
    | IF.EAssume b-> (gen_name_pairs vname b.IF.formula_assume_simpl)
    | IF.ECase b -> fold_l_snd (gen_name_pairs_struc vname) b.IF.formula_case_branches
    | IF.EBase {IF.formula_struc_base =fb; IF.formula_struc_continuation = cont}->
        (gen_name_pairs vname fb) @(fold_opt (gen_name_pairs_struc vname) cont)
    | IF.EInfer b -> gen_name_pairs_struc vname b.IF.formula_inf_continuation
    | IF.EList b ->  fold_l_snd (gen_name_pairs_struc vname) b
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
    let todo_unk = (List.map
        (fun (v1, v2) -> NG.add_edge g (NG.V.create v1) (NG.V.create v2))
        edges) in
    let scclist = NGComponents.scc_list g in
    let mr = List.filter (fun l -> (List.length l)>1) scclist in
    (* let str = pr_list (pr_list pr_id) mr in *)
    let mutrec = List.concat mr in
    let selfrec = (Gen.BList.difference_eq (=) selfrec mutrec) in
    (* let () = print_endline ("Self Rec :"^selfstr) in *)
    view_rec := selfrec@mutrec ;
    view_scc := scclist ;
    (* if not(mr==[]) *)
    (* then report_warning no_pos ("View definitions "^str^" are mutually recursive") ; *)
    g
        (* if DfsNG.has_cycle g *)
        (* then failwith "View definitions are mutually recursive" *)
        (* else g *)
  in

  let g = build_graph view_decls0 in

  (* take out the view names in reverse order *)
  let view_names = ref ([] : ident list) in
  let store_name n = view_names := n :: !view_names in
  let () = (TopoNG.iter store_name g) in

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
  in
  (r1 @ r2,List.filter (fun ls -> List.length ls > 1) !view_scc)

let order_views (view_decls0 : I.view_decl list) : I.view_decl list * (ident list list) =
  let pr x = string_of_ident_list (List.map (fun v -> v.I.view_name) x) in
  let pr2 = (pr_list (pr_list pr_id)) in
  Debug.no_1 "order_views" pr (pr_pair pr pr2) order_views  view_decls0

let loop_procs : (C.proc_decl list) ref = ref []

let rec seq_elim (e:C.exp):C.exp = match e with
  | C.Label b -> C.Label {b with C.exp_label_exp = seq_elim b.C.exp_label_exp;}
  | C.Assert _ -> e
    (*| C.ArrayAt b -> C.ArrayAt {b with C.exp_arrayat_index = (seq_elim b.C.exp_arrayat_index); } (* An Hoa *)*)
    (*| C.ArrayMod b -> C.ArrayMod {b with C.exp_arraymod_lhs = C.arrayat_of_exp (seq_elim (C.ArrayAt b.C.exp_arraymod_lhs)); C.exp_arraymod_rhs = (seq_elim b.C.exp_arraymod_rhs); } (* An Hoa *)*)
  | C.Assign b -> C.Assign {b with C.exp_assign_rhs = (seq_elim b.C.exp_assign_rhs); }
  | C.Bind b -> C.Bind {b with C.exp_bind_body = (seq_elim b.C.exp_bind_body);}
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
      C.Try ({  C.exp_try_type = b.C.exp_seq_type;
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
  | C.Par b -> C.Par { b with
      C.exp_par_cases = List.map (fun c -> { c with 
        C.exp_par_case_body = seq_elim c.C.exp_par_case_body }) b.C.exp_par_cases }


let conv_exp_to_var e = 
  match e with
    | CP.IConst(i, _) -> Some (CP.mk_sp_const i)
    | CP.Null _ -> Some CP.null_var
    | CP.Var(v, _) -> Some v
    | _ -> None

let merge_ieq_w_eq emap ie_lst =
  let req = ref [] in        
  let new_ie_lst =  List.map (fun ieq ->
      match ieq with
        | CP.BForm (b, lb) ->
              begin
                match b with
                  | (CP.Lt (ex1, ex2, s), l) -> 
                        begin
                          match conv_exp_to_var ex1, conv_exp_to_var ex2 with
                            |  Some v1, Some v2 ->
                                   if CP.EMapSV.is_equiv emap v1 v2 then 
                                     begin
                                       req  := (v1, v2) :: !req;
                                       CP.BForm ((CP.Lte (ex1,  ex2, s), l), lb)
                                     end
                                   else ieq
                            | _, _ -> ieq
                        end
                  | (CP.Gt (ex1, ex2, s), l) ->
                        begin
                          match conv_exp_to_var ex1, conv_exp_to_var ex2 with
                            |  Some v1, Some v2 ->
                                   if CP.EMapSV.is_equiv emap v1 v2 then 
                                     begin
                                       req  := (v1, v2) :: !req;
                                       CP.BForm ((CP.Gte (ex1,  ex2, s), l), lb)
                                     end
                                   else ieq
                            | _, _ -> ieq
                        end
                  | (CP.Neq (ex1, ex2, _), _) ->
                        begin
                          match conv_exp_to_var ex1, conv_exp_to_var ex2 with
                            |  Some v1, Some v2 ->
                                   if CP.EMapSV.is_equiv emap v1 v2 then 
                                     begin
                                       req  := (v1, v2) :: !req;
                                       CP.mkTrue no_pos
                                     end
                                   else ieq
                            | _, _ -> ieq
                        end
                  | (CP.Lte (ex1, ex2, _), _)
                  | (CP.Gte (ex1, ex2, _), _)
                  | (CP.Eq  (ex1, ex2, _), _) ->
                        begin
                          match conv_exp_to_var ex1, conv_exp_to_var ex2 with
                            | Some v1, Some v2 ->
                                   if CP.EMapSV.is_equiv emap v1 v2 then req := (v1, v2) :: !req;
                                   ieq
                            | _, _ -> ieq
                        end
                  | _ -> ieq
              end
        | _ -> ieq
  ) ie_lst in
  (!req, new_ie_lst)

let make_srtict_ieq ieq =
  match ieq with
    | CP.BForm (b, lb) ->
          begin
            match b with
              | (CP.Lte (CP.IConst (i, loci), (CP.Var(v,_) as var), s), l)
              | (CP.Gte ((CP.Var(v,_) as var),CP.IConst (i, loci),  s), l) ->  CP.BForm ((CP.Lt (CP.IConst ((i-1), loci), var, s), l), lb)
              | (CP.Lte ((CP.Var(v,_) as var), CP.IConst (i, loci), s), l)
              | (CP.Gte (CP.IConst (i, loci), (CP.Var(v,_) as var), s), l) ->  CP.BForm ((CP.Lt (var, CP.IConst ((i+1), loci), s), l), lb)
              | _ -> ieq
          end
    | _ -> ieq

let fv_in_common fv f =
  let comm =  Gen.BList.intersect_eq CP.eq_spec_var fv (CP.fv f) in
  match comm with 
    | [] -> false
    | _  -> true

let eq_pair eq (e11,e12) (e21,e22) = 
  eq e11 e21 && eq e12 e22

let is_common_and_not_consumed consumed lst c =
  if Gen.BList.mem_eq CP.equalFormula c lst then 
    match c with
      | CP.BForm (b, _) ->
            begin
              match b with
                | (CP.Eq  (CP.Var(v1,_) , CP.Var(v2,_), _), _) -> 
                      if (Gen.BList.mem_eq (eq_pair CP.eq_spec_var) (v1,v2) consumed) || (Gen.BList.mem_eq  (eq_pair CP.eq_spec_var) (v2,v1) consumed) then false
                      else true
                | _ -> true
            end
      | _ -> true
  else
    false

let hull f1 f2 =  TP.hull (CP.mkOr f1 f2 None no_pos)(* f1 *) (* fix *)
  (* if CP.equalFormula f1 f2 then f1 *)
  (* else *)
  (*   let all1 = CP.fv f1 in *)
  (*   let all2 = CP.fv f2 in *)

  (*   let emap1 = x_add_1 Label_aggr.build_eset_of_conj_formula f1 in *)
  (*   let emap2 = x_add_1 Label_aggr.build_eset_of_conj_formula f2 in *)

  (*   let f1_conj = (CP.split_conjunctions f1) in    *)
  (*   let f1_conj = List.filter (fv_in_common all2) f1_conj in *)
  (*   let f2_conj = (CP.split_conjunctions f2) in *)
  (*   let f2_conj = List.filter (fv_in_common all1) f2_conj in *)

  (*   (\*  todo: replace vars with constants where possible*\) *)
  (*   let (ie1_conj, conj1) = List.partition CP.is_ieq f1_conj in *)
  (*   let (ie2_conj, conj2) = List.partition CP.is_ieq f2_conj in *)

  (*   let ie1 = List.map make_srtict_ieq ie1_conj in *)
  (*   let ie2 = List.map make_srtict_ieq ie2_conj in *)

  (*   let (consumed1, new_ieq2) =  merge_ieq_w_eq emap1 ie2 in *)
  (*   let (_, new_ieq1) =  merge_ieq_w_eq emap2 ie1 in *)

  (*   let conj1 = List.filter (is_common_and_not_consumed consumed1 conj2) conj1 in *)
  (*   (\* let conj2 = List.filter (is_common_and_not_consumed req2 conj1) conj2 in *\) *)

  (*   (\* add extra guards: eg hull(x=0 & z>2 | x>0 & z=2) = 0<=x & 2<=z & 3 < x+z *\) *)
  (*   let hull_f = CP.join_conjunctions (new_ieq1@new_ieq2@conj1) in *)
  (*   (\* to remove dupl and req1 and req2 *\) *)
  (*   hull_f *)
  (*   (\* TP.hull (CP.mkOr f1 f2 None no_pos) *\) *)

let join_hull a f =
  match a,f with
    | CP.AndList f1,CP.AndList f2
          -> 
          let l2_labels =  LP.get_labels f2 in
          let common = List.filter (fun l -> Gen.BList.mem_eq LO.is_equal l l2_labels ) (LP.get_labels f1) in
          let l1 = LP.sort (List.filter (fun (l,_) -> Gen.BList.mem_eq  LO.is_equal l common) f1) in
          let l2 = LP.sort (List.filter (fun (l,_) -> Gen.BList.mem_eq  LO.is_equal l common) f2) in
          let res = 
          match l1, l2 with
            | [], [] ->  if List.length f1 > List.length f2  then f else a (* hull one of the branches *)
            | _ -> 
                  let pairs = List.combine l1 l2 in
                  let merged = List.map (fun ((lx,fx),(ly,fy) ) -> let new_f = hull fx fy in (LO.merge lx ly, new_f)) pairs in
                  let res = CP.mkAndList merged in 
                  res
          in res
    | _,_ -> hull a f

let join_hull a f =
  let pr = Cprinter.string_of_pure_formula in
  Debug.no_2 "join_hull"  pr pr pr join_hull a f 

let join_hull_andlist_lst ls =
  match ls with
    | [] -> CP.mkTrue no_pos
    | f::fs -> List.fold_left (fun a f -> join_hull a f) f fs

let is_AndList f =
  match f with
    | CP.AndList _ -> true
    | _ -> false

let norm_andlist_br ls =
  let ls = List.sort (fun (l,_) (l2,_) -> LO.compare l l2) ls in
  let rec aux l f ls = match ls with
    | [] -> [(l,f)]
    | (l2,f2)::rest -> 
          if LO.is_equal l l2 
          then aux (x_add LO.comb_norm 1 l l2) (CP.mkAnd f f2 no_pos) rest
            else (l,f)::(aux l2 f2 rest)
  in match ls with
    | [] -> ls
    | (l,f)::ls -> aux l f ls
        

let strip_andlist af =
  match af with
    | CP.AndList br -> br
    | _ -> report_error no_pos "expecting andList as argument of strip_andlist"

let to_andlist_form f =
  let fs = CP.split_conjunctions f in
  let (af,f2) = List.partition (is_AndList) fs in
  let f2 = CP.join_conjunctions f2 in
  if af==[] then f2
  else CP.AndList (norm_andlist_br ((LO.unlabelled,f2)::
      (List.concat (List.map strip_andlist af))))

let hull_disj f =
  let df = CP.split_disjunctions f in
  let df2 = List.map to_andlist_form df in
  let df3 = join_hull_andlist_lst df2 in
  [df3]

let remove_disj_clauses (mf: mix_formula): mix_formula = 
  let pf = pure_of_mix mf in
  let rm_disj f = 
    let mf_conjs = CP.split_conjunctions f in
    x_tinfo_hp (add_str "mf_conjs0" (pr_list !CP.print_formula)) mf_conjs no_pos;
    if List.length mf_conjs == 1 then hull_disj f
    else 
      let (disj,mf_conjs) = List.partition CP.is_disjunct mf_conjs in
      x_tinfo_hp (add_str "mf_conjs3" (pr_list !CP.print_formula)) mf_conjs no_pos;
      mf_conjs 
  in
  let mf_conjs = rm_disj pf in
  x_tinfo_hp (add_str "mf_conjs1" (pr_list !CP.print_formula)) mf_conjs no_pos;
  let mf_conjs = List.map (fun x -> match x with 
    | CP.AndList xs -> 
          let ys = List.map (fun (l,a) -> (l,CP.join_conjunctions (rm_disj a))) xs in
          CP.AndList ys
    | y -> y) mf_conjs in
  x_tinfo_hp (add_str "mf_conjs2" (pr_list !CP.print_formula)) mf_conjs no_pos;
  let mf = CP.join_conjunctions (mf_conjs) in
  mix_of_pure mf

let remove_disj_clauses (mf: mix_formula): mix_formula = 
  let pr = !print_mix_formula in
  Debug.no_1 "remove_disj_clauses" pr pr remove_disj_clauses mf

(*transform labels into exceptions, remove the finally clause,
should also check that 
*)
let rec while_labelling (e:I.exp):I.exp = 
  (*let () = print_endline("while_labelling"^Iprinter.string_of_exp e) in*)
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
            | I.NoJumpLabel -> ("default"(*(fresh_label pos)*),false)
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
          (*new class extend __Exc*)
          (* let new_exc = {I.data_name = "rExp" ; *)
          (*                I.data_fields =[]; *)
          (*                I.data_parent_name = raisable_class; *)
          (*                I.data_invs = []; *)
          (*                I.data_pos = no_pos; *)
          (*                I.data_is_template = false; *)
          (*                I.data_methods = [] *)
          (*               } *)
          (* in *)
          (* Added by Zhuohong*)
(*          let new_class_name ret_type = 
            match ret_type with
              | Int -> "ret_int"
              | Bool -> "ret_bool"
              | _ -> failwith "while_return: TO BE IMPLEMENTED"
          in
*)

          let new_raise_val v =
            match v with
              | Some e ->
                    let loc = I.get_exp_pos e in
                    Some (I.New { exp_new_class_name = "ret_"^(new_string_of_typ ret_type);
                    exp_new_arguments=[e];
                    exp_new_pos = loc
                    })
              | None -> v
          in
          (*==================*)
          (*let new_body = I.map_exp b.I.exp_while_body (fun c -> match c with | I.Return b-> 
              Some (I.mkRaise (I.Const_flow loop_ret_flow) true b.I.exp_return_val false b.I.exp_return_path_id b.I.exp_return_pos) | _ -> None) in
          *)
          let new_body = I.map_exp b.I.exp_while_body (fun c -> match c with | I.Return b-> 
              Some (I.mkRaise (I.Const_flow ("ret_"^(new_string_of_typ ret_type))) true (new_raise_val b.I.exp_return_val) false b.I.exp_return_path_id b.I.exp_return_pos) | _ -> None) in
          let b = {b with I.exp_while_body = new_body} in
          let pos = b.I.exp_while_pos in
          let nl2 = fresh_branch_point_id "" in
          let vn = fresh_name () in
          let return_target = I.mkMember (I.mkVar vn pos) ["val"] None pos in 
          (*let return  = I.Return { I.exp_return_val = Some (I.Var { I.exp_var_name= vn; I.exp_var_pos = pos}); I.exp_return_path_id = nl2; I.exp_return_pos = pos} in*)
          let return  = I.Return { I.exp_return_val = Some (return_target); I.exp_return_path_id = nl2; I.exp_return_pos = pos} in
          (*let catch = I.mkCatch (Some vn) (Some ret_type) loop_ret_flow None return pos in*)
          let catch = I.mkCatch (Some vn) (Some (Named ("ret_"^(new_string_of_typ ret_type)))) loop_ret_flow  None return pos in

          (* Modified by Zhuohong*)
          (*let () = exlist # add_edge (string_of_typ ret_type) c_flow in*)
          (***********************)
          (*Some (I.mkTry (I.While b) [catch] [] nl2 pos)*)
          (Some (I.While b))
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
    | Some e->
          let () = fct.proc_has_while_return <- (I.exists_while_return e) in
          (*let () = 
            if fct.proc_has_while_return then
              let _ =print_endline("prepare_lables_x:proc_has_while_return is set\n"^Iprinter.string_of_exp e) in
              ()
            else ()
              
in*)
          (syntax_err_breaks e false []; {fct with I.proc_body = Some (while_labelling (while_return e fct.I.proc_return))})

and prepare_labels (fct: I.proc_decl): I.proc_decl =
  let pr = Iprinter.string_of_proc_decl in
  Debug.no_1 "prepare_labels" pr pr prepare_labels_x fct 

and substitute_seq (fct: C.proc_decl): C.proc_decl = match fct.C.proc_body with
  | None -> fct
  | Some e-> {fct with C.proc_body = Some (seq_elim e)}

let trans_logical_vars lvars =
  List.map (fun (id,_,_)-> CP.SpecVar(lvars.I.exp_var_decl_type, id, Unprimed)) lvars.I.exp_var_decl_decls

let rec add_case_coverage in_pre ctx all pos =
  (* (instant:Cpure.spec_var list)(f:CF.struc_formula): CF.struc_formula  *)
  let pr = Cprinter.string_of_pure_formula in
  let pr2 = pr_list (pr_pair pr Cprinter.string_of_struc_formula) in
  Debug.no_2 "add_case_coverage" pr pr 
      pr2 (fun _ _ -> add_case_coverage_x in_pre ctx all pos) ctx all

(* ctx - pure context of case expression *)
(* all - disj of pure formula encountered *)
and add_case_coverage_x in_pre ctx all pos =
(* (instant:Cpure.spec_var list)(f:CF.struc_formula): CF.struc_formula  *)
  (* let pos = CP.pos_of_formula ctx in *)
  let sat_subno  = ref 0 in
  let f_sat = Cpure.mkAnd ctx (Cpure.mkNot all None no_pos) no_pos in
  let coverage_error = 
    Tpdispatcher.is_sat_sub_no 11 f_sat sat_subno
        (*not (Tpdispatcher.simpl_imply_raw ctx all)*) in
  if coverage_error then
    let simp_all = TP.pairwisecheck f_sat in
    (* let () = Debug.info_hprint (add_str "case pure" Cprinter.string_of_pure_formula) all no_pos in *)
    let warn_str = "case construct has missing scenario" in
    let found_str = (add_str "Found : " Cprinter.string_of_pure_formula) all in
    let add_str = (add_str "Added : " Cprinter.string_of_pure_formula) simp_all in
    let () = x_tinfo_pp ("WARNING : "^warn_str) no_pos in
    let () = x_tinfo_pp found_str no_pos in

    let () = x_tinfo_pp add_str no_pos in

    report_warning pos
        ("WARNING : case construct has missing scenario\n"^found_str^"\n"^add_str^"\n");
    let cont = 
      if in_pre then 
        CF.mkETrue_ensures_True (CF.mkNormalFlow ()) no_pos (* CF.mkEFalse (CF.mkFalseFlow) no_pos *) 
      else CF.mkETrue (CF.mkTrueFlow ()) no_pos in
    [(simp_all,cont)]
        (* let s = (Cprinter.string_of_struc_formula f) in *)
        (* Error.report_error {  Err.error_loc = b.CF.formula_case_pos; *)
        (* Err.error_text = "the guards don't cover the whole domain for : "^s^"\n";} *)
  else []  
  
let line_split (br_cnt:int)(br_n:int)(cons:CP.b_formula)(line:(Cpure.constraint_rel*(int* Cpure.b_formula *(Cpure.spec_var list))) list)
      :Cpure.b_formula*int list * int list =
  (*let () = print_string ("\n line split start "^(Cprinter.string_of_b_formula cons)^"\n") in*)
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
    
    (*let () = print_string ("\n line split: "^
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

  (* int -> *)
  (* CP.b_formula -> *)
  (* (Cpure.constraint_rel * *)
  (*  (int * Cpure.b_formula * Immutable.CP.spec_var list)) *)
  (* list -> Cpure.b_formula * int list * int list *)

let line_split (br_cnt:int)(br_n:int)(cons:CP.b_formula)(line:(Cpure.constraint_rel*(int* Cpure.b_formula *(Cpure.spec_var list))) list)
      :Cpure.b_formula*int list * int list =
  let pr1 = Cprinter.string_of_b_formula in
  let pr_svl = Cprinter.string_of_spec_var_list in
  let pr_cr = Cprinter.string_of_constraint_relation in
  let pr2 = pr_list (fun (cr,(i,b,svl)) -> (pr_quad pr_cr string_of_int pr1 pr_svl) (cr,i,b,svl)) in
  let pr4 = pr_list string_of_int in
  let pr3 = pr_triple pr1 pr4 pr4 in
  Debug.no_2 "line_split" pr1 pr2 pr3 (fun _ _ -> line_split br_cnt  br_n cons line) cons line

let rec splitter_x (f_list_init:(Cpure.formula*CF.struc_formula) list) (v1:Cpure.spec_var list) : CF.struc_formula list =
  (*let () = print_string ("\n splitter got: "^(
    List.fold_left (fun a (c1,c2)-> a^"\n"^(Cprinter.string_of_pure_formula c1)^"--"^
    (Cprinter.string_of_ext_formula c2)) "" f_list_init)
    ^"\n" ) in
    let () = print_string ("\n vars: "^(Cprinter.string_of_spec_var_list v1)^"\n") in*)
  if (List.length v1)<1 then [CF.EList (List.map CF.mkSingle (snd (List.split f_list_init)))]
  else match (List.length f_list_init) with
    | 0 -> raise Not_found
    | 1 -> [(snd (List.hd f_list_init))]
    | _ ->
	  let crt_v = List.hd v1 in
	  let rest_vars = List.tl v1 in	
	  let br_cnt = List.length f_list_init in
          (* type: (CP.formula * CF.struc_formula * Immutable.CP.spec_var list * *)
          (*    Solver.CP.b_formula list) *)
          (* list *)
	  let f_list = List.map (fun (c1,c2)-> 
	      (* let aset = Context.get_aset ( Context.alias_nth 11 ((crt_v, crt_v) :: (CP.pure_ptr_equations c1))) crt_v in *)
              let aset = x_add Csvutil.get_aset (Csvutil.alias_nth 11 ((crt_v, crt_v) :: (CP.pure_ptr_equations c1))) crt_v in
	      let aset = List.filter (fun c-> (String.compare "null" (Cpure.name_of_spec_var c))!=0) aset in
	      let eqs = (CFS.get_equations_sets c1 aset)in
	      let eqs = (CFS.transform_null eqs) in
	      (*let () = print_string ("\n aset: "^(Cprinter.string_of_spec_var_list aset)) in
		let () = print_string ("\n eqs: "^(List.fold_left (fun a c-> a^" -- "^(Cprinter.string_of_b_formula c)) "" eqs )) in*)
	      (c1,c2,aset,eqs)) f_list_init in
          let pr = pr_list (fun (f,_,vl,bf) -> pr_triple Cprinter.string_of_pure_formula Cprinter.string_of_spec_var_list 
	      (pr_list Cprinter.string_of_b_formula) (f,vl,bf)) in
          let () = x_tinfo_hp (add_str "splitter-f_list" pr) f_list no_pos in
	  let f_a_list = Gen.Profiling.add_index f_list in
	  let constr_list = List.concat (List.map (fun (x,(c1,c2,c3,c4))->  List.map (fun c-> (x,c,c3)) c4) f_a_list) in
	  let constr_list = Gen.BList.remove_dups_eq (fun (x1,c1,_)(x2,c2,_)-> (x1=x2)&&(Cpure.equalBFormula c1 c2)) constr_list in
	  let constr_array = Array.of_list constr_list in
	  let sz = Array.length constr_array in
	  let matr = Array.make_matrix sz sz Cpure.Unknown in
	  let f_sat f = x_add TP.is_sat_sub_no 12 f (ref 0) in
	  let f_imply f1 f2 = if (CP.fast_imply [] [f1] f2>0) then true else false in
	  let filled_matr = 
	    Array.mapi(fun x c->(Array.mapi (fun y c->
		if (x>y) then Cpure.compute_constraint_relation f_sat f_imply (constr_array.(x)) (constr_array.(y)) 
		else if x=y then Cpure.Equal 
		else matr.(x).(y) ) c)) matr in
	  let filled_matr = Array.mapi(fun x c->(Array.mapi (fun y c->
	      if (x<y) then filled_matr.(y).(x)
	      else filled_matr.(x).(y)) c)) filled_matr in
	  (*let () = print_string ("\n constr_array: "^(List.fold_left (fun a (x,c,c3)-> a^" \n( "^
	    (string_of_int x)^","^(Cprinter.string_of_b_formula c)^",   "^
	    (Cprinter.string_of_spec_var_list c3))"" constr_list)^"\n") in
	    let () = print_string ("\n matr: "^( Array.fold_right (fun c a-> a^(
	    Array.fold_right (fun c a-> a^" "^(Cprinter.string_of_constraint_relation c )) c "\n ")
	    ) filled_matr "")^"\n") in*)
	  
	  let splitting_constraints = Array.mapi (fun x (br_n,cons,_)->
			let rec arr_exists i b = 
				if i=x then b 
				else if filled_matr.(i).(x)=Cpure.Contradicting || (filled_matr.(i).(x)=Cpure.Equal) then true 
				else arr_exists (i+1) b in 
		  if (arr_exists 0 false) then ((Cpure.BForm (cons, None)),(Cpure.BForm (cons, None)),[],[])
		  else 
			let line_pair =List.combine (Array.to_list filled_matr.(x)) constr_list in
			let neg_cons,l1,l2 = line_split br_cnt br_n cons line_pair in
			let l1_br = List.map (fun c1-> let (_,(v1,v2,_,_))=List.find (fun c2->(fst c2)=c1) f_a_list in (v1,v2)) l1 in
			let l2_br = List.map (fun c1-> let (_,(v1,v2,_,_))=List.find (fun c2->(fst c2)=c1) f_a_list in (v1,v2)) l2 in
			((Cpure.BForm (cons, None)),(Cpure.BForm (neg_cons, None)),l1_br,l2_br)
	  ) constr_array in
          (* type: (Cpure.formula * Cpure.formula  *)
          (*       * (CP.formula * CF.struc_formula) list * *)
          (*       (CP.formula * CF.struc_formula) list)  list *)
          let sc = (Array.to_list splitting_constraints) in
	      let prp = Cprinter.string_of_pure_formula in 
          let pr2 = pr_list (pr_pair prp Cprinter.string_of_struc_formula) in
          let pr = pr_list (pr_quad prp prp pr2 pr2) in
          let () = x_tinfo_hp (add_str "split-ctr" pr) sc no_pos in
          let splitting_constraints = List.filter (fun (_,_,l1,l2)-> ((List.length l2)>0 && (List.length l1)>0))  sc in
          let () = x_tinfo_hp (add_str "split-ctr (filter)" pr) splitting_constraints no_pos in
          if (List.length splitting_constraints)>0 then
            List.concat (List.map (fun (constr,neg_constr,l1,l2)->
                let nf1 = splitter_x l1 rest_vars in
                let nf2 = splitter_x l2 rest_vars in
                List.concat (List.map (fun c1-> List.map (fun c2-> 
                let nf = add_case_coverage true (CP. mkTrue no_pos) (Cpure.mkStupid_Or constr neg_constr None no_pos) no_pos in
	            CF.ECase{					
	                CF.formula_case_branches =[(constr,c1);(neg_constr,c2)]@nf;
	                CF.formula_case_pos = no_pos;} ) nf2) nf1)					
            ) splitting_constraints)
          else splitter_x f_list_init rest_vars

let splitter (f_list_init:(Cpure.formula*CF.struc_formula) list) (v1:Cpure.spec_var list) : CF.struc_formula list =
  let pr1 l = pr_list (pr_pair !CP.print_formula !CF.print_struc_formula) l in
  let pr2 (l:CP.spec_var list) :string = !CP.print_svl l in
  let pr3 (l:CF.struc_formula list):string = pr_list !CF.print_struc_formula l in
  Debug.no_2 "splitter" pr1 pr2 pr3 splitter_x f_list_init v1
		  
(* TODO *)
let rec move_instantiations_x (f:CF.struc_formula):CF.struc_formula*(Cpure.spec_var list) = match f with
  | CF.EBase b->
	let nc, vars = Gen.map_opt_res move_instantiations_x b.CF.formula_struc_continuation in
	let qvars, nf = CF.split_quantifiers b.CF.formula_struc_base in
	let global_ex, imp_inst = (b.CF.formula_struc_exists, b.CF.formula_struc_implicit_inst) in
	let n_qvars = Gen.BList.difference_eq (=) qvars vars in
	let n_globals = Gen.BList.difference_eq (=) global_ex vars in
	let inst_from_qvars = Gen.BList.difference_eq (=) vars qvars in
	let inst_from_global = Gen.BList.difference_eq (=) vars global_ex in
	(CF.EBase {b with 
	    CF.formula_struc_continuation = nc;
	    CF.formula_struc_base = CF.push_exists n_qvars nf ;
	    CF.formula_struc_exists = n_globals;
	    CF.formula_struc_implicit_inst = b.CF.formula_struc_implicit_inst @ inst_from_global @ inst_from_qvars;
	},(Gen.BList.difference_eq (=) vars (inst_from_qvars@inst_from_global)))
  | CF.ECase b-> 
	let new_cases, var_list = 
	  List.split 
	      (List.map 
	          (fun (c1,c2)-> 
		      let nf , vars = move_instantiations_x c2 in
		      ((c1,nf), (vars@(Cpure.fv c1)))
	          ) 
	          b.CF.formula_case_branches) in
	(
	    (CF.ECase {b with 
		CF.formula_case_branches = new_cases}),
	    (List.concat var_list))			
  | CF.EAssume b-> (f,[])
	(*| CF.EVariance b ->
	  let m_var_list = List.fold_left (fun rs (e1, e2) -> rs@(match e2 with
	  | None -> Cpure.afv e1
	  | Some e -> (Cpure.afv e1)@(Cpure.afv e))) [] b.CF.formula_var_measures in
	  let i_var_list = List.fold_left (fun rs e -> rs@(Cpure.afv e)) [] b.CF.formula_var_infer in
	  let new_cont, c_var_list = helper b.CF.formula_var_continuation in
	  (CF.EVariance {b with CF.formula_var_continuation = new_cont}, (m_var_list@i_var_list@c_var_list))*)
  | CF.EInfer b ->
        let new_cont, c_var_list = move_instantiations_x b.CF.formula_inf_continuation in
        (CF.EInfer {b with CF.formula_inf_continuation = new_cont}, c_var_list)
  | CF.EList l -> 
	let l,vars = map_l_snd_res move_instantiations_x l in
	(CF.EList l, List.concat vars)
	
and move_instantiations f = 
  let pr = Cprinter.string_of_struc_formula in
  Debug.no_1 "move_instantiations" pr (pr_pair pr !CP.print_svl) move_instantiations_x f
      
      
and formula_case_inference cp (f_ext:CF.struc_formula)(v1:Cpure.spec_var list) : CF.struc_formula = 
  let pr = Cprinter.string_of_struc_formula in
  let pr2 = Cprinter.string_of_spec_var_list in
  Debug.no_2 "formula_case_inference" pr pr2 pr (fun _ _ -> formula_case_inference_x cp f_ext v1) f_ext v1


and formula_case_inference_x cp (f_ext:CF.struc_formula)(v1:Cpure.spec_var list) : CF.struc_formula = 
  (*let () = print_string (" case inference, this feature needs to be revisited \n") in*)
  match f_ext with 
    | CF.EList l -> 
      let rec norm_list a l = match l with 
	      [] -> a 
	    | h:: t -> (match (snd h) with 
		| CF.EList ll ->  norm_list a (ll@t)
		| _ -> norm_list (a@[h]) t) in 
	  let l = norm_list [] l in
	  (try 
            let f_list = List.map (fun (_,c)->
		let d = match c with
		  | CF.EBase b-> if b.CF.formula_struc_continuation <> None then
		      Error.report_error { Error.error_loc = no_pos; Error.error_text ="malfunction: trying to infer case guard on a struc formula"}
		    else b.CF.formula_struc_base 
		  | _ -> 
			(print_string ("Found: "^(Cprinter.string_of_struc_formula c)^"n");
			Error.report_error { Error.error_loc = no_pos; Error.error_text ="malfunction: trying to infer case guard on a struc formula"})
		in
		let f_aux = !force_verbose_xpure in
		force_verbose_xpure:=true;
		let not_fact,_, _ = (x_add Cvutil.xpure_symbolic 11 cp d) in
		force_verbose_xpure:=f_aux;
		let fact = x_add_1 Solver.normalize_to_CNF (pure_of_mix not_fact) no_pos in
                (* let fact = CP.drop_disjunct fact in *)
                let sfact = TP.simplify fact in
                (* let sfact = fact in *)
                let hfact = TP.hull sfact in
                let () = x_tinfo_hp (add_str "not_fact" Cprinter.string_of_mix_formula) not_fact no_pos in
                let () = x_tinfo_hp (add_str "after norm" Cprinter.string_of_pure_formula) fact no_pos in
                let () = x_tinfo_hp (add_str "after simplify" Cprinter.string_of_pure_formula) sfact no_pos in
                let () = x_tinfo_hp (add_str "after hull" Cprinter.string_of_pure_formula) hfact no_pos in
                let fact = hfact in
 		(* let fact = Cpure.drop_disjunct fact in *)
                (* let () = x_tinfo_hp (add_str "drop_disj" Cprinter.string_of_pure_formula) fact no_pos in *)
		let fact = Cpure.rename_top_level_bound_vars fact in
                let () = x_tinfo_hp (add_str "rename" Cprinter.string_of_pure_formula) fact no_pos in
		let fact,_,_(*all,exist*) = Cpure.float_out_quantif fact in
                let () = x_tinfo_hp (add_str "float out" Cprinter.string_of_pure_formula) fact no_pos in
		let fact = Cpure.check_not fact in
                let () = x_tinfo_hp (add_str "check not" Cprinter.string_of_pure_formula) fact no_pos in
		(fact,c)) l in    
            let pr = pr_list (fun (f,_) -> Cprinter.string_of_pure_formula f) in
            let () = x_tinfo_hp (add_str "f_list" pr) f_list no_pos in
            let sp = splitter f_list v1 in
	    fst (move_instantiations (List.hd sp))
	  with _ -> f_ext)
    | _ -> f_ext 
          
and view_case_inference_x cp (ivl:Iast.view_decl list) (cv:Cast.view_decl):Cast.view_decl = 
  try
    let iv = List.find (fun c->c.Iast.view_name = cv.Cast.view_name) ivl in
    if (iv.Iast.try_case_inference) then
      let () = Debug.ninfo_pprint "perform view case_infer" no_pos in
      let sf = (CP.SpecVar (Named cv.Cast.view_data_name, self, Unprimed)) in
      let vp = cv.Cast.view_vars in
      let () = x_tinfo_hp (add_str "view params" Cprinter.string_of_spec_var_list) vp no_pos in
      (*TODO: disallow variables that are not instantiated in the case guards, more specifically, 
        view parameters should not be in case guards*)
      let f = formula_case_inference cp cv.Cast.view_formula ([sf]@vp) in
      {cv with 
	  Cast.view_formula = f; 
	  Cast.view_case_vars =Gen.BList.intersect_eq (=) (sf::cv.C.view_vars) (CF.guard_vars f); }
    else cv
  with _ -> cv 	

and view_case_inference cp (ivl:Iast.view_decl list) (cv:Cast.view_decl):Cast.view_decl =
  let pr = Cprinter.string_of_view_decl in
  Debug.no_1 "view_case_inference" pr pr (fun _ -> view_case_inference_x cp ivl cv) cv

and case_inference_x (ip: Iast.prog_decl) (cp:Cast.prog_decl):Cast.prog_decl = 
  {cp with Cast.prog_view_decls = List.map (view_case_inference cp ip.Iast.prog_view_decls) cp.Cast.prog_view_decls}

and case_inference (ip: Iast.prog_decl) (cp:Cast.prog_decl):Cast.prog_decl = 
  Debug.no_1 "case_inference" pr_none pr_none (fun _ -> case_inference_x ip cp) ip

let mk_new_return_data_decl_from_typ (t:typ):(I.data_decl) =
  let type_name = new_string_of_typ t in
  let new_data_fields = [((t,"val"),no_pos,false,[])] in
  {
      I.data_name = "ret_"^type_name;
      I.data_fields = new_data_fields;
      I.data_parent_name = "__RET";
      I.data_invs = [];
      I.data_is_template = false;
      I.data_methods = [];
      I.data_pos = no_pos;
  }

let mk_ret_type_into_data_decls (prog:I.prog_decl):(I.data_decl list)=
  let rec helper (typlst:typ list):(I.data_decl list)=
    match typlst with
      | h::rest -> (mk_new_return_data_decl_from_typ h) :: (helper rest)
      | [] -> []
  in
  let typ_list = I.no_duplicate_while_return_type_list prog.prog_proc_decls in
  helper typ_list

(*HIP*)
let rec trans_prog_x (prog4 : I.prog_decl) (*(iprims : I.prog_decl)*): C.prog_decl * I.prog_decl=
  (*let () = print_string ("--> input prog4 = \n"^(Iprinter.string_of_program prog4)^"\n") in*)
  (* print_string "trans_prog\n"; *)
  let () = (exlist # add_edge "Object" "") in
  let () = (exlist # add_edge "String" "Object") in
  let () = (exlist # add_edge raisable_class "Object") in
  (* let () = (exlist # add_edge c_flow "Object") in *)
  let () = I.inbuilt_build_exc_hierarchy () in (* for inbuilt control flows *)
  (* let () = (exlist # add_edge error_flow "Object") in *)
  (* let () = I.build_exc_hierarchy false iprims in (\* Errors - defined in prelude.ss*\) *)
  let prog4 = if (!Globals.perm = Globals.Dperm)
  then I.add_bar_inits prog4 
  else prog4
  in
  (*let () = print_string (Iprinter.string_of_program prog4) in*)
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
  (* Added by Zhuohong *)
  let prog4 = {prog4 with I.prog_data_decls = (mk_ret_type_into_data_decls prog4)@prog4.I.prog_data_decls; } in
  (*let () = print_endline ("@@prog4\n"^Iprinter.string_of_program prog4^"@@prog4\n") in*)
  (* ***************** *)

  let () = I.build_exc_hierarchy true prog4 in  (* Exceptions - defined by users *)
  (* let prog3 = *)
  (*         { prog4 with I.prog_data_decls = iprims.I.prog_data_decls @ prog4.I.prog_data_decls; *)
  (*                      I.prog_proc_decls = iprims.I.prog_proc_decls @ prog4.I.prog_proc_decls; *)
  (*         } *)
  (* in *)
  (*let () = exlist # compute_hierarchy in*)
  (* let () = print_endline (exlist # string_of ) in *)
  let prog3 = prog4 in
  
  (*let () = print_endline ("@@prog3\n"^Iprinter.string_of_program prog3^"@@prog3\n") in*)
  let prog2 = { prog3 with I.prog_data_decls =
          ({I.data_name = raisable_class;I.data_fields = [];I.data_parent_name = "Object";I.data_invs = [];I.data_is_template = false;I.data_methods = []; I.data_pos = no_pos; })
          ::({I.data_name = error_flow;I.data_fields = [];I.data_parent_name = "Object";I.data_invs = [];I.data_is_template = false;I.data_methods = []; I.data_pos = no_pos; })
          ::({I.data_name = mayerror_flow;I.data_fields = [];I.data_parent_name = "Object";I.data_invs = [];I.data_is_template = false;I.data_methods = []; I.data_pos = no_pos; })
          ::({I.data_name = bfail_flow;I.data_fields = [];I.data_parent_name = "Object";I.data_invs = [];I.data_is_template = false;I.data_methods = []; I.data_pos = no_pos; })
          :: prog3.I.prog_data_decls;} in
  (* let () = print_endline (exlist # string_of ) in *)
  (* let () = I.find_empty_static_specs prog2 in *)
  let prog2 = I.add_normalize_lemmas prog2 in
  let prog1 = { prog2 with
      I.prog_proc_decls = List.map prepare_labels prog2.I.prog_proc_decls;
      I.prog_data_decls = List.map (fun c-> {c with I.data_methods = List.map prepare_labels c.I.data_methods;}) prog2.I.prog_data_decls; } in
  (*let () = print_string ("exc: "^(exlist#string_of)^"\n") in*)
  let () = exlist # compute_hierarchy in   
  (*let () = print_string ("exc: "^(exlist#string_of)^"\n") in*)
  (* let () = print_endline (Exc.string_of_exc_list (3)) in *)
  (* let () = I.find_empty_static_specs prog1 in *)
  let prog0 = { prog1 with
      I.prog_data_decls = I.remove_dup_obj prog1.I.prog_data_decls;} in
  
  (* let () = print_string ("--> input \n"^(Iprinter.string_of_program prog0)^"\n") in *)
  (* let () = I.find_empty_static_specs prog0 in *)
  let () = I.build_hierarchy prog0 in
  (* let () = print_string "trans_prog :: I.build_hierarchy PASSED\n" in *)
  let check_overridding = Chk.overridding_correct prog0 in
  let check_field_dup = Chk.no_field_duplication prog0 in
  let check_method_dup = Chk.no_method_duplication prog0 in
  let check_field_hiding = Chk.no_field_hiding prog0 in
  if check_field_dup && (check_method_dup && (check_overridding && check_field_hiding))
  then
    ( begin
      (* let () = print_flush (Exc.string_of_exc_list (10)) in *)
      (* exlist # compute_hierarchy; *)
      (* let () = print_endline (Exc.string_of_exc_list (11)) in *)
      let prims,prim_rels = gen_primitives prog0 in
      (* let prim_rel_ids = List.map (fun rd -> (RelT,rd.I.rel_name)) prim_rels in *)
      let () = Debug.ninfo_hprint (add_str "prims" (pr_list Iprinter.string_of_proc_decl)) prims no_pos in
      let prims = List.map (fun p -> {p with I.proc_is_main = false}) prims in
      (* let prims,prim_rels = ([],[]) in *)
      let prog = { (prog0) with I.prog_proc_decls = prims @ prog0.I.prog_proc_decls;
	  (* AN HOA : adjoint the program with primitive relations *)
	  I.prog_rel_decls = prim_rels @ prog0.I.prog_rel_decls;
	  (* I.prog_rel_ids = prim_rel_ids @ prog0.I.prog_rel_ids; *)
      } in
      (*let () = print_string ("--> input \n"^(Iprinter.string_of_program prog)^"\n") in*)
      (set_mingled_name prog;
      let all_names =(List.map (fun p -> p.I.proc_mingled_name) prog0.I.prog_proc_decls) @
        (List.map (fun ddef -> ddef.I.data_name) prog0.I.prog_data_decls) @
        (List.map (fun vdef -> vdef.I.view_name) prog0.I.prog_view_decls)(*@
			                                                   (List.map (fun bdef -> bdef.I.barrier_name) prog0.I.prog_barrier_decls)*) in
      let dups = Gen.BList.find_dups_eq (=) all_names in
      (* let () = I.find_empty_static_specs prog in *)
      if not (Gen.is_empty dups) then
	(print_string ("duplicated top-level name(s): " ^((String.concat ", " dups) ^ "\n")); failwith "Error detected - astsimp")
      else (
	  (* let () = print_string ("\ntrans_prog: Iast.prog_decl: before case_normalize" ^ (Iprinter.string_of_program prog) ^ "\n") in *)
	  let prog = case_normalize_program prog in

	  let prog = if !infer_slicing then slicing_label_inference_program prog else prog in

	  (* let () = print_string ("\ntrans_prog: Iast.prog_decl: " ^ (Iprinter.string_of_program prog) ^ "\n") in *)
          (***************************************************)
          let prog =
            if (!Globals.allow_ptr) then 
              let () = print_string ("Eliminating variable aliasing...\n"); flush stdout in
              let new_prog = x_add_1 Pointers.trans_pointers prog in
              let () = if (!Globals.print_input) then print_string (Iprinter.string_of_program new_prog) else () in
              let () = print_string ("Eliminating pointers...PASSED \n"); flush stdout in
              new_prog
            else prog
          in 
          let prog = 
            if (!Globals.infer_mem) then 
              let infer_views =  List.map (fun c -> Mem.infer_mem_specs c prog) prog.I.prog_view_decls in
              {prog with I.prog_view_decls = infer_views}
            else prog 
          in 
          (***************************************************)
	  (* let () =  print_endline " after case normalize" in *)
          (* let () = I.find_empty_static_specs prog in *)
          let ctempls = List.map (trans_templ prog) prog.I.prog_templ_decls in
          let tmp_views,ls_mut_rec_views = order_views prog.I.prog_view_decls in
          let cuts = List.map (trans_ut prog) prog.I.prog_ut_decls in
	  (* let () = x_add Iast.set_check_fixpt prog.I.prog_data_decls tmp_views in *)
	  (* let () = print_string "trans_prog :: going to trans_view \n" in *)
          x_tinfo_hp (add_str "trans_prog 1 (views)" (pr_list Iprinter.string_of_view_decl))  prog.I.prog_view_decls  no_pos;
          let todo_unk = List.map (fun v ->  v.I.view_imm_map <- Immutable.icollect_imm v.I.view_formula v.I.view_vars v.I.view_data_name  prog.I.prog_data_decls )  prog.I.prog_view_decls  in
          x_tinfo_hp (add_str "trans_prog 2 (views)" (pr_list Iprinter.string_of_view_decl))  prog.I.prog_view_decls  no_pos;
          let tmp_views_derv,tmp_views= List.partition (fun v -> v.I.view_derv) tmp_views in
          (* let cviewsb = List.fold_left (fun transed_views v -> *)
          (*     let nview = trans_view prog (List.concat ls_mut_rec_views) *)
          (*       transed_views [] v in *)
          (*     transed_views@[nview] *)
          (* ) [] tmp_views in *)
          (* (\* Loc: to compute invs for mut-rec views *\) *)
          (* let cviewsa = Fixcalc.compute_inv_mutrec ls_mut_rec_views cviewsb in *)
          let cviewsa = trans_views prog ls_mut_rec_views (List.map (fun v -> (v,[])) tmp_views) in
          let tmp_views_derv1 = mark_rec_and_der_order tmp_views_derv in
          let () = x_tinfo_hp (add_str "derv length" (fun ls -> string_of_int (List.length ls))) tmp_views_derv1 no_pos in
          let cviews_derv = List.fold_left (fun norm_views v ->
              let der_view = x_add_1 Derive.trans_view_dervs prog Rev_ast.rev_trans_formula trans_view norm_views v in
              (norm_views@[der_view])
          ) cviewsa tmp_views_derv1 in
          let cviews = (* cviews_orig@ *)cviews_derv in
          let cviews1 =
            (*todo: after elim useless, update methos specs. tmp: do not elim*)
            if (* !Globals.pred_elim_useless *) false then
              Norm.norm_elim_useless cviews (List.map (fun vdef -> vdef.C.view_name) cviews)
            else cviews
          in
          let cviews2 =
            if !Globals.norm_cont_analysis then
              Norm.cont_para_analysis prog cviews1
            else
              cviews1
          in
          (* let () = print_string "trans_prog :: trans_view PASSED\n" in *)
          let crels0 = List.map (trans_rel prog) prog.I.prog_rel_decls in (* An Hoa *)
          let () = prog.I.prog_rel_ids <- List.map (fun rd -> (RelT[],rd.I.rel_name)) prog.I.prog_rel_decls in
          let pr_chps = List.map (trans_hp prog) prog.I.prog_hp_decls in 
      let chps1, pure_chps = List.split pr_chps in
          let () = prog.I.prog_hp_ids <- List.map (fun rd -> (HpT,rd.I.hp_name)) prog.I.prog_hp_decls in
      let crels1 = crels0@pure_chps in
      let caxms = List.map (trans_axiom prog) prog.I.prog_axiom_decls in (* [4/10/2011] An Hoa *)
          (* let () = print_string "trans_prog :: trans_rel PASSED\n" in *)
      let cdata =  List.map (trans_data prog) prog.I.prog_data_decls in
	  (* let () = print_string "trans_prog :: trans_data PASSED\n" in *)
	  (* let () = print_endline ("trans_prog :: trans_data PASSED :: procs = " ^ (Iprinter.string_of_proc_decl_list prog.I.prog_proc_decls)) in *)
          let todo_unk = List.map (fun p ->
          if p.I.proc_is_main then
            I.detect_invoke prog p
          else
                let () = p.I.proc_is_invoked <- false in
            []
      ) (prog.I.prog_proc_decls) in
      let old_i_hp_decls = prog.I.prog_hp_decls in
          let () = ihp_decl:= [] in
          let cprocs1 = List.map (trans_proc prog) prog.I.prog_proc_decls in
          let iloop_hp_decls = !ihp_decl in
          (* List.filter (fun hpdecl -> *)
          (*     not (List.exists (fun hp -> String.compare hpdecl.I.hp_name hp.I.hp_name = 0) *)
          (*         old_i_hp_decls) *)
          (* ) (prog.I.prog_hp_decls) in *)
      let pr_loop_chps = List.map (trans_hp prog) iloop_hp_decls in 
      let c_loophps, loop_pure_chps = List.split pr_loop_chps in
      let chps = chps1@c_loophps in
      let crels = crels1@loop_pure_chps in
	  (* let () = print_string "trans_prog :: trans_proc PASSED\n" in *)
      (* Start calling is_sat,imply,simplify from trans_proc *)
      let cprocs = !loop_procs @ cprocs1 in
          (* let () = print_newline () in *)
          (* let () = List.iter (fun p -> *)
      (*     if p.C.proc_is_main then *)
      (*     print_endline (p.C.proc_name ^ " : " ^ string_of_bool(p.C.proc_is_invoked)) *)
      (*     else () *)
      (* ) cprocs in *)
      (* let (l2r_coers, r2l_coers) = trans_coercions prog in (\* Andreeac: Lemma - to unify here *\) *)
          (* let () = Lem_store.all_lemma # set_coercion l2r_coers r2l_coers in *)
          (* let () = List.iter proc_one_lemma cmds; *)
      let log_vars = List.concat (List.map (trans_logical_vars) prog.I.prog_logical_var_decls) in 
      let bdecls = List.map (trans_bdecl prog) prog.I.prog_barrier_decls in
          let ut_vs = cuts @ C.ut_decls # get_stk in
          let () = Debug.ninfo_hprint (add_str "ut_vs added" (pr_list (fun ut -> ut.C.ut_name))) ut_vs no_pos in
      let cprog = {
	  C.prog_data_decls = cdata;
	  C.prog_view_decls = cviews2;
	  C.prog_barrier_decls = bdecls;
	  C.prog_logical_vars = log_vars;
	  C.prog_rel_decls = crels; (* An Hoa *)
	      C.prog_templ_decls = ctempls;
              C.prog_ut_decls = (ut_vs);
	      C.prog_hp_decls = chps;
	      C.prog_view_equiv = []; (*to update if views equiv is allowed to checking at beginning*)
	  C.prog_axiom_decls = caxms; (* [4/10/2011] An Hoa *)
	  (*C.old_proc_decls = cprocs;*)
	  C.new_proc_decls = C.create_proc_decls_hashtbl cprocs;
	  (*C.prog_left_coercions = l2r_coers;*)
	  (*C.prog_right_coercions = r2l_coers;*)} in
      
      let cprog1 = { cprog with			
	  (* C.old_proc_decls = List.map substitute_seq cprog.C.old_proc_decls; *)
              C.new_proc_decls = C.proc_decls_map substitute_seq cprog.C.new_proc_decls; 
	      C.prog_data_decls = List.map (fun c-> {c with C.data_methods = List.map substitute_seq c.C.data_methods;}) cprog.C.prog_data_decls; } in
          (ignore (List.map (fun vdef ->  (compute_view_x_formula cprog vdef !Globals.n_xpure )) cviews2);
          ignore (List.map (fun vdef ->  set_materialized_prop vdef ) cprog1.C.prog_view_decls);
          ignore (C.build_hierarchy cprog1);
	  let cprog1 = fill_base_case cprog1 in
          let cprog2 = sat_warnings cprog1 in   
	  let cprog2 = Solver.normalize_perm_prog cprog2 in
	  let cprog2 = if (!Globals.enable_case_inference) then sat_warnings (case_inference prog cprog2) else cprog2 in 
          let cprog3 = if (!Globals.enable_case_inference || (not !Globals.dis_ps) (* or !Globals.allow_pred_spec *)) 
          then pred_prune_inference cprog2 else cprog2 in
	  (*let cprog3 = normalize_fracs cprog3 in*)
          let todo_unk = List.map (check_barrier_wf cprog3) cprog3.C.prog_barrier_decls in   
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
          (* TNT: Automatically adding @post for dependence methods of @term methods *)
          let c = if !Globals.tnt_add_post then C.add_post_for_tnt_prog c else c in
          (* let () = print_endline (exlist # string_of) in *)
          (* let () = exlist # sort in *)
	  (* let () = if !Globals.print_core then print_string (Cprinter.string_of_program c) else () in *)
	  (c,prog))))
    end)
  else failwith "Error detected at trans_prog"

and trans_prog (prog : I.prog_decl) : C.prog_decl * I.prog_decl=
  let pr_in = Iprinter.string_of_program in
  let pr_out (cprog,iprog) = Cprinter.string_of_program cprog in
  Debug.no_1 "trans_prog" pr_in pr_out (fun x -> trans_prog_x prog) prog

(* Replaced to use new_proc_decls *)
(*  
    and add_pre_to_cprog cprog = 
    {cprog with C.old_proc_decls = List.map (fun c -> 
    let ns = add_pre(*_debug*) cprog c.Cast.proc_static_specs in
    let () = c.Cast.proc_stk_of_static_specs # push ns in
    c
(* {c with  Cast.proc_static_specs_with_pre = add_pre(\*_debug*\) cprog c.Cast.proc_static_specs; *)
(*     (\*Cast.proc_dynamic_specs = add_pre cprog c.Cast.proc_dynamic_specs;*\)} *)
    ) cprog.C.old_proc_decls;}  
*)
and add_pre_to_cprog_one cprog c =
  let ns = add_pre cprog c.C.proc_static_specs in
  (*to handle @C. should handle copy on prim types?*)
  let ns_caller = if c.C.proc_by_copy_params = [] then ns else
    trans_copy_spec_4caller c.C.proc_by_copy_params ns
  in
  let () = c.C.proc_stk_of_static_specs # push ns_caller in
  c

and add_pre_to_cprog cprog = 
  { cprog with C.new_proc_decls = C.proc_decls_map (fun c -> 
      (* let ns = add_pre cprog c.C.proc_static_specs in *)
      (* (\*to handle @C. should handle copy on prim types?*\) *)
      (* let ns_caller = if c.C.proc_by_copy_params = [] then ns else *)
      (*   trans_copy_spec_4caller c.C.proc_by_copy_params ns *)
      (* in *)
      (* let () = c.C.proc_stk_of_static_specs # push ns_caller in *)
      (* c *)
      add_pre_to_cprog_one cprog c
  ) cprog.C.new_proc_decls; }   

and sat_warnings cprog = 
  let sat_warnings_op () =
    let warn n discard = 
      print_string_quiet ("WARNING : the view body for "^n^" contains unsat branch(es) :"^(List.fold_left (fun a c-> a^"\n   "^(Cprinter.string_of_formula c)) "" discard)^"\n") in
    let trim_unsat (f:CF.formula):(CF.formula* CF.formula list) =  
      let () = proving_loc #set (CF.pos_of_formula f) in
      if CF.is_trivial_f f then (f,[])
      else 
        let goods,unsat_list = x_add_1 Solver.find_unsat cprog f in
        let nf = match goods with
	  | x::[]-> x
	  | _ -> List.fold_left ( fun a c -> CF.mkOr c a no_pos) (CF.mkFalse (CF.mkTrueFlow ()) no_pos) goods in
        (nf,unsat_list) 
    in
    let trim_unsat (f:CF.formula):(CF.formula* CF.formula list) =
      let pr = Cprinter.string_of_formula in
      Debug.no_1 "trim_unsat" pr (pr_pair pr (pr_list pr)) trim_unsat f
    in

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
	      | None -> 
		    let filtered = fst (Solver.find_unsat cprog b.CF.formula_struc_base) in
		    List.map (fun d-> 
			if CF.isAnyConstFalse d then CF.mkEBase d None no_pos
			else CF.EBase {b with CF.formula_struc_base = d}) filtered 
	      | _ -> [f])
	  | _ -> [f] in
        let ncf = match c.Cast.view_formula with 
	  | CF.EList b-> CF.EList (List.concat (List.map (fun (l,c)-> List.map (fun c-> (l,c)) (test c)) b))
	  | _ -> (match test c.Cast.view_formula with 
	      | x::[] -> x
	      | _ as l-> CF.EList (List.map (fun c-> (empty_spec_label_def,c)) l)) in
        (*      List.fold_left (fun a c-> match (snd c) with
                | CF.EBase b -> if ((List.length b.CF.formula_ext_continuation)>0) then c::a
                else 
                let goods, unsat_list = x_add_1 Solver.find_unsat cprog b.CF.formula_ext_base in 
                (List.map (fun d-> (fst c, CF.EBase {b with CF.formula_ext_base = d})) goods) @ a 
                |  _ -> c::a) [] c.Cast.view_formula in      *)
        {c with Cast.view_un_struc_formula = nf; Cast.view_formula = ncf; 
	    Cast.view_user_inv = if CF.isConstDFalse ncf then MCP.mkMFalse no_pos else c.Cast.view_user_inv;}    
    ) cprog.Cast.prog_view_decls in  
    {cprog with Cast.prog_view_decls = n_pred_list;}
  in
  wrap_proving_kind PK_Sat_Warning sat_warnings_op ()    

and trans_data (prog : I.prog_decl) (ddef : I.data_decl) : C.data_decl =
  let pr_in = Iprinter.string_of_data_decl in
  let pr_out = Cprinter.string_of_data_decl in
  Debug.no_1 "trans_data" pr_in pr_out (fun _ -> trans_data_x prog ddef) ddef

and trans_data_x (prog : I.prog_decl) (ddef : I.data_decl) : C.data_decl =
  (* Update the list of undefined data types *)
  (** 
      * An Hoa [22/08/2011] : translate field with inline consideration.
  **)
  (* let trans_field_ann ann= *)
  (*   match ann with *)
  (*     | Iast.VAL -> Cast.VAL *)
  (*     | Iast.REC -> Cast.REC *)
  (*     | Iast.F_NO_ANN -> Cast.F_NO_ANN *)
  (* in *)
  let trans_field ((t, c), pos, il, ann) =
    let n_ann = if ann = [] then [gen_field_ann t] else ann in
    (((trans_type prog t pos), c),(* trans_field_ann *) n_ann)
  in
  (* let () = print_endline ("[trans_data] translate data type { " ^ ddef.I.data_name ^ " }") in
     let temp = expand_inline_fields ddef.I.data_fields in
     let () = print_endline "[trans_data] expand inline fields result :" in
     let () = print_endline (Iprinter.string_of_decl_list temp "\n") in *)
  (* let pr1 ((t, c), pos, il, ann) = (pr_triple string_of_typ pr_id (pr_list pr_id)) (t,c,ann) in *)
  (* let () = Debug.info_hprint (add_str "    ddef.I.data_fields:" (pr_list pr1)) ddef.I.data_fields no_pos in *)
  let fields = 
    List.map trans_field (I.expand_inline_fields prog.I.prog_data_decls ddef.I.data_fields)
  in
  (* let () = Debug.info_hprint (add_str "    fields:" (pr_list (pr_pair (pr_pair string_of_typ pr_id) (pr_list pr_id)))) *)
  (*     fields no_pos in *)
  let res = {
      C.data_name = ddef.I.data_name;
      C.data_pos = ddef.I.data_pos;
      C.data_fields = fields;
      C.data_parent_name = ddef.I.data_parent_name;
      C.data_methods = List.map (trans_proc prog) ddef.I.data_methods;
      C.data_invs = [];
  } in
  (* let () = print_endline ("[trans_data] output = " ^ (Cprinter.string_of_data_decl res)) in *)
  res

(* TODO CG : should normalise nxpure better *)
(* xform: self=null & n=0 | n=1 & self!=null | n=2 & self!=null |  *)
(*          self!=null & 3<=n *)
and compute_view_x_formula (prog : C.prog_decl) (vdef : C.view_decl) (n : int) =
  let foo () =
    Debug.no_eff_2 "compute_view_x_formula" [true]
        (* Cprinter.string_of_program *)
        Cprinter.string_of_view_decl  
        string_of_int 
        (fun x ->   "void")
        (* Cprinter.string_of_view_decl vdef) *)
        (compute_view_x_formula_x prog) vdef n in
  let foo = wrap_lbl_dis_aggr foo in
  wrap_proving_kind PK_Pred_Check_Inv foo () 

      
(* and compute_view_x_formula_x (prog : C.prog_decl) (vdef : C.view_decl) (n : int) = *)
(*   let compute_view_x_formula_x_op ()= *)
(*     let pos = CF.pos_of_struc_formula vdef.C.view_formula in *)
(*     let _=proving_loc # set pos in *)
(*     (if (n > 0 && not(vdef.C.view_is_prim)) then *)
(*       (       *)
(*        let (xform', addr_vars', ms) = Solver.xpure_symbolic prog (C.formula_of_unstruc_view_f vdef) in    *)
(*        let addr_vars = CP.remove_dups_svl addr_vars' in *)
(*        let xform = MCP.simpl_memo_pure_formula Solver.simpl_b_formula Solver.simpl_pure_formula xform' (x_add TP.simplify_a 10) in *)
(*        let formula1 = CF.formula_of_mix_formula xform pos in *)
(*        let ctx = CF.build_context (CF.true_ctx ( CF.mkTrueFlow ()) Lab2_List.unlabelled pos) formula1 pos in *)
(*        let formula = CF.formula_of_mix_formula vdef.C.view_user_inv pos in *)
(*        let (rs, _) = x_add Solver.heap_entail_init prog false (CF.SuccCtx [ ctx ]) formula pos in *)
(*        let () = if not(CF.isFailCtx rs) then *)
(*          (vdef.C.view_x_formula <- xform; *)
(*             vdef.C.view_xpure_flag <- TP.check_diff vdef.C.view_user_inv xform;          *)
(*             vdef.C.view_addr_vars <- addr_vars; *)
(*          vdef.C.view_baga <- (match ms.CF.mem_formula_mset with | [] -> [] | h::_ -> h) ; *)
(*          compute_view_x_formula_x prog vdef (n - 1)) *)
(*        else report_error pos "view formula does not entail supplied invariant\n" in () *)
(*       ) *)
(*     else (); *)
(*     if !Globals.print_x_inv && (n = 0) *)
(*     then *)
(*       (print_string ("\ncomputed invariant for view: " ^ vdef.C.view_name ^"\n" ^(Cprinter.string_of_mix_formula vdef.C.view_x_formula) ^"\n"); *)
(*       print_string ("addr_vars: " ^(String.concat ", "(List.map CP.name_of_spec_var vdef.C.view_addr_vars))^ "\n\n")) *)
(*     else ()) *)
(*   in  *)
(*   wrap_proving_kind "PRED CHECK-INVARIANT" compute_view_x_formula_x_op ()  *)

and compute_view_x_formula_x (prog : C.prog_decl) (vdef : C.view_decl) (n : int) =
  let pos = CF.pos_of_struc_formula vdef.C.view_formula in
  let _=proving_loc # set pos in
  let rec helper n do_not_compute_flag =
    (* let compute_view_x_formula_x_op ()= *)
    (if (n > 0 (* && not(vdef.C.view_is_prim) *)) then
      (
          let old_baga_imm_flag = !Globals.baga_imm in
          let () = Globals.baga_imm := true in
	  let (xform', addr_vars', ms) = x_add Cvutil.xpure_symbolic 1 prog (C.formula_of_unstruc_view_f vdef) in
          let () = Globals.baga_imm := old_baga_imm_flag in
	  let addr_vars = CP.remove_dups_svl addr_vars' in
	  let xform = MCP.simpl_memo_pure_formula Cvutil.simpl_b_formula Cvutil.simpl_pure_formula xform' (x_add TP.simplify_a 10) in
          (* let () = print_endline ("\n xform: " ^ (Cprinter.string_of_mix_formula xform)) in *)
          let xform1 = (x_add TP.simplify_with_pairwise 1 (CP.drop_rel_formula (MCP.pure_of_mix xform))) in
          let ls_disj = CP.list_of_disjs xform1 in
          let xform2 = MCP.mix_of_pure (CP.disj_of_list (Gen.BList.remove_dups_eq CP.equalFormula ls_disj) pos) in
          (* let () = print_endline ("\n xform1: " ^ (Cprinter.string_of_pure_formula xform1)) in *)
          (* let () = print_endline ("\n xform2: " ^ (Cprinter.string_of_mix_formula xform2)) in *)
	  (* let formula1 = CF.formula_of_mix_formula xform pos in *)
	  (* let ctx = CF.build_context (CF.true_ctx ( CF.mkTrueFlow ()) Lab2_List.unlabelled pos) formula1 pos in *)
	  (* let formula = CF.formula_of_mix_formula vdef.C.view_user_inv pos in *)
	  (* let (rs, _) = x_add Solver.heap_entail_init prog false (CF.SuccCtx [ ctx ]) formula pos in *)
	  (* let () = if not(CF.isFailCtx rs) then *)
          (* if disj user-supplied inv; just use it *)
          x_dinfo_hp (add_str "xform1" !CP.print_formula) xform1 pos;
          x_dinfo_hp (add_str "xform2" !MCP.print_mix_formula) xform2 pos;
          let compute_unfold_baga baga_over body =
            match baga_over with
              | None -> None
              | Some lst ->
                    if List.length lst == 1 then
                      let unf_baga = x_add Cvutil.xpure_symbolic_baga prog body in
                      Some (Expure.simplify unf_baga)
                    else Some (Expure.simplify lst) (* baga_over *)
          in
          if do_not_compute_flag then
            vdef.C.view_xpure_flag <- true
          else
            begin
              let baga_over = vdef.C.view_baga_over_inv in
              let body = C.formula_of_unstruc_view_f vdef in
              let u_b = compute_unfold_baga baga_over body in
              (* let xform2 = match u_b with *)
              (*   | None -> xform2 *)
              (*   | Some disj -> Mcpure.mix_of_pure (Excore.EPureI.ef_conv_disj disj) *)
              (* in *)
              x_tinfo_hp (add_str "old view_x_formula" Cprinter.string_of_mix_formula) vdef.C.view_x_formula pos;
              x_tinfo_hp (add_str "xform2" Cprinter.string_of_mix_formula) xform2 pos;
              x_tinfo_hp (add_str "old x_formula" (pr_option Excore.EPureI.string_of_disj)) baga_over pos;
              x_tinfo_hp (add_str "baga_over" (pr_option Excore.EPureI.string_of_disj)) baga_over pos;
              x_tinfo_hp (add_str "view body" Cprinter.string_of_formula) body pos;
              x_tinfo_hp (add_str "baga_over(unfolded)" (pr_option Excore.EPureI.string_of_disj)) u_b pos;
              vdef.C.view_baga_x_over_inv <- u_b ;
	      vdef.C.view_x_formula <- xform2;
              vdef.C.view_xpure_flag <- TP.check_diff vdef.C.view_user_inv xform2
            end
          ;
          vdef.C.view_addr_vars <- addr_vars;
          (* let xf = pure_of_mix xform' in *)
          (* let xf = strip_exists_pure xf in *)
          (* let (subs,_) = x_add_1 Mcpure.get_all_vv_eqs_mix xform' in *)
          (* let () = Debug.info_hprint (add_str "xform(mix)" Cprinter.string_of_mix_formula) xform' no_pos in *)
          (* let () = Debug.info_hprint (add_str "view_addr_vars" !Cast.print_svl) addr_vars no_pos in *)
          (* let () = Debug.info_hprint (add_str "view_vars" !Cast.print_svl) vdef.C.view_vars no_pos in *)
          let baga = (match ms.CF.mem_formula_mset with | [] -> [] | h::_ -> h) in
          (* let () = Debug.info_hprint (add_str "view_baga" !Cast.print_svl) baga no_pos in *)
          (* let new_baga = Gen.BList.intersect_eq (CP.eq_spec_var) baga addr_vars in *)
          (* let () = Debug.info_hprint (add_str "new_baga" !Cast.print_svl) new_baga no_pos in *)
          (* intersection ensures we remove existential vars *)
          let new_baga = baga in
	  vdef.C.view_baga <- new_baga
          ;
	  helper (n - 1) do_not_compute_flag
              (* else report_error pos "view formula does not entail supplied invariant\n" in () *)
      )
    else
      begin
        (* let () = Debug.info_zprint (lazy ("code when -nxpure 0 !")) no_pos in *)
        validate_mem_spec prog vdef (* verify the memory specs using predicate definition *)
      end;
    if !Globals.print_x_inv && (n = 0)
    then
      (print_string ("\ncomputed invariant for view: " ^ vdef.C.view_name ^"\n" ^(Cprinter.string_of_mix_formula vdef.C.view_x_formula) ^"\n");
      print_string ("addr_vars: " ^(String.concat ", "(List.map CP.name_of_spec_var vdef.C.view_addr_vars))^ "\n\n"))
    else ())
  in
  let check_and_compute () =
    let vn = vdef.C.view_name in
    if not(vdef.C.view_is_prim) then
      let old_baga_imm_flag = !Globals.baga_imm in
      let () = Globals.baga_imm := true in
      let form_body_inv_baga  vdef =
        let uns_view = C.formula_of_unstruc_view_f vdef in
        let ep_disj = x_add Cvutil.xpure_symbolic_baga prog uns_view in
        let lhs_pure = Excore.EPureI.ef_conv_disj ep_disj in
        let () = x_tinfo_hp (add_str "uns_view" Cprinter.string_of_formula) uns_view no_pos in
        let () = x_tinfo_hp (add_str "ante(ef_disj)" Cprinter.string_of_ef_pure_disj) ep_disj no_pos in
        let () = x_tinfo_hp (add_str "lhs_pure" Cprinter.string_of_pure_formula) lhs_pure no_pos in
        CF.formula_of_pure_formula lhs_pure pos in
      let form_body_inv_baga  vdef =
        let pr vd = pr_id vd.C.view_name in
        Debug.no_1 "form_body_inv_baga" pr Cprinter.string_of_formula form_body_inv_baga vdef in
      let form_body_inv_baga_enum  vdef =
        let uns_view = C.formula_of_unstruc_view_f vdef in
        let ep_disj = x_add Cvutil.xpure_symbolic_baga prog uns_view in
        let lhs_pure_enum = Excore.EPureI.ef_conv_enum_disj ep_disj in
        let () = x_tinfo_hp (add_str "uns_view" Cprinter.string_of_formula) uns_view no_pos in
        let () = x_tinfo_hp (add_str "ante(ef_disj)" Cprinter.string_of_ef_pure_disj) ep_disj no_pos in
        let () = x_tinfo_hp (add_str "lhs_pure_enum" Cprinter.string_of_pure_formula) lhs_pure_enum no_pos in
        CF.formula_of_pure_formula lhs_pure_enum pos in
      let form_body_inv_baga_enum  vdef =
        let pr vd = pr_id vd.C.view_name in
        Debug.no_1 "form_body_inv_baga_enum" pr Cprinter.string_of_formula form_body_inv_baga_enum vdef in
      let form_body_inv  vdef =
        let uns_view = C.formula_of_unstruc_view_f vdef in
        let (xform', _ (*addr_vars'*), ms) = x_add Cvutil.xpure_symbolic 2 prog uns_view in
        let () = x_tinfo_hp (add_str "uns_view" Cprinter.string_of_formula) uns_view no_pos in
        let () = x_tinfo_hp (add_str "xform'" Cprinter.string_of_mix_formula) xform' no_pos in
        let () = Globals.baga_imm := old_baga_imm_flag in
        let () = x_tinfo_hp (add_str "view_name" (fun x -> x)) vn no_pos in
        let () = x_tinfo_hp (add_str "(1) view_x_formula" Cprinter.string_of_mix_formula) vdef.C.view_x_formula no_pos in
        (*let addr_vars = CP.remove_dups_svl addr_vars' in*)
        let xform = MCP.simpl_memo_pure_formula Cvutil.simpl_b_formula Cvutil.simpl_pure_formula xform' (x_add TP.simplify_a 10) in
        let () = x_tinfo_hp (add_str "xform" Cprinter.string_of_mix_formula) xform no_pos in
        let xform1 =
          if vdef.C.view_kind = C.View_EXTN then
            let r = x_add Predicate.leverage_self_info (MCP.pure_of_mix xform) (C.formula_of_unstruc_view_f vdef) vdef.C.view_prop_extns vdef.C.view_data_name
            in
            (MCP.mix_of_pure r)
          else xform
        in CF.formula_of_mix_formula xform1 pos
      in
      let form_body_inv i  vdef =
        let pr vd = pr_id vd.C.view_name in
        Debug.no_1_num i "form_body_inv" pr Cprinter.string_of_formula form_body_inv vdef in
      (* let formula1 = CF.formula_of_mix_formula xform1 pos in *)
      let form_body_enum,form_body_sym = 
        if !Globals.use_baga then form_body_inv_baga_enum,form_body_inv_baga
        else (form_body_inv 1),(form_body_inv 2) in
      let formula1 = form_body_enum vdef in
      let () = x_tinfo_hp (add_str "formula1" Cprinter.string_of_formula) formula1 no_pos in
      let templ_vars = List.filter (fun v -> is_FuncT (CP.type_of_spec_var v)) (CF.fv formula1) in
      let formula1_under = wrap_under_baga form_body_sym vdef in
      let ctx = CF.build_context (CF.true_ctx ( CF.mkTrueFlow ()) Lab2_List.unlabelled pos) formula1 pos in
      let ctx = CF.add_infer_vars_templ_ctx ctx templ_vars in
      let formula = CF.formula_of_mix_formula vdef.C.view_user_inv pos in
      let () = x_tinfo_hp (add_str "formula1" Cprinter.string_of_formula) formula1 no_pos in
      let () = x_tinfo_hp (add_str "formula1_under" Cprinter.string_of_formula) formula1_under no_pos in
      let () = x_tinfo_hp (add_str "context" Cprinter.string_of_context) ctx no_pos in
      let () = x_tinfo_hp (add_str "formula" Cprinter.string_of_formula) formula no_pos in
      let (rs, _) = x_add Solver.heap_entail_init prog false (CF.SuccCtx [ ctx ]) formula pos in
      let (baga_formula, baga_enum_formula) = match vdef.C.view_baga_inv with
        | None ->
              let f1 = CF.mkTrue (CF.mkTrueFlow ()) pos in
              let f2 = CF.mkFalse (CF.mkTrueFlow ()) pos in
              (f1, f2)
        | Some disj ->
              let f1 = CF.formula_of_pure_formula (Excore.EPureI.ef_conv_disj disj) pos in
              let f2 = CF.formula_of_pure_formula (Excore.EPureI.ef_conv_enum_disj disj) pos in
              (* let f2 = CF.mkFalse (CF.mkTrueFlow ()) pos in *)
              (f1, f2)
      in
      let (baga_rs1, _) = x_add Solver.heap_entail_init prog false (CF.SuccCtx [ ctx ]) baga_formula pos in
      let ctx1 = CF.build_context (CF.true_ctx (CF.mkTrueFlow ()) Lab2_List.unlabelled pos) baga_enum_formula pos in
      (* TODO:WN:under Why do we need formula1_under in RHS here? *)
      let (baga_rs2, _) = x_add Solver.heap_entail_init prog false (CF.SuccCtx [ ctx1 ]) formula1_under pos in
      (* let () = x_tinfo_hprint (add_str "context1" Cprinter.string_of_context) ctx1 no_pos in *)
      let () = x_tinfo_hp (add_str "formula1" Cprinter.string_of_formula) formula1 no_pos in
      let pr_d = pr_opt Cprinter.string_of_ef_pure_disj in
      let over_f = vdef.C.view_baga_over_inv in
      x_tinfo_hp (add_str "over(baga)" pr_d) over_f no_pos;
      let baga_over_formula = match over_f with
        | None -> CF.mkTrue (CF.mkTrueFlow ()) pos
        | Some disj -> CF.formula_of_pure_formula (Excore.EPureI.ef_conv_disj disj) pos
      in
      let () = x_tinfo_hp (add_str "baga_over_formula" Cprinter.string_of_formula) baga_over_formula no_pos in
      let () = x_tinfo_hp (add_str "ctx" Cprinter.string_of_context) ctx no_pos in
      let (baga_over_rs, _) = x_add Solver.heap_entail_init prog false (CF.SuccCtx [ ctx ]) baga_over_formula pos in
      let under_f = vdef.C.view_baga_under_inv in
      (* WN : this is an update on under-approx to false if absent*)
      (* let new_under = match under_f with *)
      (*   | None -> Excore.EPureI.mk_false_disj *)
      (*   | Some f -> f in *)
      (* let () = vdef.C.view_baga_under_inv <- Some new_under in *)
      (* let under_f = vdef.C.view_baga_under_inv in *)
      let baga_under_formula = match under_f with
        | None -> CP.mkFalse pos
        | Some disj -> Excore.EPureI.ef_conv_enum_disj disj
      in
      (* let baga_under_formula = match under_f with *)
      (*   | None -> CF.mkFalse (CF.mkTrueFlow ()) pos *)
      (*   | Some disj -> CF.formula_of_pure_formula (Excore.EPureI.ef_conv_enum_disj disj) pos *)
      (* in *)
      (* let ctx1 = CF.build_context (CF.true_ctx (CF.mkTrueFlow ()) Lab2_List.unlabelled pos) baga_under_formula pos in *)
      (* let (baga_under_rs, _) = x_add Solver.heap_entail_init prog false (CF.SuccCtx [ ctx1 ]) formula1_under pos in *)
      let over_fail = (CF.isFailCtx baga_over_rs) in
      (* let under_fail = (CF.isFailCtx baga_under_rs) in *)
      (* type: int -> Excore.EPureI.epure -> CF.formula list -> string -> bool *)
      let check_under no uf fl vn =
        (* unfold helper, now unfold 3 times *)
        let rec helper_unfold no bfs ifs =
          if no = 0 then []
          else
            let new_bfs = List.fold_left (fun acc f ->
                acc@(List.map (fun bf ->
                    Cast.unfold_base_case_formula f vdef bf
                ) bfs)
            ) [] ifs
            in
            new_bfs@(helper_unfold (no - 1) new_bfs ifs)
        in
        let helper_unfold no bfs ifs =
          let pr = pr_list Cprinter.string_of_formula in
          Debug.no_2 "helper_unfold" pr pr pr (fun _ _ -> helper_unfold no bfs ifs) bfs ifs in
        let upf = Excore.EPureI.ef_conv_enum_disj [uf] in
        let () = Debug.ninfo_hprint (add_str "baga_under" Cprinter.string_of_pure_formula) upf no_pos in
        let (ifs,bfs) = List.partition CF.is_inductive fl in
        let bfs = bfs@(helper_unfold no bfs ifs) in
        let rs1 = List.exists (fun f ->
            let pf = Excore.EPureI.ef_conv_disj (wrap_under_baga (x_add Cvutil.xpure_symbolic_baga prog) f) in
            let () = Debug.ninfo_hprint (add_str "pf base" Cprinter.string_of_pure_formula) pf no_pos in
            TP.imply_raw upf pf
        ) bfs in
        if rs1 then true
        else
          let rs2 = List.exists (fun f ->
              let pf = Excore.EPureI.ef_conv_disj (wrap_under_baga (x_add Cvutil.xpure_symbolic_baga2 prog vn uf) f) in
              let () = Debug.ninfo_hprint (add_str "pf indu" Cprinter.string_of_pure_formula) pf no_pos in
              TP.imply_raw upf pf
          ) ifs in
          if rs2 then false
          else
            let pf = List.fold_left (fun acc f ->
                let pf = Excore.EPureI.ef_conv_disj (wrap_under_baga (x_add Cvutil.xpure_symbolic_baga2 prog vn uf) f) in
                CP.mkOr acc pf None no_pos
            ) (CP.mkFalse no_pos) (bfs@ifs) in
            let () = Debug.ninfo_hprint (add_str "pf all" Cprinter.string_of_pure_formula) pf no_pos in
            TP.imply_raw upf pf
      in
      (* type: int -> Excore.EPureI.epure -> CF.formula list -> string -> bool *)
      let check_under no uf fl vn =
        Debug.no_3 "check_under" Cprinter.string_of_ef_pure (pr_list Cprinter.string_of_formula) pr_id string_of_bool (fun _ _ _ -> check_under  no uf fl vn) uf fl vn  in
      (* let _ = x_binfo_hp (add_str "formula1_under" Cprinter.string_of_formula) formula1_under no_pos in *)
      let body_under = [formula1_under] in
      let under_fail = match under_f with
        | None -> false
        | Some ufl -> if (CP.is_False baga_under_formula) then (* false *) true else
            List.exists (fun uf ->
                not(check_under 3 uf body_under vdef.view_name)
            ) ufl
                (* let baga_under_formula_list = CP.split_disjunctions baga_under_formula in *)
                (* List.exists (fun baga_under_formula -> *)
                (*     let () = x_tinfo_hp (add_str "baga_under_formula" Cprinter.string_of_pure_formula) baga_under_formula no_pos in *)
                (*     not(check_under 3 baga_under_formula (fst (List.split vdef.view_un_struc_formula)) vdef.view_name under_f) *)
                (* ) baga_under_formula_list *)
      in
      let under_fail = if under_fail then
        let body_under = fst (List.split vdef.view_un_struc_formula) in
        match under_f with
          | None -> false
          | Some ufl -> if (CP.is_False baga_under_formula) then (* false *) true else
              List.exists (fun uf ->
                  not(check_under 3 uf body_under vdef.view_name)
              ) ufl
      else under_fail in
      let do_test_inv msg inv fail_res =
        if !Globals.do_test_inv then
          match inv with
            | Some f ->
                  if fail_res then
                    print_endline_quiet ("\nInv Check: Fail.("^msg^")")
                        (* else *)
                        (*   print_endline_quiet ("\nInv Check: Valid.("^msg^")") *)
            | None -> ()
        else ()
      in
      let () = do_test_inv "Over" over_f over_fail in
      let () = do_test_inv "Under" under_f under_fail in
      (* let () = print_endline (string_of_bool (not(CF.isFailCtx rs))) in *)
      (* let () = print_endline (string_of_bool (not(CF.isFailCtx baga_rs1))) in *)
      (* let () = print_endline (string_of_bool (not(CF.isFailCtx baga_rs2))) in *)
      let () =
        if not(CF.isFailCtx rs) && not(CF.isFailCtx baga_rs1) && not(CF.isFailCtx baga_rs2) &&
          not(over_fail) && not(under_fail) then
            begin
              let () = x_tinfo_pp ("XX View defn for " ^ vn ^ " has precise invariant\n") no_pos in
	      let pf = pure_of_mix vdef.C.view_user_inv in
	      let (disj_form,disj_f) = CP.split_disjunctions_deep_sp pf in
              let do_not_recompute_flag = disj_form (* (List.length disj_f>1) *) && not(!Globals.disj_compute_flag) in
              if n>0 then helper n do_not_recompute_flag;
              if vdef.C.view_xpure_flag then
                begin
                  let pr = Cprinter.string_of_mix_formula in
                  let sf = remove_disj_clauses vdef.C.view_user_inv in
                  (* Debug.info_hprint (add_str "disj_form" string_of_bool) disj_form no_pos; *)
                  if disj_form && !Globals.compute_xpure_0 then
                    (vdef.C.view_user_inv <- sf; vdef.C.view_xpure_flag <- false);
	          x_tinfo_zp (lazy (("Using a simpler inv for xpure0 of "^vdef.C.view_name))) pos;
                  x_tinfo_hp (add_str "inv(xpure0)" pr) vdef.C.view_user_inv pos;
                  x_tinfo_hp (add_str "inv_lock" (pr_option Cprinter.string_of_formula)) vdef.C.view_inv_lock pos;

	          x_tinfo_hp (add_str "inv(xpure1)" pr) vdef.C.view_x_formula pos
                end
            end
        else
          let s1 = if over_fail then "-- incorrect over-approx inv : "^(pr_d over_f)^"\n" else "" in
          let s2 = if under_fail then "-- incorrect under-approx inv : "^(pr_d under_f)^"\n" else "" in
          let msg = ("view defn for "^vn^" has incorrectly supplied invariant\n"^s1^s2) in
          (* WN : this test is unsound *)
          (* if !Globals.do_test_inv then report_warning pos msg *)
          (* else report_warning pos msg *)
          ()
      in ()
    else ()
  in
  check_and_compute ()

and find_pred_by_self vdef data_name = vdef.I.view_pt_by_self
  (* Gen.BList.difference_eq (=) vdef.I.view_pt_by_self [data_name] *)

and trans_view_kind vk=
  match vk with
    | Iast.View_NORM -> Cast.View_NORM
    | Iast.View_PRIM -> Cast.View_PRIM
    | Iast.View_EXTN -> Cast.View_EXTN
    | Iast.View_DERV -> Cast.View_DERV
    | Iast.View_SPEC -> Cast.View_SPEC

and create_mix_formula_with_ann_constr (h1: CF.h_formula) (h2: CF.h_formula) (p_f: MCP.mix_formula option) : MCP.mix_formula =
  let p1 = add_param_ann_constraints_to_pure h1 None in
  let p2 = add_param_ann_constraints_to_pure h2 None in
  let p = CF.add_mix_formula_to_mix_formula p1 p2 in
  (match p_f with
    | Some x -> CF.add_mix_formula_to_mix_formula p x
    | None -> p)

and add_param_ann_constraints_to_pure (h_f: CF.h_formula) (p_f: MCP.mix_formula option): MCP.mix_formula =
  let mix_f =
    match h_f with
      | CF.Star h  -> create_mix_formula_with_ann_constr h.CF.h_formula_star_h1 h.CF.h_formula_star_h2 p_f
      | CF.Conj h  -> create_mix_formula_with_ann_constr h.CF.h_formula_conj_h1 h.CF.h_formula_conj_h2 p_f
      | CF.ConjStar h  -> create_mix_formula_with_ann_constr h.CF.h_formula_conjstar_h1 h.CF.h_formula_conjstar_h2 p_f
      | CF.ConjConj h  -> create_mix_formula_with_ann_constr h.CF.h_formula_conjconj_h1 h.CF.h_formula_conjconj_h2 p_f
      | CF.Phase h -> create_mix_formula_with_ann_constr h.CF.h_formula_phase_rd h.CF.h_formula_phase_rw p_f
      | CF.DataNode h -> let data_ann = h.CF.h_formula_data_imm in
        let helper1 (param_imm: CP.ann) =
	  match (CP.mkExpAnn data_ann no_pos), (CP.mkExpAnn param_imm no_pos) with
	    | CP.IConst i1, CP.IConst i2 -> None (* if i1<=i2 then mkMTrue  no_pos else mkMFalse no_pos  *)
	    | (_ as n), (_ as f) -> Some (MCP.mix_of_pure(CP.BForm((CP.Lte(n, f, no_pos), None), None))) in
        let p = match p_f with
          | Some x -> List.fold_left (fun pf ann ->
                match helper1 ann with
                  | None -> pf
                  | Some mf -> CF.add_mix_formula_to_mix_formula mf pf) x h.CF.h_formula_data_param_imm
          | None ->
                let rec helper2 ann_lst =
                  match ann_lst with
                    | [] -> MCP.mkMTrue no_pos
                    | h1 :: t  ->
                          match helper1 h1 with
                            | None    -> helper2 t
                            | Some mf -> CF.add_mix_formula_to_mix_formula mf (helper2 t) in
                helper2 h.CF.h_formula_data_param_imm in
        p
      | _          -> match p_f with
          | Some x -> x
          | None   -> MCP.mkMTrue no_pos
  in MCP.remove_dupl_conj_mix_formula mix_f

(* below is not needed  anymore because of norm: push outer ann to inner *)
and add_param_ann_constraints_formula_x (cf: CF.formula): CF.formula =
  match cf with
    | CF.Base f   -> CF.Base { f with
          CF.formula_base_pure = add_param_ann_constraints_to_pure f.CF.formula_base_heap (Some f.CF.formula_base_pure); }
    | CF.Or f     -> CF.Or { f with
          CF.formula_or_f1 =  add_param_ann_constraints_formula_x f.CF.formula_or_f1;
          CF.formula_or_f2 =  add_param_ann_constraints_formula_x f.CF.formula_or_f2; }
    | CF.Exists f -> CF.Exists { f with
          CF.formula_exists_pure = add_param_ann_constraints_to_pure f.CF.formula_exists_heap (Some f.CF.formula_exists_pure); }

and add_param_ann_constraints_formula (cf: CF.formula): CF.formula = cf

(* add data param ann constraints to pure formula. 
   ex1. x::node<val1@A, val2@v, q@I>@I & n = 2 => 
   (x::node<val1@A, val2@v, q@I>@I & @I<:@A & @I<:@V & @I<:@I & n = 2) will be translated to (x::node<val1@A, val2@v, q@I>@I & 1<=3 & 1<=v & 1<=1 & n = 2)
   ex2. x::node<val1@M, val2@v, q@I>@I & n = 2 => 
   (x::node<val1@A, val2@v, q@I>@I & @I<:@M & @I<:@V & @I<:@I & n = 2) will be translated to (x::node<val1@A, val2@v, q@I>@I & 1<=0 & 1<=v & 1<=1 & n = 2)
*)
and add_param_ann_constraints_struc_x (cf: CF.struc_formula) : CF.struc_formula = 
  if (!Globals.allow_field_ann) then 
    let rec helper cf = 
      match cf with
        | CF.EList b          -> CF.EList (map_l_snd helper b)
        | CF.ECase b          -> CF.ECase {b with CF.formula_case_branches = map_l_snd helper b.CF.formula_case_branches;}
        | CF.EBase b          -> CF.EBase {b with
              CF.formula_struc_base =  add_param_ann_constraints_formula b.CF.formula_struc_base;
              CF.formula_struc_continuation = map_opt helper b.CF.formula_struc_continuation; }
        | CF.EAssume b -> CF.EAssume {b with 
	      CF.formula_assume_simpl = add_param_ann_constraints_formula b.CF.formula_assume_simpl;
	      CF.formula_assume_struc = helper b.CF.formula_assume_struc;}
        | CF.EInfer b         -> CF.EInfer {b with CF.formula_inf_continuation = helper b.CF.formula_inf_continuation}
    in helper cf
  else cf

and add_param_ann_constraints_struc (cf: CF.struc_formula) : CF.struc_formula =  (*cf disabled inner <> outer annotation relation *)
  let pr =  Cprinter.string_of_struc_formula in
  Debug.no_1 "add_param_ann_constraints_struc" pr pr  (fun _ -> add_param_ann_constraints_struc_x cf) cf

and trans_view (prog : I.prog_decl) mutrec_vnames transed_views ann_typs (vdef : I.view_decl): C.view_decl =
  let pr = Iprinter.string_of_view_decl in
  let pr_r = Cprinter.string_of_view_decl in
  Debug.no_1 "trans_view" pr pr_r  (fun _ -> trans_view_x prog  mutrec_vnames
      transed_views ann_typs vdef) vdef

and trans_view_x (prog : I.prog_decl) mutrec_vnames transed_views ann_typs (vdef : I.view_decl): C.view_decl =
  let view_formula1 = vdef.I.view_formula in
  let () = IF.has_top_flow_struc view_formula1 in
  (*let recs = rec_grp prog in*)
  let data_name = if (String.length vdef.I.view_data_name) = 0  then
    I.incr_fixpt_view prog  prog.I.prog_data_decls prog.I.prog_view_decls
  else vdef.I.view_data_name in
  (vdef.I.view_data_name <- data_name;
  let vtv = vdef.I.view_typed_vars in
  let tlist = List.map (fun (t,c) -> (c,{sv_info_kind=t; id=fresh_int() })) vtv in
  let tlist = ([(self,{ sv_info_kind = (Named data_name);id = fresh_int () })]@tlist) in
  let (n_tl,cf) = trans_I2C_struc_formula 1 prog false true (self :: vdef.I.view_vars) vdef.I.view_formula (ann_typs@tlist) false
    true (*check_pre*) in
  let () = Debug.ninfo_hprint (add_str "cf 3" Cprinter.string_of_struc_formula) cf no_pos in
  (* let () = print_string ("cf: "^(Cprinter.string_of_struc_formula cf)^"\n") in *)
  let inv_lock = vdef.I.view_inv_lock in
  let (n_tl,inv_lock) =
    (match inv_lock with
      | None -> (n_tl, None)
      | Some f ->
            let (n_tl_tmp,new_f) = trans_formula prog true (self :: vdef.I.view_vars) true f (ann_typs@n_tl) false in
            (*find existential variables*)
            let fvars = CF.fv new_f in
            let evars = List.filter (fun sv -> not (List.exists (fun name -> name = (CP.name_of_spec_var sv)) (self :: vdef.I.view_vars))) fvars in
            let new_f2 = if evars!=[] then CF.push_exists evars new_f else new_f in
            (* let () = print_endline ("new_f = " ^ (Cprinter.string_of_formula new_f)) in *)
            (* let () = print_endline ("new_f2 = " ^ (Cprinter.string_of_formula new_f2)) in *)
            (* let () = print_endline ("fvars = " ^ (Cprinter.string_of_spec_var_list fvars)) in *)
            (* let () = print_endline ("evars = " ^ (Cprinter.string_of_spec_var_list evars)) in *)

            (****************************)
            (n_tl_tmp, Some new_f2))
  in
  let cf = CF.mark_derv_self vdef.I.view_name cf in 
  let inv = vdef.I.view_invariant in
  let (n_tl,mem_form) = (
      match vdef.I.view_mem with
        | Some a -> 
              let () = Mem.check_mem_formula vdef prog.I.prog_data_decls in 
              let (new_typ_mem,n_tl) = fresh_tvar n_tl in 
              let (n_tl,_) = gather_type_info_exp prog a.IF.mem_formula_exp n_tl new_typ_mem in 
              (n_tl,trans_view_mem vdef.I.view_mem n_tl)
        | None -> (n_tl,None)
  ) in 
  let inv = if(!Globals.allow_mem) then Mem.add_mem_invariant inv vdef.I.view_mem else inv in
  let n_tl = gather_type_info_pure prog inv n_tl in 
  let inv_pf = trans_pure_formula inv n_tl in   
  (* Thai : pf - user given invariant in core form *) 
  let inv_pf = Cpure.arith_simplify 1 inv_pf in
  let cf_fv = List.map CP.name_of_spec_var (CF.struc_fv cf) in
  let inv_lock_fv = match inv_lock with
    | None -> []
    | Some f -> List.map CP.name_of_spec_var (CF.fv f)
  in
  let pf_fv = List.map CP.name_of_spec_var (CP.fv inv_pf) in

  if (List.mem res_name cf_fv) || (List.mem res_name pf_fv) || (List.mem res_name inv_lock_fv)  then
    report_error (IF.pos_of_struc_formula view_formula1) "res is not allowed in view definition or invariant"
  else(
      let pos = IF.pos_of_struc_formula view_formula1 in
      let view_sv_vars = List.map (fun c-> trans_var (c,Unprimed) n_tl pos) vdef.I.view_vars in
      let view_prop_extns =  List.map (fun (t,c)-> trans_var (c,Unprimed) n_tl pos) vdef.I.view_prop_extns in
      let self_c_var = Cpure.SpecVar ((Named data_name), self, Unprimed) in
      let null_c_var = Cpure.null_var in 
      let _ =
        let vs1 = (CF.struc_fv cf) in
        let vs2 = (null_c_var::self_c_var::view_sv_vars) in
        let vs1a = CP.fv inv_pf in
        x_tinfo_hp (add_str "vs1a" Cprinter.string_of_spec_var_list) vs1a no_pos;
        let vs1 = vs1@vs1a in
        let ffv = Gen.BList.difference_eq (CP.eq_spec_var) vs1 vs2 in
        (* filter out holes (#) *)
        (* let ffv = List.filter (fun v -> not (CP.is_hole_spec_var v)) ffv in *)
	let ffv = List.filter (fun v -> not 
            (CP.is_hprel_typ v || CP.is_rel_typ v || CP.is_hole_spec_var v 
              || is_FuncT (CP.type_of_spec_var v))) ffv in
        (* let ffv = List.filter (fun v -> not (is_FuncT (CP.type_of_spec_var v))) ffv in *)
        let ffv = CP.diff_svl ffv view_prop_extns in
        (* filter out intermediate dereference vars and update them to view vars *)
        
        let ffv = List.filter (fun v ->
            let is_deref_var = CP.is_inter_deference_spec_var v in
            if (is_deref_var) then (
                match v with
                  | CP.SpecVar (_, n, _) -> vdef.I.view_vars <- vdef.I.view_vars @ [n];
            );
            not (is_deref_var)
        ) ffv in
        if (ffv!=[]) then report_error no_pos ("error 1: free variables "^(Cprinter.string_of_spec_var_list ffv)^" in view def "^vdef.I.view_name^" ") in
      let typed_vars = List.map ( fun (Cpure.SpecVar (c1,c2,c3))-> (c1,c2)) view_sv_vars in
      let () = vdef.I.view_typed_vars <- typed_vars in
      let mvars =  List.filter 
	(fun c-> List.exists (fun v-> String.compare v (CP.name_of_spec_var c) = 0) vdef.I.view_materialized_vars) view_sv_vars in
      let mvars = List.map (fun v -> C.mk_mater_prop v false []) mvars in
      let cf = CF.label_view cf in
      let n_un_str =  CF.get_view_branches cf in   
      let rec f_tr_base f = 
        let mf f h fl pos = if (CF.is_complex_heap h) then (CF.mkFalse fl pos)  else f in
        match f with
          | CF.Base b -> mf f b.CF.formula_base_heap b.CF.formula_base_flow b.CF.formula_base_pos
          | CF.Exists b -> mf f b.CF.formula_exists_heap b.CF.formula_exists_flow b.CF.formula_exists_pos
          | CF.Or b -> CF.mkOr (f_tr_base b.CF.formula_or_f1) (f_tr_base b.CF.formula_or_f2) no_pos in
      let is_prim_v = vdef.I.view_is_prim in
      let rbc = 
        if is_prim_v then None
        else List.fold_left (fun a (c,l)-> 
            let fc = f_tr_base c in
            if (CF.isAnyConstFalse fc) then a 
            else match a with 
              | Some f1  -> Some (CF.mkOr f1 fc no_pos)
              | None -> Some fc) None n_un_str 
      in
      (* TODO : This has to be generalised to mutual-recursion *)
      let ir = not(is_prim_v) && is_view_recursive vdef.I.view_name in
      let sf = find_pred_by_self vdef data_name in
      let () = Debug.ninfo_hprint (add_str "cf 1" Cprinter.string_of_struc_formula) cf no_pos in
      let cf = CF.struc_formula_set_lhs_case false cf in
      let () = Debug.ninfo_hprint (add_str "cf 2" Cprinter.string_of_struc_formula) cf no_pos in
      (* Thai : we can compute better pure inv named new_pf here that 
         should be stronger than pf *)
      let new_pf = if Gen.BList.mem_eq (fun s1 s2 -> String.compare s1 s2 = 0)
        vdef.I.view_name  mutrec_vnames then inv_pf
      else Fixcalc.compute_inv vdef.I.view_name view_sv_vars n_un_str data_name transed_views inv_pf in
      x_dinfo_hp (add_str "inv_pf" Cprinter.string_of_pure_formula) inv_pf no_pos;
      x_dinfo_hp (add_str "new_pf" Cprinter.string_of_pure_formula) new_pf no_pos;
      let memo_pf_P = MCP.memoise_add_pure_P (MCP.mkMTrue pos) new_pf in
      let memo_pf_N = MCP.memoise_add_pure_N (MCP.mkMTrue pos) new_pf in
      let xpure_flag = TP.check_diff memo_pf_N memo_pf_P in
      let view_kind = trans_view_kind vdef.I.view_kind in
      let vn = vdef.I.view_name in
      let () = if view_kind = Cast.View_PRIM then CF.view_prim_lst # push vn  in
      (* let view_vars_gen = CP.sv_to_view_arg_list view_sv_vars in *)
      (* let view_sv_vars, labels, ann_params = CP.split_view_args (List.combine view_vars_gen (fst vdef.I.view_labels)) in *)
      (* let ann_params, view_vars_gen = Immutable.initialize_positions_for_args ann_params view_vars_gen cf data_name prog.I.prog_data_decls in *)
      let view_sv, labels, ann_params, view_vars_gen = x_add_1 Immutable.split_sv view_sv_vars vdef in
      let view_ho_sv = List.map (fun (fk,i,sk) -> (fk, CP.SpecVar (FORM,i,Unprimed), sk)) vdef.I.view_ho_vars in (* TODO;HO *)
      let conv_baga_inv baga_inv =
        match baga_inv with
          | None -> None
          | Some lst ->
                let rr = List.map (fun (idl,pf) ->
                    let svl = List.map (fun c -> trans_var (c,Unprimed) n_tl pos) idl in
                    (* let svl, _, _, _ = x_add_1 Immutable.split_sv svl vdef in *)
                    let cpf = trans_pure_formula pf n_tl in
                    let cpf = Cpure.arith_simplify 1 cpf in
                    (svl,cpf)
                ) lst in
                Some rr
      in
      let unfold_once baga =
        match baga with
          | None -> None
          | Some lst ->
                if List.length lst == 1 then
                  Some lst (* unfold once *)
                else baga in
      let vbi = conv_baga_inv vdef.I.view_baga_inv in
      let (vboi,vbui,user_inv,user_x_inv) = match vbi with
        | Some ef ->
              let new_f = Excore.EPureI.ef_conv_disj ef in
              let new_mix_f = x_add_1 Mcpure.mix_of_pure new_f in
              (vbi,vbi,new_mix_f,new_mix_f)
        | _ -> (conv_baga_inv vdef.I.view_baga_over_inv,
          conv_baga_inv vdef.I.view_baga_under_inv,memo_pf_N,memo_pf_P) in
      (* let () = match vbi with *)
      (*   | None -> x_dinfo_hp (add_str ("baga inv("^vn^")") (fun x -> x)) "None" no_pos *)
      (*   | Some vbi -> x_dinfo_hp (add_str ("baga inv("^vn^")") (Cprinter.string_of_ef_pure_disj)) vbi no_pos in *)
      let vboi = match vboi with
        | None ->
              begin
                x_dinfo_hp (add_str "pure to_be added" Cprinter.string_of_pure_formula) new_pf no_pos;
                (Some [([],new_pf)])
                    (* Debug.ninfo_hprint (add_str ("baga inv("^vn^")") (fun x -> x)) "None" no_pos *)
              end
        | Some vbi -> vboi
              (* x_dinfo_hp (add_str ("baga over inv("^vn^")") (Cprinter.string_of_ef_pure_disj)) vbi no_pos  *)
      in
      (* let () = match vbui with *)
      (*   | None -> x_dinfo_hp (add_str ("baga under inv("^vn^")") (fun x -> x)) "None" no_pos *)
      (*   | Some vbui -> x_dinfo_hp (add_str ("baga under inv("^vn^")") (Cprinter.string_of_ef_pure_disj)) vbui no_pos in *)
      (* let () = x_dinfo_pp "\n" no_pos in *)
      (* let () = Debug.info_pprint ("!!! Trans_view HERE") no_pos in *)
      let pr = Cprinter.string_of_ef_pure_disj in
      Debug.ninfo_hprint (add_str "name" (fun x -> x)) vn no_pos;
      Debug.ninfo_hprint (add_str "vboi" (pr_option pr)) vboi no_pos;
      Debug.ninfo_hprint (add_str "vbui" (pr_option pr)) vbui no_pos;
      Debug.ninfo_hprint (add_str "vbi" (pr_option pr)) vbi no_pos;
      let cvdef = {
          C.view_name = vn;
          C.view_pos = vdef.I.view_pos;
          C.view_is_prim = is_prim_v;
          C.view_is_touching = false;           (* temporarily assigned *)
          C.view_is_segmented = false;          (* temporarily assigned *)
          C.view_is_tail_recursive = false;     (* temporarily assigned *)
          C.view_residents = [];
	  C.view_forward_ptrs = [];
          C.view_forward_fields = [];
          C.view_backward_ptrs = [];
          C.view_backward_fields = [];
          C.view_kind = view_kind;
          C.view_type_of_self = vdef.I.view_type_of_self;
          C.view_prop_extns = view_prop_extns;
          C.view_parent_name = None;
          C.view_domains = [];
          C.view_vars = view_sv;
          C.view_ho_vars = view_ho_sv;
          C.view_cont_vars = [];
          C.view_seg_opz = None;
          C.view_uni_vars = [];
          C.view_labels = labels;
          C.view_modes = vdef.I.view_modes;
          C.view_contains_L_ann = false;
          C.view_ann_params  = ann_params;
          C.view_params_orig = view_vars_gen;      (* andreeac: TODO annot *)
          C.view_partially_bound_vars = [];
          C.view_materialized_vars = mvars;
          C.view_data_name = data_name;
          C.view_formula = cf;
          C.view_x_formula = user_x_inv;
          C.view_fixcalc = None;
          C.view_baga_inv = vbi;
          C.view_baga_over_inv = vboi;
          C.view_baga_x_over_inv = vboi;
          C.view_baga_under_inv = vbui;
          C.view_xpure_flag = xpure_flag;
          C.view_addr_vars = [];
          C.view_baga = [];
          C.view_complex_inv = None;
          C.view_user_inv = user_inv;
          C.view_mem = mem_form;
          C.view_inv_lock = inv_lock;
          C.view_un_struc_formula = n_un_str;
          C.view_linear_formula = n_un_str;
          C.view_base_case = None;
          C.view_is_rec = ir;
          C.view_pt_by_self = sf;
          C.view_case_vars = CP.intersect_svl view_sv_vars (CF.guard_vars cf);
          C.view_raw_base_case = rbc;
          C.view_prune_branches = [];
          C.view_prune_conditions = [];
          C.view_prune_conditions_baga = [];
          C.view_ef_pure_disj = None;
          C.view_prune_invariants = []} in
      (x_dinfo_zp (lazy ("\n" ^ (Cprinter.string_of_view_decl cvdef))) (CF.pos_of_struc_formula cf);
      cvdef)
  )
  )

and trans_views iprog ls_mut_rec_views ls_pr_view_typ =
  let pr = pr_list (fun v -> v.Cast.view_name) in
  let pr2 = pr_list (fun (v,_) -> v.Iast.view_name) in
  Debug.no_2 "trans_views" (pr_list (pr_list pr_id)) pr2 pr (fun _ _ -> trans_views_x iprog ls_mut_rec_views ls_pr_view_typ) ls_mut_rec_views ls_pr_view_typ

(* type: I.prog_decl ->
   String.t list list ->
   (I.view_decl * (Globals.ident * Typeinfer.spec_var_info) list) list ->
   C.view_decl list *)


and trans_views_x iprog ls_mut_rec_views ls_pr_view_typ =
  let () = Debug.ninfo_hprint (add_str "ls_mut_rec_views" (pr_list (pr_list pr_id))) ls_mut_rec_views no_pos in
  let all_mutrec_vnames = (List.concat ls_mut_rec_views) in
  (*******************************)
  let cmp_id s1 s2=  String.compare s1 s2 = 0 in
  let cmp_list_id ls1 ls2=
    ((List.length ls1) = (List.length ls2)) &&
        Gen.BList.difference_eq cmp_id ls1 ls2 = []
  in
  (*cur_mutrec_views: used to capture all views of a loop. when all views of a loop
    have been translated, we compute their invs together*)
  let trans_one_view (transed_views, cur_mutrec_views) (view,typ_infos)=
    let mutrec_views = if Gen.BList.mem_eq cmp_id
      view.Iast.view_name all_mutrec_vnames
    then (cur_mutrec_views@[view.Iast.view_name])
    else cur_mutrec_views
    in
    let nview = trans_view iprog mutrec_views transed_views typ_infos view in
    let transed_views1 = transed_views@[nview] in
    (* Loc: to compute invs for mut-rec views *)
    let transed_views2,mutrec_views = if mutrec_views!=[] &&
      Gen.BList.mem_eq cmp_list_id mutrec_views ls_mut_rec_views
    then
      let transed_views3 = Fixcalc.compute_inv_mutrec mutrec_views transed_views1 in
      (transed_views3, [] (*complete one loop, reset it*))
    else (transed_views1, mutrec_views)
    in
    (transed_views2,mutrec_views)
  in
  (*******************************)
  let cviews0,_ = List.fold_left trans_one_view ([],[]) ls_pr_view_typ in
  let has_arith = !Globals.gen_baga_inv && not(!Globals.smt_compete_mode) && List.exists (fun cv ->
      Expure.is_ep_view_arith cv) cviews0 in
  (* this was incorrect (due to simplifier) since spaguetti benchmark disables it inv_baga; please check to ensure all SMT benchmarks passes..*)
  (* let () = if has_arith then *)
  (*   begin *)
  (*     x_tinfo_pprint "Disabling --inv-baga due to arith\n" no_pos; *)
  (*     Globals.dis_inv_baga () *)
  (*   end *)
  (* else () in *)
  let cviews0 =
    if !Globals.gen_baga_inv then
      let () = x_binfo_pp "Generate baga inv\n" no_pos in
      let cviews0 = List.filter (fun cv ->
          not cv.Cast.view_is_prim
      ) cviews0 in
      let () = List.iter (fun cv ->
          Hashtbl.add Excore.map_baga_invs cv.C.view_name Excore.EPureI.mk_false_disj;
          Hashtbl.add Excore.map_precise_invs cv.C.view_name true
      ) cviews0 in
      let cviews0_with_index = Expure.add_index_to_views cviews0 in
      let ls_mut_rec_views1 = List.fold_left (fun ls cv ->
          if List.mem cv.C.view_name (List.flatten ls) then
            ls
          else if (List.mem cv.C.view_name (List.flatten ls_mut_rec_views)) then
            let mut_rec_views = List.find (fun mr_views ->
                List.mem cv.C.view_name mr_views) ls_mut_rec_views in
            ls@[mut_rec_views]
          else
            ls@[[cv.C.view_name]]
      ) [] cviews0_with_index in
      (* let map_baga_invs = Hashtbl.create 1 in *)
      (* moved to cpure.ml *)
      let () = List.iter (fun idl ->
          (* if !Globals.gen_baga_inv then *)
          let view_list_baga0 = List.filter (fun vd ->
              List.mem vd.Cast.view_name idl
          ) cviews0 in
          let view_list_baga = List.map (fun vd ->
              let new_un_struc_formula = List.map (fun (cf,lbl) ->
                  let num_svl = List.filter CP.is_int_typ vd.Cast.view_vars in
                  let new_cf = CF.wrap_exists num_svl cf in
                  let () = Debug.ninfo_hprint (add_str "new_cf" Cprinter.string_of_formula) new_cf no_pos in
                  (new_cf,lbl)
              ) vd.Cast.view_un_struc_formula in
              {vd with Cast.view_un_struc_formula = new_un_struc_formula}
          ) view_list_baga0 in
          let view_list_num0 = List.filter (fun vd ->
              List.mem vd.Cast.view_name idl
          ) cviews0_with_index in
          let view_list_num = List.map (fun vd ->
              let new_un_struc_formula = List.map (fun (cf,lbl) ->
                  let baga_svl = List.filter (fun sv -> not (CP.is_int_typ sv)) vd.Cast.view_vars in
                  let baga_svl = [CP.mk_spec_var "self"]@baga_svl in
                  let new_cf = CF.wrap_exists baga_svl cf in
                  (new_cf,lbl)
              ) vd.Cast.view_un_struc_formula in
              {vd with Cast.view_un_struc_formula = new_un_struc_formula}
          ) view_list_num0 in
          let todo_unk = Wrapper.wrap_infer_inv Expure.fix_ef view_list_baga cviews0 in
          let view_list_num_with_inv = Fixcalc.compute_inv_mutrec (List.map (fun vd -> vd.Cast.view_name) view_list_num) view_list_num in
          let () = x_tinfo_hp (add_str "fixcalc (view with inv)" (pr_list (fun vd -> pr_option Cprinter.string_of_mix_formula vd.Cast.view_fixcalc))) view_list_num_with_inv no_pos in
          let fixcalc_invs_inv = List.map (fun vd -> match vd.Cast.view_fixcalc with Some f -> f | None -> MCP.mkMTrue no_pos) view_list_num_with_inv in
          let num_invs_wrap_index = List.map (fun mf ->
              let pf = MCP.pure_of_mix mf in
              let idx = CP.mk_typed_spec_var Int "idx" in
              let pf_svl = CP.fv pf in
              let new_pf = if List.mem idx pf_svl then CP.wrap_exists_svl pf [idx] else pf in
              Tpdispatcher.simplify new_pf
          ) fixcalc_invs_inv in
          let () = Debug.ninfo_hprint (add_str "fixcalc_invs_inv" (pr_list Cprinter.string_of_mix_formula)) fixcalc_invs_inv no_pos in
          (* WN : Need to check if supplied inv is a fixpoint! *)
          let infer_vs_user = List.combine view_list_num_with_inv num_invs_wrap_index in
          let num_invs = List.map (fun (vd,fixc) ->
              (* if not(CP.isConstTrue (MCP.pure_of_mix vd.Cast.view_user_inv)) then *)
              (*   vd.Cast.view_user_inv *)
              (* else *)
              (*   vd.Cast.view_x_formula *)
              let user_inv = MCP.pure_of_mix vd.Cast.view_user_inv in
              let better =
                if List.exists (fun sv -> (CP.type_of_spec_var sv) != Int) (CP.fv user_inv) then fixc (* user inv is not just numeric *)
                else if (Tpdispatcher.imply_raw fixc user_inv) then fixc
                else
                  (* to check view_form ==> usr_inv *)
                  let body = CF.project_body_num vd.Cast.view_un_struc_formula user_inv vd.Cast.view_vars in
                  let () = x_binfo_hp (add_str "fixc" Cprinter.string_of_pure_formula) fixc no_pos in
                  let () = x_binfo_hp (add_str "body" Cprinter.string_of_pure_formula) body no_pos in
                  let () = x_binfo_hp (add_str "user_inv" Cprinter.string_of_pure_formula) user_inv no_pos in
                  let () = x_binfo_pp "WARNING: TODO fixpt check" no_pos in
                  if (true (* Tpdispatcher.imply_raw body user_inv *)) then
                    let () = x_binfo_hp (add_str "User supplied is more precise" Cprinter.string_of_pure_formula) user_inv no_pos in
                    user_inv
                  else
                    let () = x_binfo_hp (add_str "User supplied is unsound" Cprinter.string_of_pure_formula) user_inv no_pos in
                    let () = x_binfo_hp (add_str "Using fixcalc version" Cprinter.string_of_pure_formula) fixc no_pos in
                    fixc
              in better
          )  infer_vs_user in
          let precise_num_invs = List.map (fun (vd,fixc) ->
              (* if not(CP.isConstTrue (MCP.pure_of_mix vd.Cast.view_user_inv)) then *)
              (*   vd.Cast.view_user_inv *)
              (* else *)
              (*   vd.Cast.view_x_formula *)
              try
                let body = CF.project_body_num vd.Cast.view_un_struc_formula fixc vd.Cast.view_vars in
                (* let root = CP.mk_spec_var "self" in *)
                let ptrs_vars = List.filter (fun (CP.SpecVar(t,id,_)) -> (string_compare id "idx") || (is_node_typ t)) vd.Cast.view_vars in
                let body = CP.wrap_exists_svl body (* [root] *) ptrs_vars in
                let () = Debug.ninfo_hprint (add_str "body" Cprinter.string_of_pure_formula) body no_pos in
                let () = Debug.ninfo_hprint (add_str "num_inv" Cprinter.string_of_pure_formula) fixc no_pos in
                let is_precise_num = if Tpdispatcher.imply_raw fixc body then
                  let () = x_binfo_pp ("Predicate " ^ vd.Cast.view_name ^ " has precise invariant\n") no_pos in
                  (true,fixc)
                else
                  let idx = CP.mk_typed_spec_var Int "idx" in
                  let alter_num_inv =
                    let f1 = CF.project_body_num vd.Cast.view_un_struc_formula (CP.mkFalse no_pos) vd.Cast.view_vars in
                    let f1 = x_add_1 Tpdispatcher.simplify_raw (CP.wrap_exists_svl f1 [idx]) in
                    let f2 = CF.project_body_num vd.Cast.view_un_struc_formula f1 vd.Cast.view_vars in
                    let f2 = x_add_1 Tpdispatcher.simplify_raw (CP.wrap_exists_svl f2 [idx]) in
                    let f3 = CF.project_body_num vd.Cast.view_un_struc_formula f2 vd.Cast.view_vars in
                    let f3 = x_add_1 Tpdispatcher.simplify_raw (CP.wrap_exists_svl f3 [idx]) in
                    let f3p = TP.pairwisecheck_raw f3 in
                    let f4 = CF.project_body_num vd.Cast.view_un_struc_formula f3p vd.Cast.view_vars in
                    let f4 = x_add_1 Tpdispatcher.simplify_raw (CP.wrap_exists_svl f4 [idx]) in
                    let f5 = Fixcalc.widen f3 f4 in
                    f5
                  in
                  let () = x_tinfo_hp (add_str "alter_num_inv" Cprinter.string_of_pure_formula) alter_num_inv no_pos in
                  let alter_body = CF.project_body_num vd.Cast.view_un_struc_formula alter_num_inv vd.Cast.view_vars in
                  let alter_body = x_add_1 Tpdispatcher.simplify_raw (CP.wrap_exists_svl alter_body [idx]) in
                  if Tpdispatcher.imply_raw alter_num_inv alter_body then
                    let () = x_binfo_pp ("Predicate " ^ vd.Cast.view_name ^ " has precise invariant\n") no_pos in
                    (true,alter_num_inv)
                  else
                    let () = x_binfo_pp ("Predicate " ^ vd.Cast.view_name ^ " has over invariant\n") no_pos in
                    (false,fixc)
                in
                is_precise_num
              with _ ->
                  let () = x_binfo_pp ("Predicate " ^ vd.Cast.view_name ^ " has over invariant (exc) \n") no_pos in
                  (false,fixc)
          )  (List.combine view_list_num_with_inv num_invs) in
          let precise_list,num_invs = List.split precise_num_invs in
          (* let baga_invs = List.map (fun vd -> Hashtbl.find Excore.map_baga_invs vd.Cast.view_name) view_list_baga in *)
          let baga_invs = List.map (fun vd -> Hashtbl.find Excore.map_baga_invs vd.Cast.view_name) view_list_num_with_inv in
          let fixcalc_invs = List.map (fun vd -> vd.Cast.view_fixcalc) view_list_baga in
          let fixcalc_invs_cviews0 = List.map (fun vd -> vd.Cast.view_fixcalc) cviews0 in
          let () = x_tinfo_hp (add_str "fixcalc_invs" (pr_list (pr_option Cprinter.string_of_mix_formula))) fixcalc_invs no_pos in
          (* let () = x_tinfo_hp (add_str "fixcalc_invs_inv" (pr_list (pr_option Cprinter.string_of_mix_formula))) fixcalc_invs_inv no_pos in *)
          let () = x_tinfo_hp (add_str "fixcalc_invs (cviews0)" (pr_list (pr_option Cprinter.string_of_mix_formula))) fixcalc_invs_cviews0 no_pos in
          let () = x_tinfo_hp (add_str "num_invs" (pr_list Cprinter.string_of_pure_formula)) num_invs_wrap_index no_pos in
          let () = x_tinfo_hp (add_str "baga_invs" (pr_list Excore.EPureI.string_of_disj)) baga_invs no_pos in
          let () = List.iter (fun (vd,inv) ->
              Hashtbl.add Excore.map_num_invs vd.Cast.view_name ((CP.mk_self None)::vd.Cast.view_vars,inv)
          ) (List.combine view_list_baga0 num_invs) in
          let baga_num_invs = List.combine baga_invs num_invs in
          let combined_invs = List.map (fun (disj,pf) ->
              let disj1 = List.hd (Excore.EPureI.mk_epure pf) in
              let new_disj = List.map (fun disj2 -> Excore.EPureI.mk_star disj1 disj2) disj in
              new_disj
          ) baga_num_invs in
          let () = x_tinfo_hp (add_str "combined_invs" (pr_list Excore.EPureI.string_of_disj)) combined_invs no_pos in
          let () = List.iter (fun (vd,inv) ->
              Hashtbl.replace Excore.map_baga_invs vd.Cast.view_name inv
          ) (List.combine view_list_baga0 combined_invs) in
          let unfold_cnt = new Gen.change_flag in
          let rec unfold precise old_invs =
            if unfold_cnt # exceed 10 then
              let () = x_binfo_pp "WARNING : Unfolding for baga-inv exceeded 10" no_pos in
              old_invs
            else
              let () = unfold_cnt # inc in
              (* let () = x_binfo_hp (add_str "old_invs" (pr_list Excore.EPureI.string_of_disj)) old_invs no_pos in *)
              let new_invs = List.map (fun vd ->
                  let new_inv = Wrapper.wrap_infer_inv (x_add Cvutil.xpure_symbolic_baga3) cviews0 (Cast.formula_of_unstruc_view_f vd) in
                  let new_inv = List.map (fun (svl,pf) ->
                      let idx = CP.mk_typed_spec_var Int "idx" in
                      let new_pf_svl = CP.fv pf in
                      let new_pf = if List.mem idx new_pf_svl then CP.wrap_exists_svl pf [idx] else pf in
                      (svl,new_pf)
                  ) new_inv in
                  let () = Debug.ninfo_hprint (add_str "new_inv" Excore.EPureI.string_of_disj) new_inv no_pos in
                  new_inv
              ) view_list_baga0 in
              let () = Debug.ninfo_hprint (add_str "new_invs" (pr_list Excore.EPureI.string_of_disj)) new_invs no_pos in
              if List.length old_invs = 0 then
                let () = List.iter (fun (vd,new_inv) ->
                    Hashtbl.replace Excore.map_baga_invs vd.Cast.view_name new_inv
                ) (List.combine view_list_baga0 new_invs) in
                unfold precise new_invs
              else if not precise then
                let () = List.iter (fun (vd,new_inv) ->
                    Hashtbl.replace Excore.map_baga_invs vd.Cast.view_name new_inv;
                    Hashtbl.replace Excore.map_precise_invs vd.Cast.view_name false
                ) (List.combine view_list_baga0 new_invs) in
                new_invs
              else if List.for_all (fun (ante,cons) ->
                  Excore.EPureI.imply_disj ante cons) (List.combine old_invs new_invs) then
                old_invs
              else
                let () = List.iter (fun (vd,new_inv) ->
                    Hashtbl.replace Excore.map_baga_invs vd.Cast.view_name new_inv
                ) (List.combine view_list_baga0 new_invs) in
                unfold precise new_invs
          in
          (* let precise_list = List.map (fun (vd, num_inv) -> *)
          (*     let is_precise_num = *)
          (*       let pr = Cprinter.string_of_mix_formula in *)
          (*       let () = x_binfo_hp (add_str "precise? view_user_inv" pr) vd.Cast.view_user_inv no_pos in *)
          (*       let () = x_binfo_hp (add_str "(2) view_x_formula" pr) vd.Cast.view_x_formula no_pos in *)
          (*       let () = x_binfo_hp (add_str "view_fixcalc" (pr_option pr)) vd.Cast.view_fixcalc no_pos in *)
          (*       if not(CP.isConstTrue (MCP.pure_of_mix vd.Cast.view_user_inv)) then true *)
          (*       else if CP.isConstTrue num_inv then true *)
          (*       else *)
          (*         let body = CF.project_body_num vd.Cast.view_un_struc_formula num_inv vd.Cast.view_vars in *)
          (*         let root = CP.mk_spec_var "self" in *)
          (*         let body = CP.wrap_exists_svl body [root] in *)
          (*         let () = x_tinfo_hp (add_str "body" Cprinter.string_of_pure_formula) body no_pos in *)
          (*         let () = x_tinfo_hp (add_str "num_inv" Cprinter.string_of_pure_formula) num_inv no_pos in *)
          (*         Tpdispatcher.imply_raw num_inv body *)
          (*     in *)
          (*     in is_precise_num *)
          (* ) (List.combine view_list_baga0 num_invs) in *)
          (* WN : Looping at unfold with imprecise inv *)
          let new_invs = unfold (List.for_all (fun a -> a) precise_list) combined_invs in
          let () = Debug.ninfo_hprint (add_str "new_invs" (pr_list Excore.EPureI.string_of_disj)) new_invs no_pos in
          ()
              (* let new_invs_list = x_add_1 Expure.fix_ef view_list cviews0 in *)
              (* let new_invs_list = List.map (fun epd -> Excore.EPureI.to_cpure_disj epd) new_invs_list in *)
              (* let () = x_tinfo_hp (add_str "view invs" (pr_list (fun v -> *)
              (*     Cprinter.string_of_mix_formula v.Cast.view_user_inv))) view_list no_pos in *)
              (* let () = x_tinfo_hp (add_str "baga_invs" (pr_list Cprinter.string_of_ef_pure_disj)) new_invs_list no_pos in *)
              (* if user inv stronger than baga inv, invoke dis_inv_baga() *)
              (* let lst = List.combine view_list new_invs_list in *)
              (* let baga_stronger = List.for_all *)
              (*   (fun (vd,bi) -> *)
              (*       match vd.Cast.view_baga_inv with *)
              (*         | None -> true *)
              (*         | Some uv -> *)
              (*               let () = Debug.ninfo_hprint (add_str ("infered baga inv("^vd.Cast.view_name^")") (Cprinter.string_of_ef_pure_disj)) bi no_pos in *)
              (*               Excore.EPureI.imply_disj (Excore.EPureI.from_cpure_disj bi) uv *)
              (*   ) lst in *)
              (* let pr = pr_list (pr_pair (fun vd -> vd.Cast.view_name)  Cprinter.string_of_ef_pure_disj) in *)
              (* x_binfo_hp pr lst no_pos; *)
              (* if (not baga_stronger) then ( *)
              (*     () *)
            (* x_binfo_pp "not baga_stronger\n" no_pos; *)
            (* Globals.dis_inv_baga () *)
              (* ) else *)
              (*   () *)
            (* update with stronger baga invariant *)
            (* () *)
            (* let new_map = List.combine views_list new_invs_list in *)
            (* List.iter (fun (cv,inv) -> Hashtbl.add CP.map_baga_invs cv.C.view_name inv) new_map *)
      ) ls_mut_rec_views1 in
      let cviews1 = (* if !Globals.gen_baga_inv then *)
        List.map (fun cv ->
            let inv = Hashtbl.find Excore.map_baga_invs cv.C.view_name in
            let precise = Hashtbl.find Excore.map_precise_invs cv.C.view_name in
            let () = x_binfo_hp (add_str ("infered baga inv("^cv.C.view_name^")") (Cprinter.string_of_ef_pure_disj)) inv (* (Excore.EPureI.pairwisecheck_disj inv) *) no_pos in
            let () = print_string_quiet "\n" in
            let user_inv = MCP.pure_of_mix cv.Cast.view_user_inv in
            let body = CF.project_body_num cv.Cast.view_un_struc_formula user_inv cv.Cast.view_vars in
            let is_sound = x_add Tpdispatcher.imply_raw body user_inv in
            let () = if not is_sound then
              x_binfo_hp (add_str "User supplied inv is not sound: " !CP.print_formula) user_inv no_pos
            else () in
            if precise then
              match cv.Cast.view_baga_inv with
                | None -> {cv with
                      C.view_baga_inv = Some inv;
                      C.view_baga_over_inv = Some inv;
                      C.view_baga_under_inv = Some inv;
                      C.view_baga_x_over_inv = Some inv;
                      C.view_user_inv = x_add_1 Mcpure.mix_of_pure (Excore.EPureI.ef_conv_disj inv);
                      C.view_x_formula = x_add_1 Mcpure.mix_of_pure (Excore.EPureI.ef_conv_disj inv);
                  }
                | Some inv0 ->
                      if Excore.EPureI.imply_disj (Excore.EPureI.from_cpure_disj inv) inv0 then {cv with
                          C.view_baga_inv = Some inv;
                          C.view_baga_over_inv = Some inv;
                          C.view_baga_under_inv = Some inv;
                          C.view_baga_x_over_inv = Some inv;
                          C.view_user_inv = x_add_1 Mcpure.mix_of_pure (Excore.EPureI.ef_conv_disj inv);
                          C.view_x_formula = x_add_1 Mcpure.mix_of_pure (Excore.EPureI.ef_conv_disj inv);
                      }
                      else cv
            else
              let inf_inv = Excore.EPureI.ef_conv_disj inv in
              if (Tpdispatcher.imply_raw inf_inv user_inv) || (not is_sound) then
              {cv with
                  C.view_baga_over_inv = Some inv;
                  C.view_baga_x_over_inv = Some inv;
                  C.view_user_inv = x_add_1 Mcpure.mix_of_pure (Excore.EPureI.ef_conv_disj inv);
                  C.view_x_formula = x_add_1 Mcpure.mix_of_pure (Excore.EPureI.ef_conv_disj inv);
              }
              else cv
        ) cviews0
            (* else *)
            (*   cviews0 *)
      in
      (* let () = (\* if !Globals.gen_baga_inv then *\) ( *)
      (*   x_binfo_pp "end gen baga\n" no_pos; *)
      (*   Globals.dis_inv_baga () *)
      (* ) in *)
      cviews1
    else
      cviews0
  in
  cviews0

and fill_one_base_case prog vd = Debug.no_1 "fill_one_base_case" Cprinter.string_of_view_decl Cprinter.string_of_view_decl (fun vd -> fill_one_base_case_x prog vd) vd

and fill_one_base_case_x prog vd =
  if vd.C.view_is_prim then
    (Debug.ninfo_zprint (lazy ("fill_one_base - prim")) no_pos;
    {vd with C.view_base_case = None; C.view_raw_base_case = None})
  else
    begin
      {vd with C.view_base_case = (* WN : smt-compete problem : can be large! *)
              (* if !Globals.smt_compete_mode then None *)
              (* else *)
              compute_base_case prog vd.C.view_name vd.C.view_un_struc_formula (Cpure.SpecVar ((Named vd.C.view_data_name), self, Unprimed) ::vd.C.view_vars)
      }
    end

and  fill_base_case prog =  {prog with C.prog_view_decls = List.map (fill_one_base_case prog) prog.C.prog_view_decls }

(* An Hoa : trans_rel *)
and trans_rel (prog : I.prog_decl) (rdef : I.rel_decl) : C.rel_decl =
  let pos = IP.pos_of_formula rdef.I.rel_formula in
  let rel_sv_vars = List.map (fun (var_type, var_name) -> CP.SpecVar (trans_type prog var_type pos, var_name, Unprimed)) rdef.I.rel_typed_vars in
  let n_tl = List.map (fun (var_type, var_name) -> (var_name,{ sv_info_kind = (trans_type prog var_type pos);id = fresh_int () })) rdef.I.rel_typed_vars in
  (* Need to collect the type information before translating the formula *)
  let n_tl = gather_type_info_pure prog rdef.I.rel_formula n_tl in
  let crf = trans_pure_formula rdef.I.rel_formula n_tl in
  let crdef = {C.rel_name = rdef.I.rel_name; 
  C.rel_vars = rel_sv_vars;
  C.rel_formula = crf; }
  in
  (* Forward the relation to the smt solver. *)
  let _ = Smtsolver.add_relation crdef.Cast.rel_name rel_sv_vars crf in
  crdef

and trans_templ (prog: I.prog_decl) (tdef: I.templ_decl): C.templ_decl =
  let pos = tdef.I.templ_pos in
  let c_ret_typ = trans_type prog tdef.I.templ_ret_typ pos in
  let c_params = List.map (fun (t, n) -> 
      CP.SpecVar (trans_type prog t pos, n, Unprimed)) tdef.I.templ_typed_params in 
  let n_tl = List.map (fun (t, n) -> 
      (n, { sv_info_kind = (trans_type prog t pos); id = fresh_int (); })) tdef.I.templ_typed_params in
  let c_body = match tdef.I.templ_body with
    | None -> 
          let unk_coes = List.map 
            (fun (t, n) -> CP.SpecVar (trans_type prog t pos, tdef.I.templ_name ^ "_" ^ n, Unprimed)) 
            tdef.I.templ_typed_params in 
          let unk_const = CP.SpecVar (Int, tdef.I.templ_name ^ "_" ^ (string_of_int 0), Unprimed) in
          let unk_exps = List.map (fun v -> CP.mkVar v pos) (unk_const::unk_coes) in
          let body = List.fold_left (fun a (c, v) -> CP.mkAdd a (CP.mkMult c (CP.mkVar v pos) pos) pos) 
            (List.hd unk_exps) (List.combine (List.tl unk_exps) c_params) in
          Some body
    | Some bd -> 
          let n_tl = gather_type_info_exp prog bd n_tl tdef.I.templ_ret_typ in
          Some (trans_pure_exp bd (fst n_tl))
  in
  let c_templ = {
      C.templ_name = tdef.I.templ_name;
      C.templ_ret_typ = c_ret_typ;
      C.templ_params = c_params;
      C.templ_body = c_body;
      C.templ_pos = pos; } in
  C.templ_decls # push c_templ; c_templ
      
and trans_ut (prog: I.prog_decl) (utdef: I.ut_decl): C.ut_decl =
  let pos = utdef.I.ut_pos in
  let c_params = List.map (fun (t, n) -> 
      CP.SpecVar (trans_type prog t pos, n, Unprimed)) utdef.I.ut_typed_params in 
  let n_tl = List.map (fun (t, n) -> 
      (n, { sv_info_kind = (trans_type prog t pos); id = fresh_int (); })) utdef.I.ut_typed_params in
  let c_ut = {
      C.ut_name = utdef.I.ut_name;
      C.ut_params = c_params;
      C.ut_is_pre = utdef.I.ut_is_pre;
      C.ut_pos = pos; } in
  c_ut

and trans_hp_x (prog : I.prog_decl) (hpdef : I.hp_decl) : (C.hp_decl * C.rel_decl) =
  let pos = IF.pos_of_formula hpdef.I.hp_formula in
  let hp_sv_vars = List.map (fun (var_type, var_name, i) -> (CP.SpecVar (trans_type prog var_type pos, var_name, Unprimed), i))
    hpdef.I.hp_typed_inst_vars in
  let n_tl = List.map (fun (var_type, var_name, i) -> (var_name,{ sv_info_kind = (trans_type prog var_type pos);id = fresh_int () })) hpdef.I.hp_typed_inst_vars in
  (* Need to collect the type information before translating the formula *)
  let n_tl = gather_type_info_formula prog hpdef.I.hp_formula n_tl false in
  let (n_tl,crf) = trans_formula  prog false [] false hpdef.I.hp_formula n_tl false in
  (*non-ptrs are @NI by default*)
  let hp_sv_vars1 = List.map (fun (sv, i_kind) ->
      let n_i_kind = if not (CP.is_node_typ sv) then NI else i_kind in
      (sv, n_i_kind)
  ) hp_sv_vars in
  let chprel = {C.hp_name = hpdef.I.hp_name; 
  C.hp_vars_inst = hp_sv_vars1;
  C.hp_part_vars = hpdef.I.hp_part_vars;
  Cast.hp_root_pos = 0; (*default, reset when def is inferred*)
  C.hp_is_pre = hpdef.I.hp_is_pre;
  C.hp_formula = crf; }
  in
  let c_p_hprel = Cast.generate_pure_rel chprel in
  chprel,c_p_hprel

and trans_hp (prog : I.prog_decl) (hpdef : I.hp_decl) : (C.hp_decl * C.rel_decl) =
  let pr1 = Iprinter.string_of_hp_decl in
  let pr2 = Cprinter.string_of_hp_decl in
  Debug.no_1 "trans_hp" pr1 (pr_pair pr2 Cprinter.string_of_rel_decl)
      (fun _ -> trans_hp_x (prog : I.prog_decl) (hpdef : I.hp_decl)) hpdef

and trans_axiom (prog : I.prog_decl) (adef : I.axiom_decl) : C.axiom_decl =
  let pr1 adef = Iprinter.string_of_axiom_decl_list [adef] in
  let pr2 adef = Cprinter.string_of_axiom_decl_list [adef] in
  Debug.no_1 "trans_axiom" pr1 pr2 (fun x -> trans_axiom_x prog adef) adef

(**
   * An Hoa : translate an axiom 
*)
and trans_axiom_x (prog : I.prog_decl) (adef : I.axiom_decl) : C.axiom_decl =
  (* Collect types of variables in the formula *)
  let n_tl = gather_type_info_pure prog adef.I.axiom_hypothesis [] in
  let n_tl = gather_type_info_pure prog adef.I.axiom_conclusion n_tl in
  (* Translate the hypothesis and conclusion *)
  let chyp = trans_pure_formula adef.I.axiom_hypothesis n_tl in
  let ccln = trans_pure_formula adef.I.axiom_conclusion n_tl in
  (* let () = Smtsolver.add_axiom_def (Smtsolver.AxmDefn (chyp,ccln)) in *)
  let cadef = { C.axiom_id=adef.I.axiom_id; 
  C.axiom_hypothesis = chyp;
  C.axiom_conclusion = ccln; }
  in
  (* Forward the axiom to the smt solver. *)
  let _ = Smtsolver.add_axiom chyp Smtsolver.IMPLIES ccln in
  cadef
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
      
and compute_base_case prog vn cf vars = 
  let pr1 x = Cprinter.string_of_list_formula (fst (List.split x)) in
  let pr2 = Cprinter.string_of_spec_var_list in
  let pr3 = pr_option (fun (p, _) -> Cprinter.string_of_pure_formula p) in
  Debug.no_3(* _loop *) "compute_base_case" pr_id pr1 pr2 pr3 (fun _ _ _ -> compute_base_case_x prog vn cf vars) vn cf vars

and compute_base_case_x prog vn cf vars = (*flatten_base_case cf s self_c_var *)
  let compute_base_case_x_op ()=
    let xpuring f = 
      let (xform', _ , _) = x_add Cvutil.xpure_symbolic 3 prog f in
      let xform = simpl_memo_pure_formula Cvutil.simpl_b_formula Cvutil.simpl_pure_formula xform' (x_add TP.simplify_a 10) in
      ([],[fold_mem_lst (CP.mkTrue no_pos) true true xform]) in
    let rec part f = match f with
      | CF.Or b -> 
            let (c1,c2) = part b.CF.formula_or_f1 in
            let (d1,d2) = part b.CF.formula_or_f2 in
            (c1@d1,c2@d2)
      | CF.Base b -> 
            let () = Debug.ninfo_hprint (add_str "f (base)" ( Cprinter.string_of_formula)) f no_pos in
            if (CF.is_complex_heap b.CF.formula_base_heap) then
              if (CF.is_rec_br vn f) then
                xpuring f
              else
                let l1, l2 = xpuring f in
                (List.map MCP.mix_of_pure l2,l1)
            else ([b.CF.formula_base_pure],[])
      | CF.Exists e ->
            let () = Debug.ninfo_hprint (add_str "f (exists)" ( Cprinter.string_of_formula)) f no_pos in
            if (CF.is_complex_heap e.CF.formula_exists_heap) then
              if (CF.is_rec_br vn f) then
                xpuring f
              else
                let l1, l2 = xpuring f in
                let () = Debug.ninfo_hprint (add_str "l2" (pr_list !CP.print_formula )) l2 no_pos in
                (List.map MCP.mix_of_pure l2,l1)
            else
              let l1,qv = e.CF.formula_exists_pure, e.CF.formula_exists_qvars in
              ([MCP.memo_pure_push_exists qv l1],[])
    in
    let sim,co = List.split (List.map (fun (c,_)->
        let _=proving_loc #set (CF.pos_of_formula c) in
        let () = Debug.ninfo_hprint (add_str "c" ( Cprinter.string_of_formula)) c no_pos in
        part c
    ) cf) in
    let sim,co = List.concat sim, List.concat co in
    let () = Debug.ninfo_hprint (add_str "sim" (pr_list Cprinter.string_of_mix_formula)) sim no_pos in
    if (sim==[]) then None 
    else
      let guards = List.map (fold_mem_lst (CP.mkTrue no_pos) true true) sim in
      let cases = sim in
      let cases = List.fold_left mkOr_mems (mkMFalse no_pos) cases in  
      let bcg = List.fold_left (fun a p -> a@(CP.split_conjunctions (x_add TP.simplify_a (-1) p))) [] guards in
      let bcg = Gen.BList.remove_dups_eq (CP.equalFormula_f CP.eq_spec_var) bcg in
      let one_bc = List.fold_left (fun a c -> CP.mkOr a c None no_pos) (CP.mkFalse no_pos) guards in
      let bc_impl c = let r,_,_ = TP.imply_sub_no one_bc c "0" false None in r in
      let sat_subno  = ref 0 in
      let bcg = List.filter (fun c->(not (CP.isConstTrue c))&& (bc_impl c)&& List.for_all 
	  (fun d-> not (x_add TP.is_sat_sub_no 10 (CP.mkAnd c d no_pos) sat_subno)) co ) bcg in
      match bcg with
        | []-> None
        | _ -> Some (CP.disj_of_list bcg no_pos,cases)
  in
  wrap_proving_kind PK_Compute_Base_Case compute_base_case_x_op ()
      
and set_materialized_prop_x cdef =
  let args = (CP.SpecVar (Named cdef.C.view_data_name, self, Unprimed))::cdef.C.view_vars in
  let mvars = find_materialized_prop args cdef.C.view_materialized_vars (C.formula_of_unstruc_view_f cdef) in
  (cdef.C.view_materialized_vars <- mvars; cdef)
      
and set_materialized_prop cdef = 
  let pr1 = Cprinter.string_of_view_decl in
  Debug.no_1(* _loop *)  "set_materialized_prop" pr1 pr1 set_materialized_prop_x cdef
      
and find_m_prop_heap params eq_f h = 
  let pr = Cprinter.string_of_h_formula in
  let pr1 = Cprinter.string_of_spec_var_list in
  (* let prr = pr_list Cprinter.string_of_mater_property in *)
  let prr x = Cprinter.string_of_mater_prop_list x in (*string_of_int (List.length x) in*)
  Debug.no_2 "find_m_prop_heap" pr pr1 prr (fun _ _ -> find_m_prop_heap_x params eq_f h) h params
      
and find_m_prop_heap_x params eq_f h = 
  let rec helper h =
    match h with
      | CF.ThreadNode h ->
            let l = eq_f h.CF.h_formula_thread_node in
            x_tinfo_hp (add_str "thread:l" (Cprinter.string_of_spec_var_list)) l no_pos;
            let res = List.map (fun v -> C.mk_mater_prop v true []) l in
            res (*TOCHECK: currently ignore resource*)
      | CF.DataNode h ->
            let l = if (Immutable.isLend h.CF.h_formula_data_imm) then [] else eq_f h.CF.h_formula_data_node in
            x_tinfo_hp (add_str "data:l" (Cprinter.string_of_spec_var_list)) l no_pos;
            List.map (fun v -> C.mk_mater_prop v true []) l 
      | CF.ViewNode h -> 
            let l = if (Immutable.isLend h.CF.h_formula_view_imm) then [] else eq_f h.CF.h_formula_view_node in
            x_tinfo_hp (add_str "view:l" (Cprinter.string_of_spec_var_list)) l no_pos;
            if l==[] then []
            else
              let ret =  List.map (fun v -> C.mk_mater_prop v true [ h.CF.h_formula_view_name]) l in
              let () = x_tinfo_hp (add_str "ret" (pr_list Cprinter.string_of_mater_property)) ret no_pos in 
              ret
      | CF.HRel (hp,e,_) ->
            let args = CP.diff_svl (CF.get_all_sv h) [hp] in
            (* let l, _  = Sautility.find_root prog [hp] args  [] in *)
            (* let l = eq_f l in *)
            let l = args in
            (* andreeac: to do smth because this is not correct for hrel with more than one arg (args should be [root]) *)
            x_tinfo_hp (add_str "hrel:l" (Cprinter.string_of_spec_var_list)) l no_pos;
            if l==[] then []
            else
              let ret =  List.map (fun v -> C.mk_mater_prop v true [Cprinter.string_of_spec_var hp]) l in
              let () = x_tinfo_hp (add_str "ret" (pr_list Cprinter.string_of_mater_property)) ret no_pos in 
              ret
      | CF.Star h -> (helper h.CF.h_formula_star_h1)@(helper h.CF.h_formula_star_h2)
      | CF.StarMinus h -> (helper h.CF.h_formula_starminus_h1)@(helper h.CF.h_formula_starminus_h2)
      | CF.Conj h -> (helper h.CF.h_formula_conj_h1)@(helper h.CF.h_formula_conj_h2)
      | CF.ConjStar h -> (helper h.CF.h_formula_conjstar_h1)@(helper h.CF.h_formula_conjstar_h2)
      | CF.ConjConj h -> (helper h.CF.h_formula_conjconj_h1)@(helper h.CF.h_formula_conjconj_h2)    
      | CF.Phase h -> (helper h.CF.h_formula_phase_rd)@(helper h.CF.h_formula_phase_rw)  
      | CF.Hole _ | CF.FrmHole _
      | CF.HTrue 
      | CF.HFalse 
              (* | CF.HRel _ *)
      | CF.HEmp | CF.HVar _ -> [] in
  helper h

and find_trans_view_name_x ff self pos =
  let params = [self] in
  let is_member (aset :(CP.spec_var list * CP.spec_var)list) v = 
    let l = List.filter (fun (l,_) -> List.exists (CP.eq_spec_var v) l) aset in
    snd (List.split l) in
  let find_m_prop_heap_aux params pf hf =
    let rec cycle p acc_p v_p =
      if p==[] then v_p
      else
        let has = param_alias_sets pf p in
        let eq_f = (is_member has) in
        let (ls,vs) = find_node_vars eq_f hf in (* returns: (args, [data/view_name]) *)
        let rs = Gen.BList.difference_eq CP.eq_spec_var ls acc_p in 
        cycle rs (rs@p@acc_p) (vs@v_p)  (* why the arguments become the targeted search param? *)
    in cycle params [] [] in
  let find_m_one f = match f with
    | CF.Base b ->
          find_m_prop_heap_aux params b.CF.formula_base_pure b.CF.formula_base_heap
    | CF.Exists b->
          find_m_prop_heap_aux params b.CF.formula_exists_pure b.CF.formula_exists_heap
    | _ -> Error.report_error
          {Error.error_loc = no_pos; Error.error_text = "find_materialized_prop: unexpected disjunction"} in
  let lm = find_m_one ff in
  lm

and find_trans_view_name ff self pos =
  let pr1 = Cprinter.string_of_formula in
  let pr2 = Cprinter.string_of_spec_var in
  Debug.no_2 "find_trans_view_name" pr1 pr2 (pr_list pr_id) (fun _ _ -> find_trans_view_name_x ff self pos) ff self


(*TO CHECK: why there are diferences between DataNode and ViewNode ??? *)
and find_node_vars_x eq_f h =
  let join (a,b) (c,d) = (a@c,b@d) in
  let rec helper h =  match h with
    | CF.DataNode h ->
          let l = eq_f h.CF.h_formula_data_node in
          let () = x_tinfo_hp (add_str "data:l" (Cprinter.string_of_spec_var_list)) l no_pos in
          if l==[] then ([],[])
          else (h.CF.h_formula_data_arguments,[h.CF.h_formula_data_name]) (*TO CHECK*)
    | CF.ViewNode h ->
          let l = eq_f h.CF.h_formula_view_node in
          x_tinfo_hp (add_str "view:l" (Cprinter.string_of_spec_var_list)) l no_pos;
          if l==[] then ([],[])
          else ([],[h.CF.h_formula_view_name])
    | CF.ThreadNode h ->
          let l = eq_f h.CF.h_formula_thread_node in
          x_tinfo_hp (add_str "thread:l" (Cprinter.string_of_spec_var_list)) l no_pos;
          if l==[] then ([],[])
          else ([],[h.CF.h_formula_thread_name])
    | CF.HRel (hp, e, _) ->        
          let l = List.fold_left (fun lst exp ->  
              match exp with
                | (CP.Var (v,_)) ->  (eq_f v)@lst
                | _ -> lst) [] e in
          x_tinfo_hp (add_str "hrel:l" (Cprinter.string_of_spec_var_list)) l no_pos;
          if l==[] then ([],[])
          else ([], [CP.name_of_spec_var hp])
    | CF.Star h -> join (helper  h.CF.h_formula_star_h1) (helper  h.CF.h_formula_star_h2)
    | CF.StarMinus h -> join (helper  h.CF.h_formula_starminus_h1) (helper  h.CF.h_formula_starminus_h2)
    | CF.Conj h -> join (helper  h.CF.h_formula_conj_h1) (helper  h.CF.h_formula_conj_h2)
    | CF.ConjStar h -> join (helper  h.CF.h_formula_conjstar_h1) (helper  h.CF.h_formula_conjstar_h2)
    | CF.ConjConj h -> join (helper  h.CF.h_formula_conjconj_h1) (helper  h.CF.h_formula_conjconj_h2)    
    | CF.Phase h -> join (helper h.CF.h_formula_phase_rd)(helper h.CF.h_formula_phase_rw)  
    | CF.Hole _ | CF.FrmHole _
    | CF.HTrue 
    | CF.HFalse 
    | CF.HEmp | CF.HVar _  -> ([],[]) in
  (* let helper h =  *)
  (*   let pr1 = Cprinter.string_of_h_formula in *)
  (*   let pr2 = Cprinter.string_of_spec_var_list in *)
  (*   Debug.no_1 "find_node_vars" pr1 (pr_pair pr2 pr_id) helper h  in *)
  helper h

and find_node_vars eq_f h =
  let pr_list_id = (pr_list pr_id) in
  let pr = pr_pair (pr_list Cprinter.string_of_spec_var) pr_list_id in
  Debug.no_1 "find_node_vars" Cprinter.string_of_h_formula pr (fun _ -> find_node_vars_x eq_f h) h

and param_alias_sets p params = 
  let eqns = ptr_equations_with_null p in
  (* let asets = Context.alias_nth 10 eqns in *)
  let asets = Csvutil.alias_nth 10 eqns in
  (* let aset_get x = x:: (Context.get_aset asets x) in *)
  let aset_get x = x:: (Csvutil.get_aset asets x) in
  List.map (fun c-> ( aset_get c,c)) params

and find_materialized_prop params forced_vars (f0 : CF.formula) : C.mater_property list =
  let pr1 = Cprinter.string_of_spec_var_list in
  let pr2 = Cprinter.string_of_formula in
  let pr3 = pr_list Cprinter.string_of_mater_property in
  Debug.no_2 "find_materialized_prop" pr1 pr2 pr3 (fun _ _ -> find_materialized_prop_x params forced_vars f0) params f0

and find_materialized_prop_x params forced_vars (f0 : CF.formula) : C.mater_property list = 
  let f_l = CF.list_of_disjuncts f0 in
  let is_member (aset :(CP.spec_var list * CP.spec_var)list) v = 
    let l = List.filter (fun (l,_) -> List.exists (CP.eq_spec_var v) l) aset in
    snd (List.split l) in
  let find_m_prop_heap_aux params pf hf = find_m_prop_heap params (is_member (param_alias_sets pf params)) hf in
  (* let rec cycle p acc_p v_p =
     find_m_prop_heap params (is_member (param_alias_sets pf p)) hf
  (* if p==[] then *)
  (*   find_m_prop_heap params (is_member (param_alias_sets pf v_p)) hf *)
  (* else *)
  (*   let has = param_alias_sets pf p in *)
  (*   let eq_f = (is_member has) in *)
  (*   let (ls,vs) = find_node_vars eq_f hf in *)
  (*   let rs = Gen.BList.difference_eq CP.eq_spec_var ls acc_p in *)
  (*   cycle rs (rs@p@acc_p) (vs@v_p) *)
     in cycle params [] [] in*)
  
  let find_m_one f = match f with
    | CF.Base b ->    
          find_m_prop_heap_aux params b.CF.formula_base_pure b.CF.formula_base_heap
    | CF.Exists b->
          find_m_prop_heap_aux params b.CF.formula_exists_pure b.CF.formula_exists_heap      
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
  let res = if  (List.length lm ==0) then []
  else List.fold_left (fun a c -> merge_mater_lists a c)(List.hd lm) (List.tl lm) in
  if (Gen.BList.subset_eq C.mater_prop_cmp_var forced_vars res) then res
  else (* Error.report_error {Error.error_loc = no_pos; Error.error_text = "find_materialized_prop: the view body does not ensure that all the @R annotated variables would be materialized"} *)
    let () = report_warning no_pos "find_materialized_prop: the view body does not ensure that all the @R annotated variables would be materialized" in []
                                                                                                                                                           
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
  Context.get_aset asets (CP.SpecVar (Globals.null_type, self, Unprimed))
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
    | I.Par _ -> false
    | I.Raise _ -> true
    | I.Try e -> (all_paths_return e.I.exp_try_block) || (List.fold_left (fun a b-> a && (all_paths_return b)) true e.I.exp_catch_clauses)
          || match e.I.exp_finally_clause with 
            | [] -> false
            | h::t -> (all_paths_return h)

and check_return (proc : I.proc_decl) : bool =
  match proc.I.proc_body with
    | None -> true
    | Some e ->
      if (not (I.are_same_type I.void_type proc.I.proc_return)) && (not (all_paths_return e))
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
    | CF.EAssume _ -> f0
    | CF.EInfer b -> CF.EInfer {b with CF.formula_inf_continuation = helper b.CF.formula_inf_continuation}
    | CF.EList b -> CF.EList (map_l_snd helper b) 
  in
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
    | IF.EAssume b-> check_valid_flows_f b.IF.formula_assume_simpl
    | IF.EInfer b -> helper b.IF.formula_inf_continuation
    | IF.EList b -> List.iter (fun c-> helper(snd c)) b in
  helper f

and rename_var sst v =
  try
    List.assoc v sst
  with _ -> v

and rename_proc (proc: I.proc_decl) : I.proc_decl =
  let vs = proc.proc_args in
  let p_vs = List.map (fun p -> p.I.param_name) vs in
  let trail_rex = Str.regexp "_[1-9][0-9]*" in
  let search x = 
    let n = String.length x in
    try 
      Str.search_backward trail_rex x (n-1)
    with _ -> -1 
  in
  let p_pos = List.map search p_vs in
  let new_vs = List.combine p_vs p_pos in
  let new_vs = List.filter (fun (_,n) -> n>0) new_vs in
  (* let _ = x_binfo_hp (add_str "proc params" Iprinter.string_of_param_list) vs no_pos in *)
  let body = proc.I.proc_body in
  if new_vs==[] || body==None then proc
  else
    (* DONE(WN): check if range(new_vs) clash with free_vars of body *)
    let exp_vs = match body with 
        Some body ->IastUtil.find_free_vars_only body 
      | None -> IS.empty in 
    (* let el = IS.elements exp_vs in *)
    (* let _ = x_binfo_hp (add_str "free vars body" (pr_list pr_id)) el no_pos in *)
    let vs2 = List.map (fun (v,n) -> (v,String.sub v 0 n)) new_vs in 
    let clash_flag = IS.exists (fun v -> List.exists (fun (_,n) -> v=n) vs2) exp_vs in
    let _ = x_tinfo_hp (add_str "clash_flag" (string_of_bool)) clash_flag no_pos in
    if clash_flag then
      (* do not rename if there is some name clash *)
      proc
    else
      let new_body = opt_map (x_add rename_exp vs2) proc.I.proc_body in
      let sst = concatMap (fun (v1,v2) -> 
          [((v1,Unprimed),(v2,Unprimed));((v1,Primed),(v2,Primed))]) vs2 in
      let new_static_specs = Iformula.subst_struc sst proc.I.proc_static_specs in
      let new_vs = List.map (fun s ->
          {s with I.param_name = rename_var vs2 s.I.param_name}) vs in
      let _ = x_binfo_hp (add_str "renaming proc" (pr_list (pr_pair pr_id pr_id))) vs2 no_pos in
      let _ = x_tinfo_hp (add_str "renamed specs" Iprinter.string_of_struc_formula) new_static_specs no_pos in
      let _ = x_tinfo_hp (add_str "renamed body" (pr_opt Iprinter.string_of_exp)) new_body no_pos in
      let _ = x_tinfo_hp (add_str "renamed proc params" Iprinter.string_of_param_list) new_vs no_pos in
      { proc with I.proc_static_specs = new_static_specs;
          I.proc_body = new_body;
          I.proc_args = new_vs;
      }

(*
  This is for auxiliary procedures that represent loops.

  addr_vars: a list of addr_vars that need to be translated
  in case they belong to args of the loop aux proc

  proc.proc_body has been processed to eliminate pointers.
  Here we only need to translate the specs and then call
  the original trans_proc

*)
and trans_loop_proc (prog : I.prog_decl) (proc : I.proc_decl) (addr_vars:ident list): C.proc_decl =
  let pr  x = add_str (x.I.proc_name^" Spec") Iprinter.string_of_struc_formula x.I.proc_static_specs in
  let iproc = Iprinter.string_of_proc_decl in
  let cproc = Cprinter.string_of_proc_decl in
  let pr2 x = add_str (x.C.proc_name^" Spec") Cprinter.string_of_struc_formula x.C.proc_static_specs in
  Debug.no_2 "trans_loop_proc" 
      iproc (pr_list pr_id) pr2 
      (fun _ _ -> trans_loop_proc_x prog proc addr_vars) proc addr_vars

and trans_loop_proc_x (prog : I.prog_decl) (proc : I.proc_decl) (addr_vars: ident list): C.proc_decl =
  (* Loop parameters renaming: Temporarily disable due to some erros with sv-comp *)
  (* let proc = rename_proc proc in *)
  (*variables that have been taken address-of*)
  if (addr_vars!=[]) then
    let pos = proc.I.proc_loc in
    let trans_arg_addr arg (* param *) =
      (*Maybe we only need to translate for primitive types*)
      (*If this argument var needs to be translate*)
      if (List.mem arg.I.param_name addr_vars) then
        (true) (*need to be processed*)
      else
        (false)
    in
    let flags = List.map (fun arg -> trans_arg_addr arg) proc.I.proc_args in
    if not (List.exists (fun (b:bool) -> b) flags) then
      (*IF NOT -> DO NOT NEED TO trans_spec*)
      (trans_proc prog proc)
    else
      (*If there is some args to be convert -> DO IT*)
      (*These params have correct types*)
      let params = proc.I.proc_args in
      (* let () = print_endline ("params = " ^ (Iprinter.string_of_param_list params)) in *)
      (******** translate specification >>> ****************)
      let new_static_specs = x_add Pointers.trans_specs proc.I.proc_static_specs params flags pos in
      let new_dynamic_specs = x_add Pointers.trans_specs proc.I.proc_dynamic_specs params flags pos in
      (********<<< translate specification ****************)
      let new_proc = {proc with
          I.proc_static_specs = new_static_specs;
          I.proc_dynamic_specs = new_dynamic_specs;
      }
      in (trans_proc prog new_proc)
  else (trans_proc prog proc)

and comp_vp_add_pre_post f p_ref p_val =
  let check_vp vp pref p_val =
    let orig_full = vp.vperm_full_vars in
    let orig_val = vp.vperm_value_vars in
    let vp_ref = orig_full @ vp.vperm_zero_vars @ vp.vperm_lend_vars @ (List.map snd vp.vperm_frac_vars) in
    let vp_val = orig_full @ orig_val @ vp.vperm_zero_vars @ vp.vperm_lend_vars in
    let res_ref =  Cpure.diff_svl p_ref vp_ref in
    let res_val =  Cpure.diff_svl p_val vp_val in
    let pr_svl = Cprinter.string_of_spec_var_list in
    let () = Debug.ninfo_hprint (add_str "orig_full" pr_svl) orig_full no_pos in
    let () = Debug.ninfo_hprint (add_str "orig_val" pr_svl) orig_val no_pos in
    let () = Debug.ninfo_hprint (add_str "add_full" pr_svl) res_ref no_pos in
    let () = Debug.ninfo_hprint (add_str "add_val" pr_svl) res_val no_pos in
    let new_vp = { vp with vperm_full_vars = orig_full @ res_ref; vperm_value_vars = orig_val@res_val; } in
    new_vp,res_ref
  in
  match f with 
      CF.Base b ->
          let vp = b.CF.formula_base_vperm in
          let n_vp,rem_vp = check_vp vp p_ref p_val in
          (CF.Base {b with CF.formula_base_vperm=n_vp},p_ref)
    | CF.Exists g -> 
          let vp = g.CF.formula_exists_vperm in
          let n_vp,rem_vp = check_vp vp p_ref p_val in
          (CF.Exists {g with CF.formula_exists_vperm=n_vp},p_ref)
    | _ -> 
          let () = x_winfo_pp "VPerm cannot be added to OR" no_pos in
          (f,[]) (* print warning *)

and add_perm_to_spec p_ref p_val (expr : CF.struc_formula) : CF.struc_formula  =
  let pr_f = Cprinter.string_of_struc_formula in
  let pr_svl = Cprinter.string_of_spec_var_list in
  Debug.no_2 (* (fun res -> true) *) "add_perm_to_spec" pr_f pr_svl pr_f (fun _ _ -> add_perm_to_spec_x p_ref p_val expr) expr p_ref

and add_perm_to_spec_x p_ref p_val (expr : CF.struc_formula) : CF.struc_formula  =
  let rec helper flag e =
    (* let f_none _ _ = None in *)
    let f1_term a e = Some(e,a) in
    (* let f_f a e = Some(e,a)  in *)
    let rec f_struc_f a e =
      
      match e with
        | CF.EBase b ->
              (* let () = print_endline ("!!!!! f_struc_f EBase"^(Cprinter.string_of_struc_formula e)) in *)
              (match a with
                | Some (flag,e) -> 
                      (* flag indicates we are inside a structured EAssume *)
                      if flag then
                        let (nf,_) = comp_vp_add_pre_post b.CF.formula_struc_base e [] in
                        Some (CF.EBase {b with CF.formula_struc_base = nf},None)
                            (*failwith "inside EAssume - TODO must add permission here"*)
                      else None
                | None ->
                      begin
                        match b.CF.formula_struc_continuation with
                            None -> Some (e,None)
                          | Some c -> 
                                let f = b.CF.formula_struc_base in
                                let (nf,post_perm)=comp_vp_add_pre_post f p_ref p_val in (* compute pre & post-permission *)
                                let cf= 
                                  if post_perm==[] then c (* no post-perm to add *)
                                  else helper (Some (false,post_perm)) (* adding post-permission to EAssume *) c in
                                Some (CF.EBase { b with CF.formula_struc_base = nf; CF.formula_struc_continuation = Some cf}, None)
                    end)
      | CF.EAssume f ->
            (* let () = print_endline ("!!!!! f_struc_f EAssume"^(Cprinter.string_of_struc_formula e)) in *)
            begin
              match a with 
                  None -> Some (e,None)
                | Some (_,post_perm) -> 
                      (* let assume_simpl = f.CF.formula_assume_simpl in (\* TODO : must add vperm here *\) *)
                      let (assume_simpl,_) = comp_vp_add_pre_post (f.CF.formula_assume_simpl) post_perm [] in
                      let assume_struc = helper (Some(true,post_perm)) f.CF.formula_assume_struc in (* need to add vperm if we have classic/exact post *)
	              let () = Debug.ninfo_hprint (add_str "assume_simpl" Cprinter.string_of_formula) assume_simpl no_pos in
	              let () = Debug.ninfo_hprint (add_str "assume_struc" Cprinter.string_of_struc_formula) assume_struc no_pos in
                      Some (CF.EAssume 
                          {f with CF.formula_assume_struc=assume_struc;
                              CF.formula_assume_simpl=assume_simpl},None) 

            end
      | _ -> None in
  (* let f2 a e = None in *)
  let f_pure = (f1_term,f1_term,f1_term) in
  let f_memo a e = Some(e,a) in
  let f_arg =
    let f1 e _ = e in
    (f1,f1,f1,(f1,f1,f1),f1) in
  let f_gen = (f_struc_f, f1_term, f1_term, f_pure, f_memo) in
  let (a,b) = CF.trans_n_struc_formula e flag f_gen f_arg (fun lst -> None) in
      (* List.fold_left (fun r e -> match r with None -> e | _ -> r) None lst) in *)
  a
  in helper None expr

and add_perm_proc  p = 
  if not(!Globals.ann_vp) then p
  else
    let p_ref = p.C.proc_by_name_params in
    let p_val = p.C.proc_by_value_params @ p.C.proc_by_copy_params in
    let ss = p.C.proc_static_specs in
    let () = Debug.ninfo_hprint (add_str "spec" Cprinter.string_of_struc_formula) ss no_pos in
    let () = Debug.ninfo_hprint (add_str "ref" Cprinter.string_of_spec_var_list) p.C.proc_by_name_params no_pos in
    let () = Debug.ninfo_hprint (add_str "value" Cprinter.string_of_spec_var_list) p.C.proc_by_value_params no_pos in
    let ns = add_perm_to_spec p_ref p_val ss in
    { p with C.proc_static_specs = ns}

and rgx_prelude = Str.regexp ".*prelude"

(* below will trace only files which do not contain "prelude" *)
and trans_proc (prog : I.prog_decl) (proc : I.proc_decl) : C.proc_decl =
  (*let pr  x = add_str (x.I.proc_name^" Spec") Iprinter.string_of_struc_formula x.I.proc_static_specs in
    let pr2 x = add_str (x.C.proc_name^" Spec") Cprinter.string_of_struc_formula x.C.proc_static_specs in
  *)let pr  = Iprinter.string_of_proc_decl in
  let pr2 = Cprinter.string_of_proc_decl 5 in
  let pr_sel f = 
    let source = f.C.proc_source in
    (* print_endline ("source :"^source); *)
    not (Str.string_match rgx_prelude source 0) in
  Debug.no_1_opt pr_sel "trans_proc" pr pr2 (fun p -> add_perm_proc (trans_proc_x prog p)) proc

and trans_proc_x (prog : I.prog_decl) (proc : I.proc_decl) : C.proc_decl =
  let trans_proc_x_op () =
    let _= proving_loc # set (proc.I.proc_loc) in
    let dup_names = Gen.BList.find_one_dup_eq (fun a1 a2 -> a1.I.param_name = a2.I.param_name) proc.I.proc_args in
    let check_return_res = check_return proc in
    if not (Gen.is_empty dup_names) then
      (let p = List.hd dup_names in
      Err.report_error{
          Err.error_loc = p.I.param_loc;
          Err.error_text = "parameter " ^ (p.I.param_name ^ " is duplicated");})
    else if (not check_return_res) && (String.compare proc.I.proc_name "main" != 0) then
      Err.report_error {
          Err.error_loc = proc.I.proc_loc;
          Err.error_text = "not all paths of " ^ (proc.I.proc_name ^ " contain a return"); }
    else
      (E.push_scope ();
      (
      let ho_arg = match proc.I.proc_ho_arg with
        | None -> [] 
        | Some ha -> [ha]  
      in
      let all_args =
        if Gen.is_some proc.I.proc_data_decl then
          (let cdef = Gen.unsome proc.I.proc_data_decl in
          let this_arg ={
              I.param_type = Named cdef.I.data_name;
              I.param_name = this;
              I.param_mod = I.NoMod;
              I.param_loc = proc.I.proc_loc;} in
          let ls_arg ={
              I.param_type = ls_typ;
              I.param_name = ls_name;
              I.param_mod = I.NoMod;
              I.param_loc = proc.I.proc_loc;} in
          let lsmu_arg ={
              I.param_type = lsmu_typ;
              I.param_name = lsmu_name;
              I.param_mod = I.NoMod;
              I.param_loc = proc.I.proc_loc;} in
          let waitlevel_arg ={
              I.param_type = waitlevel_typ;
              I.param_name = waitlevel_name;
              I.param_mod = I.NoMod;
              I.param_loc = proc.I.proc_loc;} in
          waitlevel_arg::lsmu_arg::ls_arg::this_arg :: proc.I.proc_args @ ho_arg)
        else proc.I.proc_args @ ho_arg in
      let p2v (p : I.param) = {
          E.var_name = p.I.param_name;
          E.var_alpha = p.I.param_name;
          E.var_type = p.I.param_type; } in
      let vinfos = List.map p2v all_args in
      let todo_unk = List.map (fun v -> E.add v.E.var_name (E.VarInfo v)) vinfos in
      let cret_type = trans_type prog proc.I.proc_return proc.I.proc_loc in
      let free_vars = List.map (fun p -> p.I.param_name) all_args in
      let add_param p = (p.I.param_name,
      {sv_info_kind =  (trans_type prog p.I.param_type p.I.param_loc);
      id = fresh_int () }) in
      let n_tl = List.map add_param all_args in
      let n_tl = type_list_add res_name { sv_info_kind = cret_type;id = fresh_int () } n_tl in
      let n_tl = type_list_add eres_name { sv_info_kind = UNK ;id = fresh_int () } n_tl in
      let is_primitive = not (proc.I.proc_is_main) in
      (* Termination: Add info of logical vars *)
      let add_logical tl (CP.SpecVar (t, i, _)) = type_list_add i {
          sv_info_kind = t;
          id = fresh_int () } tl in
      let log_vars = List.concat (List.map (trans_logical_vars) prog.I.prog_logical_var_decls) in
      let n_tl =  List.fold_left add_logical n_tl log_vars in
      (*let () = print_endline ("@@@before") in*)
      let () = check_valid_flows proc.I.proc_static_specs in
      let () = check_valid_flows proc.I.proc_dynamic_specs in
      (*let () = print_endline ("@@@after") in*)
      (* let () = print_endline ("trans_proc: "^ proc.I.proc_name ^": before set_pre_flow: specs = " ^ (Iprinter.string_of_struc_formula (proc.I.proc_static_specs@proc.I.proc_dynamic_specs))) in *)
      (* let () = Debug.info_zprint (lazy (("  transform I2C: " ^  proc.I.proc_name ))) no_pos in *)
      (* let () = Debug.info_zprint (lazy (("   static spec" ^(Iprinter.string_of_struc_formula proc.I.proc_static_specs)))) no_pos in *)
      let (n_tl,cf) = trans_I2C_struc_formula 2 prog false true free_vars proc.I.proc_static_specs n_tl true true (*check_pre*) in
      let cf = CF.add_inf_cmd_struc is_primitive cf in
      let static_specs_list = set_pre_flow cf in
      (* let () = Debug.info_zprint (lazy (("   static spec" ^(Cprinter.string_of_struc_formula static_specs_list)))) no_pos in *)
      (* let () = print_string "trans_proc :: set_pre_flow PASSED 1\n" in *)
      let (n_tl,cf) = trans_I2C_struc_formula 3 prog false true free_vars proc.I.proc_dynamic_specs n_tl true true (*check_pre*) in
      let cf = CF.add_inf_cmd_struc is_primitive cf in
      let dynamic_specs_list = set_pre_flow cf in
      (****** Infering LSMU from LS if there is LS in spec >>*********)
      let static_specs_list =
        if (!Globals.allow_locklevel && !Globals.allow_lsmu_infer) then
          let vars = CF.struc_fv static_specs_list in
          let b = List.exists (fun sv -> (CP.name_of_spec_var sv)=Globals.ls_name) vars in
          if b then
            CF.infer_lsmu_struc_formula static_specs_list
          else static_specs_list
        else static_specs_list
      in
      let dynamic_specs_list =
        if (!Globals.allow_locklevel && !Globals.allow_lsmu_infer) then
          let vars = CF.struc_fv dynamic_specs_list in
          let b = List.exists (fun sv -> (CP.name_of_spec_var sv)=Globals.ls_name) vars in
          if b then
            CF.infer_lsmu_struc_formula dynamic_specs_list
          else dynamic_specs_list
        else dynamic_specs_list
      in
      (******<< Infering LSMU from LS if there is LS in spec  *********)
      (* WN : what is LSMU? lockset? *)
      (* Termination: Normalize the specification 
       * with the default termination information
       * Primitive functions: Term[] 
       * User-defined functions: MayLoop 
       * or TermR and TermU if @term *)
      let args = List.map (fun p ->
          ((trans_type prog p.I.param_type p.I.param_loc), (p.I.param_name))) proc.I.proc_args in
      let ho_arg = map_opt (fun ha -> 
        ((trans_type prog ha.I.param_type ha.I.param_loc), (ha.I.param_name))) proc.I.proc_ho_arg in
      (* let fname = proc.I.proc_name in                                                                                        *)
      (* let params = List.map (fun (t, v) -> CP.SpecVar (t, v, Unprimed)) args in                                              *)
      (* let rec find_vars sp = match sp with                                                                                   *)
      (*   | IF.ECase _ (* {I.formula_case_branches = lst} *) -> []                                                             *)
      (*   | IF.EBase b -> b.IF.formula_struc_implicit_inst                                                                     *)
      (*   | _ -> [] in                                                                                                         *)
      (* let params2 = List.map (fun (v,p) -> CP.SpecVar (Int, v, p)) (find_vars proc.I.proc_static_specs) in                   *)
      (* (* let () = Debug.ninfo_hprint (add_str "params" Cprinter.string_of_spec_var_list) params no_pos in *)                  *)
      (* (* let () = Debug.ninfo_hprint (add_str "specs" Iprinter.string_of_struc_formula) proc.I.proc_static_specs no_pos in *) *)
      (* let imp_spec_vars = CF.collect_important_vars_in_spec true static_specs_list in                                        *)
      (* let () = x_tinfo_hp (add_str "params2" Cprinter.string_of_spec_var_list) params2 no_pos in                      *)
      (* let () = x_tinfo_hp (add_str "imp_spec_vars" Cprinter.string_of_spec_var_list) imp_spec_vars no_pos in          *)
      (* let () = x_tinfo_hp (add_str "specs" Cprinter.string_of_struc_formula) static_specs_list no_pos in              *)
      (* let params = imp_spec_vars @ params  in                                                                                *)
      (* let params = List.filter                                                                                               *)
      (*   (fun sv -> match sv with                                                                                             *)
      (*     | CP.SpecVar(t,_,_) ->                                                                                             *)
      (*       (match t with                                                                                                    *)
      (*       | Int | Bool -> true                                                                                             *)
      (*       | _ -> false)) params in                                                                                         *)
      (* let pos = proc.I.proc_loc in                                                                                           *)

      (* let utpre_name = fname ^ "pre" in                                                                                      *)
      (* let utpost_name = fname ^ "post" in                                                                                    *)

      (* let utpre_decl = {                                                                                                     *)
      (*   C.ut_name = utpre_name;                                                                                              *)
      (*   C.ut_params = params;                                                                                                *)
      (*   C.ut_is_pre = true;                                                                                                  *)
      (*   C.ut_pos = pos } in                                                                                                  *)
      (* let utpost_decl = { utpre_decl with                                                                                    *)
      (*   C.ut_name = utpost_name;                                                                                             *)
      (*   C.ut_is_pre = false; } in                                                                                            *)

      (* let () = Debug.ninfo_hprint (add_str "added to UT_decls" (pr_list pr_id)) [utpre_name; utpost_name] no_pos in           *)
      (* let () = C.ut_decls # push_list [utpre_decl; utpost_decl] in                                                            *)

      (* let uid = {                                                                                                            *)
      (*   CP.tu_id = 0;                                                                                                        *)
      (*   CP.tu_sid = fname;                                                                                                   *)
      (*   CP.tu_fname = fname;                                                                                                 *)
      (*   CP.tu_call_num = 0;                                                                                                  *)
      (*   CP.tu_args = List.map (fun v -> CP.mkVar v pos) params;                                                              *)
      (*   CP.tu_cond = CP.mkTrue pos;                                                                                          *)
      (*   CP.tu_icond = CP.mkTrue pos;                                                                                         *)
      (*   CP.tu_sol = None;                                                                                                    *)
      (*   CP.tu_pos = pos; } in                                                                                                *)

      let static_specs_list =
        if not !Globals.dis_term_chk then
          CF.norm_struc_with_lexvar is_primitive false None static_specs_list
        else static_specs_list
      in
      let dynamic_specs_list =
        if not !Globals.dis_term_chk then
          CF.norm_struc_with_lexvar is_primitive false None dynamic_specs_list
        else dynamic_specs_list
      in
      
      let exc_list = (List.map (exlist # get_hash) proc.I.proc_exceptions) in
      let r_int = exlist # get_hash abnormal_flow in
      (*annotated may and must error in specs*)
      (* let t_int = exlist # get_hash top_flow in *)
      (* let e_int = exlist # get_hash error_flow in *)
      (* let exc_list = exc_list@[t_int;e_int] in *)
      (if (List.exists is_false_flow exc_list)|| (List.exists (fun c-> not (CF.subsume_flow r_int c)) exc_list) then
	Error.report_error {Err.error_loc = proc.I.proc_loc;Err.error_text =" can not throw an instance of a non throwable class"}
      else ()) ;
      (* let () = print_endline ("Static spec list : " ^ proc.I.proc_name) in *)
      (* let () = print_endline (Cprinter.string_of_struc_formula static_specs_list) in *)
      (* only check procs from user-supplied *)
      let () = if proc.I.proc_is_main then
        let () = x_add Cast.check_proper_return cret_type exc_list dynamic_specs_list in 
        let () = x_add Cast.check_proper_return cret_type exc_list static_specs_list in 
        ()
      else ()
      in
      (* let () = print_string "trans_proc :: Cast.check_proper_return PASSED \n" in *)
      (* let () = print_endline "WN : removing result here" in *)
      (* let n_tl = List.remove_assoc res_name n_tl in *)
      
      let body = match proc.I.proc_body with
        | None -> None
        | Some e -> (* Some (fst (trans_exp prog proc new_body_e)) in *)
          (* let () = print_string ("trans_proc :: Translate body " ^ Iprinter.string_of_exp e ^ "\n") in *)
          (* Wrap the body of the proc with "try and catch" or not, except for proc created from a while loop *)
          if proc.I.proc_is_while || (not proc.I.proc_has_while_return) then Some (fst (trans_exp prog proc e))
          else
            let vn = fresh_name () in
            let pos = I.get_exp_pos e in
            let nl2 = fresh_branch_point_id "" in
            let return_target = I.mkMember (I.mkVar vn pos) ["val"] None pos in
            let return_exp  = I.Return { I.exp_return_val = Some (return_target); I.exp_return_path_id = nl2; I.exp_return_pos = pos} in
            let return_name ret_type =
              match ret_type with
              | Int -> "ret_int"
              | Bool  -> "ret_bool"
              | _ -> "__RET"
            in
            let constant_flow = "ret_"^(new_string_of_typ proc.I.proc_return) in
            let catch_clause = I.mkCatch (Some vn) (Some (Named (constant_flow))) constant_flow None return_exp pos in
            let new_body_e = I.mkTry e [catch_clause] [] nl2 pos in
            let new_body = fst (trans_exp prog proc new_body_e) in
            (*let () = print_endline ("[final result] = "^Cprinter.string_of_exp new_body) in*)
            Some new_body
      in
      (* let () = print_string "trans_proc :: proc body translated PASSED \n" in *)
      (* let args = List.map (fun p -> ((trans_type prog p.I.param_type p.I.param_loc), (p.I.param_name))) proc.I.proc_args in *)
      (** An Hoa : compute the important variables **)
      let ftypes, fnames = List.split args in
      (* fsvars are the spec vars corresponding to the parameters *)
      let imp_vars = List.map2 (fun t -> fun v -> CP.SpecVar (t, v, Unprimed)) ftypes fnames in
      (*    let () = print_string "Function parameters : " in                    *)
      (*    let () = print_endline (Cprinter.string_of_spec_var_list imp_vars) in*)
      (** An Hoa : end **)
      let (by_names_tmp,rest_lst) = List.partition (fun p -> p.I.param_mod = I.RefMod) proc.I.proc_args in
      let (by_copies_tmp,no_mod_tmp) = List.partition (fun p -> p.I.param_mod = I.CopyMod) rest_lst in      
      let new_pt p = trans_type prog p.I.param_type p.I.param_loc in
      let by_names = List.map (fun p -> CP.SpecVar (new_pt p, p.I.param_name, Unprimed)) by_names_tmp in
      let by_copies = List.map (fun p -> CP.SpecVar (new_pt p, p.I.param_name, Unprimed)) by_copies_tmp in
      let by_values = List.map (fun p -> CP.SpecVar (new_pt p, p.I.param_name, Unprimed)) no_mod_tmp in
        (* (List.filter (fun p -> p.I.param_mod = I.CopyMod) proc.I.proc_args) in *)
      (******LOCKSET variable>>*********)
      (*only add lockset into ref_vars if it is mentioned in the spec
        This is to avoid adding too many LS in sequential settings*)
      let by_names = if !Globals.allow_ls then
        let s_f_vars = CF.struc_fv static_specs_list in
        (*let d_f_vars = CF.struc_fv dynamic_specs_list in*)
        if (List.exists (fun v -> CP.name_of_spec_var v = Globals.ls_name) (s_f_vars@s_f_vars)) then
          let ls_var = CP.mkLsVar Unprimed in
          let lsmu_var = CP.mkLsmuVar Unprimed in
          let waitlevel_var = CP.mkWaitlevelVar Unprimed in
          (waitlevel_var::lsmu_var::ls_var::by_names)
        else by_names
      else by_names
      in
      (* let () = print_string "trans_proc :: lockset translated PASSED \n" in *)
      (******<<LOCKSET variable*********)
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
          (* (\*add primeness to distinguish*\) *)
	  (* let by_names = List.map (fun sv ->  *)
          (*     match sv with *)
          (*       | CP.SpecVar (v,t,_) -> CP.SpecVar (v, t, Primed)) by_names  *)
          (* in *)
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
      (* let () = print_string "trans_proc :: vperm translated PASSED \n" in *)
      (*=============================*)
      let final_static_specs_list = 
	if CF.isConstDTrue static_specs_list then 
	  Cast.mkEAssume_norm proc.I.proc_loc 
	else static_specs_list in
      (** An Hoa : print out final_static_specs_list for inspection **)
      (* let () = print_endline ("Static spec list : " ^ proc.I.proc_name) in *)
      (* let () = print_endline (Cprinter.string_of_struc_formula final_static_specs_list) in *)
      let imp_spec_vars = CF.collect_important_vars_in_spec false final_static_specs_list in
      let imp_vars = List.append imp_vars imp_spec_vars in
      let imp_vars = List.append imp_vars [CP.mkRes cret_type] in (* The res variable is also important! *)
      (* let () = print_string "Important variables found: " in *)
      (*    let () = print_endline (Cprinter.string_of_spec_var_list imp_vars) in*)
      (** An Hoa : end **)
      let final_dynamic_specs_list = dynamic_specs_list in
      (* TODO: is below being computed multiple times? *)
      let args2 = args@(prog.I.prog_rel_ids) in
      let () = 
        let cmp x (_,y) = (String.compare (CP.name_of_spec_var x) y) == 0 in

        let log_vars = List.concat (List.map (trans_logical_vars) prog.I.prog_logical_var_decls) in 
        let struc_fv = CP.diff_svl (CF.struc_fv_infer final_static_specs_list) log_vars in
        (*LOCKSET variable*********)
        let ls_var = (ls_typ,ls_name) in
        let lsmu_var = (lsmu_typ,lsmu_name) in
        let waitlevel_var = (waitlevel_typ,waitlevel_name) in
        let lock_vars = [waitlevel_var;lsmu_var;ls_var] in
        (**************************)
        let ffv = Gen.BList.difference_eq cmp (*(CF.struc_fv_infer final_static_specs_list)*) struc_fv (lock_vars@((cret_type,res_name)::(Named raisable_class,eres_name)::args2)) in
        let ffv = List.filter (fun v -> not (CP.is_form_typ v)) ffv in
        let str = Cprinter.string_of_spec_var_list ffv in
        if (ffv!=[]) then 
          Debug.info_zprint (lazy (("WARNING : uninterpreted free variables "^str^" in specification."))) no_pos
              (* Error.report_error {  *)
              (*     Err.error_loc = no_pos; *)
              (*     Err.error_text = "error 3: free variables "^(Cprinter.string_of_spec_var_list ffv)^" in proc "^proc.I.proc_name^" "}  *)
      in
      let args_wi = if proc.Iast.proc_is_main then Iast.extract_mut_args prog proc
      else proc.Iast.proc_args_wi
      in
      let cproc ={
          C.proc_name = proc.I.proc_mingled_name;
          C.proc_source = proc.I.proc_source;
          C.proc_flags = proc.I.proc_flags;
          C.proc_args = args;
          C.proc_ho_arg = ho_arg;
          C.proc_args_wi = args_wi;
          C.proc_imm_args = List.map (fun (id,_) -> (id,false)) args_wi;
          C.proc_return = trans_type prog proc.I.proc_return proc.I.proc_loc;
          C.proc_important_vars =  imp_vars(*(Gen.Basic.remove_dups (proc.I.proc_important_vars @imp_vars))*); (* An Hoa *)
          C.proc_static_specs = (* if proc.I.proc_is_main then CF.elim_exists_struc_preserve_pre_evars [] final_static_specs_list else *) final_static_specs_list;
          C.proc_dynamic_specs = final_dynamic_specs_list;
          (* C.proc_static_specs_with_pre =  []; *)
          C.proc_stk_of_static_specs = new Gen.stack (* _noexc Cprinter.string_of_struc_formula (=) *);
          C.proc_hprel_ass = [];
          C.proc_hprel_unkmap = [];
          C.proc_sel_hps = [];
          C.proc_sel_post_hps = [];
          C.proc_hpdefs = [];
          C.proc_callee_hpdefs = [];
          C.proc_by_name_params = by_names;
          C.proc_by_copy_params = by_copies; (* copy entire structure *)
          C.proc_by_value_params = by_values; 
          C.proc_body = body;
          C.proc_logical_vars = [];
          C.proc_call_order = 0;
          C.proc_is_main = proc.I.proc_is_main;
          C.proc_is_invoked = proc.I.proc_is_invoked;
          C.proc_verified_domains = proc.I.proc_verified_domains;
          C.proc_is_recursive = false;
          C.proc_file = proc.I.proc_file;
          C.proc_loc = proc.I.proc_loc;
          (* C.proc_while_with_return = None; *)
          C.proc_test_comps = trans_test_comps prog proc.I.proc_test_comps} in
      (E.pop_scope (); cproc)))
  in
  wrap_proving_kind (PK_Trans_Proc (*^proc.I.proc_name*)) trans_proc_x_op ()

and ident_to_spec_var id n_tl p prog =
  let v = get_spec_var_ident n_tl id p (* Unprimed  *)in
  match v with
  | CP.SpecVar(t,id,pr) ->
    if t == UNK then
      try
        let todo_unk = I.look_up_rel_def_raw prog.I.prog_rel_decls id in
        CP.SpecVar(RelT[],id,pr)
      with _ ->
        try
          let todo_unk = I.look_up_func_def_raw prog.I.prog_func_decls id in
          CP.SpecVar(RelT[],id,pr)
        with _ ->
          try
            let todo_unk = I.look_up_hp_def_raw prog.I.prog_hp_decls id in
            CP.SpecVar(HpT,id,pr)
          with _ -> 
            try
              let tdef = I.look_up_templ_def_raw prog.I.prog_templ_decls id in
              let ftyp = mkFuncT (List.map (fun (t, _) -> t) tdef.I.templ_typed_params) tdef.I.templ_ret_typ in
              CP.SpecVar (ftyp, id, pr)
            with _ -> 
              try
                let todo_unk = I.look_up_ut_def_raw prog.I.prog_ut_decls id in
                CP.SpecVar(UtT, id, pr)
              with _ -> v
    else v

and ident_list_to_spec_var_list ivs n_tl prog =
  let new_ivs = List.map (fun (i,p) -> ident_to_spec_var i n_tl p prog ) ivs in
  new_ivs

(* transform coercion lemma from iast to cast *)
and trans_coercions (prog : I.prog_decl) :
      ((C.coercion_decl list) * (C.coercion_decl list)) =
  let tmp =
    List.map (fun coer -> trans_one_coercion prog coer)
        (List.fold_left (fun a coerc_lst -> a@(coerc_lst.I.coercion_list_elems)) [] (prog.I.prog_coercion_decls)) in
  let (tmp1, tmp2) = List.split tmp in
  let tmp3 = List.concat tmp1 in let tmp4 = List.concat tmp2 in (tmp3, tmp4)

(* and unfold_self prog body =  *)
(*   let pri_f = Iprinter.string_of_formula in *)
(*   Debug.info_hprint (add_str "orig body" pri_f) body no_pos; *)
(*   body *)

and trans_one_coercion (prog : I.prog_decl) (coer : I.coercion_decl) :
      ((C.coercion_decl list) * (C.coercion_decl list)) =
  let pr x =  Iprinter.string_of_coerc_decl x in
  let pr2 (r1,r2) = pr_list Cprinter.string_of_coercion (r1@r2) in
  Debug.no_1 "trans_one_coercion" pr pr2 (fun _ -> trans_one_coercion_a prog coer) coer

(* let pr x = "?" in *)
(* let pr2 (r1,r2) = pr_list Cprinter.string_of_coercion (r1@r2) in *)
(* Debug.no_1 "trans_one_coercion" pr pr2 (fun _ -> trans_one_coercion_x prog coer) coer *)

and trans_one_coercion_a (prog : I.prog_decl) (coer : I.coercion_decl) :
      ((C.coercion_decl list) * (C.coercion_decl list)) =
  if !Globals.allow_lemma_switch && coer.I.coercion_infer_vars ==[] then
    (* complex_lhs <- rhs    ==> rhs    -> complex_lhs                    *)
    (* complex_lhs <-> rhs   ==> complex_lhs -> rhs && rhs -> complex_lhs *)
    let  coercion_lhs_type = (IF.type_of_formula coer.I.coercion_head) in
    (* let  coercion_rhs_type = (IF.type_of_formula coer.I.coercion_body) in *)
    if coercion_lhs_type == Complex then 
      if coer.I.coercion_type == I.Right then
        let () = Debug.info_pprint "WARNING : changing lemma from <- to -> " no_pos in
        let new_coer = {coer with I.coercion_head = coer.I.coercion_body;
            I.coercion_body = coer.I.coercion_head;
            I.coercion_type_orig = Some coer.I.coercion_type; (* store origin coercion type *)
            I.coercion_type = I.Left} in
        trans_one_coercion_x prog new_coer
      else if (coer.I.coercion_type == I.Equiv) then 
        let () = Debug.info_pprint "WARNING : split equiv lemma into two -> lemmas " no_pos in
        let new_coer1 = {coer with I.coercion_head = coer.I.coercion_head;
            I.coercion_body = coer.I.coercion_body;
            I.coercion_type_orig = Some I.Left; (* store origin coercion type *)
            I.coercion_type = I.Left} in
        let new_coer2 = {coer with I.coercion_head = coer.I.coercion_body;
            I.coercion_body = coer.I.coercion_head;
            I.coercion_type_orig = Some I.Right; (* store origin coercion type *)
            I.coercion_type = I.Left} in
        let (cdl11, cdl12) = trans_one_coercion_x prog new_coer1 in
        let (cdl21, cdl22) = trans_one_coercion_x prog new_coer2 in
        (cdl11@cdl21, cdl12@cdl22)
      else trans_one_coercion_x prog coer
    else trans_one_coercion_x prog coer
  else trans_one_coercion_x prog coer

(* TODO : add lemma name to self node to avoid cycle*)
and trans_one_coercion_x (prog : I.prog_decl) (coer : I.coercion_decl) :
      ((C.coercion_decl list) * (C.coercion_decl list)) =
  (***********INTERNAL************)
  let trans_head new_head fnames quant n_tl=
    let h = List.map (fun c-> (c,Unprimed)) fnames in
    let p = List.map (fun c-> (c,Primed)) fnames in
    let wf,_ = case_normalize_struc_formula 2 prog h p (IF.formula_to_struc_formula new_head) false 
      false (*allow_post_vars*) true [] in
    let (n_tl,cs_head_norm) = trans_I2C_struc_formula 5 prog false quant (* fv_names  *) fnames  wf n_tl false 
      true (*check_pre*) in
    let c_head_norm = CF.struc_to_formula cs_head_norm in
    (n_tl,c_head_norm)
  in
  (*******************************)
  let i_lhs = coer.I.coercion_head in
  let lhs_vars = IF.all_fv i_lhs in
  let () = x_tinfo_hp (add_str "lhs_vars" (pr_list string_of_primed_ident)) lhs_vars no_pos in
  let i_rhs = coer.I.coercion_body in
  let i_rhs = 
    if !Globals.allow_lemma_norm then case_normalize_formula prog lhs_vars i_rhs 
    else i_rhs 
  in
  let  coercion_lhs_type = (IF.type_of_formula i_lhs) in
  let  coercion_rhs_type = (IF.type_of_formula i_rhs) in
  let coer_type = coer.I.coercion_type in
  let () = x_tinfo_hp (add_str "coer_type" Cprinter.string_of_coercion_type) coer_type no_pos in
  let () = x_tinfo_hp (add_str "i_lhs" Iprinter.string_of_formula) i_lhs no_pos in
  let () = x_tinfo_hp (add_str "i_rhs" Iprinter.string_of_formula) i_rhs no_pos in
  let n_tl = gather_type_info_formula prog i_lhs (* coer.I.coercion_head *) [] false in
  let n_tl = gather_type_info_formula prog i_rhs (* coer.I.coercion_body *) n_tl false in
  let (n_tl,c_lhs) = trans_formula prog false [ self ] false i_lhs (* coer.I.coercion_head *) n_tl false in
  let () = x_tinfo_hp (add_str "c_lhs 1 " Cprinter.string_of_formula) c_lhs no_pos in
  (*translate TrueFlow to NormalFlow*)
  (* let c_lhs = CF.substitute_flow_in_f !norm_flow_int !top_flow_int  c_lhs in *)
  let c_lhs =
    if (coer.I.coercion_kind = LEM_PROP) then
      c_lhs (* LEM_PROP lemmas do not have self *)
    else
      CF.add_origs_to_node self c_lhs [coer.I.coercion_name]
  in
  let () = x_tinfo_hp (add_str "c_lhs 2 " Cprinter.string_of_formula) c_lhs no_pos in
  let c_lhs = if (!Globals.allow_field_ann) then add_param_ann_constraints_formula c_lhs else c_lhs in
  let () = x_tinfo_hp (add_str "c_lhs 3 " Cprinter.string_of_formula) c_lhs no_pos in
  let lhs_fnames0 = List.map CP.name_of_spec_var (CF.fv c_lhs) in (* free vars in the LHS *)
  let compute_univ () =
    let h, p, vp, _, _,_ = CF.split_components c_lhs in
    let pvars =mfv p in
    let pvars = List.filter (fun (CP.SpecVar (_,id,_)) -> not (id= Globals.cyclic_name || id = Globals.acyclic_name || id = Globals.concrete_name || id = Globals.set_comp_name)) pvars in (*ignore cyclic & acyclic rels *)
    let hvars = CF.h_fv h in
    let univ_vars = Gen.BList.difference_eq CP.eq_spec_var pvars hvars in 
    Gen.BList.remove_dups_eq CP.eq_spec_var univ_vars in
  let univ_vars = compute_univ () in
  let () = x_tinfo_hp (add_str "univ_vars" Cprinter.string_of_spec_var_list) univ_vars no_pos in
  let lhs_fnames = Gen.BList.difference_eq (=) lhs_fnames0 (List.map CP.name_of_spec_var univ_vars) in
  let (n_tl,c_rhs) = trans_formula prog (Gen.is_empty univ_vars) ((* self :: *) lhs_fnames) false i_rhs (* coer.I.coercion_body *) n_tl false in
  (*translate TrueFlow to NormalFlow*)
  (* let c_rhs = CF.substitute_flow_in_f !norm_flow_int !top_flow_int c_rhs in *)
  (*LDK: TODO: check for interraction with lemma proving*)
  (*pass lhs_heap into add_origs *)
  let lhs_heap ,_,_,_, _,_  = CF.split_components c_lhs in
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
              | CF.StarMinus {CF.h_formula_starminus_h1 = h1;
                CF.h_formula_starminus_h2 = h2;
                CF.h_formula_starminus_pos = pos} -> (match h1 with
                  | CF.ViewNode vn -> vn.CF.h_formula_view_name
                  | CF.DataNode dn -> dn.CF.h_formula_data_name
                  | _ -> let ()= let b = 
                                   match coer.I.coercion_kind with
                                     | RLEM -> true | _ -> false in 
                    if b
                    then () 
                    else print_string ("[astimp] Warning: head node of ramification is neither a view node nor a data node "^(Cprinter.string_of_h_formula head)^" \n") in "")
              | _ -> 
                    let () = print_string "[astsimp] Warning: lhs head node of a coercion is neither a view node nor a data node\n" in 
                    ""
          else
            let () = print_string "[astsimp] Warning: lhs of a coercion is neither simple or complex\n" in 
            ""
  in
  (*LDK: In the body of a coercions, there may be multiple nodes with
    a same name with self => only add [coercion_name] to origins of the
    first node*)
  let c_rhs = if (coer.I.coercion_kind = LEM_PROP) then c_rhs else
    match (coercion_lhs_type) with
      | Simple ->
            if (Perm.allow_perm ()) then
              let rec helper f = 
                match f with
                  | CF.Base _
                  | CF.Exists _ ->
                        let h, p, vp, _, _,_ = CF.split_components f in
                        let heaps = CF.split_star_conjunctions h in
                        let heaps = List.filter (fun h ->
                            match h with
                              | CF.HEmp
                              | CF.HTrue -> false
                              | _ -> true) heaps
                        in
                        (List.length heaps)
                  | CF.Or {CF.formula_or_f1=f1; CF.formula_or_f2=f2;} ->
                        let len1 = helper f1 in
                        let len2 = helper f2 in
                        (if len1>len2 then len1 else len2)
              in
              let len = helper c_rhs in
              if (len>1) then
                (*only do this if having more than 1 heap*)
                CF.add_origs_to_first_node self lhs_view_name c_rhs [coer.I.coercion_name] true (*set original of the rest of nodes = true to allow permission splitting*)
              else c_rhs
            else
              CF.add_origs_to_first_node self lhs_view_name c_rhs [coer.I.coercion_name] false
      | Complex -> c_rhs
  in
  (* c_body_norm is used only for proving l2r part of a lemma (left & equiv lemmas) *)
  let h = List.map (fun c-> (c,Unprimed)) lhs_fnames0 in
  let p = List.map (fun c-> (c,Primed)) lhs_fnames0 in
  (* let unfold_body = unfold_self prog coer.I.coercion_body in *)
  let wf,_ = case_normalize_struc_formula 1 prog h p (IF.formula_to_struc_formula i_rhs (* coer.I.coercion_body *)) false 
    false (*allow_post_vars*) true [] in
  let quant = true in
  let (n_tl,cs_body_norm) = trans_I2C_struc_formula 4 prog false quant (* fv_names *) lhs_fnames0 wf n_tl false 
    true (*check_pre*) in
  let cs_body_norm =
    if (coer.I.coercion_kind = LEM_PROP) then
      cs_body_norm
    else
      CF.struc_add_origs_to_first_node self lhs_view_name cs_body_norm [coer.I.coercion_name] false
  in
  let cs_body_norm = CF.add_struc_original false cs_body_norm in
  (* let cs_body_norm = CF.reset_struc_origins cs_body_norm in *)
  (* c_head_norm is used only for proving r2l part of a lemma (right & equiv lemmas) *)
  let (qvars, form) = IF.split_quantifiers i_lhs (* coer.I.coercion_head *) in 
  let c_hd0, c_guard0, vp0, c_fl0, c_a0 = IF.split_components form in
  (* remove the guard from the normalized head as it will be later added to the body of the right lemma *)
  let head_pure = if coer_type = I.Left || coer_type = I.Equiv then c_guard0 else (IP.mkTrue no_pos) in
  let new_head =  IF.mkExists qvars c_hd0 (* (IP.mkTrue no_pos) *) head_pure vp0 c_fl0 [] no_pos in
  let guard_fnames = List.map (fun (id, _) -> id ) (IP.fv c_guard0) in
  let rhs_fnames = List.map CP.name_of_spec_var (CF.fv c_rhs) in
  let fnames = Gen.BList.remove_dups_eq (=) (guard_fnames@rhs_fnames) in
  let quant = true in
  (*moved to internal trans_head*)
  (* let h = List.map (fun c-> (c,Unprimed)) fnames in *)
  (* let p = List.map (fun c-> (c,Primed)) fnames in *)
  (* let wf,_ = case_normalize_struc_formula 2 prog h p (IF.formula_to_struc_formula new_head) false  *)
  (*   false (\*allow_post_vars*\) true [] in *)
  (* let (n_tl,cs_head_norm) = trans_I2C_struc_formula 5 prog false quant (\* fv_names  *\) fnames  wf n_tl false  *)
  (*   true (\*check_pre*\) in *)
  (* let c_head_norm = CF.struc_to_formula cs_head_norm in *)
  (**********moved END*************)
  let (n_tl,c_head_norm) = trans_head new_head fnames quant n_tl in
  let c_head_norm =  CF.add_original c_head_norm false in
  let c_head_norm_rlem = if coer_type = I.Equiv then
    let new_head =  IF.mkExists qvars c_hd0 (IP.mkTrue no_pos) IVP.empty_vperm_sets c_fl0 [] no_pos in
    snd (trans_head new_head (Gen.BList.remove_dups_eq (=)  rhs_fnames) quant n_tl)
  else c_head_norm in
  (* free vars in RHS but not LHS *)
  let hrels = List.map (fun (a,_) -> a) (CF.get_HRels_f c_rhs ) in
  let ex_vars = Gen.BList.remove_dups_eq CP.eq_spec_var 
    (List.filter (fun v -> not(List.mem (CP.name_of_spec_var v) lhs_fnames0) ) (Gen.BList.difference_eq CP.eq_spec_var (CF.fv c_rhs) hrels)) in 
  (* wrap exists for RHS - no implicit instantiation*)
  let c_rhs = CF.push_exists ex_vars c_rhs in
  let lhs_name = find_view_name c_lhs self (IF.pos_of_formula i_lhs (* coer.I.coercion_head *)) in
  let sv = CP.SpecVar (UNK,self,Unprimed) in
  let xx = find_trans_view_name c_rhs sv no_pos in
  (* let rhs_name = *)
  (*   if (List.exists (fun s -> String.compare s lhs_name = 0) xx) then lhs_name *)
  (*   else  *)
  (*     try (List.hd xx) *)
  (*       (\* find_view_name c_rhs self (IF.pos_of_formula coer.I.coercion_body) *\) *)
  (*     with | _ -> "" in *)
  let rhs_name = find_view_name c_rhs self  (IF.pos_of_formula i_rhs) in (* andreeac: temporarily replace above body name with this simpler version *)
  if lhs_name = "" && (coer.I.coercion_kind != LEM_PROP) then raise (Failure "root pointer of node on LHS must be self")
  else
    (  
        let args = CF.fv_simple_formula c_lhs in 
        let m_vars = find_materialized_prop args [] c_rhs in
        let c_coer ={ C.coercion_type = coer_type;
        C.coercion_type_orig = None;
	C.coercion_exact= coer.I.coercion_exact;
        C.coercion_name = coer.I.coercion_name ;
        C.coercion_head = c_lhs;
        C.coercion_head_norm = c_head_norm;
        C.coercion_body = c_rhs;
        C.coercion_body_norm = cs_body_norm;
        C.coercion_impl_vars = []; (* ex_vars; *)
        C.coercion_univ_vars = univ_vars;
        C.coercion_infer_vars = ident_list_to_spec_var_list (List.map (fun id -> (id, Unprimed)) coer.I.coercion_infer_vars ) n_tl prog; 
        C.coercion_head_view = lhs_name;
        C.coercion_fold_def = new Gen.mut_option;
        (* C.vdef_lemma_fold prog c_lhs cs_body_norm; *)
        C.coercion_body_view = rhs_name;
        C.coercion_mater_vars = m_vars;
        C.coercion_case = (Cast.case_of_coercion c_lhs c_rhs);
        C.coercion_kind = coer.I.coercion_kind;
        C.coercion_origin = coer.I.coercion_origin;
        } in
        let change_univ c = match c.C.coercion_univ_vars with
            (* move LHS guard to RHS regardless of universal lemma *)
          | v ->
                let c_hd, c_guard,c_vp, c_fl, c_t, c_a = CF.split_components c.C.coercion_head in
                let new_body = CF.normalize 1 c.C.coercion_body (CF.formula_of_mix_formula c_guard no_pos) no_pos in
                let () = Debug.ninfo_hprint (add_str "new_body_norm" Cprinter.string_of_formula) new_body no_pos in
                let new_body = CF.push_exists c.C.coercion_univ_vars new_body in
                let () = Debug.ninfo_hprint (add_str "new_body_norm (after push exists)" Cprinter.string_of_formula) new_body no_pos in
                (* let new_body_norm =  c.C.coercion_body_norm in *)
                (* let new_body_norm = CF.struc_formula_of_formula new_body no_pos in *)
                let new_body_norm = CF.normalize_struc c.C.coercion_body_norm (CF.mkBase_rec (CF.formula_of_mix_formula c_guard no_pos) None no_pos) in
                let new_body_norm = CF.push_struc_exists c.C.coercion_univ_vars new_body_norm in
                (*                 let new_body_norm = CF.push_exists c.C.coercion_univ_vars new_body_norm in *)
                let () = Debug.ninfo_hprint (add_str "new_body_norm" Cprinter.string_of_struc_formula) new_body_norm no_pos in
                let () = Debug.ninfo_hprint (add_str "old_body_norm" Cprinter.string_of_struc_formula) c.C.coercion_body_norm no_pos in
                (* let new_body_norm = CF.normalize_struc c.C.coercion_body_norm *)
                (*   (CF.mkBase_rec (CF.formula_of_mix_formula c_guard no_pos) None no_pos) in *)
                (* let new_body_norm = CF.push_struc_exists c.C.coercion_univ_vars new_body_norm in *)
                {c with
                    C.coercion_type = Iast.Right;
                    C.coercion_head = CF.mkBase c_hd (mkMTrue no_pos) c_vp c_t c_fl c_a no_pos;
                    (* C.coercion_head_norm = new_head_norm; *)
                    C.coercion_body = new_body;
                    C.coercion_head_norm = c_head_norm_rlem; (*w/o guard*)
                    C.coercion_body_norm = new_body_norm;
                    C.coercion_univ_vars = [];} in
        match coer_type with
          | I.Left -> 
                let c_coer = {c_coer with 
                    C.coercion_head = CF.set_lhs_case c_coer.C.coercion_head true;
                    C.coercion_body = CF.set_lhs_case c_coer.C.coercion_body false}
                in
                ([ c_coer ], [])
          | I.Equiv ->
                let c_coer = {c_coer with
                    C.coercion_name = c_coer.C.coercion_name ^ "_left";
                    C.coercion_head = CF.set_lhs_case c_coer.C.coercion_head true;
                    C.coercion_body = CF.set_lhs_case c_coer.C.coercion_body false}
                in
                let c_coer1 = {c_coer with
                    C.coercion_name = c_coer.C.coercion_name ^ "_right";
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
              | CF.StarMinus
                      {
                          CF.h_formula_starminus_h1 = h1;
                          CF.h_formula_starminus_h2 = h2;
                          CF.h_formula_starminus_pos = _
                      }                       
              | CF.Conj
                      {
                          CF.h_formula_conj_h1 = h1;
                          CF.h_formula_conj_h2 = h2;
                          CF.h_formula_conj_pos = _
                      } 
              | CF.ConjStar
                      {
                          CF.h_formula_conjstar_h1 = h1;
                          CF.h_formula_conjstar_h2 = h2;
                          CF.h_formula_conjstar_pos = _
                      } 
              | CF.ConjConj
                      {
                          CF.h_formula_conjconj_h1 = h1;
                          CF.h_formula_conjconj_h2 = h2;
                          CF.h_formula_conjconj_pos = _
                      }                                           
              | CF.Phase {CF.h_formula_phase_rd = h1;
                CF.h_formula_phase_rw = h2;
                CF.h_formula_phase_pos = _} ->
                    let name1 = find_view_heap h1 in
                    let name2 = find_view_heap h2 in
                    if name1 = "" then name2
                    else if name2 = "" then name1
                    else if (name1=name2) then name1
                    else (
                        Debug.ninfo_hprint (add_str "phase h0" !CF.print_h_formula) h0 pos;
                        name1 (*TOCHECK: temporarily return name1*)
                            (* raise (Failure ("phase: " ^ v ^ " must point to only one view 11")) *)
                    )
              | CF.ThreadNode
                      {
                          CF.h_formula_thread_node = p;
                          CF.h_formula_thread_name = c;
                          CF.h_formula_thread_perm = _; (*LDK*)
                          CF.h_formula_thread_pos = _
                      } ->
                    if (CP.name_of_spec_var p) = v
                    then c
                      (*Err.report_error
                        {
                        Err.error_loc = pos;
                        Err.error_text = v ^ " must point to a view";
                        }*)
                    else ""
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
              | CF.HTrue | CF.HFalse | CF.HEmp | CF.HVar _ | CF.HRel _ | CF.Hole _ | CF.FrmHole _ -> "")
          in find_view_heap h
    | CF.Or _ ->
          Err.report_error
              {
                  Err.error_loc = pos;
                  Err.error_text =
                      "Pre- and post-conditions of coercion rules must not be disjunctive";
              }

and trans_exp (prog : I.prog_decl) (proc : I.proc_decl) (ie : I.exp) : trans_exp_type =
  Debug.no_1 "trans_exp"
      Iprinter.string_of_exp
      (pr_pair Cprinter.string_of_exp string_of_typ) 
      (fun _ -> trans_exp_x prog proc ie) ie 

and trans_exp_x (prog : I.prog_decl) (proc : I.proc_decl) (ie : I.exp) : trans_exp_type =
  (* let () = print_endline ("[trans_exp] input = { " ^ (Iprinter.string_of_exp ie) ^ " }") in *)
  let rec helper ie =
    match ie with
      | I.Label (pid, e)-> 
            let e1,t1 = (helper e) in
            (C.Label {C.exp_label_type = t1; C.exp_label_path_id = pid; C.exp_label_exp = e1;},t1)
      | I.Unfold { I.exp_unfold_var = (v, p); I.exp_unfold_pos = pos } ->
            ((C.Unfold {
                C.exp_unfold_var = CP.SpecVar (Globals.null_type, v, p);
                C.exp_unfold_pos = pos;
            }), C.void_type)
                (* An Hoa MARKED *)
      | I.ArrayAt { I.exp_arrayat_array_base = a; 
        I.exp_arrayat_index = index;
        I.exp_arrayat_pos = pos } ->
            let r = List.length index in
            let new_e = I.CallNRecv {
                I.exp_call_nrecv_method = array_access_call ^ (string_of_int r) ^ "d"; (* Update call *)                    (* TODO CHECK IF THE ORDER IS CORRECT! IT MIGHT BE IN REVERSE ORDER *)
                I.exp_call_nrecv_lock = None;
                I.exp_call_nrecv_arguments = a :: index;
                I.exp_call_nrecv_ho_arg = None;
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
      | I.Assert { 
          I.exp_assert_asserted_formula = assert_f_o;
          I.exp_assert_assumed_formula = assume_f_o;
          I.exp_assert_path_id = pi;
          I.exp_assert_type = atype;
          I.exp_assert_pos = pos } ->
            let tmp_names = E.visible_names () in
            let all_names = List.map (fun (t, n) -> ((trans_type prog t pos), n)) tmp_names in
            let free_vars = List.map snd all_names in
            let n_tl = List.map (fun (t, n) -> (n,{ sv_info_kind = t;id = fresh_int () })) all_names in
            let (n_tl,assert_cf_o) = match assert_f_o with
              | Some f -> 
                    let (n_tl,cf) = trans_I2C_struc_formula 6 prog false false free_vars (fst f) n_tl false true in  
                    (n_tl,Some cf)
              | None -> (n_tl,None) in
            let (n_tl,assume_cf_o) = match assume_f_o with
              | None -> (n_tl,None)
              | Some f ->
                    let (n_tl,cf) = trans_formula prog false free_vars true f n_tl false in  
                    (n_tl,Some cf) in
            let assert_e = C.Assert { C.exp_assert_asserted_formula = assert_cf_o;
            C.exp_assert_assumed_formula = assume_cf_o;
            C.exp_assert_path_id = pi;
            C.exp_assert_type = atype;
            C.exp_assert_pos = pos; } in 
            (assert_e, C.void_type)
      | I.Assign  {
            I.exp_assign_op = aop;
            I.exp_assign_lhs = lhs;
            I.exp_assign_rhs = rhs;
            I.exp_assign_path_id = pid;
            I.exp_assign_pos = pos_a  } ->
            (* An Hoa : WORKING *)
            (* let () = print_endline ("[trans_exp] assignment input = { " ^ Iprinter.string_of_exp lhs ^ " , " ^ Iprinter.string_of_exp rhs ^ " }") in *)
            (* An Hoa : pre-process the inline field access *)
            let is_member_exp e = match e with | I.Member _ -> true | _ -> false in
            (* [Internal] function to expand an expression with a list of field access *)
            let rec produce_member_exps base fseqs = match base with
              | I.Member{   I.exp_member_base = base_e;
                I.exp_member_fields = fs;
                I.exp_member_path_id = pid;
                I.exp_member_pos = pos } ->
                    List.map (fun x -> I.Member {   I.exp_member_base = base_e;
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
              (* let () = print_endline ("[trans_exp] expand the inline field of lhs and rhs { " ^ String.concat " , " expand_field_list ^ " }") in *)
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
                              (* let () = print_string ("trans_exp :: lhs = " ^ Cprinter.string_of_exp ce1 ^ "\n") in *)
                              let (ce2, te2) = trans_exp prog proc rhs in
                              (* let () = print_string ("trans_exp :: rhs = " ^ Cprinter.string_of_exp ce2 ^ "\n") in *)
                              (* let () = print_string ("trans_exp :: te2 = " ^  Typeinfer.string_of_spec_var_kind te2 ^ "\n") in *)
                              (* let () = print_string ("trans_exp :: te1 = " ^  Typeinfer.string_of_spec_var_kind te1 ^ "\n") in *)
                              if not (sub_type te2 te1) then  Err.report_error {
                                  Err.error_loc = pos;
                                  Err.error_text = "OpAssign : lhs and rhs do not match 2";  }
                              else
                                (let v = C.get_var ce1 in
                                let assign_e = C.Assign{
                                    C.exp_assign_lhs = v;
                                    C.exp_assign_rhs = ce2;
                                    C.exp_assign_pos = pos;} in
                                if C.is_var ce1 then
                                  (* let vsv = CP.SpecVar (te1, v, Primed) in
                                     let () = proc.I.proc_important_vars <- proc.I.proc_important_vars @ [vsv] in*)
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
                                  I.exp_call_nrecv_ho_arg = None;
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
                                  (* flatten_to_bind prog proc base_e (List.rev fs) (Some fn_var) pid (CF.TempAnn(CP.ConstAnn(Mutable))) false pos (*(andreeac)to check, insertion.ss -p insert fails with CF.TempAnn(....)*)*) 
                                  flatten_to_bind prog proc base_e (List.rev fs) (Some fn_var) pid (CP.ConstAnn(Mutable)) false pos

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
                  I.exp_call_nrecv_ho_arg = None;
                  I.exp_call_nrecv_path_id = pid (*stub_branch_point_id ("primitive "^b_call)*);
                  I.exp_call_nrecv_pos = pos;}in 
              helper new_e)
            else if not (I.is_num e1) && not (I.is_num e2) && (I.is_mult_op b_op) then
              let new_e = I.CallNRecv {
                  (* mults for linearizing non-linear mult *)
                  (* sv-comp/termination-numeric/LogRecursive_true-termination *)
                  I.exp_call_nrecv_method = "mults___"; 
                  I.exp_call_nrecv_lock = None;
                  I.exp_call_nrecv_arguments = [ e1; e2 ];
                  I.exp_call_nrecv_ho_arg = None;
                  I.exp_call_nrecv_path_id = pid;
                  I.exp_call_nrecv_pos = pos; } in 
              helper new_e
            else if not (I.is_num e2) && (I.is_div_op b_op) then
              let new_e = I.CallNRecv {
                  (* mults for linearizing non-linear div *)
                  (* sv-comp/termination-numeric/ex1_true-termination              *)
                  (* sv-comp/termination-memory-alloca/ex1-alloca_true-termination *)
                  (* sv-comp/termination-numeric/ex2_true-termination              *)
                  (* sv-comp/termination-memory-alloca/ex2-alloca_true-termination *)
                  (* sv-comp/termination-numeric/ex3a_true-termination             *)
                  (* sv-comp/termination-numeric/ex3b_true-termination             *)
                  I.exp_call_nrecv_method = "divs___"; 
                  I.exp_call_nrecv_lock = None;
                  I.exp_call_nrecv_arguments = [ e1; e2 ];
                  I.exp_call_nrecv_ho_arg = None;
                  I.exp_call_nrecv_path_id = pid;
                  I.exp_call_nrecv_pos = pos; } in 
              helper new_e
            else
              (let b_call = if !Globals.check_integer_overflow then (let func exp = match exp with
                | I.Var v -> Some([v.I.exp_var_name])
                | _ -> Some([]) in
              let e1_vars = I.fold_exp e1 func List.flatten [] in
              (*let () = print_string ("\ne1_vars: "^(String.concat " " e1_vars)) in*)
              let e2_vars = I.fold_exp e2 func List.flatten [] in
              (*let () = print_string ("\ne2_vars: "^(String.concat " " e2_vars)) in*)
              let local_vars = List.map (fun (t,id) -> id) (E.names_on_top ()) in
              (*let () = print_string ("\nlocal_vars: "^(String.concat " " local_vars)) in*)
              let flag1 = List.for_all (fun c -> List.mem c local_vars) e1_vars in
              let flag2 = List.for_all (fun c -> List.mem c local_vars) e2_vars in
              if flag1 && flag2 then get_binop_call b_op
              else get_binop_call_safe_int b_op
              )
              else get_binop_call b_op in
              let new_e = I.CallNRecv {
                  I.exp_call_nrecv_method = b_call;
                  I.exp_call_nrecv_lock = None;
                  I.exp_call_nrecv_arguments = [ e1; e2 ];
                  I.exp_call_nrecv_ho_arg = None;
                  I.exp_call_nrecv_path_id = pid (*stub_branch_point_id ("primitive "^b_call)*);
                  I.exp_call_nrecv_pos = pos; } in 
              helper new_e)
      | I.Bind {
            I.exp_bind_bound_var = v;
            I.exp_bind_fields = vs;
            I.exp_bind_body = e;
            I.exp_bind_pos = pos;
            I.exp_bind_path_id = pid;} ->
            let ipid = pid in
            let pid = match pid with | None -> fresh_strict_branch_point_id "" | Some s -> s in
            (try
              let vinfo_tmp = E.look_up v in
              match vinfo_tmp with
                | E.VarInfo vi ->
                      (match vi.E.var_type with
                        | Named c -> 
                              let ddef = I.look_up_data_def 5 pos prog.I.prog_data_decls c in
                              if ( != ) (List.length vs) (List.length ddef.I.data_fields) then
                                Err.report_error { Err.error_loc = pos; Err.error_text = "bind " ^ (v ^ ": different number of variables");}
                              else
                                (E.push_scope ();
                                (let todo_unk = List.map2 
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
                                let () = E.pop_scope ()in
                                let initial_ann_lst =  (List.map (fun f -> (f, (CP.ConstAnn(Accs)))) vs) in
                                let ann_lst = Immutable.read_write_exp_analysis ce initial_ann_lst in 
                                let _,ann_lst = List.split ann_lst in
                                let bind_e =  create_bind_exp te (vt, v) (List.combine vs_types vs) ce false pos pid in
                                (* let bind_e = (C.Bind { *)
                                (*     C.exp_bind_type = te; *)
                                (*     C.exp_bind_bound_var = (vt, v); *)
                                (*     C.exp_bind_fields = List.combine vs_types vs; *)
                                (*     C.exp_bind_body = ce; *)
                                (*     C.exp_bind_imm = CP.ConstAnn(Mutable); (\* can it be true? *\) (\*WN : conservatively @M *\) *)
                                (*     C.exp_bind_param_imm = List.map (fun _ -> CP.ConstAnn(Mutable)) vs ; *)
                                (*     C.exp_bind_read_only = false; (\*conservative. May use read/write analysis to figure out*\) *)
				(*     C.exp_bind_pos = pos; *)
                                (*     C.exp_bind_path_id = pid; }) in *)
                                (bind_e, te)))
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
            let _ = Debug.ninfo_hprint (add_str "args" (pr_list !Iast.print_exp)) (args) no_pos in
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
              let cdef = I.look_up_data_def 4 pos prog.I.prog_data_decls class_name in
              let all_methods = I.look_up_all_methods prog cdef in
              let pdef = I.look_up_proc_def_mingled_name all_methods mingled_mn in
              if ( != ) (List.length args) (List.length pdef.I.proc_args) then
                Err.report_error{ Err.error_loc = pos; Err.error_text = "number of arguments does not match"; }
              else
                let _ = Debug.ninfo_hprint (add_str "CallRecv:pdef.I.proc_args" (!Iast.print_param_list)) (pdef.I.proc_args) no_pos in
                let _ = Debug.ninfo_hprint (add_str "CallRecv:cts" (pr_list  Typeinfer.string_of_spec_var_kind)) cts no_pos in
                (let parg_types = List.map (fun p -> trans_type prog p.I.param_type p.I.param_loc) pdef.I.proc_args in
                if List.exists2 (fun t1 t2 -> not (sub_type t1 t2)) cts parg_types then
                  Err.report_error{ Err.error_loc = pos;Err.error_text = "argument types do not match 1";}
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
            I.exp_call_nrecv_ho_arg = ho_arg;
            I.exp_call_nrecv_path_id = pi;
            I.exp_call_nrecv_pos = pos } ->
            (* let () = print_string "trans_exp :: case CallNRecv\n" in*)
            let tmp = List.map (helper) args in
            let (cargs, cts) = List.split tmp in
            let proc_decl = I.look_up_proc_def_raw prog.I.prog_proc_decls mn in
            (*TO CHECK: not sure what is it for? but it may not be
              applicable to concurrency as these invocations (except join())
              are generic to the number of arguments *)
            let cts = if (mn=Globals.fork_name || mn=Globals.acquire_name || mn=Globals.release_name || mn=Globals.finalize_name || mn=Globals.init_name) then cts
            else if (mn=Globals.join_name) then
              (if (!Globals.allow_threads_as_resource) then [Globals.thrd_typ] else [Globals.thread_typ])
                else (
                    let _ = Debug.ninfo_hprint (add_str "length proc_decl.I.proc_args" (string_of_int)) (List.length proc_decl.I.proc_args) no_pos in
                    let _ = Debug.ninfo_hprint (add_str "proc_decl.I.proc_args" (!Iast.print_param_list)) (proc_decl.I.proc_args) no_pos in
                    if ((List.length args) != (List.length proc_decl.I.proc_args)) then
                      report_error pos ("trans_exp :: case CallNRecv :: procedure call " ^ mn ^ " has invalid number of arguments")
                    else
                      List.map2 (fun p1 t2 ->
                          let t1 = p1.I.param_type in
                          match t1, t2 with
                            | Globals.Named _, Globals.Named "" -> t1  (* null case *)
                            | _ -> t2
                      ) proc_decl.I.proc_args cts
                )
            in
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
                        Err.report_error { Err.error_loc = pos; Err.error_text = "argument types do not match 2"; }
                      else if Inliner.is_inlined mn then (let inlined_exp = Inliner.inline prog pdef ie in helper inlined_exp)
                      else 
                        (let ret_ct  = if (!Globals.allow_threads_as_resource) then Globals.thrd_typ else Globals.thread_typ in (*return a thread _type*) 
                        let positions = List.map I.get_exp_pos method_args in
                        let (local_vars, init_seq, arg_vars) = trans_args (Gen.combine3 cargs cts positions) in
                        let call_e = C.SCall {
                            C.exp_scall_type = ret_ct;
                            C.exp_scall_method_name = mingled_mn;
                            C.exp_scall_lock = lock;
                            C.exp_scall_arguments = mingled_forked_mn::arg_vars;
                            C.exp_scall_ho_arg = None;
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
                    let () = match lock with
                      | None -> ()
                            (* Err.report_error { Err.error_loc = pos; Err.error_text = ("trans_exp :: CallNRecv :: init/finalize/acquire/release requires an associated lock");} *)
                      | Some v ->
                            (try
                              let vdef = I.look_up_view_def_raw 8 prog.I.prog_view_decls v in
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
                        C.exp_scall_ho_arg = None;
                        C.exp_scall_is_rec = false; (* default value - it will be set later in trans_prog *)
                        C.exp_scall_pos = pos;
                        C.exp_scall_path_id = pi; } in
                    let seq_1 = C.mkSeq ret_ct init_seq call_e pos in
                    ((C.Block {
                        C.exp_block_type = ret_ct;
                        C.exp_block_body = seq_1;
                        C.exp_block_local_vars = local_vars;
                        C.exp_block_pos = pos; }),ret_ct)
                  with | Not_found -> 
                      Err.report_error { Err.error_loc = pos; Err.error_text = "trans_exp :: case CallNRecv :: procedure 1 " ^ (mingled_mn ^ " is not found");}))
                    (*======== <<<<INIT ==========*)
            else (
                try (
                    let pdef = if (mn=Globals.join_name) then proc_decl else
                       let _ = Debug.ninfo_hprint (add_str "mingled_mn" pr_id) mingled_mn no_pos in
                       I.look_up_proc_def_mingled_name prog.I.prog_proc_decls mingled_mn
                    in
                    let proc_args = if (mn=Globals.join_name) then
                      if (!Globals.allow_threads_as_resource) then
                        (*threads as resource -> thrd type*)
                        let param = {Iast.param_type = Globals.thrd_typ;
                        Iast.param_name = "id";
                        Iast.param_mod = Iast.NoMod;
                        Iast.param_loc = pos;}
                        in [param]
                      else
                        (*Threads as AND-conj*)
                        let param = {Iast.param_type = Globals.thread_typ;
                        Iast.param_name = "id";
                        Iast.param_mod = Iast.NoMod;
                        Iast.param_loc = pos;}
                        in [param]
                    else pdef.I.proc_args
                    in
                    let tmp_names = E.visible_names () in
                    let all_names = List.map (fun (t, n) -> ((trans_type prog t pos), n)) tmp_names in
                    let free_vars = List.map snd all_names in
                    let n_tl = List.map (fun (t, n) -> (n,{ sv_info_kind = t;id = fresh_int () })) all_names in
                    let c_ho_arg = match ho_arg with
                      | None -> None
                      | Some f ->
                        let (_, cf) = trans_formula prog false free_vars true f n_tl false in
                        Some cf 
                    in
                    if ( != ) (List.length args) (List.length proc_args) then
                      Err.report_error { Err.error_loc = pos; Err.error_text = "number of arguments does not match"; }
                    else if (mn=Globals.join_name) &&  ((List.length args) != 1) then

                      Err.report_error { Err.error_loc = pos; Err.error_text = "join has other than one argument"; }
                    else
                      (let parg_types = List.map (fun p -> trans_type prog p.I.param_type p.I.param_loc) proc_args in
                      if List.exists2 (fun t1 t2 -> not (sub_type t1 t2)) cts parg_types then
                        Err.report_error { Err.error_loc = pos; Err.error_text = "argument types do not match 3"; }
                      else if Inliner.is_inlined mn then (let inlined_exp = Inliner.inline prog pdef ie in helper inlined_exp)
                      else
                        let _ = Debug.ninfo_hprint (add_str "length proc_decl.I.proc_args" (string_of_int)) (List.length proc_decl.I.proc_args) no_pos in
                        (let ret_ct = trans_type prog pdef.I.proc_return pdef.I.proc_loc in
                        let positions = List.map I.get_exp_pos args in
                        let (local_vars, init_seq, arg_vars) = trans_args (Gen.combine3 cargs cts positions) in
                        let call_e = C.SCall {
                            C.exp_scall_type = ret_ct;
                            C.exp_scall_method_name = mingled_mn;
                            C.exp_scall_lock = lock;
                            C.exp_scall_arguments = arg_vars;
                            C.exp_scall_ho_arg = c_ho_arg;
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
                )
                with Not_found -> (
                    try
                      let todo_unk = I.look_up_proc_def_raw prog.I.prog_proc_decls mn in
                      let _ = print_string_quiet (get_backtrace_quiet ()) in
                      report_error pos ("trans_exp :: case CallNRecv :: procedure call " ^ mingled_mn ^ " has invalid argument types (exc)")
                    with Not_found -> 
                        report_error pos ("trans_exp :: case CallNRecv :: procedure " ^ (mingled_mn ^ " is not found"))
                )
            )
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
                        (*Need to add info about cv*)
                        (*TO CHECK: diffrent between then and else ??? *)
                        let alpha = E.alpha_name x in
                        let () = E.add x (E.VarInfo {E.var_name = x; E.var_alpha = alpha; E.var_type = (Named cvt)}) in
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
                        (*let () = print_string ("\n rrr1 -> \n"^Iprinter.string_of_exp cb^"\n") in*)
                        let new_bd, ct2 = helper cb in
                        (*let () = print_string ("\n rrr2 -> \n") in*)
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
                      (C.Catch{ C.exp_catch_flow_type = exlist # get_hash cvt;
                      C.exp_catch_flow_var = cfv;
                      C.exp_catch_var = None;
                      C.exp_catch_body = new_bd;                                                                                       
                      C.exp_catch_pos = pos;},ct2)
            end
      | I.Cond {I.exp_cond_condition = e1;
        I.exp_cond_then_arm = e2;
        I.exp_cond_else_arm = e3;
        I.exp_cond_path_id = pi;
        I.exp_cond_pos = pos } ->
            (* let str_pi=match pi with                                                          *)
            (*          | None -> print_endline "none path id of cond"                              *)
            (*          | Some (x,y)->  print_endline ("Cond id: "^(string_of_int x)^" and "^y) in *)
            (* let () = print_string ("trans_exp :: cond = " ^ Iprinter.string_of_exp e1 ^ " then branch = " ^ Iprinter.string_of_exp e2 ^ " else branch = " ^ Iprinter.string_of_exp e3 ^ "\n") in *) 
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
                      ((C.Cond{C.exp_cond_type = te2;
                      C.exp_cond_condition = v;
                      C.exp_cond_then_arm = ce2;
                      C.exp_cond_else_arm = ce3;
                      C.exp_cond_pos = pos;
                      C.exp_cond_path_id = mk_strict_branch_point pi ""; }), te2)
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
                          C.exp_cond_path_id = mk_strict_branch_point pi ""; } in
                      let tmp_e1 = C.Seq {
                          C.exp_seq_type = te2;
                          C.exp_seq_exp1 = init_e;
                          C.exp_seq_exp2 = cond_e;
                          C.exp_seq_pos = e_pos; } in
                      let tmp_e2 = C.Seq {
                          C.exp_seq_type = te2;
                          C.exp_seq_exp1 = vd;
                          C.exp_seq_exp2 = tmp_e1;
                          C.exp_seq_pos = pos; } in
                      (tmp_e2, te2))
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
            let id_string f = List.fold_left (fun x y -> x ^ ";" ^ y) "" f in
            (* An Hoa : compact the field access sequence *)
            let et = snd (helper e) in
            let fs,rem,_ = compact_field_access_sequence prog et fs in
            if not (rem = "") then
              failwith ("[trans_exp] expect non-inline field access but still got { " ^ rem ^ " }")
            else
              (* ... = o.f => read_only = true *)
              let r = 
	        (* if (!Globals.allow_imm) || (!Globals.allow_field_ann) then *)
                flatten_to_bind prog proc e (List.rev fs) None pid (CP.ConstAnn(Lend)) true pos (* ok to have it lend instead of Imm? *)
                    (* else *)
                    (*   flatten_to_bind prog proc e (List.rev fs) None pid (CP.ConstAnn(Mutable)) true pos *)
              in
              (* let () = print_string ("after: "^(Cprinter.string_of_exp (fst r))) in *)
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
                I.exp_call_nrecv_ho_arg = None;
                I.exp_call_nrecv_path_id = None;
                I.exp_call_nrecv_pos = pos; }
            in helper newie
      | I.New {
            I.exp_new_class_name = c;
            I.exp_new_arguments = args;
            I.exp_new_pos = pos } ->
            let data_def = I.look_up_data_def 3 pos prog.I.prog_data_decls c in
            let all_fields = I.look_up_all_fields prog data_def in
            let field_types = 
              if !Globals.allow_locklevel  && c=lock_name then [level_data_typ] else
                List.map I.get_field_typ all_fields in
            let nargs = List.length args in
            let nfields = List.length field_types in
            (*=========processing waitlevel===============*)
            if (!Globals.allow_locklevel && c=lock_name && nargs>1) then
              Err.report_error{ Err.error_loc = pos; Err.error_text = "number of arguments does not match: " ^ lock_name ^ " should have at most 1 arguments";}
            else if (!Globals.allow_locklevel && c=lock_name && nargs=0) then
              (*add an extra local variable for locklevel*)
              let fn = fresh_ty_var_name (Globals.level_data_typ) pos.start_pos.Lexing.pos_lnum in
              let fn_decl = C.VarDecl
                {
                    C.exp_var_decl_type = Globals.level_data_typ;
                    C.exp_var_decl_name = fn;
                    C.exp_var_decl_pos = pos;
                }
              in
              let arg = (Globals.level_data_typ,fn) in
              let new_e = C.New {
                  C.exp_new_class_name = c;
                  C.exp_new_parent_name = data_def.I.data_parent_name;
                  C.exp_new_arguments = [arg];
                  C.exp_new_pos = pos;} in
              let new_t = Named c in
              let seq_e = C.mkSeq new_t fn_decl new_e pos in
              ((C.Block {
                  C.exp_block_type = new_t;
                  C.exp_block_body = seq_e;
                  C.exp_block_local_vars = []; (*the new fresh var can be out of the scope of this block*)
                  C.exp_block_pos = pos; }),new_t)
            else
              (*=========processing locklevel===============*)
              if ((!Globals.perm != Globals.Bperm && (nargs!=nfields))
              || (!Globals.perm == Globals.Bperm && nargs!=nfields+1)) && (nargs!=0)
                && (not (c=lock_name)) then
                  begin
                    let () = Debug.info_hprint (add_str "nargs" (string_of_int)) nargs no_pos in
                    let () = Debug.info_hprint (add_str "nfields" (string_of_int)) nfields no_pos in
                    let () = Debug.info_hprint (add_str "args" (pr_list Iprinter.string_of_exp)) args no_pos in
                    let () = Debug.info_hprint (add_str "args" (pr_list string_of_typ)) field_types no_pos in
                    Err.report_error{ Err.error_loc = pos; Err.error_text = "number of arguments does not match in New?? " ^ c;}
                  end
              else
                begin
                  let field_types = if (!Globals.perm == Globals.Bperm) then
                    (*LDK: in case of bounded permission, the first field
                      in the args list is the bound (permission total).
                      nargs=|field_types|+1 and bound=List.hd nargs
                    *)
                    Int::field_types
                  else field_types
                  in
                  (* let () = Debug.info_hprint (add_str "field_types" (pr_list string_of_typ)) field_types no_pos in *)
                  let nargs = List.length field_types in
                  let tmp = 
                    if args==[] then List.map (fun t -> (None,t)) field_types
                    else List.map (fun x -> (let (e,t)=helper x in (Some e,t))) args 
                  in
                  let (cargs, cts) = List.split tmp in
                  let parg_types = List.map (fun ft -> trans_type prog ft pos) field_types in
                  if List.exists2 (fun t1 t2 -> not (sub_type t1 t2)) cts parg_types then
                    Err.report_error { Err.error_loc = pos; Err.error_text = "argument types do not match 4";}
                  else ( let positions = Gen.repeat pos nargs in
                  let (local_vars, init_seq, arg_vars) = trans_args_gen (Gen.combine3 cargs cts positions) in
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
                      C.exp_block_pos = pos; }),new_t))
                end
                    (***********<< processing New ********)
      | I.Null pos -> ((C.Null pos), Globals.null_type)
      | I.Return {I.exp_return_val = oe;
        I.exp_return_path_id = pi; (*control_path_id -> option (int * string)*)
        I.exp_return_pos = pos} ->  begin
          let cret_type = trans_type prog proc.I.proc_return proc.I.proc_loc in
          let _=if(!Globals.proof_logging_txt) then (*proof logging*)   
            Globals.return_exp_pid := !Globals.return_exp_pid @ [pi] in
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
                  (* let  _ = Debug.info_zprint (lazy (((string_of_loc e_pos) ^ ":e_pos" ))) pos in *)
                  let ce, ct = helper e in
                  (*
                    139::return v_null_21_541
                    !!! return(iast-e):x
                    !!! return(cast-ce):x
                    !!! return(cast-tmp_e2):node v_node_30_542;
                    v_node_30_542 = x;
                    138::return v_node_30_542
                  *)
                  if sub_type ct cret_type then
                    let tmp_e2 =
                      let ce_iv,ce_name = match ce with
                        | Cast.Var {Cast.exp_var_name=v} -> (true,v)
                        | _ -> (false,"")
                      in
                      (* Debug.info_hprint (add_str "return(cast-ce)" Cprinter.string_of_exp) ce e_pos; *)
                      (* Debug.info_hprint (add_str "return(is_var ce)" string_of_bool) ce_iv e_pos; *)
                      if ce_iv then
                        (* let fn = (fresh_ty_var_name (ct) e_pos.start_pos.Lexing.pos_lnum) in *)
                        let shar = C.Sharp ({
                            C.exp_sharp_type = C.void_type;
                            C.exp_sharp_flow_type = C.Sharp_ct {CF.formula_flow_interval = !ret_flow_int ; CF.formula_flow_link = None};
                            C.exp_sharp_unpack = false;
                            C.exp_sharp_val = Cast.Sharp_var (ct,ce_name);
                            C.exp_sharp_path_id = pi;
                            C.exp_sharp_pos = pos}) in
                        shar
                      else
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
                        C.Seq { 
                            C.exp_seq_type = C.void_type;
                            C.exp_seq_exp1 = vd;
                            C.exp_seq_exp2 = tmp_e1;
                            C.exp_seq_pos = e_pos;} in 
                    begin
                      (* Debug.info_hprint (add_str "return(iast-e)" Iprinter.string_of_exp) e e_pos; *)
                      (* Debug.info_hprint (add_str "return(cast-ce)" Cprinter.string_of_exp) ce e_pos; *)
                      (* Debug.info_hprint (add_str "return(cast-tmp_e2)" Cprinter.string_of_exp) tmp_e2 e_pos; *)
                      (tmp_e2, C.void_type)
                    end
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
                        I.exp_call_nrecv_ho_arg = None;
                        I.exp_call_nrecv_path_id = pid;
                        I.exp_call_nrecv_pos = pos;} in helper call_e
              | I.OpPostInc ->
                    if not (!Globals.check_integer_overflow) then 
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
                    else 
                      let add1_e = I.Binary {
                          I.exp_binary_op = I.OpPlus;
                          I.exp_binary_oper1 = e;
                          I.exp_binary_oper2 = I.IntLit { I.exp_int_lit_val = 1; I.exp_int_lit_pos = pos; };
                          I.exp_binary_path_id = pid;
                          I.exp_binary_pos = pos; } in
                      helper (I.Assign {
                          I.exp_assign_op = I.OpAssign;
                          I.exp_assign_lhs = e;
                          I.exp_assign_rhs = add1_e;
                          I.exp_assign_path_id = None;
                          I.exp_assign_pos = pos;})                     
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
              | I.OpUMinus ->
                    let sub_e = I.Binary {
                        I.exp_binary_op = I.OpMinus;
                        I.exp_binary_oper1 = I.IntLit { I.exp_int_lit_val = 0; I.exp_int_lit_pos = pos; };
                        I.exp_binary_oper2 = e;
                        I.exp_binary_path_id = pid;
                        I.exp_binary_pos = pos; } in
                    helper sub_e
              | _ -> failwith "u_op not supported yet")
      | I.Var { I.exp_var_name = v; I.exp_var_pos = pos } ->
            (try
              let vinfo_tmp = E.look_up v in
              match vinfo_tmp with
                | E.VarInfo vi ->
                      let ct = trans_type prog vi.E.var_type pos in
                      (*let () = print_string ("llok bf: "^v^" after: "^vi.E.var_alpha^"\n") in*)
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
                  (* let () = print_endline ("trans_exp: before trans_typ") in *)
                  let ct = trans_type prog proc_typ pos in
                  (* let () = print_endline ("trans_exp: after trans_typ") in *)
                  ((C.Var {
                      C.exp_var_type = ct;
                      C.exp_var_name = v;
                      C.exp_var_pos = pos; }), ct)
                else
                  Err.report_error { Err.error_loc = pos; Err.error_text = "Var " ^ v ^ " is not defined"; })
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
            I.exp_while_addr_vars = addr_vars;
            I.exp_while_specs = prepost;
            I.exp_while_f_name = a_wn;
            I.exp_while_wrappings = wrap;
            I.exp_while_path_id = pi;
            I.exp_while_pos = pos } ->
            let () = Debug.ninfo_pprint ("       ASTSIMP.trans_exp WHILE:") no_pos in
            let tvars = E.visible_names () in
            let tvars = Gen.BList.remove_dups_eq (=) tvars in
            let () =  Debug.ninfo_hprint (add_str "tvars" (pr_list (fun (_,id) -> pr_id id))) tvars no_pos in
            let () =  Debug.ninfo_hprint (add_str "proc_args" (pr_list (fun p -> pr_id p.Iast.param_name))) proc.Iast.proc_args no_pos in
            (*ONLY NEED THOSE that are modified in the body and condition*)
            (*INDEED: we could identify readSET and writeSET. This will
              help reduce annotation for read-only variables
              However, this may not be important.*)
            let _,fvars_body,fw_body = x_add Pointers.modifies body [] prog in
            let _,fvars_cond,fw_cond = x_add Pointers.modifies cond [] prog in
            let () = Debug.ninfo_hprint (add_str "fw_body" (pr_list pr_id)) fw_body no_pos in
            let () = Debug.ninfo_hprint (add_str "fw_cond" (pr_list pr_id)) fw_cond no_pos in
            let fvars_while = fvars_body@fvars_cond in
            let () = Debug.ninfo_hprint (add_str "fvars_while" (pr_list pr_id)) fvars_while no_pos in
            let () = Debug.ninfo_hprint (add_str "spec" Iprinter.string_of_struc_formula) prepost no_pos in
            let all_prime = List.fold_left (fun acc (id,pr) ->
                if pr=Primed then acc@[id] else acc) [] (IF.struc_free_vars false prepost) in
            let () = Debug.ninfo_hprint (add_str "all_prime" (pr_list pr_id)) all_prime no_pos in
            let prime_var_to_add = Gen.BList.intersect_eq (=) all_prime fvars_while in
            let fvars_while_write = prime_var_to_add@fw_body@fw_cond in
            let fvars_specs, _ = List.split (Iformula.struc_free_vars false prepost) in
            let fvars = Gen.BList.remove_dups_eq (=) (fvars_while@fvars_specs) in
            (* let () = print_endline ("fvars = " ^ (string_of_ident_list fvars)) in *)
            let tvars = List.filter (fun (t,id) -> List.mem id fvars) tvars in
            (************************************************)
            let w_args = List.map (fun tv -> I.Var { I.exp_var_name = snd tv; I.exp_var_pos = pos; }) tvars in
            let fn3 = fresh_name () in
            (* let w_name = fn3 ^ ("_" ^ (Gen.replace_path_sep_with_uscore *)
            (*     (Gen.replace_dot_with_uscore (string_of_loc pos)))) in  *)
            let w_name = if String.compare a_wn "" == 0 then (* fn3 ^ "_" ^ *) "while_" ^ (string_of_pos_plain pos.start_pos)
            else a_wn
            in
            (*if exists return inside body:w2a.ss*)
            (*check exists return inside loop body*)
            let exist_return_inside = if proc.I.proc_return <> Void && I.exists_return body then true else false in
            let () = Debug.ninfo_zprint (lazy (("       exist_return_inside: " ^ (string_of_bool exist_return_inside)))) no_pos in
            let w_body_1 = body in
            let w_body_2 = I.Block {
                I.exp_block_jump_label = I.NoJumpLabel; 
                I.exp_block_body = I.Seq{
                    I.exp_seq_exp1 = w_body_1;
                    I.exp_seq_exp2 = I.CallNRecv {
                  I.exp_call_nrecv_method = w_name;
                  I.exp_call_nrecv_lock = None;
                  I.exp_call_nrecv_arguments = w_args;
                  I.exp_call_nrecv_ho_arg = None;
                  I.exp_call_nrecv_pos = pos;
                  I.exp_call_nrecv_path_id = pi; };
                    I.exp_seq_pos = pos; };
                I.exp_block_local_vars = [];
                I.exp_block_pos = pos;} in
            let w_body_wo_brk = I.Cond {
                I.exp_cond_condition = cond;
                I.exp_cond_then_arm = w_body_2;
                I.exp_cond_else_arm = I.Empty pos;
                I.exp_cond_pos = pos;
                I.exp_cond_path_id = pi;} in
            let w_body_w_brk = match wrap with
              | None -> w_body_wo_brk
              | Some (e,_) -> (*let e,et = helper e in*)
                    match e with
                      | I.Try b -> I.Try{b with I.exp_try_block  = w_body_wo_brk}
                      | _ ->  Err.report_error { Err.error_loc = pos; Err.error_text = "Translation of loop break wrapping failed";} in
            let w_body = I.Block {
                I.exp_block_jump_label = I.NoJumpLabel; 
                I.exp_block_body = w_body_w_brk ;
                I.exp_block_local_vars = [];
                I.exp_block_pos = pos;} in
            let prepost = match wrap with 
              | None -> prepost
              | Some _ -> IF.add_post_for_flow (I.get_breaks w_body) prepost
            in
            let w_formal_args = List.map (fun tv ->{
                I.param_type = fst tv;
                I.param_name = snd tv;
                I.param_mod = if (List.mem (snd tv) fvars_while_write) then I.RefMod
                else I.NoMod; (* other vars from specification, declared with NoMod *)
                I.param_loc = pos; }) tvars in
            let w_proc = {
                I.proc_hp_decls = [];
                I.proc_name = w_name;
                I.proc_source = (proc_files # top) ^ "(while_loop)";
                I.proc_flags = [];
                I.proc_mingled_name = mingle_name_enum prog w_name (List.map fst tvars);
                I.proc_data_decl = proc.I.proc_data_decl;
                I.proc_constructor = false;
                I.proc_args = w_formal_args;
                I.proc_args_wi = List.map (fun p -> (p.I.param_name,Globals.I)) w_formal_args;
                I.proc_ho_arg = None;
                I.proc_return = I.void_type;
                (* I.proc_important_vars= [];*)
                I.proc_static_specs = prepost;
                I.proc_exceptions = [brk_top]; (*should be ok, other wise while will have a throws set and this does not seem ergonomic*)
                I.proc_dynamic_specs = IF.mkEFalseF ();
                I.proc_body = Some w_body;
                I.proc_is_main = proc.I.proc_is_main;
                I.proc_is_while = true;
                I.proc_has_while_return = false;
                I.proc_is_invoked = true;
                I.proc_verified_domains = [];
                I.proc_file = proc.I.proc_file;
                I.proc_loc = pos; 
                I.proc_test_comps = if not !Globals.validate then None else
                  I.look_up_test_comps prog.I.prog_test_comps w_name} in
            let () = Debug.ninfo_hprint (add_str "w_proc.I.proc_static_specs" Iprinter.string_of_struc_formula)  w_proc.I.proc_static_specs no_pos in
            let w_proc = match w_proc.I.proc_static_specs with
              |  IF.EList [] ->
                     if Globals.infer_const_obj # is_shape then
                       let infer_args, ninfer_args = List.partition (fun p -> List.exists (fun p2 ->
                           String.compare p.Iast.param_name p2.Iast.param_name = 0) proc.Iast.proc_args
                       ) w_formal_args in (*??*)
                     let () =  Debug.ninfo_hprint (add_str "infer_args" (pr_list (fun p -> pr_id p.Iast.param_name))) infer_args no_pos in
                     let () =  Debug.ninfo_hprint (add_str "ninfer_args" (pr_list (fun p -> pr_id p.Iast.param_name))) ninfer_args no_pos in
                       let infer_args = w_formal_args in
                       let new_prepost, hp_decls, args_wi = I.genESpec w_proc.I.proc_mingled_name w_proc.I.proc_body infer_args I.void_type (Iformula.mkTrue_nf pos) (Iformula.mkTrue_nf pos) INF_SHAPE [] pos in
                     let () = prog.I.prog_hp_decls <- prog.I.prog_hp_decls@hp_decls in
                       let full_args_wi = if ninfer_args = [] then args_wi
                       else List.fold_left (fun r p ->
                           try
                             let iarg = List.find (fun (id,_) -> String.compare id p.Iast.param_name = 0) args_wi in
                             r@[iarg]
                           with _ -> r@[(p.Iast.param_name, NI)]
                       ) [] w_formal_args in
                       {w_proc with I.proc_hp_decls = w_proc.I.proc_hp_decls@hp_decls;
                           I.proc_static_specs = new_prepost;
                           I.proc_args_wi = full_args_wi;
                       }
                     else w_proc
              | IF.EInfer i_sf ->
                    let () =  Debug.ninfo_hprint (add_str " i_sf.IF.formula_inf_obj" pr_id) ( i_sf.IF.formula_inf_obj# string_of) no_pos in
                    if Globals.infer_const_obj # is_shape || i_sf.IF.formula_inf_obj # is_shape then
                      let is_simpl, pre,post = IF.get_pre_post i_sf.IF.formula_inf_continuation in
                      if is_simpl then
                        let infer_args, ninfer_args = List.partition (fun p -> List.exists (fun p2 ->
                            String.compare p.Iast.param_name p2.Iast.param_name = 0) proc.Iast.proc_args
                        ) w_formal_args in (*???*)
                        let () =  Debug.ninfo_hprint (add_str "infer_args" (pr_list (fun p -> pr_id p.Iast.param_name))) infer_args no_pos in
                        let () =  Debug.ninfo_hprint (add_str "ninfer_args" (pr_list (fun p -> pr_id p.Iast.param_name))) ninfer_args no_pos in
                        let infer_args = w_formal_args in
                        let new_prepost, hp_decls, args_wi = I.genESpec w_proc.I.proc_mingled_name w_proc.I.proc_body infer_args I.void_type pre
                          post INF_SHAPE i_sf.IF.formula_inf_obj #get_lst pos in
                        let () = prog.I.prog_hp_decls <- prog.I.prog_hp_decls@hp_decls in
                        let full_args_wi = if ninfer_args = [] then args_wi
                        else List.fold_left (fun r p ->
                            try
                              let iarg = List.find (fun (id,_) -> String.compare id p.Iast.param_name = 0) args_wi in
                              r@[iarg]
                            with _ -> r@[(p.Iast.param_name, NI)]
                        ) [] w_formal_args in
                        {w_proc with I.proc_hp_decls = w_proc.I.proc_hp_decls@hp_decls;
                            I.proc_static_specs = new_prepost;
                            I.proc_args_wi = full_args_wi;
                        }
                      else  w_proc
                    else w_proc
              | _ -> w_proc
            in
            let temp_call =  I.CallNRecv {
                I.exp_call_nrecv_method = w_name;
                I.exp_call_nrecv_lock = None;
                I.exp_call_nrecv_arguments = w_args;
                  I.exp_call_nrecv_ho_arg = None;
                I.exp_call_nrecv_pos = pos;
                I.exp_call_nrecv_path_id = pi; } in
            let w_call = temp_call (*match wrap with
                                     | None -> temp_call
                                     | Some (e,_) -> (*let e,et = helper e in*)
                                     match e with
                                     | I.Try b -> I.Try{b with I.exp_try_block  = temp_call}
                                     | _ ->  Err.report_error { Err.error_loc = pos; Err.error_text = "Translation of loop break wrapping failed";}*) in
            let w_proc = case_normalize_proc prog w_proc in
            let new_prog = { (prog) with I.prog_proc_decls = w_proc :: prog.I.prog_proc_decls;
                (* I.prog_hp_decls = prog.I.prog_hp_decls@w_proc.I.proc_hp_decls; *)
            } in
              let () = ihp_decl := !ihp_decl@w_proc.I.proc_hp_decls in
              (* let () = print_endline ("while : " ^ (Iprinter.string_of_struc_formula prepost)) in *)
              (* let () = print_endline ("w_proc : " ^ (Iprinter.string_of_proc_decl w_proc)) in *)
            let (iw_call, _) = trans_exp new_prog w_proc w_call in
            let cw_proc = trans_loop_proc new_prog w_proc addr_vars in
            (loop_procs := cw_proc :: !loop_procs; (iw_call, C.void_type))
      | Iast.FloatLit {I.exp_float_lit_val = fval; I.exp_float_lit_pos = pos} -> 
            (C.FConst {C.exp_fconst_val = fval; C.exp_fconst_pos = pos}, C.float_type)
      | Iast.Cast {I.exp_cast_target_type = ty;
        I.exp_cast_body = exp;
        I.exp_cast_pos = pos} ->
            let org_exp, _ = trans_exp prog proc exp in
            let org_ty = Gen.unsome (C.type_of_exp org_exp) in
            if (ty = org_ty) then
              (org_exp, ty)
            else if (org_ty = Bool && ty = Int) then (
                (* cast bool exp to int exp *)
                let tmp_name = (fresh_var_name "int" pos.start_pos.Lexing.pos_lnum) in
                let tmp_var_decl = Iast.mkVarDecl Int [(tmp_name, None, pos)] pos in
                let tmp_var = I.mkVar tmp_name pos in
                let then_exp = I.mkAssign I.OpAssign tmp_var (I.mkIntLit 1 pos) None pos in
                let else_exp = I.mkAssign I.OpAssign tmp_var (I.mkIntLit 0 pos) None pos in
                let if_exp = I.Cond {I.exp_cond_condition = exp;
                I.exp_cond_then_arm = then_exp;
                I.exp_cond_else_arm = else_exp;
                I.exp_cond_path_id = None;
                I.exp_cond_pos = pos } in
                let cast_exp = I.mkSeq tmp_var_decl (I.mkSeq if_exp tmp_var pos) pos in
                trans_exp prog proc cast_exp
            )
            else (
                let cast_exp = C.Cast {C.exp_cast_target_type = ty;
                C.exp_cast_body = org_exp;
                C.exp_cast_pos = pos} in
                (cast_exp, ty)
            )
      | Iast.Finally b ->  Err.report_error { Err.error_loc = b.I.exp_finally_pos; Err.error_text = "Translation of finally failed";}
      | Iast.ConstDecl _ -> failwith (Iprinter.string_of_exp ie)
      | Iast.Break _ -> failwith (Iprinter.string_of_exp ie)
      | Iast.Continue _ -> failwith (Iprinter.string_of_exp ie)
      | I.Raise ({ 
            I.exp_raise_type = ot;
            I.exp_raise_val = oe;
            I.exp_raise_use_type = use_type;
            I.exp_raise_from_final = ff;
            I.exp_raise_path_id = pi;
            I.exp_raise_pos = pos })->
            (*let () = print_string ("\n trt : "^(string_of_bool ff)^"\n") in*)
            (* let () = Debug.info_pprint ("       ASTSIMP.trans_exp Raise:") no_pos in *)
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
                      (*allow raise c_flow*)
                      if exlist # sub_type_obj (string_of_typ ct) c_flow (* raisable_class *) then                           
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
                  (*let () = print_string ("\n rrr1 -> \n"^Iprinter.string_of_exp cb^"\n") in*)
                      let new_bd, ct2 = helper cb in
                  (*let () = print_string ("\n rrr2 -> \n") in*)
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
                      { C.exp_catch_flow_type = Exc.get_hash_of_exc cvt;
                      C.exp_catch_flow_var = cfv;
                      C.exp_catch_var = None;
                      C.exp_catch_body = new_bd;
                      C.exp_catch_pos = pos;}
                      end
                  (*| _ -> Err.report_error { Err.error_loc = pos; Err.error_text = "translation failed, catch clause got mistranslated" }*)
                  *)
      | I.Par p ->
        let pos = p.I.exp_par_pos in
        let tmp_names = E.visible_names () in
        (* let () = print_endline ("PAR: tmp_names: " ^ (Iprinter.string_of_typed_var_list tmp_names)) in *)
        let all_names = List.map (fun (t, n) -> ((trans_type prog t pos), n)) tmp_names in
        let free_vars = List.map snd all_names in
        let n_tl = List.map (fun (t, n) -> (n, { sv_info_kind = t; id = fresh_int () })) all_names in
        
        let trans_par_case c =
          let cpos = c.I.exp_par_case_pos in 
          let cond = map_opt (fun f -> 
            snd (trans_formula prog false free_vars true f n_tl false)) c.I.exp_par_case_cond 
          in
          let body, _ = helper c.I.exp_par_case_body in
          let vp = trans_vperm_sets c.I.exp_par_case_vperm n_tl cpos in
          { C.exp_par_case_cond = cond;
            C.exp_par_case_vperm = vp;
            C.exp_par_case_body = body;
            C.exp_par_case_else = c.I.exp_par_case_else;
            C.exp_par_case_pos = cpos; }
        in
        let trans_lend_heap = snd (trans_formula prog false free_vars true p.I.exp_par_lend_heap n_tl false) in
        if CF.isLend_formula trans_lend_heap then
          (C.Par {
            C.exp_par_vperm = trans_vperm_sets p.I.exp_par_vperm n_tl pos;
            C.exp_par_lend_heap = trans_lend_heap;
            C.exp_par_cases = List.map trans_par_case p.I.exp_par_cases;
            C.exp_par_pos = pos; }, C.void_type)
        else 
          let err_pos = CF.pos_of_formula trans_lend_heap in
          let msg = "Only @L heap data/view is allowed in par." in
          (Debug.print_info ("(" ^ (Cprinter.string_of_formula trans_lend_heap) ^ ") ") msg err_pos;
           Debug.print_info ("(Cause of Par Failure)") (Cprinter.string_of_formula trans_lend_heap) err_pos;
           Err.report_error { Err.error_loc = err_pos; Err.error_text = msg })
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
    | List _ | FORM | Tup2 _ ->
          failwith "default_value: list/FORM/Tup2 can only be used for constraints"
    | INFInt ->
          failwith "default_value: INFInt can only be used for constraints"
    | RelT _ ->
          failwith "default_value: RelT can only be used for constraints"
    | FuncT _ ->
          failwith "default_value: FuncT can only be used for constraints"
    | UtT ->
          failwith "default_value: UtT can only be used for constraints"
    | HpT ->
          failwith "default_value: HpT can only be used for constraints"
    | Named _ (* | SLTyp *) -> C.Null pos
    | Pointer ptr -> C.Null pos
    | Tree_sh ->  failwith
          "default_value: tree_sh in variable declaration should have been rejected"
    | Array (t, d) ->
          C.EmptyArray { C.exp_emparray_type = t; 
          C.exp_emparray_dim = d; 
          C.exp_emparray_pos = pos}
    | Bptyp ->
          failwith "default_value: Bptyp can only be used for constraints"

(* and flatten_to_bind prog proc b r rhs_o pid imm read_only pos  = *)
(*   Debug.no_3 "flatten_to_bind "  *)
(*     (Iprinter.string_of_exp)  *)
(*     (fun x -> match x with *)
(*       | Some x1 -> (Cprinter.string_of_exp x1) | None -> "") *)
(*     (string_of_heap_ann) *)
(*     (pr_pair Cprinter.string_of_exp string_of_typ)  *)
(*     (fun b rhs_o _ -> flatten_to_bind_x prog proc b r rhs_o pid imm read_only pos) b rhs_o imm *)

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
  (* let () = print_endline ("[compact_field_access_sequence] input = { " ^ (string_of_typ root_type) ^ " ; { " ^ (String.concat " ; " field_seq) ^ " } }") in *)
  (* [Internal] Folding function: 
   * cfsq = current folding sequence; cf = accumulated field
   * ct = current type; fn = field name
   * Output : next state of (cfsq,cf,ct)
   *)
  let fold_function (cfsq,cf,ct) fn = 
    let f = I.get_field_from_typ prog.I.prog_data_decls ct fn in
    let ncf = cf ^ (if cf = "" then "" else  inline_field_expand) ^ fn in
    let nct = I.get_field_typ f in
    if (I.is_inline_field f) then
      (cfsq,ncf,nct)
    else
      (List.append cfsq [ncf],"",nct) in
  let res = List.fold_left fold_function ([],"",root_type) field_seq in
  (* let () = print_endline ("[compact_field_access_sequence] output = { " ^ (String.concat " ; " res) ^ " }") in *)
  res

and create_bind_exp typ bound_v fields body read_only pos pid =
  let _, vs = List.split fields in
  let initial_ann_lst =  (List.map (fun f -> (f, (CP.ConstAnn(Accs)))) vs) in
  let ann_lst = Immutable.read_write_exp_analysis body initial_ann_lst in 
  let _,ann_lst = List.split ann_lst in
  let ann = Immutable.get_strongest_imm ann_lst in
  C.Bind {
      C.exp_bind_type = typ;
      C.exp_bind_bound_var = bound_v;
      C.exp_bind_fields = fields;
      C.exp_bind_body = body;
      C.exp_bind_imm = CP.ConstAnn(Mutable); 
      C.exp_bind_param_imm = ann_lst;
      C.exp_bind_read_only = read_only;
      C.exp_bind_pos = pos;
      C.exp_bind_path_id = pid; 
  }

and flatten_to_bind prog proc (base : I.exp) (rev_fs : ident list)
      (rhs_o : C.exp option) (pid:control_path_id) imm (read_only : bool) pos =
  let pid_s = match pid with | None -> fresh_strict_branch_point_id "" | Some s -> s in
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
          let ddef = I.look_up_data_def 2 pos prog.I.prog_data_decls dname in
          let rec gen_names (fn : ident) (flist : I.typed_ident list) :
                ((I.typed_ident option) * (ident list)) =
            (match flist with
              | [] -> (None, [])
              | f :: rest ->
                    let fn1 = fresh_trailer () in
                    let line = if pos.start_pos.Lexing.pos_lnum > 0 then
                      string_of_int pos.start_pos.Lexing.pos_lnum
                    else "0" in
                    let fresh_fn = (snd f) ^ "_" ^ line ^ fn1 in
                    let (tmp, new_rest) = gen_names fn rest in
                    if (snd f) = fn then ((Some (fst f, fresh_fn)), (fresh_fn :: new_rest))
                    else (tmp, (fresh_fn :: new_rest))) in
          let all_fields = I.look_up_all_fields prog ddef in
          let ann_list = x_add Immutable.compute_ann_list all_fields rev_fs imm in
          let id_string lst = List.fold_left (fun x (a,b,c,d) -> x ^ "," ^ (snd a)) "" lst in
          x_tinfo_hp (add_str "\nrev_fs: " (List.fold_left (fun x str -> x ^ "," ^ str) "")) rev_fs no_pos;
          x_tinfo_hp (add_str "\nBound Ann"  (String.concat "," )) (List.map Cprinter.string_of_imm  ann_list) no_pos;
          x_tinfo_hp (add_str "\nall_fields: " id_string) all_fields no_pos;
          let field_types = List.map (fun f -> trans_type prog (I.get_field_typ f) pos) all_fields in
          let (tmp1, fresh_names) = gen_names f (List.map I.get_field_typed_id all_fields) in
          if not (Gen.is_some tmp1) then
            Err.report_error {
                Err.error_loc = pos;
                Err.error_text = "field " ^ (f ^ " is not accessible");}
          else
            (let (vt, fresh_v) = Gen.unsome tmp1 in
            let _ =  Debug.ninfo_hprint (add_str "vt" string_of_typ) vt no_pos in
            let ct = trans_type prog vt pos in
            let (bind_body, bind_type) = match rhs_o with
              | None -> ((C.Var {
                    C.exp_var_type = ct;
                    C.exp_var_name = fresh_v;
                    C.exp_var_pos = pos; }), ct)
              | Some rhs_e ->
                    (* let () =  Debug.info_hprint (add_str "rhs_e" !Cast.print_prog_exp) rhs_e no_pos in *)
                    (*Loc: should type checking be postponed to after typeinfer? *)
                    let rhs_t = C.type_of_exp rhs_e in
                    if (Gen.is_some rhs_t) && (sub_type (Gen.unsome rhs_t) ct) then
                      ((C.Assign {
                          C.exp_assign_lhs = fresh_v;
                          C.exp_assign_rhs = rhs_e;
                          C.exp_assign_pos = pos;}), C.void_type)
                    else Err.report_error {
                        Err.error_loc = pos;
                        Err.error_text = "lhs and rhs do not match 1"; }
            (* let () = print_string ("\n(andreeac)astsimp.ml flatten_to_bind_x, vs to become lent ann: " ^ (List.fold_left (fun x y -> x ^ " " ^ y) "" fresh_names) ^ ("\n   annf: " ^ (List.fold_left (fun x y -> x ^ (Cprinter.string_of_imm y)  ) ""  ann_list))) *) in
            let bind_fields =  List.combine field_types fresh_names in
            (* let bind_e = create_bind_exp bind_type ((Named dname), fn)  bind_fields  bind_body read_only pos pid_s in *)
            let bind_e = C.Bind {
                C.exp_bind_type = bind_type;
                C.exp_bind_bound_var = ((Named dname), fn);
                C.exp_bind_fields = List.combine field_types fresh_names;
                C.exp_bind_body = bind_body;
	        C.exp_bind_imm = imm;
	        C.exp_bind_param_imm = ann_list;
                C.exp_bind_read_only = read_only;
                C.exp_bind_pos = pos;
                C.exp_bind_path_id = pid_s;} in
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

and trans_args args =
  let pr1 = pr_list (fun (e,t,_) -> pr_pair (Cprinter.string_of_exp) string_of_typ (e,t)) in
  let pr2 = pr_triple (pr_list pr_none) Cprinter.string_of_exp (pr_list pr_id) in
  Debug.no_1 "trans_args" pr1 pr2 trans_args_x args

and trans_args_x args = trans_args_gen (List.map (fun (a,b,c) -> (Some a,b,c)) args)

and trans_args_gen (args : ((C.exp option) * typ * loc) list) :
      ((C.typed_ident list) * C.exp * (ident list)) =
  match args with
    | arg :: rest ->
          let (rest_local_vars, rest_e, rest_names) = trans_args_gen rest
          in
          (match arg with
            | (Some (C.Var { C.exp_var_type = _; C.exp_var_name = v; C.exp_var_pos = _
              }),
              _, _) -> (rest_local_vars, rest_e, (v :: rest_names))
            | (Some(arg_e), at, pos) ->
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
                  in ((local_var :: rest_local_vars), seq2, (fn :: rest_names))
            | (None, at, pos) ->
                  let fn = fresh_ty_var_name (at) pos.start_pos.Lexing.pos_lnum in
                  let fn_decl =
                    C.VarDecl
                        {
                            C.exp_var_decl_type = at;
                            C.exp_var_decl_name = fn;
                            C.exp_var_decl_pos = pos;
                        } in
                  (* let fn_init = *)
                  (*   C.Assign *)
                  (*       { *)
                  (*           C.exp_assign_lhs = fn; *)
                  (*           C.exp_assign_rhs = arg_e; *)
                  (*           C.exp_assign_pos = pos; *)
                  (*       } in *)
                  (* let seq1 = C.mkSeq C.void_type fn_init rest_e pos in *)
                  let seq2 = C.mkSeq C.void_type fn_decl rest_e pos in
                  let local_var = (at, fn)
                  in ((local_var :: rest_local_vars), seq2, (fn :: rest_names)))
    | [] -> ([], (C.Unit no_pos), [])

and get_type_name_for_mingling (prog : I.prog_decl) (t : typ) : ident =
  match t with
    | Named c ->
          (try let todo_unk = I.look_up_enum_def_raw prog.I.prog_enum_decls c in "int"
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

(* and case_coverage (instant:Cpure.spec_var list)(f:CF.struc_formula): bool = *)
(*   Debug.no_2 "case_coverage" (Gen.BList.string_of_f Cpure.string_of_typed_spec_var)   *)
(*       Cprinter.string_of_struc_formula string_of_bool *)
(*       case_coverage_x instant f *)

(*and case_coverage_x (instant:Cpure.spec_var list)(f:CF.struc_formula): bool =
  let () = trans_case_coverage instant f in
  true*)
(* let sat_subno  = ref 0 in *)
(* let rec struc_case_coverage (instant:Cpure.spec_var list) ctx (f1:CF.struc_formula):bool = match f1 with *)
(*   | CF.EAssume b ->  struc_case_coverage instant ctx b.CF.formula_assume_struc *)
(*   | CF.EBase b -> (match b.CF.formula_struc_continuation with  *)
(*       | None -> true *)
(*       | Some l -> struc_case_coverage (instant@ b.CF.formula_struc_explicit_inst@ b.CF.formula_struc_implicit_inst@ b.CF.formula_struc_exists) (CP.mkAnd (CF.extract_pure b.CF.formula_struc_base) ctx no_pos)l) *)
(*   | CF.ECase b ->  *)
(*         let r1,r2 = List.split b.CF.formula_case_branches in *)
(*         let all = List.fold_left (fun a c->(Cpure.mkStupid_Or a c None no_pos) ) (Cpure.mkFalse b.CF.formula_case_pos) r1  in *)
(*         (\** An Hoa Temporary Printing **\) *)
      (*         (\* let () = print_endline ("An Hoa : all = " ^ (Cprinter.string_of_pure_formula all)) in*\) *)
      (*         let () = if not(Gen.BList.subset_eq (=) (Cpure.fv all) instant) then  *)
      (*           let () = print_string ( *)
(*               (List.fold_left (fun a c1-> a^" "^ (Cprinter.string_of_spec_var c1)) "\nall:" (Cpure.fv all))^"\n"^ *)
(*                   (List.fold_left (fun a c1-> a^" "^ (Cprinter.string_of_spec_var c1)) "instant:" instant)^"\n")in             *)
(*           Error.report_error {  Err.error_loc = b.CF.formula_case_pos; *)
(*           Err.error_text = "all guard free vars must be instantiated";} in *)
      (*         let () =  *)
(*           let coverage_error =  *)
(*               let f_sat = Cpure.mkAnd ctx (Cpure.mkNot all None no_pos) no_pos in *)
(*               Tpdispatcher.is_sat_sub_no 11 f_sat sat_subno *)
(*               (\*not (Tpdispatcher.simpl_imply_raw ctx all)*\) in *)
(*           if coverage_error then *)
      (*             let () = Debug.info_hprint (add_str "case pure" Cprinter.string_of_pure_formula) all no_pos in *)
(*             let s = (Cprinter.string_of_struc_formula f) in *)
(*             Error.report_error {  Err.error_loc = b.CF.formula_case_pos; *)
(*             Err.error_text = "the guards don't cover the whole domain for : "^s^"\n";}    in *)
              
(*         let rec p_check (p:Cpure.formula list):bool = match p with *)
(*           | [] -> false  *)
(*           | p1i::p2 ->  *)
(*               let p1 = Cpure.mkAnd p1i ctx no_pos in *)
(*               if (List.fold_left  *)
(*                   (fun a c-> *)
(*                       if (x_add Tpdispatcher.is_sat_sub_no 12 (Cpure.mkAnd p1i c no_pos) sat_subno) then  *)
(*                           if (x_add Tpdispatcher.is_sat_sub_no 13 (Cpure.mkAnd p1 c no_pos) sat_subno) then  *)
(*                               (print_string ("in the context :"^(Cprinter.string_of_pure_formula ctx)^ *)
(*                                             "\n the guards "^(Cprinter.string_of_pure_formula p1i)^"and"^ *)
(*                                             (Cprinter.string_of_pure_formula c)^" are not disjoint\n"); *)
(*                               true) *)
(*                           else a *)
(*                       else a)  *)
(*                   false p2 ) *)
(*               then true *)
(*               else p_check p2 in *)
              
(*         let () = if (p_check r1) then  *)
(*           Error.report_error {  Err.error_loc = b.CF.formula_case_pos; *)
(*           Err.error_text = "the guards are not disjoint : "^(Cprinter.string_of_struc_formula f)^"\n";} in *)
(*         let todo_unk = List.map (fun (c1,c2)->struc_case_coverage instant (CP.mkAnd c1 ctx no_pos) c2) b.CF.formula_case_branches in true *)
(*   | CF.EInfer b -> struc_case_coverage instant ctx b.CF.formula_inf_continuation *)
(*   | CF.EList b -> List.for_all (fun c-> struc_case_coverage instant ctx (snd c)) b in *)
(* struc_case_coverage instant (CP. mkTrue no_pos) f *)

and trans_case_coverage prepost_flag (instant:Cpure.spec_var list)(f:CF.struc_formula): CF.struc_formula =
  let pr = Cprinter.string_of_struc_formula in
  Debug.no_2 "trans_case_coverage" (Gen.BList.string_of_f Cpure.string_of_typed_spec_var)  
      pr pr
      (trans_case_coverage_x prepost_flag) instant f

and trans_case_coverage_x  prepost_flag (instant:Cpure.spec_var list)(f:CF.struc_formula): CF.struc_formula =
  let sat_subno  = ref 0 in
  let rec struc_case_coverage in_pre (instant:Cpure.spec_var list) ctx (f1:CF.struc_formula):CF.struc_formula
        = match f1 with
          | CF.EAssume b ->  
                let nf = (struc_case_coverage false instant ctx b.CF.formula_assume_struc) 
                in CF.EAssume { b with CF.formula_assume_struc = nf }
          | CF.EBase b -> (match b.CF.formula_struc_continuation with 
              | None -> f1
              | Some l -> 
                    begin
                      let nf = (struc_case_coverage in_pre (instant@ b.CF.formula_struc_explicit_inst@ b.CF.formula_struc_implicit_inst@ b.CF.formula_struc_exists) (CP.mkAnd (CF.extract_pure b.CF.formula_struc_base) ctx no_pos)l)
                      in CF.EBase { b with CF.formula_struc_continuation = Some nf}
                    end)
          | CF.ECase b -> 
                let r1,r2 = List.split b.CF.formula_case_branches in
                let all = List.fold_left (fun a c->(Cpure.mkStupid_Or a c None no_pos) ) (Cpure.mkFalse b.CF.formula_case_pos) r1  in
                (** An Hoa Temporary Printing **)
          (* let () = print_endline ("An Hoa : all = " ^ (Cprinter.string_of_pure_formula all)) in*)
                (* WN : syntactic check for case now a WARNING *)
          let () = if prepost_flag && not(Gen.BList.subset_eq (=) (Cpure.fv all) instant) then
                  let var_case = pr_list Cprinter.string_of_spec_var (Cpure.fv all) in
                  let lhs_vars = pr_list Cprinter.string_of_spec_var (instant) in
            (* let () = print_string ( *)
                  (*     (List.fold_left (fun a c1-> a^" "^ (Cprinter.string_of_spec_var c1)) "\nall:" (Cpure.fv all))^"\n"^ *)
                  (*         (List.fold_left (fun a c1-> a^" "^ (Cprinter.string_of_spec_var c1)) "instant:" instant)^"\n")in *)
                  Debug.info_pprint ("WARNING : LHS vars: "^lhs_vars^"; Guards in pre/post use unknown vars:"^var_case) no_pos 
                      (* Error.report_error {  Err.error_loc = b.CF.formula_case_pos; *)
                      (* Err.error_text = "all guard free vars must be instantiated";}  *)
                in
                let rec p_check (p:Cpure.formula list):bool = match p with
                  | [] -> false 
                  | p1i::p2 -> 
                        let p1 = Cpure.mkAnd p1i ctx no_pos in
                        if (List.fold_left 
                            (fun a c->
                                if (x_add Tpdispatcher.is_sat_sub_no 12 (Cpure.mkAnd p1i c no_pos) sat_subno) then 
                                  if (x_add Tpdispatcher.is_sat_sub_no 13 (Cpure.mkAnd p1 c no_pos) sat_subno) then 
                                    (print_string ("in the context :"^(Cprinter.string_of_pure_formula ctx)^
                                        "\n the guards "^(Cprinter.string_of_pure_formula p1i)^"and"^
                                        (Cprinter.string_of_pure_formula c)^" are not disjoint\n");
                                    true)
                                  else a
                                else a) 
                            false p2 )
                        then true
                        else p_check p2 in
                
          let () = if (p_check r1) then 
                  Error.report_error {  Err.error_loc = b.CF.formula_case_pos;
                  Err.error_text = "the guards are not disjoint : "^(Cprinter.string_of_struc_formula f)^"\n";} in
                let nf = add_case_coverage in_pre ctx all b.CF.formula_case_pos in
                (*   let f_sat = Cpure.mkAnd ctx (Cpure.mkNot all None no_pos) no_pos in *)
                (*   let coverage_error =  *)
                (*       Tpdispatcher.is_sat_sub_no 11 f_sat sat_subno *)
                (*       (\*not (Tpdispatcher.simpl_imply_raw ctx all)*\) in *)
                (*   if coverage_error then *)
                (*     let simp_all = TP.pairwisecheck f_sat in *)
          (*     (\* let () = Debug.info_hprint (add_str "case pure" Cprinter.string_of_pure_formula) all no_pos in *\) *)
          (*     let () = Debug.info_pprint "WARNING : case construct has missing scenario" no_pos in *)
          (*     let () = Debug.info_hprint (add_str "Found : " Cprinter.string_of_pure_formula) all no_pos in *)
          (*     let () = Debug.info_hprint (add_str "Added : " Cprinter.string_of_pure_formula) simp_all no_pos in *)
                (*     [(simp_all,(CF.mkEFalse (CF.mkFalseFlow) no_pos))] *)
                (*     (\* let s = (Cprinter.string_of_struc_formula f) in *\) *)
                (*     (\* Error.report_error {  Err.error_loc = b.CF.formula_case_pos; *\) *)
                (*     (\* Err.error_text = "the guards don't cover the whole domain for : "^s^"\n";} *\) *)
                (*   else [] *)
                (* in *)
                let new_br = List.map (fun (c1,c2)->(c1,struc_case_coverage in_pre instant (CP.mkAnd c1 ctx no_pos) c2)) b.CF.formula_case_branches 
                in CF.ECase {b with CF.formula_case_branches = new_br@nf}
          | CF.EInfer b -> 
                begin
                  let nf = (struc_case_coverage in_pre instant ctx b.CF.formula_inf_continuation)
                  in CF.EInfer { b with CF.formula_inf_continuation = nf}
                end
          | CF.EList b -> 
                CF.EList (List.map (fun (l,c) -> (l,struc_case_coverage in_pre instant ctx c)) b) 
  in struc_case_coverage true instant (CP. mkTrue no_pos) f

and trans_var p (tlist: spec_var_type_list) pos =
  let pr = pr_var_prime in
  Debug.no_1 "trans_var" pr Cprinter.string_of_spec_var (fun _ -> trans_var_x p tlist pos) p

(* TODO WN : need to test how type checking handle # vars *)
and trans_var_x (ve, pe) (tlist: spec_var_type_list) pos =
  (* An Hoa [23/08/2011] Variables with "#" should not be considered.*)
  if (ve.[0] = '#') then
    CP.SpecVar (UNK,"_2_",Unprimed)
        (* if (is_dont_care_var ve) then  *)
        (*   CP.SpecVar (UNK,"_",Unprimed) *)
  else (* An Hoa : END *)
    try
      let ve_info = snd(List.find (fun (v,en)->v=ve) tlist)
      in
      (match ve_info.sv_info_kind with
          (* | UNK -> *)
          (*       Err.report_error *)
          (*           { *)
          (*               Err.error_loc = pos; *)
          (*               Err.error_text = "couldn't infer type for " ^ ve^(match pe with |Unprimed->""|Primed -> "'")^" in "^(string_of_tlist tlist)^"\n"; *)
          (*           } *)
        | t -> CP.SpecVar (t, ve, pe)

      )
    with Not_found ->   
        (* relaxing type inferring for smt-compete *)
        CP.SpecVar (UNK, ve, pe)
            (* if !Globals.smt_compete_mode then CP.SpecVar (UNK, ve, pe) *)
            (* else *)
            (* Err.report_error *)
            (*     { *)
            (*         Err.error_loc = pos; *)
            (*         Err.error_text = "type table does not contain an entry for " ^ ve^(match pe with |Unprimed->""|Primed -> "'")^" in "^(string_of_tlist tlist)^"\n, could it be an unused var?\n"; *)
            (*     } *)
            
and trans_var_safe (ve, pe) et tlist pos =
  (* An Hoa [23/08/2011] Variables with "#" should not be considered.*)
  if (ve.[0] = '#') 
  then   CP.SpecVar (UNK,"_3_",Unprimed)
    (* if (is_dont_care_var ve) then  *)
    (*   CP.SpecVar (UNK,"_",Unprimed) *)
  else (* An Hoa : END *)
    try
      let ve_info = snd(List.find (fun (v,en)->v=ve) tlist)
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
          let xpure_pre2_prim = Cvutil.xpure_consumed_pre prog b.CF.formula_struc_base in
          let new_pf = Cpure.mkAnd pf (Cpure.mkExists b.CF.formula_struc_exists xpure_pre2_prim None no_pos) no_pos in
          CF.EBase{b with CF.formula_struc_continuation = map_opt (helper new_pf) b.CF.formula_struc_continuation;}
    | CF.EAssume b -> 
          let f = CF.formula_of_pure_N pf no_pos in
          CF.EAssume {b with 
              CF.formula_assume_simpl = CF.normalize 2 b.CF.formula_assume_simpl f no_pos;
              CF.formula_assume_struc = CF.normalize_struc b.CF.formula_assume_struc (CF.mkBase_rec f None no_pos);}
    | CF.EInfer b -> CF.EInfer {b with CF.formula_inf_continuation = helper pf b.CF.formula_inf_continuation;}
    | CF.EList b -> CF.EList (map_l_snd (helper pf) b)
  in
  helper (Cpure.mkTrue no_pos) f

and add_pre prog f =
  let pr = Cprinter.string_of_struc_formula in
  Debug.no_1 "add_pre"  pr pr (add_pre_x prog) f 

and trans_copy_spec_4caller_x copy_params sf=
  let convert_to_L hf=
    match hf with
      | CF.DataNode dn ->
            (* let () = Debug.info_hprint (add_str "dn.CF.h_formula_data_node" !CP.print_sv) dn.CF.h_formula_data_node no_pos in *)
            if CP.mem_svl dn.CF.h_formula_data_node copy_params then
              CF.DataNode {dn with
                  CF.h_formula_data_imm = CP.ConstAnn(Lend);
                  CF.h_formula_data_param_imm = List.map (fun _ -> CP.ConstAnn(Lend)) dn.CF.h_formula_data_param_imm;
              }
            else
              hf
      | CF.ViewNode dn ->
            if CP.mem_svl dn.CF.h_formula_view_node copy_params then
              CF.ViewNode {dn with CF.h_formula_view_imm = CP.ConstAnn(Lend); }
            else
              hf
      | _ -> hf
  in
  let drop_heapsC hf=
    match hf with
      | CF.DataNode dn ->
            if CP.mem_svl dn.CF.h_formula_data_node copy_params then
              CF.HEmp
            else
              hf
      | CF.ViewNode dn ->
            if CP.mem_svl dn.CF.h_formula_view_node copy_params then
              CF.HEmp
            else
              hf
      | _ -> hf
  in
  let rec helper (f:CF.struc_formula): CF.struc_formula =
    match f with
      | CF.ECase b -> CF.ECase{b with CF.formula_case_branches =  List.map (fun (c1,c2)->(c1,(helper c2))) b.CF.formula_case_branches;}
      | CF.EBase b ->
            (*@L for @C*)
            CF.EBase{b with
                CF.formula_struc_base = CF.formula_trans_heap_node convert_to_L b.CF.formula_struc_base;
                CF.formula_struc_continuation = map_opt helper b.CF.formula_struc_continuation;}
      | CF.EAssume b ->
            (*remove heaps of @C*)
            CF.EAssume {b with
                CF.formula_assume_simpl = CF.formula_trans_heap_node drop_heapsC b.CF.formula_assume_simpl ;
                CF.formula_assume_struc = helper b.CF.formula_assume_struc ;}
      | CF.EInfer b -> CF.EInfer {b with CF.formula_inf_continuation = helper b.CF.formula_inf_continuation;}
      | CF.EList b ->
            CF.EList (map_l_snd helper b)
  in
  helper sf

and trans_copy_spec_4caller copy_params sf=
  let pr = Cprinter.string_of_struc_formula in
  Debug.no_2 "trans_copy_spec_4caller" !Cpure.print_svl pr pr trans_copy_spec_4caller_x copy_params sf
      
and trans_I2C_struc_formula i (prog : I.prog_decl) (prepost_flag:bool) (quantify : bool) (fvars : ident list) (f0 : IF.struc_formula) 
      (tlist:spec_var_type_list) (check_self_sp:bool) (*disallow self in sp*) (check_pre:bool) : (spec_var_type_list*CF.struc_formula) = 
  let prb = string_of_bool in
  let pr_out (_, f) = Cprinter.string_of_struc_formula f in
  (* Debug.no_5_loop    *)
  Debug.no_eff_5_num  i
      "trans_I2C_struc_formula" [true] string_of_tlist prb (add_str "check_pre" prb) Cprinter.str_ident_list 
      (add_str "Input Struc:" Iprinter.string_of_struc_formula) 
      (add_str "Output Struc:" pr_out)
      (fun _ _ _ _ _ -> trans_I2C_struc_formula_x prog prepost_flag quantify  fvars f0 tlist check_self_sp (check_pre:bool)) 
      tlist (* type table *) quantify (* quantified flag *) check_pre
      fvars (* free vars *) f0 (*struc formula *)

and trans_I2C_struc_formula_x (prog : I.prog_decl) (prepost_flag:bool) (quantify : bool) (fvars : ident list)
      (f0 : IF.struc_formula) (tlist:spec_var_type_list) (check_self_sp:bool) (check_pre:bool): (spec_var_type_list*CF.struc_formula) = 
  let rec trans_struc_formula (fvars : ident list) (tl:spec_var_type_list) (f0 : IF.struc_formula) : (spec_var_type_list*CF.struc_formula) = (
      match f0 with
        | IF.EAssume b ->   (*add res, self*)
              let (n_tl,f) = trans_formula prog true (self::res_name::eres_name::fvars) false b.IF.formula_assume_simpl tl true in
              let (n_tl,f_struc) = trans_I2C_struc_formula_x prog prepost_flag true (res_name::eres_name::fvars) b.IF.formula_assume_struc n_tl check_self_sp false in
              (n_tl,CF.mkEAssume [] f f_struc b.IF.formula_assume_lbl b.IF.formula_assume_ensures_type)
        | IF.ECase b-> (
              let rec aux tlist clist = (
                  match clist with
                    | []->(tlist,[])
                    | (c1,c2)::tl ->
                          let cf1 = trans_pure_formula c1 tlist in
                          let (n_tl,cf2) = trans_struc_formula fvars tlist c2 in
                          let f1 = Cpure.arith_simplify 2 cf1 in
                          let f2 = cf2 in
                          let (n_tlist, n_cl) = aux n_tl tl in
                          (n_tlist, (f1, f2)::n_cl)
              ) in  
              let (n_tl,n_cl) = aux tl b.IF.formula_case_branches in 
              let cf = CF.ECase { (* CF.formula_case_exists = []; *)
                  CF.formula_case_branches = n_cl;
                  CF.formula_case_pos = b.IF.formula_case_pos} in
              (n_tl,cf)
          )
        | IF.EBase b-> (
              let (n_tl,nc) = (
                  match b.IF.formula_struc_continuation with
                    | None -> (tl,None)
                    | Some x -> let (n_tl,cf) = trans_struc_formula (fvars @ (fst (List.split(IF.heap_fv b.IF.formula_struc_base)))) tl x in 
                      (n_tl,Some cf) 
              ) in
              let (n_tl,nb) = trans_formula prog quantify fvars false b.IF.formula_struc_base n_tl false in
              let ex_inst = List.map (fun c-> trans_var_safe c UNK n_tl b.IF.formula_struc_pos) b.IF.formula_struc_explicit_inst in
              let ext_impl = List.map (fun c-> trans_var_safe c UNK n_tl b.IF.formula_struc_pos) b.IF.formula_struc_implicit_inst in
              let ext_exis = List.map (fun c-> trans_var_safe c UNK n_tl b.IF.formula_struc_pos) b.IF.formula_struc_exists in
              let cf = CF.EBase { CF.formula_struc_explicit_inst = ex_inst;
              CF.formula_struc_implicit_inst = ext_impl;
              CF.formula_struc_exists = ext_exis;
              CF.formula_struc_base = nb;
              CF.formula_struc_is_requires = b.IF.formula_struc_is_requires;
              CF.formula_struc_continuation = nc;
              CF.formula_struc_pos = b.IF.formula_struc_pos} in
              (n_tl,cf)    
          )
        | IF.EInfer b -> 
              (* TODO : check iv - fvars = {} *)
              let pos = b.IF.formula_inf_pos in
              let ivs = b.IF.formula_inf_vars in
              let (n_tl,ct) = trans_struc_formula fvars tl b.IF.formula_inf_continuation in
              let new_ivs = ident_list_to_spec_var_list ivs n_tl prog in
              (* TODO : any warning below should be fixed *)
              let ivs_unk = List.filter (fun v -> (CP.type_of_spec_var v)==UNK) new_ivs in
              if ivs_unk!=[] then 
                begin
                  let s = (Cprinter.string_of_spec_var_list ivs_unk) in
            print_endline_quiet ("WARNING (must fix): Vars from"^s^"has type UNK")
                end;
              if ivs_unk!=[] then
                Err.report_error { Err.error_loc = pos;
                Err.error_text = ("infer vars with unknown type "^(Cprinter.string_of_spec_var_list ivs_unk)) }
              else
                (n_tl, CF.EInfer {
                    (* CF.formula_inf_tnt = b.IF.formula_inf_tnt; *)
                    CF.formula_inf_obj = b.IF.formula_inf_obj;
                    CF.formula_inf_post = b.IF.formula_inf_post;
                    CF.formula_inf_xpost = b.IF.formula_inf_xpost;
                    CF.formula_inf_transpec = b.IF.formula_inf_transpec;
                    CF.formula_inf_vars = new_ivs;
                    CF.formula_inf_continuation = ct;
                    CF.formula_inf_pos = pos})
        | IF.EList b ->
              let rec aux tlist clist = (
                  match clist with
                    | []-> (tlist,[])
                    | (c,str)::tl -> 
                          let (n_tl,cf) = trans_struc_formula fvars tlist str in
                          let (n_tl,n_cl) = aux n_tl tl in
                          (n_tl,(c,cf)::n_cl)
              ) in
              if is_empty b then 
                (* TNT: Add default spec "requires true ensures true;" *)
                (* if there is no given spec                           *)
                (tl, CF.mkETrue_ensures_True (CF.mkNormalFlow ()) no_pos)
              else
                let (n_tl,n_cl) = aux tl b in
                (n_tl,CF.mkEList_no_flatten2 n_cl)
  ) in
  let n_tl =gather_type_info_struc_f prog f0 tlist in
  let (n_tl,r) = trans_struc_formula fvars n_tl f0 in
  let () = x_tinfo_hp (add_str "fvars" (pr_list pr_id)) fvars no_pos in
  let cfvhp1 = List.map (fun c-> trans_var_safe (c,Primed) UNK n_tl (IF.pos_of_struc_formula f0)) fvars in
  let cfvhp2 = List.map (fun sv -> match sv with | CP.SpecVar (t,v,_) -> CP.SpecVar(t,v,Unprimed)) cfvhp1 in
  let cfvhp = (cfvhp1@cfvhp2) in
  let r = trans_case_coverage prepost_flag cfvhp r in
  let tmp_vars  =  (CF.struc_post_fv r) in 
  let post_fv = List.map CP.name_of_spec_var tmp_vars in
  let () = Debug.ninfo_hprint (add_str "tmp_vars" (!CP.print_svl)) tmp_vars no_pos in
  let pre_fv = List.map CP.name_of_spec_var (Gen.BList.difference_eq (=) (CF.struc_fv r) tmp_vars) in
  let pr_s_v_l = pr_list pr_id in
  (* WN : BUG why isn't this trace working when ho is turned on? *)
  Debug.ninfo_hprint (add_str "pre_fv" pr_s_v_l) pre_fv no_pos;
  Debug.ninfo_hprint (add_str "post_fv" pr_s_v_l) post_fv no_pos;
  let r = if check_self_sp && ((List.mem self pre_fv) || (List.mem self post_fv)) then
    Err.report_error { Err.error_loc = CF.pos_of_struc_formula r; Err.error_text ="self is not allowed in pre/postcondition";}
  else if check_pre && (List.mem res_name pre_fv) then
    Err.report_error{ Err.error_loc = CF.pos_of_struc_formula r; Err.error_text = "res is not allowed in precondition";}
  else r  in
  (* let r = add_param_ann_constraints_struc r in *)
  (n_tl, r)

(* checks if two lists of annotation can be joint together. If so, it returns the list resulting after the combination of the input lists *)
(* and join_ann (ann1: CP.ann list) (ann2: CP.ann list): bool * (CP.ann list) = *)
(*   match ann1, ann2 with *)
(*     | [], [] -> (true, []) *)
(*     | (CP.ConstAnn(Accs))::t1, a::t2  *)
(*     | a::t1, (CP.ConstAnn(Accs))::t2 -> let compatible, new_ann = join_ann t1 t2 in *)
(*                   (true && compatible, a::new_ann) *)
(*     | _ -> (false, []) *)

(* Moved to mem.ml and called during entailment now *)
(* and check_node_compatibility (n1: CF.h_formula) (n2: CF.h_formula): CP.spec_var list * CP.spec_var list =  *)
(* let helper n1 n2 =  *)
(*   match n1 with *)
(*     | CF.DataNode ->  *)

(*     | CF.Star -> false *)
(*     | _ -> false *)
(*
  and compact_nodes_with_same_name_in_h_formula_x (f: CF.h_formula) (aset: CP.spec_var list list) : CF.h_formula = 
  if not (!Globals.allow_field_ann) then f else
  match f with
  | CF.Star {CF.h_formula_star_h1 = h1;
  CF.h_formula_star_h2 = h2;
  CF.h_formula_star_pos = pos } ->
  let rec helper h1 h2 = 
  match h1 with
  | CF.DataNode { CF.h_formula_data_name = name1;
  CF.h_formula_data_node = v1;
  CF.h_formula_data_param_imm = param_ann1;
  } ->
  let aset_sv = Context.get_aset aset v1 in
  let res_h1, res_h2 = 
  match h2 with
  | CF.DataNode { CF.h_formula_data_name = name2;
  CF.h_formula_data_node = v2;
  CF.h_formula_data_param_imm = param_ann2; } ->
(* h1, h2 nodes; check if they can be join into a single node. If so, h1 will contain the updated annotations, while 
  h2 will be replaced by "true". Otherwise both data nodes will remain unchanged *)
  if (String.compare name1 name2 == 0) && ((CP.mem v2 aset_sv) || (CP.eq_spec_var v1 v2)) then
  let compatible, new_param_imm = join_ann param_ann1 param_ann2 in
  match h1 with (* this match is to avoid the rewriting of all h1 parameters*)
  | CF.DataNode h -> 
  if (compatible == true) then 
  (CF.DataNode {h with CF.h_formula_data_param_imm = new_param_imm}, CF.HTrue)
  else (h1, h2)
  | _ -> (h1, h2) (* will never reach this branch *)
  else (h1, h2) (* h2 is not an alias of h1 *) 
  | CF.Star {CF.h_formula_star_h1 = h21;
  CF.h_formula_star_h2 = h22;
  CF.h_formula_star_pos = pos2 } ->
(* h1 node, h2 star formula. Try to unify h1 with nodes on the left hand side of h2 star-formula, resulting in a new h1
  which will be checked against the right side of h2 star-formula. This will result in updated part of h2 right and left hand side of '*'.
  Rejoin h2 star fomula, and apply compact_nodes_with_same_name_in_h_formula_x on the updated h2 to check for other groups of aliases.
*)
  let h31, h32 = helper h1 h21 in
  let h41, h42 = helper h31 h22 in
  let new_h2 = CF.mkStarH h32 h42 pos2 10 in
  let new_h2 = compact_nodes_with_same_name_in_h_formula_x new_h2 aset in 
  (h41, new_h2)
  | _ -> (h1,h2) in
  (res_h1, res_h2)
  | CF.Star {CF.h_formula_star_h1 = h11;
  CF.h_formula_star_h2 = h12;
  CF.h_formula_star_pos = pos1 } ->
  let new_h2 = CF.mkStarH h12 h2 pos1 11 in
  let h31, h32 = helper h11 new_h2 in
  let new_h2 = compact_nodes_with_same_name_in_h_formula_x h32 aset in 
  (h31, new_h2)
  | _ ->    (h1, h2)
  in
  let h1,h2 = helper h1 h2 in
  let res = CF.mkStarH h1 h2 pos 12 in
  res
  | CF.Conj h  -> CF.Conj {h with CF.h_formula_conj_h1 = compact_nodes_with_same_name_in_h_formula_x h.CF.h_formula_conj_h1 aset;
  CF.h_formula_conj_h2 = compact_nodes_with_same_name_in_h_formula_x h.CF.h_formula_conj_h2 aset}
  | CF.Phase h ->  CF.Phase {h with CF.h_formula_phase_rd = compact_nodes_with_same_name_in_h_formula_x h.CF.h_formula_phase_rd aset;
  CF.h_formula_phase_rw = compact_nodes_with_same_name_in_h_formula_x h.CF.h_formula_phase_rw aset}
  | _ -> f

  and compact_nodes_with_same_name_in_h_formula (f: CF.h_formula) (aset: CP.spec_var list list) : CF.h_formula =
  let pr = Cprinter.string_of_h_formula in 
  let pr_sv = pr_list Cprinter.string_of_spec_var_list in
  Debug.no_2 "compact_nodes_with_same_name_in_h_formula" pr pr_sv pr (fun _ _ -> compact_nodes_with_same_name_in_h_formula_x f aset) f aset


  and compact_nodes_with_same_name_in_formula (cf: CF.formula): CF.formula =
  match cf with
  | CF.Base f   -> CF.Base { f with
  CF.formula_base_heap = compact_nodes_with_same_name_in_h_formula f.CF.formula_base_heap
(* (Context.comp_aliases f.CF.formula_base_pure); *)
  (Csvutil.comp_aliases f.CF.formula_base_pure);
  }
  | CF.Or f     -> CF.Or { f with 
  CF.formula_or_f1 = compact_nodes_with_same_name_in_formula f.CF.formula_or_f1; 
  CF.formula_or_f2 = compact_nodes_with_same_name_in_formula f.CF.formula_or_f2; }
  | CF.Exists f -> CF.Exists { f with
  CF.formula_exists_heap = compact_nodes_with_same_name_in_h_formula f.CF.formula_exists_heap (Context.comp_aliases f.CF.formula_exists_pure); }

  and compact_nodes_with_same_name_in_struc_x (f: CF.struc_formula): CF.struc_formula = (* f *)
  if not (!Globals.allow_field_ann ) then f
  else
  match f with
  | CF.EOr sf            -> CF.EOr { sf with 
  CF.formula_struc_or_f1 = compact_nodes_with_same_name_in_struc_x sf.CF.formula_struc_or_f1;
  CF.formula_struc_or_f2 = compact_nodes_with_same_name_in_struc_x  sf.CF.formula_struc_or_f2;} 
  | CF.EList sf          -> CF.EList  (map_l_snd compact_nodes_with_same_name_in_struc_x sf) 
  | CF.ECase sf          -> CF.ECase {sf with CF.formula_case_branches = map_l_snd compact_nodes_with_same_name_in_struc_x sf.CF.formula_case_branches;} 
  | CF.EBase sf          -> CF.EBase {sf with
  CF.formula_struc_base = x_add_1 Mem.compact_nodes_with_same_name_in_formula sf.CF.formula_struc_base;
  CF.formula_struc_continuation = map_opt compact_nodes_with_same_name_in_struc_x sf.CF.formula_struc_continuation; }
  | CF.EAssume (x, f, y)-> CF.EAssume (x,(Mem.compact_nodes_with_same_name_in_formula f),y)
  | CF.EInfer sf         -> CF.EInfer {sf with CF.formula_inf_continuation = compact_nodes_with_same_name_in_struc_x sf.CF.formula_inf_continuation} (* (andreeac) ?? *)

  and compact_nodes_with_same_name_in_struc (f: CF.struc_formula): CF.struc_formula = 
  let pr = Cprinter.string_of_struc_formula in
  Debug.no_1 "compact_nodes_with_same_name_in_struc" pr pr (fun _ -> compact_nodes_with_same_name_in_struc_x f ) f
*)
and trans_formula (prog : I.prog_decl) (quantify : bool) (fvars : ident list) sep_collect
      (f0 : IF.formula) tlist (clean_res:bool) : (spec_var_type_list*CF.formula) =
  let prb = string_of_bool in
  let pr_out (_, f) = Cprinter.string_of_formula f in
  Debug.no_eff_5 "trans_formula" [true]
      string_of_tlist (add_str "quantify" prb) (add_str "cleanres" prb)
      Cprinter.str_ident_list Iprinter.string_of_formula
      pr_out
      (fun _ _ _ _ _ -> trans_formula_x (prog : I.prog_decl) (quantify : bool) (fvars : ident list) sep_collect
          (f0 : IF.formula) tlist (clean_res:bool)) tlist quantify clean_res fvars f0

and trans_formula_x (prog : I.prog_decl) (quantify : bool) (fvars : ident list) sep_collect (f0 : IF.formula) tlist (clean_res:bool) : (spec_var_type_list*CF.formula) =
  let helper_one_formula (f:IF.one_formula) tl =
    if sep_collect then 
      let n_tl = gather_type_info_pure prog f.IF.formula_pure tl in
      gather_type_info_heap prog f.IF.formula_heap n_tl
    else tl in
  let rec helper f0 tl =
    match f0 with
      | IF.Or b-> 
            let (n_tl,n_f1)= helper b.IF.formula_or_f1 tl in
            let (n_tl,n_f2) = helper b.IF.formula_or_f2 n_tl in
            (n_tl,CF.mkOr n_f1 n_f2 b.IF.formula_or_pos)
      | IF.Base ( {
            IF.formula_base_heap = hh;
            IF.formula_base_pure = p;
            IF.formula_base_vperm = vp;
            IF.formula_base_flow = fl;
            IF.formula_base_and = a;
            IF.formula_base_pos = pos} as fb) ->(
            let (n_tl,rl) = res_retrieve tl clean_res fl in
            let n_tl = 
              if sep_collect then
                let n_tl = gather_type_info_pure prog p n_tl in
                gather_type_info_heap prog hh n_tl
              else n_tl in
            let todo_unk = List.map (fun x -> helper_one_formula x tl) a in
            (* transform bexpr *)
            (* let nh, ps = IF.transform_bexp_hf prog h in *)
            (* let np = if ps = [] then p else List.fold_left (fun r p1 -> Ipure.mkAnd r p1 pos) p ps in *)
            (* let f1 = IF.Base {fb with IF.formula_base_heap = nh; *)
            (*     IF.formula_base_pure = np *)
            (* } in *)
            let (n_tl,ch, newvars) = linearize_formula prog f0 n_tl in
            let n_tlist = (
                if sep_collect then
                  if quantify then (
                      let rec copy_list fv tl = (
                          match fv with
                            | [] -> []
                            | h::t -> let (v,en) = List.find (fun (v,en) -> v=h) tl
                              in (v,en)::(copy_list t tl) 
                      ) in
                      let n_tl = copy_list fvars n_tl in
                      n_tl
                  ) else n_tl
                else n_tl
            ) in 
            (res_replace n_tlist rl clean_res fl, ch))
      | IF.Exists   {
            IF.formula_exists_qvars = qvars;
            IF.formula_exists_heap = h;
            IF.formula_exists_pure = p;
            IF.formula_exists_vperm = vp;
            IF.formula_exists_flow = fl;
            IF.formula_exists_and = a;
            IF.formula_exists_pos = pos} -> (
            let (n_tl,rl) = res_retrieve tl clean_res fl in
            let n_tl = (
                if sep_collect then 
                  let n_tl = gather_type_info_pure prog p n_tl in
                  gather_type_info_heap prog h n_tl
                else n_tl 
            ) in 
            let n_tl = List.fold_right helper_one_formula a n_tl in
            let f1 = IF.Base ( {
                IF.formula_base_heap = h;
                IF.formula_base_pure = p;
                IF.formula_base_vperm = vp;
                IF.formula_base_flow = fl;
                IF.formula_base_and = a;
                IF.formula_base_pos = pos; }) in
	    (* let () = print_string ("Cform f1: "^(Iprinter.string_of_formula f1) ^"\n" ) in *)
            (* transform bexp *)
            (* let nh, ps = IF.transform_bexp_hf prog h in *)
            (* let np = if ps = [] then p else List.fold_left (fun r p1 -> Ipure.mkAnd r p1 pos) p ps in *)
            (* let f2 = IF.Base ( { *)
            (*     IF.formula_base_heap = nh; *)
            (*     IF.formula_base_pure = np; *)
            (*     IF.formula_base_flow = fl; *)
            (*     IF.formula_base_and = a; *)
            (*     IF.formula_base_pos = pos; }) in *)
            let (n_tl,ch, newvars) = linearize_formula prog f1 n_tl in
            (* let () = print_string ("Cform ch: "^(Cprinter.string_of_formula ch) ^"\n" ) in *)
            let qsvars = List.map (fun qv -> trans_var qv n_tl pos) qvars in
            let newvars = List.map (fun qv -> trans_var qv n_tl pos) newvars in
            let ch = CF.push_exists (qsvars @ newvars) ch in
            let n_tlist = (
                if sep_collect && quantify then
                  let fvars = (List.map fst qvars) @ fvars in
                  let rec copy_list fv tl = (
                      match fv with
                        | [] -> []
                        | h::t -> 
                              let (v,en) = List.find (fun (v,en) -> v=h) tl
                              in (v,en)::(copy_list t tl) 
                  ) in
                  copy_list fvars n_tl
                else n_tl
            ) in
            (res_replace n_tlist rl clean_res fl, ch)) 
  in (* An Hoa : Add measure to combine partial heaps into a single heap *)
  let (n_tl,cf) = helper f0 tlist in
  let pr = Cprinter.string_of_formula in
  let () = x_tinfo_hp (add_str "cf" pr) cf no_pos in
  (*let cf = x_add_1 Mem.compact_nodes_with_same_name_in_formula cf in*)
  (*TO CHECK: temporarily disabled*) 
  (* let cf = CF.merge_partial_heaps cf in (\*ENABLE THIS for partial fields*\) *)
  (* let () = print_string ("\nbefore ann: "^ Cprinter.string_of_formula cf) in *)
  let cf = if (!Globals.allow_field_ann) then add_param_ann_constraints_formula cf else cf in
  (* let () = print_string ("\nafter ann: "^ Cprinter.string_of_formula cf) in *)
  (n_tl,cf)

and linearize_formula (prog : I.prog_decl)  (f0 : IF.formula) (tlist : spec_var_type_list) 
                      : (spec_var_type_list * CF.formula * (Globals.ident * VarGen.primed) list) =
  let pr1 prog = (add_str "view_decls" pr_v_decls) prog.I.prog_view_decls in
  let prR (_,f,qvar) = (pr_pair Cprinter.string_of_formula (add_str "\n qvars:" (pr_list (pr_id fst)))) (f,qvar) in
  Debug.no_3 "linearize_formula" pr1 Iprinter.string_of_formula string_of_tlist 
      prR linearize_formula_x prog f0 tlist

and linearize_formula_x (prog : I.prog_decl)  (f0 : IF.formula) (tlist : spec_var_type_list) 
                        : (spec_var_type_list * CF.formula * (Globals.ident * VarGen.primed) list) =
  let rec match_exp (hargs : (IP.exp * LO.t) list) pos : (CP.view_arg list) =
    match hargs with
      | (e, _) :: rest ->
            let e_hvars = match e with
              | IP.Var ((ve, pe), pos_e) ->   [CP.sv_to_view_arg (trans_var_safe (ve, pe) UNK tlist pos_e)]
              | IP.AConst (a, pos_e )    -> [CP.imm_to_view_arg a]
                    (* | IP.Ann_Exp (IP.AConst ((ve, pe), pos_e ), t, _) -> CP *)
              | IP.Ann_Exp (IP.Var ((ve, pe), pos_e ), t, l) -> [CP.sv_to_view_arg (trans_var_safe (ve, pe) t tlist pos_e)] (*annotated self*)
              | IP.Bptriple ((ec,et,ea), pos_e) ->
                    let apply_one e =
                      (match e with
                        | IP.Var ((ve, pe), pos_e) -> CP.sv_to_view_arg (trans_var_safe (ve, pe) UNK tlist pos_e)
                        | _ -> report_error (IF.pos_of_formula f0) ("linearize_formula : match_exp : Expecting Var in Bptriple"^(Iprinter.string_of_formula f0)))
                    in
                    List.map apply_one [ec;et;ea]
              | _ -> let s = (Iprinter.string_of_formula_exp e) in
                report_error (IF.pos_of_formula f0) ("malfunction with float out exp: "^s) in
            (* (Iprinter.string_of_formula f0))in *)
            let rest_hvars = match_exp rest pos in
            let hvars = e_hvars @ rest_hvars in
            hvars
      | [] -> [] in
  let expand_dereference_node (f: IF.h_formula) pos : (IF.h_formula * (Globals.ident * VarGen.primed) list) = (
      match f with
        | IF.HeapNode {IF.h_formula_heap_node = n;
          IF.h_formula_heap_name = c;
          IF.h_formula_heap_deref = deref;
          IF.h_formula_heap_derv = dr;
          IF.h_formula_heap_split = split;
          IF.h_formula_heap_imm = imm;
          IF.h_formula_heap_imm_param = ann_param;
          IF.h_formula_heap_perm = perm; (*LDK*)
          IF.h_formula_heap_arguments = exps;
          IF.h_formula_heap_ho_arguments = ho_exps;
          IF.h_formula_heap_full = full;
          IF.h_formula_heap_pseudo_data = pd;
          IF.h_formula_heap_with_inv = inv;
          IF.h_formula_heap_pos = l;
          IF.h_formula_heap_label = pi;} -> (
              if (c = Parser.generic_pointer_type_name) then
                report_error l "expand_dereference_node: unexpected generic pointer"
              else if (deref > 0) then (
                  let base_heap_id = (
                      try
                        let vdef = I.look_up_view_def_raw 9 prog.I.prog_view_decls c in
                        if vdef.I.view_data_name = "" then 
                          (fill_view_param_types vdef; vdef.I.view_data_name)
                        else vdef.I.view_data_name
                      with _ -> c
                  ) in
                  let expanded_heap, newvars = (
                      match base_heap_id with
                        | "int"
                        | "bool"
                        | "float"
                        | "void" -> (
                              (* dereference to a basic type *)
                              if (deref = 1) then (
                                  let base_heap_id = base_heap_id ^ "_star" in
                                  let hf = IF.mkHeapNode n base_heap_id ho_exps 0 dr split imm full inv pd perm exps ann_param pi l in
                                  (hf, [])
                              )
                              else (
                                  let new_vars = ref [] in
                                  let base_heap_id = base_heap_id ^ "_star" in
                                  let s = ref base_heap_id in
                                  let fresh_var = "deref_" ^ (fresh_name ()) in
                                  new_vars := !new_vars @ [(fresh_var, Unprimed)];
                                  let p = (fresh_var, Unprimed) in
                                  let p1 = ref p in
                                  let p2 = ref (IF.P.Var (("", Unprimed), l)) in
                                  let heaps = ref [] in
                                  for i = 3 to deref do
                                    p2 := IF.P.Var (!p1, l);
                                      let fresh_var = "deref_" ^ (fresh_name ()) in
                                      new_vars := !new_vars @ [(fresh_var, Unprimed)];
                                      p1 := (fresh_var, Unprimed);
                                      s := !s ^ "_star";
                                      let h = IF.mkHeapNode !p1 !s ho_exps 0 dr split imm inv full pd perm [!p2] ann_param None l in
                                      heaps := !heaps @ [h];
                                  done;
                                  s := !s ^ "_star";
                                  let e = IF.P.Var (!p1, l) in
                                  let h1 = IF.mkHeapNode n !s ho_exps 0 dr split imm full inv pd perm [e] ann_param None l in
                  let h2 = IF.mkHeapNode p base_heap_id ho_exps 0 dr split imm full inv pd perm (exps) ann_param pi l in
                                  let hf = List.fold_left (fun f1 f2 -> IF.mkStar f1 f2 l) h1 (!heaps @ [h2]) in
                                  (hf, !new_vars)
                              )
                          )
                        | _ -> (
                              (* dereference to a data structure *)
                              let new_vars = ref [] in
                              let s = ref base_heap_id in
                              let fresh_var = "deref_" ^ (fresh_name ()) in
                              new_vars := !new_vars @ [(fresh_var, Unprimed)];
                              let p = (fresh_var, Unprimed) in
                              let p1 = ref p in
                              let p2 = ref (IF.P.Var (("", Unprimed), l)) in
                              let heaps = ref [] in
                              for i = 2 to deref do
                                p2 := IF.P.Var (!p1, l);
                                  let fresh_var = "deref_" ^ (fresh_name ()) in
                                  new_vars := !new_vars @ [(fresh_var, Unprimed)];
                                  p1 := (fresh_var, Unprimed);
                                  s := !s ^ "_star";
                                  let h = IF.mkHeapNode !p1 !s ho_exps 0 dr split imm full inv pd perm [!p2] ann_param None l in
                                  heaps := !heaps @ [h];
                              done;
                              s := !s ^ "_star";
                              let e = IF.P.Var (!p1, l) in
                let offe = IF.P.Var (("o", Unprimed), l) in
                let h1 = IF.mkHeapNode n !s ho_exps 0 dr split imm full inv pd perm [e;offe] ann_param None l in
                let h2 = IF.mkHeapNode p c ho_exps 0 dr split imm full inv pd perm (exps) ann_param pi l in
                              let hf = List.fold_left (fun f1 f2 -> IF.mkStar f1 f2 l) h1 (!heaps @ [h2]) in
                              (hf, !new_vars)
                          )
                  ) in
                  (* return *)
                  (expanded_heap, newvars)
              )
              else
                report_error l "expand_dereference_node: expect a dereference HeapNode"
          )
        | _ -> report_error pos "expand_dereference_node: expect a HeapNode"
  ) in
  let rec linearize_heap (f : IF.h_formula) pos (tl:spec_var_type_list)
        : (( CF.h_formula (* *  (MCP.mix_formula list)  *)) * CF.t_formula * (Globals.ident * VarGen.primed) list * (spec_var_type_list)) = ( 
            (* andreeac: TODO add the constraints in a pair with  CF.h_formula *)
    let res = ( (*let () = print_string("H_formula: "^(Iprinter.string_of_h_formula f)^"\n") in*)
                match f with
                  | IF.HeapNode2 h2 -> report_error (IF.pos_of_formula f0) "malfunction with convert to heap node"
                  | IF.ThreadNode {IF.h_formula_thread_node = (v, p);
                    IF.h_formula_thread_name = c;
                    IF.h_formula_thread_resource = rsr;
                    IF.h_formula_thread_delayed = dl;
                    IF.h_formula_thread_perm = perm; (*LDK*)
                    IF.h_formula_thread_pos = pos;
                    IF.h_formula_thread_label = pi;} ->
                        let dataNode = IF.mkHeapNode (v,p) c [] 0 false SPLIT0 (Ipure.ConstAnn(Mutable)) false false false perm [] [] pi pos in
                        let dataNode2, t_f, n_tl1, sv1 = linearize_heap dataNode pos tl in
                        let new_dl = trans_pure_formula dl tl in
                        let new_dl = Cpure.arith_simplify 5 new_dl in
                        let sv2, rsr2, n_tl2 = linearize_formula prog rsr tlist in
                        let newNode = CF.ThreadNode {
              CF.h_formula_thread_name = x_add CF.get_node_name 1 dataNode2;
                            CF.h_formula_thread_node = CF.get_node_var dataNode2;
                            CF.h_formula_thread_resource = rsr2;
                            CF.h_formula_thread_delayed = new_dl;
                            CF.h_formula_thread_perm = CF.get_node_perm dataNode2;
                            CF.h_formula_thread_derv = CF.get_node_derv dataNode2;
                            CF.h_formula_thread_split = CF.get_node_split dataNode2;
                            CF.h_formula_thread_origins = CF.get_node_origins dataNode2;
                            CF.h_formula_thread_original = CF.get_node_original dataNode2;
                            CF.h_formula_thread_pos = CF.get_node_pos dataNode2;
                            CF.h_formula_thread_label = CF.get_node_label dataNode2;}
                        in
                        (newNode,t_f,n_tl2,sv1@sv2)
                  | IF.HeapNode {IF.h_formula_heap_node = (v, p);
                    IF.h_formula_heap_name = c;
                    IF.h_formula_heap_deref = deref;
                    IF.h_formula_heap_derv = dr;
                    IF.h_formula_heap_split = split;
                    IF.h_formula_heap_imm = imm;
                    IF.h_formula_heap_imm_param = ann_param;
                    IF.h_formula_heap_perm = perm; (*LDK*)
                    IF.h_formula_heap_arguments = exps;
                    IF.h_formula_heap_ho_arguments = ho_exps;
                    IF.h_formula_heap_full = full;
                    IF.h_formula_heap_pos = pos;
                    IF.h_formula_heap_label = pi;} ->
            (* expand the dereference heap node first *)
                        let trans_f f tl = trans_formula prog false [] false f tl false in
            let (tl, ho_args) = List.fold_left (fun (tl, r) a -> 
              let (ntl, b) = trans_f a.IF.rflow_base tl in 
              (ntl, ({ CF.rflow_kind = a.IF.rflow_kind; 
                           CF.rflow_base = b; })::r)) 
              (tl, []) ho_exps in
                        let ho_args = List.rev ho_args in
                        if (deref > 0) then (
                            let (f1, newvars1) = expand_dereference_node f pos in
                            let n_tl = gather_type_info_heap prog f1 tl in
                            let hf, tf, newvars2, n_tl = linearize_heap f1 pos n_tl in
                            (hf, tf, newvars1 @ newvars2, n_tl)
                        )
                        else (
	    (* let () = print_endline ("geniric_pointer") in *)
                            (* An Hoa : Handle field access *)
                            (* ASSUMPTIONS detected: exps ARE ALL VARIABLES i.e. I.Var AFTER float_out_exp PRE-PROCESSING! *)
                            if (c = Parser.generic_pointer_type_name || String.contains v '.') then (
	      (* let () = print_endline ("geniric_pointer then") in *)
                                let tokens = Str.split (Str.regexp "\\.") v in
                                let field_access_seq = List.filter (fun x -> I.is_not_data_type_identifier prog.I.prog_data_decls x) tokens in
                                let field_access_seq = List.tl field_access_seq in (* get rid of the root pointer as well *)
                                let rootptr = List.hd tokens in
                                let rpsi = snd(List.find(fun (v,en)->v=rootptr) tl) in
                                let rootptr_type = rpsi.sv_info_kind in
                                let rootptr_type_name = match rootptr_type with
                                  | Named c1 ->
                                        (* if String.compare c1 "" = 0 then c else  *)c1
                                  | _ -> failwith ("[linearize_heap] " ^ rootptr ^ " must be a pointer.")
                                in
                                let rootptr, p = 
                                  let rl = String.length rootptr in
                                  if rootptr.[rl-1] = '\'' then
                                    (String.sub rootptr 0 (rl - 1), Primed)
                                  else
                                    (rootptr, Unprimed) in 
                                let field_offset = I.compute_field_seq_offset prog.I.prog_data_decls rootptr_type_name field_access_seq in
                                let num_ptrs = I.get_typ_size prog.I.prog_data_decls rootptr_type in
                                (* An Hoa : The rest are copied from the original code with modification to account for the holes *)
                                let labels = List.map (fun _ -> LO.unlabelled) exps in
                                let hvars = CP.view_arg_to_sv_list (match_exp (List.combine exps labels) pos) in
                                (* [Internal] Create a list [x,x+1,...,x+n-1] *)
                                let rec first_naturals n x = 
                                  if n = 0 then [] 
                                  else x :: (first_naturals (n-1) (x+1)) in
                                (* [Internal] Extends hvars with holes and collect the list of holes! *)
                                let rec extend_and_collect_holes vs offset num_ptrs = (
                                    let temp = first_naturals num_ptrs 0 in
                                    let numargs = List.length vs in
                                    let holes = List.fold_left (fun l i ->
                                        let d = i - offset in
                                        if (d < 0 || d >= numargs) then List.append l [i] else l
                                    ) [] temp in
                let () = Debug.info_hprint (add_str "holes" (pr_list string_of_int)) holes no_pos in
                let () = Debug.info_hprint (add_str "vs" (Cprinter.string_of_spec_var_list)) vs no_pos in
                let () = Debug.info_hprint (add_str "offset" string_of_int) offset no_pos in
                                    let newvs = List.map (fun i ->
                                        (* let v = List.nth vs (i - offset) in *)
                                        if (List.mem i holes) then 
                                          CP.SpecVar (UNK,"Anon"^fresh_trailer(),Unprimed)
                                        else List.nth vs (i - offset) 
                                    ) temp in
                                    (newvs,holes) 
                                ) in
                                (* [Internal] End of function <extend_and_collect_holes> *)
                                let hvars, holes = extend_and_collect_holes hvars field_offset num_ptrs in
              let () = Debug.ninfo_hprint (add_str "c" (pr_id)) c no_pos in
              let () = Debug.ninfo_hprint (add_str "rootptr" (pr_id)) rootptr_type_name no_pos in
              let () = Debug.ninfo_hprint (add_str "hvars" (pr_list Cprinter.string_of_typed_spec_var)) hvars no_pos in
                                let all_fields = I.look_up_all_fields_cname prog rootptr_type_name in
                                let pr1 = pr_list (fun (ti,_,_,_) -> pr_pair string_of_typ pr_id ti) in 
              let () = Debug.ninfo_hprint (add_str "all_fields" pr1) all_fields no_pos in
                                (* !!! hvars:[a:int,Anon_19:Unknown,Anon_20:Unknown] *)
                                (* !!! all_fields:[(int,p1.x),(int,p1.y),(pair,p2)] *)
                                let comb = Debug.catch_exc "astsimpl: hvars & all_fields" (List.combine hvars) all_fields in
                                let hvars = List.map (fun (CP.SpecVar(_,i,p),((t,_),_,_,_)) -> CP.SpecVar(t,i,p)) comb in
              let () = Debug.ninfo_hprint (add_str "hvars" (pr_list Cprinter.string_of_typed_spec_var)) hvars no_pos in
	                        (*TO CHECK: for correctness*)
                                (*LDK: linearize perm permission as a spec var*)
                                let permvar = (
                                    match perm with
                                      | None -> None
                                      | Some f -> 
                                            let perms = [f] in
                                            let permlabels = List.map (fun _ -> LO.unlabelled) perms in
                                            let permvars = CP.view_arg_to_sv_list (match_exp (List.combine perms permlabels) pos) in
                                            (match !Globals.perm with
                                              | Bperm ->
                                                    (*Note: ordering is important*)
                                                    let c = List.nth permvars 0 in
                                                    let t = List.nth permvars 1 in
                                                    let a = List.nth permvars 2 in
                                                    Some (Cpure.Bptriple ((c,t,a),no_pos))
                                              | _ ->
                                                    let v = List.nth permvars 0 in
                                                    Some (Cpure.Var (v,no_pos)) ))
                                in
	                        let ann_param1,_ = List.fold_left (fun (r, n) _ ->
		                    let n_ann_param =
		                      if List.mem n holes then
		                        Some (Ipure_D.ConstAnn (Accs))
		                      else
		                        (* Some (IF.ConstAnn (Mutable)) *) None
		                    in
		                    (r@[n_ann_param], n+1)
	                        ) ([], 0) hvars in
	                        let result_heap =  CF.DataNode {
		                    CF.h_formula_data_node = CP.SpecVar (rootptr_type,rootptr,p);
                                    CF.h_formula_data_name = rootptr_type_name;
                                    CF.h_formula_data_derv = dr;
                                    CF.h_formula_data_split = split;
                                    CF.h_formula_data_imm = Immutable.iformula_ann_to_cformula_ann imm;
                                    CF.h_formula_data_param_imm = Immutable.iformula_ann_opt_to_cformula_ann_lst ann_param1;
                                    CF.h_formula_data_perm = permvar; (*??? TO CHECK: temporarily*)
                                    CF.h_formula_data_origins = []; (*??? temporarily*)
                                    CF.h_formula_data_original = true; (*??? temporarily*)
                                    CF.h_formula_data_arguments = hvars;
                                    CF.h_formula_data_holes = (* holes *) [];
                                    CF.h_formula_data_label = pi;
                                    CF.h_formula_data_remaining_branches = None;
                                    CF.h_formula_data_pruning_conditions = [];
                                    CF.h_formula_data_pos = pos;}
                                in
                                (* let result_heap = x_add_1 Immutable.normalize_field_ann_heap_node result_heap in *)
                                (result_heap, CF.TypeTrue, [], tl)
                            )
                            else (
	                        (* Not a field access, proceed with the original code *)
                                try (
                                    let vdef = I.look_up_view_def_raw 9 prog.I.prog_view_decls c in
                                    let labels = fst vdef.I.view_labels in
                                    let params_orig = match_exp (List.combine exps labels) pos in
                                    (* andreeac: TODO insert test check map compatib *)
                                    (* let hvars, labels, annot_params = CP.split_view_args (List.combine params_orig labels) in *)
                                    let hvars, labels, annot_params, params_orig = x_add_1 Immutable.split_view_args params_orig vdef in 
                                    let typ = (
                                        if (vdef.I.view_is_prim) then UNK
                                        else if vdef.I.view_data_name = "" then 
                                          (fill_view_param_types vdef;
                                          Named vdef.I.view_data_name)
                                        else Named vdef.I.view_data_name 
                                    ) in
                                    let new_v = CP.SpecVar (typ, v, p) in
                                    (*LDK: linearize perm permission as a spec var*)
                                    let permvar = (match perm with
                                      | None -> None
                                      | Some f -> 
                                            let perms = f :: [] in
                                            let permlabels = List.map (fun _ -> LO.unlabelled) perms in
                                            let permvars = CP.view_arg_to_sv_list (match_exp (List.combine perms permlabels) pos) in
                                            (match !Globals.perm with
                                              | Bperm ->
                                                    (*Note: ordering is important*)
                                                    let c = List.nth permvars 0 in
                                                    let t = List.nth permvars 1 in
                                                    let a = List.nth permvars 2 in
                                                    Some (Cpure.Bptriple ((c,t,a),no_pos))
                                              | _ ->
                                                    let v = List.nth permvars 0 in
                                                    Some (Cpure.Var (v,no_pos)) ))
                                    in
                                    let new_h = CF.ViewNode {
                                        CF.h_formula_view_node = new_v;
                                        CF.h_formula_view_name = c;
                                        CF.h_formula_view_derv = dr;
                                        CF.h_formula_view_split = split;
                                        CF.h_formula_view_imm = Immutable.iformula_ann_to_cformula_ann imm;
                                        CF.h_formula_view_perm = permvar; (*LDK: TO CHECK*)
                                        CF.h_formula_view_arguments = hvars;
                                        CF.h_formula_view_ho_arguments = ho_args; (* TODO:HO *)
                                        CF.h_formula_view_annot_arg = annot_params; (* andreeac: TODO annot *)
                                        CF.h_formula_view_args_orig = params_orig;
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
                                        CF.h_formula_view_pos = pos;} in
                                    (new_h, CF.TypeTrue, [], tl)
                                )
                                with Not_found ->
                                    let labels = List.map (fun _ -> LO.unlabelled) exps in
                                    let hvars = CP.view_arg_to_sv_list (match_exp (List.combine exps labels) pos) in
                                    let new_v = CP.SpecVar (Named c, v, p) in
                                    (* An Hoa : find the holes here! *)
                                    let rec collect_holes vars n = (match vars with
                                      | [] -> []
                                      | x::t -> (
                                            let th = collect_holes t (n+1) in 
                                            match x with 
                                              | CP.SpecVar (_,vn,_) -> if (vn.[0] = '#') then n::th else th 
                                        )
                                    ) in
                                    (*LDK: linearize perm permission as a spec var*)
                                    let permvar = (match perm with 
                                      | None -> None
                                      | Some f -> 
                                            let perms = f :: [] in
                                            let permlabels = List.map (fun _ -> LO.unlabelled) perms in
                                            let permvars = CP.view_arg_to_sv_list (match_exp (List.combine perms permlabels) pos) in
                                            (match !Globals.perm with
                                              | Bperm ->
                                                    (*Note: ordering is important*)
                                                    let c = List.nth permvars 0 in
                                                    let t = List.nth permvars 1 in
                                                    let a = List.nth permvars 2 in
                                                    Some (Cpure.Bptriple ((c,t,a),no_pos))
                                              | _ ->
                                                    let v = List.nth permvars 0 in
                                                    Some (Cpure.Var (v,no_pos)) ))
                                    in
                                    let holes = collect_holes hvars 0 in
		                    let new_h =
                                      CF.DataNode {CF.h_formula_data_node = new_v;
                                      CF.h_formula_data_name = c;
                                      CF.h_formula_data_derv = dr;
                                      CF.h_formula_data_split = split;
                                      CF.h_formula_data_imm = Immutable.iformula_ann_to_cformula_ann imm;
                                      CF.h_formula_data_param_imm = Immutable.iformula_ann_opt_to_cformula_ann_lst ann_param;
                                      CF.h_formula_data_perm = permvar; (*LDK*)
                                      CF.h_formula_data_origins = [];
                                      CF.h_formula_data_original = true;
                                      CF.h_formula_data_arguments = hvars;
                                      CF.h_formula_data_holes = holes; (* An Hoa : Set the hole *)
                                      CF.h_formula_data_label = pi;
                                      CF.h_formula_data_remaining_branches = None;
                                      CF.h_formula_data_pruning_conditions = [];
                                      CF.h_formula_data_pos = pos;} in
                                    (* let new_h = x_add_1 Immutable.normalize_field_ann_heap_node new_h in *)
                                    (new_h, CF.TypeTrue, [], tl)
                            )
                        )
                  | IF.Star {IF.h_formula_star_h1 = f1;
                    IF.h_formula_star_h2 = f2;
                    IF.h_formula_star_pos = pos} ->
                        let (lf1, type1, newvars1, n_tl) = linearize_heap f1 pos tl in
                        let (lf2, type2, newvars2, n_tl) = linearize_heap f2 pos n_tl in
                        let tmp_h = CF.mkStarH lf1 lf2 pos in
                        let tmp_type = CF.mkAndType type1 type2 in 
                        (tmp_h, tmp_type, newvars1 @ newvars2, n_tl)
                  | IF.StarMinus {IF.h_formula_starminus_h1 = f1;
                    IF.h_formula_starminus_h2 = f2;
                    IF.h_formula_starminus_pos = pos} ->
                        let (lf1, type1, newvars1, n_tl) = linearize_heap f1 pos tl in
                        let (lf2, type2, newvars2, n_tl) = linearize_heap f2 pos n_tl in
                        let tmp_h = CF.mkStarMinusH lf1 lf2 Not_Aliased pos 1 in
                        let tmp_type = CF.mkAndType type1 type2 in 
                        (tmp_h, tmp_type, newvars1 @ newvars2, n_tl)
                  | IF.Phase { IF.h_formula_phase_rd = f1;
                    IF.h_formula_phase_rw = f2;
                    IF.h_formula_phase_pos = pos } ->
                        let (lf1, type1, newvars1, n_tl) = linearize_heap f1 pos tl in
                        let (lf2, type2, newvars2, n_tl) = linearize_heap f2 pos n_tl in
                        let tmp_h = CF.mkPhaseH lf1 lf2 pos in
                        let tmp_type = CF.mkAndType type1 type2 in 
                        (tmp_h, tmp_type, newvars1 @ newvars2, n_tl)
                  | IF.Conj {IF.h_formula_conj_h1 = f1;
                    IF.h_formula_conj_h2 = f2;
                    IF.h_formula_conj_pos = pos } ->
                        let (lf1, type1, newvars1, n_tl) = linearize_heap f1 pos tl in
                        let (lf2, type2, newvars2, n_tl) = linearize_heap f2 pos n_tl in
                        let tmp_h = CF.mkConjH lf1 lf2 pos in
                        let tmp_type = CF.mkAndType type1 type2 in 
                        (tmp_h, tmp_type, newvars1 @ newvars2, n_tl)
                  | IF.HRel (r, args, pos) ->
                        let nv = trans_var_safe (r,Unprimed) HpT tl pos in
                        (* Match types of arguments with relation signature *)
                        let cpargs = trans_pure_exp_list args tl in
                        (CF.HRel (nv, cpargs, pos), CF.TypeTrue, [], tl)
                  | IF.ConjStar {IF.h_formula_conjstar_h1 = f1;
                    IF.h_formula_conjstar_h2 = f2;
                    IF.h_formula_conjstar_pos = pos} ->
                        let (lf1, type1, newvars1, n_tl) = linearize_heap f1 pos tl in
                        let (lf2, type2, newvars2, n_tl) = linearize_heap f2 pos n_tl in
                        let tmp_h = CF.mkConjStarH lf1 lf2 pos in
                        let tmp_type = CF.mkAndType type1 type2 in 
                        (tmp_h, tmp_type, newvars1 @ newvars2, n_tl)
                  | IF.ConjConj {IF.h_formula_conjconj_h1 = f1;
                    IF.h_formula_conjconj_h2 = f2;
                    IF.h_formula_conjconj_pos = pos} ->
                        let (lf1, type1, newvars1, n_tl) = linearize_heap f1 pos tl in
                        let (lf2, type2, newvars2, n_tl) = linearize_heap f2 pos n_tl in
                        let tmp_h = CF.mkConjConjH lf1 lf2 pos in
                        let tmp_type = CF.mkAndType type1 type2 in 
                        (tmp_h, tmp_type, newvars1 @ newvars2, n_tl)
                  | IF.HTrue ->  (CF.HTrue, CF.TypeTrue, [], tl)
                  | IF.HFalse -> (CF.HFalse, CF.TypeFalse, [], tl) 
                  | IF.HEmp -> (CF.HEmp, CF.TypeTrue, [], tl)
      (* URGENT:TODOWN:HVar *)
      | IF.HVar (v,hvar_vs) -> 
            let vs = List.map (fun v -> (CP.SpecVar (FORM, v, Unprimed))) hvar_vs in
            (CF.HVar (CP.SpecVar (FORM, v, Unprimed),vs), CF.TypeTrue, [], tl)
            ) in 
            res
        ) in
  let linearize_one_formula_x f pos (tl:spec_var_type_list) = (
      let h = f.IF.formula_heap in
      let p = f.IF.formula_pure in
      let dl = f.IF.formula_delayed in
      let id = f.IF.formula_thread in
      let pos = f.IF.formula_pos in
      let (new_h, type_f, newvars, n_tl) = linearize_heap h pos tl in
    (*let () = print_string("Heap: "^(Cprinter.string_of_h_formula new_h)^"\n") in*)
      let new_h, new_constr, new_vars = x_add_1 Immutable.normalize_field_ann_heap_node new_h in
      let newvars = newvars@new_vars in
      let new_p = trans_pure_formula p n_tl in
      let new_p = CP.join_disjunctions (new_p::new_constr) in
      let new_p = Cpure.arith_simplify 5 new_p in
      let mix_p = (MCP.memoise_add_pure_N (MCP.mkMTrue pos) new_p) in
      (*formula_delayed*)
      let new_dl = trans_pure_formula dl tlist in
      let new_dl = Cpure.arith_simplify 5 new_dl in
      let mix_dl = (MCP.memoise_add_pure_N (MCP.mkMTrue pos) new_dl) in
      let id_var = (match id with
        | None -> 
              (*May be redundant*)
              (*this lookup should be done when float_out_thread*)
              (*Here, try it the second chance*)
              (*look for an thread id*)
            let thread_var = Cpure.SpecVar (Globals.thread_typ, Globals.thread_name,Unprimed) in
              (*find all spec_var which is equal to "thread"*)
              let vv = MCP.find_closure_mix_formula thread_var mix_dl in 
              let vv1 = Gen.BList.difference_eq CP.eq_spec_var vv [thread_var] in
              if (vv1==[]) then Error.report_error {Error.error_loc = pos;Error.error_text = "linearize_one_formula: could not find thread id"}
              else List.hd vv1
        | Some (ve,pe) -> (trans_var (ve, pe) n_tl pos))
      in
      let new_f = { CF.formula_heap = new_h;
      CF.formula_pure = mix_p;
      CF.formula_thread = id_var;
      (* CF.formula_delayed = mix_dl; (*???*) *)
      CF.formula_delayed = MCP.mkMTrue pos; (*LDK: TO DO*)
      CF.formula_ref_vars = [];
      CF.formula_label = None;
      CF.formula_pos = pos} in
      (* let new_f = x_add_1 Immutable.normalize_field_ann_formula new_f in *)
      (new_f,type_f, newvars, n_tl)
  ) in
  
  let linearize_one_formula f pos tlist = (
      let pr (a,b) = Cprinter.string_of_one_formula a in
      let pr_out (f,_,_,_) = !CF.print_one_formula f in 
      Debug.no_1 "linearize_one_formula"
          Iprinter.string_of_one_formula pr_out
          (fun _ -> linearize_one_formula_x f pos tlist) f
  ) in
  
  let linearize_base base pos (tl:spec_var_type_list) = (
      let h = base.IF.formula_base_heap in
      let p = base.IF.formula_base_pure in
    let vp = base.IF.formula_base_vperm in
      let fl = base.IF.formula_base_flow in
      let a = base.IF.formula_base_and in
      let pos = base.IF.formula_base_pos in
      let (new_h, type_f, newvars1, n_tl) = linearize_heap h pos tl in
      let new_h, new_constr, new_vars = x_add_1 Immutable.normalize_field_ann_heap_node new_h in
      let newvars = newvars1@new_vars in
    let new_vp = trans_vperm_sets vp n_tl pos in
      let new_p = trans_pure_formula p n_tl in
    (* let () = print_string("\nForm: "^(Cprinter.string_of_pure_formula new_p)) in *)
      let new_p = CP.join_disjunctions (new_p::new_constr) in
    (* let () = print_string("\nForm: "^(Cprinter.string_of_pure_formula new_p)) in *)
      let new_p = Cpure.arith_simplify 5 new_p in
    (* let () = print_string("\nSimpleForm: "^(Cprinter.string_of_pure_formula new_p)) in *)
      let new_fl = trans_flow_formula fl pos in
      let new_a = ref [] in
      let newvars2 = ref [] in
      let new_tl = ref n_tl in
      List.iter (fun f ->
          let a1, _, nvs, new_tl1 = linearize_one_formula f pos !new_tl in
          new_tl := new_tl1;
          new_a := !new_a @ [a1];
          newvars2 := !newvars2 @ nvs;
      ) a;
    (* let () = print_string("\new_p: "^(Cprinter.string_of_pure_formula new_p)) in *)
    (new_h, new_p, new_vp, type_f, new_fl, !new_a, newvars1 @ !newvars2, n_tl)
  ) in
  match f0 with
    | IF.Or {IF.formula_or_f1 = f1;
      IF.formula_or_f2 = f2;
      IF.formula_or_pos = pos } ->
          let (n_tl,lf1, newvars1) = linearize_formula prog f1 tlist in
          let (n_tl,lf2, newvars2) = linearize_formula prog f2 n_tl in
          let result = CF.mkOr lf1 lf2 pos in
          (n_tl,result, newvars1 @ newvars2)
    | IF.Base base ->
          let pos = base.IF.formula_base_pos in
      let nh,np,nvp,nt,nfl,na,newvars,n_tl = (linearize_base base pos tlist) in
          let np = (memoise_add_pure_N (mkMTrue pos) np)  in
      (n_tl, CF.mkBase nh np nvp nt nfl na pos, newvars)
    | IF.Exists {IF.formula_exists_heap = h; 
      IF.formula_exists_pure = p;
               IF.formula_exists_vperm = vp;
      IF.formula_exists_flow = fl;
      IF.formula_exists_qvars = qvars;
      IF.formula_exists_and = a;
      IF.formula_exists_pos = pos} ->
          let base ={IF.formula_base_heap = h;
          IF.formula_base_pure = p;
                 IF.formula_base_vperm = vp;
          IF.formula_base_flow = fl;
          IF.formula_base_and = a;
          IF.formula_base_pos = pos;} in 
      let nh,np,nvp,nt,nfl,na,newvars,n_tl = linearize_base base pos tlist in
          let np = memoise_add_pure_N (mkMTrue pos) np in
          let qvars = qvars @ newvars in
      (n_tl, CF.mkExists (List.map (fun c-> trans_var_safe c UNK tlist pos) qvars) nh np nvp nt nfl na pos, [])

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

and trans_vperm_sets (vps: IVP.vperm_sets) (tlist: spec_var_type_list) pos: CVP.vperm_sets =
  let trans_v (v, p) = 
    let v_type = CP.type_of_spec_var (trans_var (v, Unprimed) tlist pos) in
    let sv = CP.SpecVar (v_type, v, p) in
    sv
  in
  let trans_vl vl = List.map trans_v vl in
  let vp = {   CVP.vperm_unprimed_flag = false;
  CVP.vperm_is_false = false;
      CVP.vperm_zero_vars = trans_vl vps.IVP.vperm_zero_vars;
    CVP.vperm_lend_vars = trans_vl vps.IVP.vperm_lend_vars;
    CVP.vperm_value_vars = trans_vl vps.IVP.vperm_value_vars;
    CVP.vperm_full_vars = trans_vl vps.IVP.vperm_full_vars;
    CVP.vperm_frac_vars = List.concat (List.map 
        (fun (frac, vl) -> List.map (fun v -> (frac, trans_v v)) vl) vps.IVP.vperm_frac_vars); } in
  CVP.norm_vperm_sets vp
  
  
and trans_pure_formula_x (f0 : IP.formula) (tlist:spec_var_type_list) : CP.formula =
  (*let  _ = print_string("\nIform: "^(Iprinter.string_of_pure_formula f0)) in*)
  let f1 = Ipure.transform_bexp_form f0 in
  match f1 with
    | IP.BForm (bf,lbl) -> CP.BForm (trans_pure_b_formula bf tlist , lbl) 
    | IP.And (f1, f2, pos) ->
          let pf1 = trans_pure_formula f1 tlist in
          let pf2 = trans_pure_formula f2 tlist in CP.mkAnd pf1 pf2 pos
    | IP.AndList b -> CP.mkAndList (map_l_snd (fun c-> trans_pure_formula c tlist) b)
    | IP.Or (f1, f2,lbl, pos) ->
          let pf1 = trans_pure_formula f1 tlist in
          let pf2 = trans_pure_formula f2 tlist in CP.mkOr pf1 pf2 lbl pos
    | IP.Not (f, lbl, pos) -> let pf = trans_pure_formula f tlist in CP.mkNot pf lbl pos
    | IP.Forall ((v, p), f, lbl, pos) ->
          let pf = trans_pure_formula f tlist in
          let v_type = Cpure.type_of_spec_var (trans_var (v,Unprimed) tlist pos) in
          let sv = CP.SpecVar (v_type, v, p) in CP.mkForall [ sv ] pf lbl pos
    | IP.Exists ((v, p), f, lbl, pos) ->
          let pf = trans_pure_formula f tlist in
          let sv = trans_var (v,p) tlist pos in
          CP.mkExists [ sv ] pf lbl pos

and trans_pure_formula (f0 : IP.formula) (tlist:spec_var_type_list) : CP.formula =
  let pr_f = !IP.print_formula in
  let pr_tlist = string_of_tlist in
  let pr_out = !CP.print_formula in
  Debug.no_2 "trans_pure_formula" pr_f pr_tlist pr_out trans_pure_formula_x f0 tlist

and trans_pure_b_formula (b0 : IP.b_formula) (tlist:spec_var_type_list) : CP.b_formula =
  Debug.no_1 "trans_pure_b_formula" (Iprinter.string_of_b_formula) (Cprinter.string_of_b_formula) (fun b -> trans_pure_b_formula_x b tlist) b0                 
      
and trans_pure_b_formula_x (b0 : IP.b_formula) (tlist:spec_var_type_list) : CP.b_formula =
  let (pf, sl) = b0 in
  let npf =  match pf with
    | IP.Frm ((v,p),pos) ->
          let v_type = Cpure.type_of_spec_var (trans_var (v,Unprimed) tlist pos) in
          let sv = CP.SpecVar (v_type, v, p) in
          CP.Frm (sv, pos)
    | IP.BConst (b, pos) -> CP.BConst (b, pos)
    | IP.BVar ((v, p), pos) -> CP.BVar (CP.SpecVar (C.bool_type, v, p), pos)
    | IP.LexVar (t_ann, ls1, ls2, pos) ->
          let cle = List.map (fun e -> trans_pure_exp e tlist) ls1 in
          let clt = List.map (fun e -> trans_pure_exp e tlist) ls2 in
          CP.LexVar {
              CP.lex_ann = trans_term_ann t_ann tlist;
              CP.lex_exp = cle;
              CP.lex_fid = "";
              CP.lex_tmp = clt;
              CP.lex_loc = pos; }
    | IP.Lt (e1, e2, pos) ->
          let pe1 = trans_pure_exp e1 tlist in
          let pe2 = trans_pure_exp e2 tlist in CP.mkLt pe1 pe2 pos
    | IP.Lte (e1, e2, pos) ->
          let pe1 = trans_pure_exp e1 tlist in
          let pe2 = trans_pure_exp e2 tlist in CP.mkLte pe1 pe2 pos
    | IP.SubAnn (e1, e2, pos) ->
          let pe1 = trans_pure_exp e1 tlist in
          let pe2 = trans_pure_exp e2 tlist in CP.SubAnn(pe1,pe2,pos)
    | IP.Gt (e1, e2, pos) ->
          let pe1 = trans_pure_exp e1 tlist in
          let pe2 = trans_pure_exp e2 tlist in CP.mkGt pe1 pe2 pos
    | IP.Gte (e1, e2, pos) ->
          let pe1 = trans_pure_exp e1 tlist in
          let pe2 = trans_pure_exp e2 tlist in CP.mkGte pe1 pe2 pos
    | IP.Eq (e1, e2, pos) ->
          let pe1 = trans_pure_exp e1 tlist in
          let pe2 = trans_pure_exp e2 tlist in 
          (check_dfrac_wf pe1 pe2 pos; CP.mkEq pe1 pe2 pos)
    | IP.Neq (e1, e2, pos) ->
          let pe1 = trans_pure_exp e1 tlist in
          let pe2 = trans_pure_exp e2 tlist in CP.mkNeq pe1 pe2 pos
    | IP.EqMax (e1, e2, e3, pos) ->
          let pe1 = trans_pure_exp e1 tlist in
          let pe2 = trans_pure_exp e2 tlist in
          let pe3 = trans_pure_exp e3 tlist in CP.EqMax (pe1, pe2, pe3, pos)
    | IP.EqMin (e1, e2, e3, pos) ->
          let pe1 = trans_pure_exp e1 tlist in
          let pe2 = trans_pure_exp e2 tlist in
          let pe3 = trans_pure_exp e3 tlist in CP.EqMin (pe1, pe2, pe3, pos)
    | IP.BagIn ((v, p), e, pos) ->
          let pe = trans_pure_exp e tlist in CP.BagIn ((trans_var (v,p) tlist pos), pe, pos)
    | IP.BagNotIn ((v, p), e, pos) ->
          let pe = trans_pure_exp e tlist in
          CP.BagNotIn ((trans_var (v,p) tlist pos), pe, pos)
    | IP.BagSub (e1, e2, pos) ->
          let pe1 = trans_pure_exp e1 tlist in
          let pe2 = trans_pure_exp e2 tlist in CP.BagSub (pe1, pe2, pos)
    | IP.BagMax ((v1, p1), (v2, p2), pos) ->
          CP.BagMax (CP.SpecVar (C.int_type, v1, p1),CP.SpecVar (C.bag_type, v2, p2), pos)
    | IP.BagMin ((v1, p1), (v2, p2), pos) ->
          CP.BagMin (CP.SpecVar (C.int_type, v1, p1), CP.SpecVar (C.bag_type, v2, p2), pos)
    (* | IP.VarPerm (ct,ls,pos) ->                                 *)
    (*       let func (v,p) =                                      *)
    (*         CP.SpecVar (UNK,v,p) (*TO CHECK: ignore type info*) *)
    (*       in                                                    *)
    (*       let ls1 = List.map func ls in                         *)
    (*       CP.VarPerm (ct,ls1,pos)                               *)
    | IP.ListIn (e1, e2, pos) ->
          let pe1 = trans_pure_exp e1 tlist in
          let pe2 = trans_pure_exp e2 tlist in CP.ListIn (pe1, pe2, pos)
    | IP.ListNotIn (e1, e2, pos) ->
          let pe1 = trans_pure_exp e1 tlist in
          let pe2 = trans_pure_exp e2 tlist in CP.ListNotIn (pe1, pe2, pos)
    | IP.ListAllN (e1, e2, pos) ->
          let pe1 = trans_pure_exp e1 tlist in
          let pe2 = trans_pure_exp e2 tlist in CP.ListAllN (pe1, pe2, pos)
    | IP.ListPerm (e1, e2, pos) ->
          let pe1 = trans_pure_exp e1 tlist in
          let pe2 = trans_pure_exp e2 tlist in CP.ListPerm (pe1, pe2, pos)
    | IP.RelForm (r, args, pos) ->    
          let nv = trans_var_safe (r,Unprimed) (RelT[]) tlist pos in
          (* Match types of arguments with relation signature *)
          let cpargs = trans_pure_exp_list args tlist in
          CP.RelForm (nv, cpargs, pos) (* An Hoa : Translate IP.RelForm to CP.RelForm *)
    | IP.XPure ({IP.xpure_view_node = vn ;
      IP.xpure_view_name = r;
      IP.xpure_view_arguments = args;
      IP.xpure_view_remaining_branches = brs;
      IP.xpure_view_pos = pos}) -> 
          let nargs = List.map (fun arg -> trans_var (arg,Unprimed) tlist pos) args in 
          CP.XPure {CP.xpure_view_node = None ;
          CP.xpure_view_name = r;
          CP.xpure_view_arguments = nargs;
          CP.xpure_view_remaining_branches = brs;
          CP.xpure_view_pos = pos
          }
  in
  (*let () = print_string("\nC_B_Form: "^(Cprinter.string_of_b_formula (npf,None))) in*)
  match sl with
    | None -> (npf, None)
    | Some (il,lbl,el) -> let nel = trans_pure_exp_list el tlist in (npf, Some (il,lbl,nel))

and trans_term_ann (ann: IP.term_ann) (tlist:spec_var_type_list): CP.term_ann =
  let trans_term_fail f = match f with
    | IP.TermErr_May -> CP.TermErr_May
    | IP.TermErr_Must -> CP.TermErr_Must in
  let trans_term_id uid tlist = {
      CP.tu_id = uid.IP.tu_id;
      CP.tu_sid = uid.IP.tu_sid;
      CP.tu_fname = uid.IP.tu_fname;
      CP.tu_call_num = 0;
      CP.tu_args = List.map (fun e -> trans_pure_exp e tlist) uid.IP.tu_args;
      CP.tu_cond = trans_pure_formula uid.IP.tu_cond tlist; 
      CP.tu_icond = CP.mkTrue no_pos;
      CP.tu_sol = None; 
      CP.tu_pos = uid.IP.tu_pos; } in 
  match ann with
    | IP.Term -> CP.Term
    | IP.Loop -> CP.Loop (Some { CP.tcex_trace = [proving_loc # get]; })
    | IP.MayLoop -> CP.MayLoop None
    | IP.TermU uid -> CP.TermU (trans_term_id uid tlist)
    | IP.TermR uid -> CP.TermR (trans_term_id uid tlist)
    | IP.Fail f -> CP.Fail (trans_term_fail f)
          
and trans_pure_exp (e0 : IP.exp) (tlist:spec_var_type_list) : CP.exp =
  Debug.no_1 "trans_pure_exp" 
      (Iprinter.string_of_formula_exp)
      (Cprinter.string_of_formula_exp) 
      (fun e -> trans_pure_exp_x e tlist) e0 
      
and trans_pure_exp_x (e0 : IP.exp) (tlist:spec_var_type_list) : CP.exp =
  match e0 with
    | IP.Null pos -> CP.Null pos
    | IP.Tsconst (t,pos) -> CP.Tsconst (t,pos)
    | IP.Bptriple ((pc,pt,pa),pos) ->
          (match pc,pt,pa with
            | Ipure.Var (vc,posc), Ipure.Var (vt,post),Ipure.Var (va,posa) ->
                  let pc = trans_var vc tlist posc in
                  let pt = trans_var vt tlist post in
                  let pa = trans_var va tlist posa in
                  CP.Bptriple ((pc,pt,pa),pos)
            | _ -> report_error pos ("trans_pure_exp: Bptriple error at location "^(string_of_full_loc pos)))
    | IP.Tup2 ((e1, e2), pos) -> CP.Tup2 ((trans_pure_exp e1 tlist, trans_pure_exp e2 tlist), pos)
    | IP.AConst(a,pos) -> CP.AConst(a,pos)
    | IP.InfConst(a,pos) -> CP.InfConst(a,pos)
    | IP.NegInfConst(a,pos) -> CP.NegInfConst(a,pos)
    | IP.Var ((v, p), pos) -> 
          CP.Var ((trans_var (v,p) tlist pos),pos)
    | IP.Level ((v, p), pos) -> 
          CP.Level ((trans_var (v,p) tlist pos),pos)
    | IP.Ann_Exp (e, t, pos) -> trans_pure_exp e tlist
    | IP.IConst (c, pos) -> CP.IConst (c, pos)
    | IP.FConst (c, pos) -> CP.FConst (c, pos)
    | IP.Add (e1, e2, pos) -> CP.Add (trans_pure_exp e1 tlist, trans_pure_exp e2 tlist, pos)
    | IP.Subtract (e1, e2, pos) -> CP.Subtract (trans_pure_exp e1 tlist, trans_pure_exp e2 tlist, pos)
    | IP.Mult (e1, e2, pos) -> CP.Mult (trans_pure_exp e1 tlist, trans_pure_exp e2 tlist, pos)
    | IP.Div (e1, e2, pos) -> CP.Div (trans_pure_exp e1 tlist, trans_pure_exp e2 tlist, pos)
    | IP.Max (e1, e2, pos) -> CP.Max (trans_pure_exp e1 tlist, trans_pure_exp e2 tlist, pos)
    | IP.Min (e1, e2, pos) -> CP.Min (trans_pure_exp e1 tlist, trans_pure_exp e2 tlist, pos)
    | IP.TypeCast (ty, e1, pos) -> CP.TypeCast (ty, trans_pure_exp e1 tlist, pos)
    | IP.Bag (elist, pos) -> CP.Bag (trans_pure_exp_list elist tlist, pos)
    | IP.BagUnion (elist, pos) -> CP.BagUnion (trans_pure_exp_list elist tlist, pos)
    | IP.BagIntersect (elist, pos) -> CP.BagIntersect (trans_pure_exp_list elist tlist, pos)
    | IP.BagDiff (e1, e2, pos) -> CP.BagDiff (trans_pure_exp e1 tlist, trans_pure_exp e2 tlist, pos)
    | IP.List (elist, pos) -> CP.List (trans_pure_exp_list elist tlist, pos)
    | IP.ListAppend (elist, pos) -> CP.ListAppend (trans_pure_exp_list elist tlist, pos)
    | IP.ListCons (e1, e2, pos) -> CP.ListCons (trans_pure_exp e1 tlist, trans_pure_exp e2 tlist, pos)
    | IP.ListHead (e, pos) -> CP.ListHead (trans_pure_exp e tlist, pos)
    | IP.ListTail (e, pos) -> CP.ListTail (trans_pure_exp e tlist, pos)
    | IP.ListLength (e, pos) -> CP.ListLength (trans_pure_exp e tlist, pos)
    | IP.ListReverse (e, pos) -> CP.ListReverse (trans_pure_exp e tlist, pos)
    | IP.Func (id, es, pos) ->
          let es = List.map (fun e -> trans_pure_exp e tlist) es in
          CP.Func (CP.SpecVar (RelT[], id, Unprimed), es, pos)
    | IP.Template t ->
          let pos = t.IP.templ_pos in
          let tid = t.IP.templ_id in
          let tdef = C.look_up_templ_def_raw (C.templ_decls # get_stk) tid in
          let tparams = tdef.C.templ_params in
          let tbody = tdef.C.templ_body in

          let templ_args = List.map (fun a -> trans_pure_exp a tlist) t.IP.templ_args in
          let sst = List.combine tparams templ_args in
          let templ_unks, templ_body = match tbody with
            | Some cb -> 
                  let inst_cb = CP.a_apply_par_term sst cb in
                  let unk_svs = Gen.BList.difference_eq CP.eq_spec_var 
                    (CP.afv inst_cb) (List.concat (List.map CP.afv templ_args)) in
                  let unk_exps = List.map (fun v -> CP.mkVar v no_pos) unk_svs in
                  (unk_exps, Some inst_cb)
            | None -> ([], None)
          in CP.Template {
              CP.templ_id = trans_var (t.IP.templ_id, Unprimed) tlist pos;
              CP.templ_args = templ_args;
              CP.templ_unks = templ_unks;
              CP.templ_body = templ_body;
              CP.templ_pos = pos; }
    | IP.ArrayAt ((a, p), ind, pos) ->
          let cpind = List.map (fun i -> trans_pure_exp i tlist) ind in
          let dim = List.length ind in (* currently only support int type array *)
          CP.ArrayAt (CP.SpecVar ((Array (C.int_type, dim)), a, p), cpind, pos)
    | IP.BExpr f1 -> report_error no_pos "trans_pure_exp BExpr"
          (* let nf1 = IP.transform_bexp f1 in *)
          (* BExpr (trans_pure_formula nf1 tlist) *)

and trans_pure_exp_list (elist : IP.exp list) (tlist:spec_var_type_list) : CP.exp list =
  match elist with
    | [] -> []
    | e :: rest -> (trans_pure_exp e tlist) :: (trans_pure_exp_list rest tlist)


(*MERGE CHECK*)
(* | IP.Bptriple ((pc,pt,pa), pos) -> *)
    (*       let todo_unk:Globals.typ = must_unify_expect_test et Bptyp pos in  *)
(*       let new_et = fresh_tvar stab in *)
(*           let t1 = gather_type_info_exp_x pc stab new_et in (\* Int *\) *)
(*           let t2 = gather_type_info_exp_x pt stab new_et in (\* Int *\) *)
(*           let t3 = gather_type_info_exp_x pa stab new_et in (\* Int *\) *)
    (*       let todo_unk:Globals.typ = must_unify_expect t1 Int stab pos in *)
    (*       let todo_unk:Globals.typ = must_unify_expect t2 Int stab pos in *)
    (*       let todo_unk:Globals.typ = must_unify_expect t3 Int stab pos in *)
(*       Bptyp *)
(* | IP.Add (a1, a2, pos) -> *)

and case_normalize_pure_formula hp b f = f

and case_normalize_renamed_struc_formula prog avail_vars posibl_expl f = 
  let rf = case_normalize_renamed_struc_formula prog avail_vars posibl_expl in
  match f with
    | IF.ECase b -> 
          let n_br = List.map (fun (c1,c2)-> c1, case_normalize_renamed_struc_formula prog (avail_vars@(IP.fv c1)) posibl_expl c2)
            b.IF.formula_case_branches in
          IF.ECase {b with IF.formula_case_branches = n_br}
    | IF.EBase b -> 
          let ann_vars = IF.collect_annot_vars b.IF.formula_struc_base in 
          let n_bf,h,_ = case_normalize_renamed_formula prog avail_vars posibl_expl b.IF.formula_struc_base ann_vars in
          let n_cont = map_opt (case_normalize_renamed_struc_formula prog (avail_vars@h) posibl_expl) b.IF.formula_struc_continuation in
          IF.EBase {b with IF.formula_struc_base = n_bf; IF.formula_struc_continuation = n_cont;}
    | IF.EAssume b -> IF.EAssume {b with 
          IF.formula_assume_simpl = 
              ( let ann_vars = IF.collect_annot_vars  b.IF.formula_assume_simpl in 
              let f,_,_ = case_normalize_renamed_formula prog avail_vars posibl_expl  b.IF.formula_assume_simpl ann_vars in
              f);
          IF.formula_assume_struc = rf b.IF.formula_assume_struc;}
    | IF.EInfer b -> IF.EInfer {b with IF.formula_inf_continuation = rf b.IF.formula_inf_continuation}
    | IF.EList b -> IF.EList (map_l_snd rf b) 

(*moved the liniarization to case_normalize_renamed_formula*)
and case_normalize_renamed_formula prog (avail_vars:(ident*primed) list) posib_expl (f:IF.formula) ann_vars : IF.formula* ((ident*primed)list) * ((ident*primed)list) =
  let pr1 prog = (add_str "view_decls" pr_v_decls) prog.I.prog_view_decls in
  let pr = (pr_list (fun (i,p) -> i)) in
  let pr_out (f,h,expl) = 
    ("\n ### f = " ^ (Iprinter.string_of_formula f)
    ^"\n ### h = " ^ (pr h)
    ^"\n ### expl = " ^ (pr expl)) 
  in 
  Debug.no_5 "case_normalize_renamed_formula" 
      pr1 pr pr pr  Iprinter.string_of_formula pr_out
      (fun _ _ _ _ _ -> case_normalize_renamed_formula_x prog avail_vars posib_expl f ann_vars) prog avail_vars posib_expl  ann_vars f

and hack_filter_global_rel prog ls =
  List.filter (fun (i,_) -> 
      try
          let todo_unk = I.look_up_rel_def_raw prog.I.prog_rel_decls i in false
      with _ -> true) ls

(*moved the liniarization to case_normalize_renamed_formula*)
and case_normalize_renamed_formula_x prog (avail_vars:(ident*primed) list) posib_expl (f:IF.formula) ann_vars:
      IF.formula* ((ident*primed)list) * ((ident*primed)list) = 
  (*existential wrapping and other magic tricks, avail_vars -> program variables, function arguments...*)
  (*returns the new formula, used variables and vars to be explicitly instantiated*)
  let rec match_exp (used_names : (ident*primed) list) (hargs : ((IP.exp * bool) * LO.t) list) pos :
        ((ident*primed) list) * (IP.exp list) * ((ident*primed) list) * IP.formula =

    match hargs with
      | ((e,rel_flag), label) :: rest ->
            let new_used_names, e_hvars, e_evars, e_link = match e with
              | IP.AConst (_,pos_e) -> ( used_names, [e ], [], IP.mkTrue pos_e)
              | IP.Var (v, pos_e) ->
                    (try
                      (* TODO :WN logic below for relational id seems wrong *)
                      if not(rel_flag) && not(List.mem v ann_vars) && ((List.mem v avail_vars) || (List.mem v used_names)) then
                        (*existential wrapping and liniarization*)
                        try
                            let todo_unk = I.look_up_rel_def_raw prog.I.prog_rel_decls (fst v) in
                          ((v :: used_names), [ e ], [],IP.mkTrue pos_e)
                              (* global relation name need not be captured in existential heap_var *)
                        with Not_found ->
                            let fresh_v =
                              (Ipure.fresh_old_name (fst v)),Unprimed
                            in
                        (* let () = print_endline ("l2: old=" ^ (fst v) ^ " new=" ^ (fst fresh_v)) in *)
                            let fresh_var = IP.Var (fresh_v,pos_e) in
                            let link_f = IP.mkEqExp fresh_var e pos_e in
                            (used_names, [ fresh_var ], [ fresh_v ], if LO.is_unlabelled label then link_f else IP.mkAndList [label, link_f])
                      else
                        if rel_flag then
                          ((v :: used_names), [ e ], [],IP.mkTrue pos_e)
                        else
                          ((v :: used_names), [ e ], [],IP.mkTrue pos_e)
                    with
                      | Not_found -> Err.report_error{ Err.error_loc = pos_e; Err.error_text = (fst v) ^ " is undefined"; })
              | _ -> Err.report_error { Err.error_loc = (IF.pos_of_formula f); Err.error_text = "malfunction with float out exp in normalizing"; } in
            let rest_used_names, rest_hvars, rest_evars, rest_link = match_exp new_used_names rest pos in
            let hvars = e_hvars @ rest_hvars in
            let evars = e_evars @ rest_evars in
            let link_f = IP.mkAnd e_link rest_link pos in
            (* Debug.info_hprint (add_str "case-norm hvars" pr_ident_list) hvars pos; *)
            (* Debug.info_hprint (add_str "case-norm evars" pr_ident_list) evars pos; *)
            (* Debug.info_hprint (add_str "case-norm link_f" Iprinter.string_of_pure_formula) link_f pos; *)
            (rest_used_names, hvars, evars, link_f)
      | [] -> (used_names, [], [], IP.mkTrue pos) in

  let match_exp (used_names : (ident*primed) list) (hargs : ((IP.exp * bool) * LO.t) list) pos :
        ((ident*primed) list) * (IP.exp list) * ((ident*primed) list) * IP.formula =
    let pr1 = pr_list (fun (i,_) -> i) in
    let pre = Iprinter.string_of_formula_exp in
    let pr2 = pr_list (fun (p,_) -> (pr_pair pre string_of_bool) p) in
    let pr3 (l1,l2,l3,f) = pr_triple pr1 (pr_list pre) pr1 (l1,l2,l3) in
    Debug.no_2 "match_exp" pr1 pr2 pr3 (fun _ _ -> match_exp used_names hargs pos) used_names hargs
  in
  let rec flatten f = match f with
    | IF.HTrue -> [IF.HTrue]
    | IF.HFalse -> []
    | IF.HEmp -> []
    | IF.Conj
            {  IF.h_formula_conj_h1 = f1;
            IF.h_formula_conj_h2 = f2;
            IF.h_formula_conj_pos = pos
            } 
    | IF.ConjStar
            {  IF.h_formula_conjstar_h1 = f1;
            IF.h_formula_conjstar_h2 = f2;
            IF.h_formula_conjstar_pos = pos
            } 
    | IF.ConjConj
            {  IF.h_formula_conjconj_h1 = f1;
            IF.h_formula_conjconj_h2 = f2;
            IF.h_formula_conjconj_pos = pos
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
            {     IF.h_formula_star_h1 = f1;
            IF.h_formula_star_h2 = f2;
            IF.h_formula_star_pos = pos
            } ->
          IF.mkStar (imm_heap f1) (imm_heap f2) pos 
    | IF.StarMinus
            {     IF.h_formula_starminus_h1 = f1;
            IF.h_formula_starminus_h2 = f2;
            IF.h_formula_starminus_pos = pos
            } ->
          IF.mkStarMinus (imm_heap f1) (imm_heap f2) pos           
    | IF.Conj
            {
                IF.h_formula_conj_h1 = f1;
                IF.h_formula_conj_h2 = f2;
                IF.h_formula_conj_pos = pos
            } ->
          IF.mkConj (imm_heap f1) (imm_heap f2) pos
    | IF.ConjStar
            {
                IF.h_formula_conjstar_h1 = f1;
                IF.h_formula_conjstar_h2 = f2;
                IF.h_formula_conjstar_pos = pos
            } ->
          IF.mkConjStar (imm_heap f1) (imm_heap f2) pos
    | IF.ConjConj
            {
                IF.h_formula_conjconj_h1 = f1;
                IF.h_formula_conjconj_h2 = f2;
                IF.h_formula_conjconj_pos = pos
            } ->
          IF.mkConjConj (imm_heap f1) (imm_heap f2) pos       
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
      | IF.ThreadNode {IF.h_formula_thread_node = (v, p);
        IF.h_formula_thread_name = c;
        IF.h_formula_thread_resource = rsr;
        IF.h_formula_thread_delayed = dl;
        IF.h_formula_thread_perm = perm; (*LDK*)
        IF.h_formula_thread_pos = pos;
        IF.h_formula_thread_label = pi;} ->
            let dataNode = IF.mkHeapNode (v,p) c [] 0 false SPLIT0 (Ipure.ConstAnn(Mutable)) false false false perm [] [] pi pos in
            let new_used_names1, evars1, datanode2, pf = linearize_heap used_names dataNode in
            let rsr2, new_used_names2, evars2 = case_normalize_renamed_formula prog avail_vars posib_expl rsr ann_vars in
            let node3 = match datanode2 with
              | IF.HeapNode { IF.h_formula_heap_node = c1; IF.h_formula_heap_name = id1;} ->
                    IF.ThreadNode {IF.h_formula_thread_node = c1;
                    IF.h_formula_thread_name = id1;
                    IF.h_formula_thread_resource = rsr2;
                    IF.h_formula_thread_delayed = dl;
                    IF.h_formula_thread_perm = perm; (*LDK*)
                    IF.h_formula_thread_pos = pos;
                    IF.h_formula_thread_label = pi;}
              | _ -> Error.report_error	{Error.error_loc = no_pos; Error.error_text = "expecting a ThreadNode"} 
            in
            (new_used_names1@new_used_names2,evars1@evars2,node3,pf)
      | IF.HeapNode b ->
            let pos = b.IF.h_formula_heap_pos in
            (*flag to check whether the heap node representing an invariant or not*)
            let isInv,labels,tp_vars = try
              let vdef = I.look_up_view_def_raw 11 prog.I.prog_view_decls b.IF.h_formula_heap_name in
              let flag = match vdef.I.view_inv_lock with
                | None -> false
                | Some _ -> true
              in
              (flag,(fst vdef.I.view_labels),vdef.I.view_typed_vars)
            with
              | Not_found -> (false,List.map (fun _ -> LO.unlabelled) b.IF.h_formula_heap_arguments,[])
            in
            (* Redundant checking: Already done in typeinfer.ml? *)
            let () = if (List.length b.IF.h_formula_heap_arguments) != (List.length labels) then
              report_error pos ("predicate "^b.IF.h_formula_heap_name^" does not have the correct number of arguments")
            in
            if (isInv) then
              (*TO CHECK: if heap node is a LOCK invariant => do nothing*)
              (used_names, [], f ,  IP.mkTrue no_pos)
            else
              let perm_labels,perm_var = 
                match b.IF.h_formula_heap_perm with
                  | None -> [],[]
                  | Some f ->
                        (match !Globals.perm with
                          | Bperm ->
                                (match f with
                                  | IP.Bptriple ((ec,et,ea),pos) ->
                                        let lbls = [LO.unlabelled;LO.unlabelled;LO.unlabelled] in
                                        lbls,[ec;et;ea]
                                  | _ ->  report_error pos ("linearize_heap : Expecting Bptriple for bperm"))
                          | _ ->  [LO.unlabelled], [f])
              in
              let args = b.IF.h_formula_heap_arguments in
              let ho_args = b.IF.h_formula_heap_ho_arguments in
            x_tinfo_hp (add_str "ty_vars" (pr_list (pr_pair string_of_typ pr_id))) tp_vars pos;
            x_tinfo_hp (add_str "heap args" (pr_list (Iprinter.string_of_formula_exp))) args pos;
            x_dinfo_hp (add_str "ho_args" (pr_list (Iprinter.string_of_rflow_formula))) ho_args pos;
              (* add a flag to indicate if it is a relational parameter or higher-order predicate
                 to disable renaming under these two scenarios *)
              let new_args = 
                if tp_vars==[] then List.map (fun e -> (e,false)) args
                else List.combine args (List.map (fun (a,_) -> is_RelT a || ho_args!=[]) tp_vars)
              in
              let perm_var = List.map (fun e -> (e,false)) perm_var in
              let heap_args = (List.combine (perm_var@new_args) (perm_labels@labels)) in
              let new_used_names, hvars, evars, link_f = match_exp used_names heap_args pos in
              (* let hvars = List.map (fun c-> Ipure.Var (c,pos)) hvars in *)
              (*split perm if any*)
              let perm_var,hvars = match b.IF.h_formula_heap_perm with
                | Some _ ->
                      (match !Globals.perm with
                        | Bperm ->
                              (*Note: ordering is important*)
                              let c = List.nth hvars 0 in
                              let t = List.nth hvars 1 in
                              let a = List.nth hvars 2 in
                              let hvars = List.tl (List.tl (List.tl hvars)) in
                              Some (IP.Bptriple ((c,t,a),no_pos)),hvars
                        | _ ->
                              (Some (List.hd hvars), List.tl hvars))
                | None -> (None,hvars)
              in
            let ho_hvars = List.map (fun ff ->
                let n_base, _ , _  = case_normalize_renamed_formula prog new_used_names posib_expl ff.IF.rflow_base ann_vars (*TOCHECH: how about two other return values*)
                in { ff with IF.rflow_base = n_base; }) b.IF.h_formula_heap_ho_arguments
              in
              let new_h = IF.HeapNode{ b with 
                  IF.h_formula_heap_arguments = hvars;
                  IF.h_formula_heap_ho_arguments = ho_hvars;
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
      | IF.StarMinus
              {
                  IF.h_formula_starminus_h1 = f1;
                  IF.h_formula_starminus_h2 = f2;
                  IF.h_formula_starminus_pos = pos
              } ->
            let new_used_names1, qv1, lf1, link1 = linearize_heap used_names f1 in
            let new_used_names2, qv2, lf2, link2 = linearize_heap new_used_names1 f2 in
            let tmp_h = IF.mkStarMinus lf1 lf2 pos in
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
      | IF.ConjStar
              {
                  IF.h_formula_conjstar_h1 = f1;
                  IF.h_formula_conjstar_h2 = f2;
                  IF.h_formula_conjstar_pos = pos
              } ->
            let new_used_names1, qv1, lf1, link1 = linearize_heap used_names f1 in
            let new_used_names2, qv2, lf2, link2 = linearize_heap new_used_names1 f2 in
            let tmp_h = IF.mkConjStar lf1 lf2 pos in
            let tmp_link = IP.mkAnd link1 link2 pos in
            (new_used_names2, (qv1 @ qv2), tmp_h, tmp_link)
      | IF.ConjConj
              {
                  IF.h_formula_conjconj_h1 = f1;
                  IF.h_formula_conjconj_h2 = f2;
                  IF.h_formula_conjconj_pos = pos
              } ->
            let new_used_names1, qv1, lf1, link1 = linearize_heap used_names f1 in
            let new_used_names2, qv2, lf2, link2 = linearize_heap new_used_names1 f2 in
            let tmp_h = IF.mkConjConj lf1 lf2 pos in
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
      | IF.HEmp -> (used_names, [], IF.HEmp, IP.mkTrue no_pos) 
      (* URGENT:TODO:WN:HVar *)
      | IF.HVar (v,hvar_vs) -> (used_names, [], IF.HVar (v,hvar_vs), IP.mkTrue no_pos) 
  in 

  (* added to filter out global relation from implicit quantification *)
  
  let linearize_heap (used_names:((ident*primed) list)) (f : IF.h_formula):
        (((ident*primed) list) * ((ident*primed) list) * IF.h_formula * Ipure.formula) =
    let (a,b,h,r) = linearize_heap used_names f in
    (* let a = hack_filter_global_rel a in  *)
    (a,b,imm_heap h,r)
  in
  let linearize_heap (used_names:((ident*primed) list)) (f : IF.h_formula):
        (((ident*primed) list) * ((ident*primed) list) * IF.h_formula * Ipure.formula) =
    let pr1 = Iprinter.string_of_h_formula in
    let pr2 (vl1,vl2,h, p) = (pr_ident_list vl1)^(pr_ident_list vl2)^(Iprinter.string_of_h_formula h)^"&&$"^(Iprinter.string_of_pure_formula p) in
    let pr0 (vs:((ident*primed) list))= 
      let idents, _ = List.split vs in
      (string_of_ident_list idents) in
    Debug.no_2 "linearize_heap" pr0 pr1 pr2 (fun _ _ -> linearize_heap used_names f) used_names f in

  let rec normalize_base heap cp vp fl a evs pos : IF.formula* ((ident*primed)list)* ((ident*primed)list) =
    (*let () = print_string("Before Normalization : "^(Iprinter.string_of_h_formula heap)^"\n") in*)
    let heap = (*if !Globals.allow_mem then heap else*) Immutable.normalize_h_formula heap false in 
    (*let () = print_string("After Normalization : "^(Iprinter.string_of_h_formula heap)^"\n") in*)
    let nu, h_evars, new_h, link_f = linearize_heap [] heap in
    (*let new_h = if !Globals.allow_mem then Mem.normalize_h_formula new_h else new_h in*)
    (****processsing formula_*_and***********)
    (*Note: f.formula_thread should appear in f.formula_pure*)
    let func evars (f:IF.one_formula) = normalize_base f.IF.formula_heap f.IF.formula_pure IVP.empty_vperm_sets top_flow [] evars f.IF.formula_pos in
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
              let f1 = {f with IF.formula_thread = f2.IF.formula_thread;
                  IF.formula_delayed = f2.IF.formula_delayed} (*TO CHECK*)
              in
              (f1::rs,evars1@evars2)
    in
    let tmp = List.combine new_a a in
    let new_a, evars_a = func2 tmp in
    let used_vars_a = List.concat used_vars_a in
    let to_expl_a = List.concat to_expl_a in
    let new_p = x_add Ipure.mkAnd cp link_f pos in
    let nu = nu@used_vars_a in
    let posib_expl = Gen.BList.remove_dups_eq (=) (posib_expl@to_expl_a) in
    let tmp_evars, to_expl =
      (let init_evars = Gen.BList.remove_dups_eq (=) (evars_a@h_evars@evs) in
      let to_evars = Gen.BList.difference_eq (=) init_evars posib_expl in
      let to_expl = Gen.BList.intersect_eq (=) init_evars posib_expl in       
      (to_evars,to_expl))in
    let result = IF.mkExists tmp_evars new_h new_p vp fl new_a pos in
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
    | IF.Base b -> normalize_base 
        b.IF.formula_base_heap b.IF.formula_base_pure b.IF.formula_base_vperm 
        b.IF.formula_base_flow b.IF.formula_base_and [] b.IF.formula_base_pos
    | IF.Exists b -> normalize_base 
        b.IF.formula_exists_heap b.IF.formula_exists_pure b.IF.formula_exists_vperm
        b.IF.formula_exists_flow b.IF.formula_exists_and b.IF.formula_exists_qvars b.IF.formula_exists_pos in
  helper f    

(* AN HOA : TODO CECK *)
and case_normalize_formula prog (h:(ident*primed) list)(f:IF.formula): IF.formula =
  let pr = Iprinter.string_of_formula in
  let pr2 = pr_list (string_of_primed_ident) in
  Debug.no_2 "case_normalize_formula" pr2 pr pr (fun _ _ -> case_normalize_formula_x prog h f) h f

and case_normalize_formula_x prog (h:(ident*primed) list)(f:IF.formula): IF.formula = 
  (*called for data invariants and assume formulas ... rename bound, convert_struc2 float out exps from heap struc*)
  (* let () = print_string ("case_normalize_formula :: CHECK POINT 0 ==> f = " ^ Iprinter.string_of_formula f ^ "\n") in *)
  let f = convert_heap2 prog f in
  (* let () = print_string ("case_normalize_formula :: CHECK POINT 1 ==> f = " ^ Iprinter.string_of_formula f ^ "\n") in *)
  let f = IF.float_out_thread f in
  let () = x_dinfo_hp (fun f -> ("case_normalize_formula :: CHECK POINT 1a ==> f = " ^ Iprinter.string_of_formula f ^ "\n")) f no_pos in
  let f = IF.float_out_exps_from_heap 1 (I.lbl_getter prog) (I.annot_args_getter prog) f in (*andreeac - check rel*)
  let () = x_dinfo_hp (fun f -> ("case_normalize_formula :: CHECK POINT 1b ==> f = " ^ Iprinter.string_of_formula f ^ "\n")) f no_pos in
  let f = IF.float_out_min_max f in
  (* let () = print_string ("case_normalize_formula :: CHECK POINT 2 ==> f = " ^ Iprinter.string_of_formula f ^ "\n") in *)
  let f = x_add_1 IF.rename_bound_vars f in
  (* let () = print_string ("case_normalize_formula :: CHECK POINT 2 ==> f = " ^ Iprinter.string_of_formula f ^ "\n") in *)
  let ann_vars = IF.collect_annot_vars f in 
  let f,_,_ = case_normalize_renamed_formula prog h [] f ann_vars in
  (* let () = print_string ("case_normalize_formula :: CHECK POINT 3 ==> f = " ^ Iprinter.string_of_formula f ^ "\n") in *)
  f

and case_normalize_formula_not_rename prog (h:(ident*primed) list)(f:IF.formula):IF.formula = 
  (*called for data invariants and assume formulas ... rename bound, convert_struc2 float out exps from heap struc*)

  (* let () = print_string ("case_normalize_formula :: CHECK POINT 0 ==> f = " ^ Iprinter.string_of_formula f ^ "\n") in *)
  let f = convert_heap2 prog f in
  let f = IF.float_out_thread f in
  let f = IF.float_out_exps_from_heap 2 (I.lbl_getter prog) (I.annot_args_getter prog) f in
  let f = IF.float_out_min_max f in
  let f = x_add_1 IF.rename_bound_vars f in
  (* let f,_,_ = case_normalize_renamed_formula prog h [] f in *)
  f

(* TODO : WN : type error with empty predicate errors/list-bug.slk *) 
and case_normalize_struc_formula i prog (h:(ident*primed) list)(p:(ident*primed) list)(f:IF.struc_formula) allow_primes
      allow_post_vars  (lax_implicit:bool)
      strad_vs :IF.struc_formula* ((ident*primed)list) =
  let pr0 = pr_list (fun (i,p) -> i) in
  let pr1 = Iprinter.string_of_struc_formula in
  let pr2 (x,_) = pr1 x in
  Debug.no_3_num i "case_normalize_struc_formula" pr0 pr0 pr1 pr2 
  (fun _ _ _ -> case_normalize_struc_formula_x prog h p f allow_primes allow_post_vars lax_implicit strad_vs) h p f

      
and case_normalize_struc_formula_x prog (h_vars:(ident*primed) list)(p_vars:(ident*primed) list)(f:IF.struc_formula) 
      allow_primes allow_post_vars (lax_implicit:bool) strad_vs :IF.struc_formula* ((ident*primed)list) =     
  
  let ilinearize_formula (f:IF.formula)(h:(ident*primed) list): IF.formula = 
    let need_quant = Gen.BList.difference_eq (=) (IF.all_fv f) h in
    let vars = List.filter (fun (c1,c2)->(c2==Primed && c1<>Globals.ls_name && c1<>Globals.lsmu_name)) need_quant in
    let () = if vars!=[] then 
      let msg = "Pass-by-value parameters and local variables can not escape out of scope: " ^ (string_of_primed_ident_list vars) in
      Err.report_error{ 
          Err.error_loc = IF.pos_of_formula f; 
          Err.error_text = msg; } 

    (*   Err.report_error{  *)
    (* Err.error_loc = IF.pos_of_formula f;  *)
    (* Err.error_text = "call-by-value parameters & existential vars should not be primed"; }  *)
    in
    (* let () = if (List.length need_quant)>0 then  *)
    (*   print_string ("\n warning "^(string_of_loc (IF.pos_of_formula f))^" quantifying: "^(Iprinter.string_of_var_list need_quant)^"\n") in *)
    x_tinfo_hp (add_str "need_quant" pr_ident_list) need_quant no_pos;
    let need_quant = hack_filter_global_rel prog need_quant in
    IF.push_exists need_quant f in
  (* let () = print_string ("case_normalize_struc_formula :: CHECK POINT 0 ==> f = " ^ Iprinter.string_of_struc_formula f ^ "\n") in *)
  let nf = convert_struc2 prog f in
  (* let () = print_string ("\ncase_normalize_struc_formula :: CHECK POINT 0.5 ==> f = " ^ Iprinter.string_of_struc_formula nf) in *)
  let nf = IF.float_out_thread_struc_formula (I.lbl_getter prog) (I.annot_args_getter prog) nf  in 
  (* let () = print_string ("\ncase_normalize_struc_formula :: CHECK POINT 1 ==> nf = " ^ Iprinter.string_of_struc_formula nf ) in *)
  let nf = IF.float_out_exps_from_heap_struc (I.lbl_getter prog) (I.annot_args_getter prog) nf  in 
  (* let () = print_string ("\ncase_normalize_struc_formula :: CHECK POINT 2 ==> nf = " ^ Iprinter.string_of_struc_formula nf) in *)
  let nf = IF.float_out_struc_min_max nf in
  (* let () = print_string ("case_normalize_struc_formula :: CHECK POINT 3 ==> nf = " ^ Iprinter.string_of_struc_formula nf ^ "\n") in *)

  (* let () = print_string ("\n b rename "^(Iprinter.string_of_struc_formula  nf))in *)
  let nf = IF.rename_bound_var_struc_formula nf in
  (* let () = print_string ("\n after ren: "^(Iprinter.string_of_struc_formula nf)^"\n") in *)
  (*convert anonym to exists*)
  let rec helper2 (h_vars:(ident*primed) list)(p_vars:(ident*primed) list)(nf:IF.struc_formula) allow_primes allow_post_vars 
        (lax_implicit:bool) strad_vs =   
    let rec helper (hv:(ident*primed) list) strad_vs vars (f0:IF.struc_formula):IF.struc_formula* ((ident*primed)list) = 
      let diff = Gen.BList.difference_eq (=) in
      let rdups = Gen.BList.remove_dups_eq (=) in
      let inters = Gen.BList.intersect_eq (=)  in
      let pr_l_v = pr_list (pr_pair pr_id string_of_primed) in
      match f0 with
        | IF.EAssume b-> 
              let onb = convert_anonym_to_exist b.IF.formula_assume_simpl in
              (*let onb_struc = convert_anonym_to_exist_struc b.IF.formula_assume_struc in*)
              let hp = rdups (hv @p_vars)in
              let ann_vars = IF.collect_annot_vars onb in 
              let nb,nh,_ = case_normalize_renamed_formula prog hp strad_vs onb ann_vars in
              (*let nb_struc = case_normalize_renamed_struc_formula prog hp stread_vs onb_struc in*)
              let nb = ilinearize_formula nb (hp@strad_vs) in
              (*let nb_struc = ilinearize_struc_formula nb_struc np in*)
                x_tinfo_hp (add_str "nb(after ilinearize)" Iprinter.string_of_formula) nb no_pos;
              let vars_list = IF.all_fv nb in
              let nb_old = nb in
              let nb = IF.prune_exists nb vars in (* Remove exists_vars included in infer_vars *) 
              (*let nb_struc = IF.prune_exists_struc nb_struc vars in*)
              let nb_struc,_ = helper2 hv p_vars b.IF.formula_assume_struc true true  false strad_vs in
              let non_ex_vars = hv@p_vars@strad_vs@vars in
              (* no automatic wrapping of exists for post-condition *)
              let nb_struc = IF.wrap_post_struc_ex (non_ex_vars) nb_struc in
                (* Debug.ninfo_hprint (add_str "simp_form(before)" Iprinter.string_of_formula) nb_old no_pos; *)
                (* Debug.ninfo_hprint (add_str "simp_form" Iprinter.string_of_formula) nb no_pos; *)
                (* Debug.ninfo_hprint (add_str "after wrap_post" Iprinter.string_of_struc_formula) nb_struc no_pos; *)
              (* and case_normalize_struc_formula_x prog (h_vars:(ident*primed) list)
                 (p_vars:(ident*primed) list)(f:IF.struc_formula) allow_primes allow_post_vars (lax_implicit:bool)
                 strad_vs :IF.struc_formula* ((ident*primed)list) *)
              let rem_vs = diff vars_list p_vars (* non_ex_vars *) in
                x_tinfo_hp (add_str "vars_list" pr_l_v) vars_list no_pos;
                x_tinfo_hp (add_str "p_list" pr_l_v) p_vars no_pos;
                x_tinfo_hp (add_str "rem_vs" pr_l_v) rem_vs no_pos;
              (IF.EAssume {b with IF.formula_assume_simpl = nb;IF.formula_assume_struc = nb_struc;},rem_vs) 
        | IF.ECase b->
              let r1,r2 = List.fold_left (fun (a1,a2)(c1,c2)->
                  let r12 = inters (Ipure.fv c1) hv in
                  let r21,r22 = helper hv strad_vs vars c2 in
                  (((c1,r21)::a1),r12::r22::a2)
              ) ([],[]) b.IF.formula_case_branches in             
              (IF.ECase {b with IF.formula_case_branches = r1 },rdups (List.concat r2))
        | IF.EBase b->        
              let pos = b.IF.formula_struc_pos in
              let init_expl = b.IF.formula_struc_explicit_inst in
                let () = if (List.length (inters hv init_expl))>0 then 
                Error.report_error {Error.error_loc = b.IF.formula_struc_pos;
                Error.error_text = "the late instantiation variables collide with the used vars"}
                else () in
              let onb = convert_anonym_to_exist b.IF.formula_struc_base in
              let ann_vars = IF.collect_annot_vars onb in 
              let nb,h3,new_expl = case_normalize_renamed_formula prog hv strad_vs onb ann_vars in
              let all_expl = rdups (new_expl @ init_expl) in
                let () = x_tinfo_hp (add_str "new_expl" pr_l_v)  new_expl pos in
                let () = x_tinfo_hp (add_str "init_expl" pr_l_v)  init_expl pos in
              let new_strad_vs = diff strad_vs new_expl in   
              let all_vars = rdups (hv@all_expl) in
              let onb_vars = IF.heap_fv onb in
                let () = x_tinfo_hp (add_str "onb_vars" pr_l_v) onb_vars pos in
              let posib_impl = diff onb_vars all_vars in
              let h1prm = rdups (all_vars@posib_impl) in
                let () = if (not allow_primes)&&(List.length (List.filter (fun (c1,c2)-> c2==Primed) (all_expl@posib_impl)))>0 then
                Error.report_error {Error.error_loc = pos; Error.error_text = "should not have prime vars"} else () in
              (*
                @1! all_expl:[]
                @1! possib_impl:[(x,'),(a,),(res2,)]
                @1! p:[(x,'),(Anon_11,'),(next_21_514,')]
              *)
                let () = x_tinfo_hp (add_str "all_expl" pr_l_v)  all_expl pos in
                let () = x_tinfo_hp (add_str "possib_impl" pr_l_v)  posib_impl pos in
                let () = x_tinfo_hp (add_str "p_vars" pr_l_v) p_vars pos in
                let () = if not(allow_post_vars) && (List.length (inters (all_expl@posib_impl) p_vars))>0 then   
                Error.report_error {Error.error_loc = pos; Error.error_text = "post variables should not appear here"} else () in
              let nc,h2 = match b.IF.formula_struc_continuation with 
                | None-> (None,[]) 
                | Some l-> 
                      let r1,r2 = helper h1prm new_strad_vs vars l in 
                      (Some r1,r2) in
                (* Debug.ninfo_hprint (add_str "struc_cont" (pr_option Iprinter.string_of_struc_formula)) nc no_pos; *)
              let implvar = diff (IF.unbound_heap_fv onb) all_vars in
                let () = if (List.length (diff implvar (IF.heap_fv onb @ fold_opt IF.struc_hp_fv nc)))>0 then 
                  Error.report_error {Error.error_loc = pos; Error.error_text = ("malfunction: some implicit vars are not heap_vars\n")} else () in
              let implvar = hack_filter_global_rel prog implvar in
              (IF.EBase {
                  IF.formula_struc_base = nb;
                  IF.formula_struc_implicit_inst =implvar;                    
                  IF.formula_struc_explicit_inst = all_expl;
                  IF.formula_struc_exists = [];
                  IF.formula_struc_is_requires = b.IF.formula_struc_is_requires;
                  IF.formula_struc_continuation = nc;
                  IF.formula_struc_pos = pos},rdups (h2@h3))
        | IF.EInfer b -> (* Tricky thing *)
              (IF.EInfer {b with IF.formula_inf_continuation = fst (helper hv strad_vs b.IF.formula_inf_vars b.IF.formula_inf_continuation)}, [])
        | IF.EList b -> 
              let ll1, ll2 = map_l_snd_res (helper hv strad_vs vars) b in   
              (IF.EList ll1, rdups (List.concat ll2))
    in    
    let pr = fun _ -> 
        let prl = pr_list !IP.print_id in
        "h_vars: "^(prl h_vars)^
            "\n p_vars: "^(prl p_vars)^
            "\n form: "^(!IF.print_struc_formula nf)^
            "\n allow_primes: "^(string_of_bool allow_primes)^
            "\n allow_post_vars: "^(string_of_bool allow_post_vars)^
            "\n lax_implicit: "^(string_of_bool lax_implicit)
        ^"\n strad_vs: "^(prl strad_vs)^"\n" in
    Debug.no_1 "case_normalize_helper2" pr (pr_pair !IF.print_struc_formula (fun _ -> "")) (helper h_vars strad_vs [])  nf 
  in helper2 h_vars p_vars nf allow_primes allow_post_vars lax_implicit strad_vs
         


         
and simpl_case_normalize_struc_formula id prog (h_vars:(ident*primed) list)(f:IF.struc_formula) 
      :IF.struc_formula = 	
  let diff = Gen.BList.difference_eq (=) in
  let rdups = Gen.BList.remove_dups_eq (=) in
  let inters = Gen.BList.intersect_eq (=)  in
  let pr_l_v = pr_list (pr_pair pr_id string_of_primed) in
  let pos = IF.pos_of_struc_formula f in
				
  let nf = convert_struc2 prog f in
  let nf = IF.float_out_thread_struc_formula (I.lbl_getter prog) (I.annot_args_getter prog) nf  in 
  let nf = IF.float_out_exps_from_heap_struc (I.lbl_getter prog) (I.annot_args_getter prog) nf  in 
  let nf = IF.float_out_struc_min_max nf in
  let nf = IF.rename_bound_var_struc_formula nf in
  
  let rec helper_x (hv:(ident*primed) list)(f0:IF.struc_formula) : IF.struc_formula = 
		match f0 with
		  | IF.EAssume _
		  | IF.EInfer _ -> Gen.report_error pos "View defs should not have postconditions or infer stages"  
		  | IF.ECase b-> IF.ECase {b with IF.formula_case_branches = 
				map_l_snd (helper hv) b.IF.formula_case_branches}
		  | IF.EBase {
			IF.formula_struc_explicit_inst = init_expl;
                        IF.formula_struc_is_requires = ir;
			IF.formula_struc_continuation = cont;
			IF.formula_struc_base = base; }->		
			if (List.length (inters hv init_expl))>0 then 
			  Gen.report_error pos  "the late instantiation variables collide with the used vars" 
			else 
			  let onb = convert_anonym_to_exist base in
                          let ann_vars = IF.collect_annot_vars onb in 
			  let nb,h3,new_expl = case_normalize_renamed_formula prog hv [] onb ann_vars in
			  let all_expl = rdups (new_expl @ init_expl) in
			  let v_no_inst = rdups (hv@all_expl) in 
			  let nb_fv = IF.heap_fv nb in
			  (*let impl_var = diff (inters nb_fv (fold_opt IF.struc_case_fv cont))
			    v_no_inst in*)
                          (* asankhs: Changed to below to avoid type error*)
                          let impl_var = diff (IF.unbound_heap_fv onb) v_no_inst in
			  let new_v_no_inst = rdups (impl_var@v_no_inst) in
			  let () = x_tinfo_hp (add_str "new_expl" pr_l_v)  new_expl pos in
			  let () = x_tinfo_hp (add_str "h3" pr_l_v)  h3 pos in
			  let () = x_tinfo_hp (add_str "v_no_inst" pr_l_v)  v_no_inst pos in
			  let () = x_tinfo_hp (add_str "nb_fv" pr_l_v)  nb_fv pos in
			  let () = x_tinfo_hp (add_str "new_v_no_inst" pr_l_v)  new_v_no_inst pos in
			  let () = x_tinfo_hp (add_str "impl_var" pr_l_v)  impl_var pos in
			  let extra_exists = IF.push_exists (diff nb_fv new_v_no_inst) nb in
			  IF.EBase {
			      IF.formula_struc_base = extra_exists;
			      IF.formula_struc_implicit_inst =hack_filter_global_rel prog impl_var;		
			      IF.formula_struc_explicit_inst = all_expl;
			      IF.formula_struc_exists = [];
                              IF.formula_struc_is_requires = ir;
			      IF.formula_struc_continuation = map_opt (helper new_v_no_inst) cont;
			      IF.formula_struc_pos = pos}
		  | IF.EList b -> IF.EList (map_l_snd (helper hv) b)
  and	 helper (h_vars:(ident*primed) list)(nf:IF.struc_formula) =   
    let pr l= "h_vars: "^(pr_list !IP.print_id l) in
    let pr2 = Iprinter.string_of_struc_formula in
    Debug.no_2(* _loop *) "case_normalize_helper" pr pr2 pr2 helper_x h_vars  nf in
  helper h_vars nf

and case_normalize_struc_formula_view i prog (h:(ident*primed) list)(p:(ident*primed) list)(f:IF.struc_formula) allow_primes allow_post_vars  (lax_implicit:bool) strad_vs :IF.struc_formula= 
	if (!Globals.simplified_case_normalize) then 
		let r2 = simpl_case_normalize_struc_formula i prog h f in
		(*let r1 = fst (case_normalize_struc_formula i prog h p f allow_primes allow_post_vars lax_implicit strad_vs) in
		let () = print_string ("\n simpl: "^(Iprinter.string_of_struc_formula r2)^"\n prev: "^ 
				  (Iprinter.string_of_struc_formula r1)^"\n") in
		*) 
		r2
	else fst (case_normalize_struc_formula i prog h p f allow_primes allow_post_vars lax_implicit strad_vs)
	
and case_normalize_coerc_x prog (cd: Iast.coercion_decl):Iast.coercion_decl = 
  let nch = case_normalize_formula prog [] cd.Iast.coercion_head in
  let ncb = case_normalize_formula prog [] cd.Iast.coercion_body in
  { Iast.coercion_type = cd.Iast.coercion_type;
    Iast.coercion_type_orig = cd.Iast.coercion_type_orig;
    Iast.coercion_exact = cd.Iast.coercion_exact;
    Iast.coercion_infer_vars = cd.Iast.coercion_infer_vars;
    Iast.coercion_name = cd.Iast.coercion_name;
    Iast.coercion_head = nch;
    Iast.coercion_body = ncb;
    Iast.coercion_proof = cd.Iast.coercion_proof;
    I.coercion_kind = cd.I.coercion_kind;
    I.coercion_origin = cd.I.coercion_origin; }

and case_normalize_coerc prog (cd: Iast.coercion_decl):Iast.coercion_decl = 
  Debug.no_1 "case_normalize_coerc" pr_none pr_none (fun _ ->  case_normalize_coerc_x prog cd) cd

and case_normalize_coerc_list prog (cdl: Iast.coercion_decl_list): Iast.coercion_decl_list =
  let new_elems = List.map (case_normalize_coerc prog) cdl.Iast.coercion_list_elems in
  {Iast.coercion_list_elems = new_elems;
   Iast.coercion_list_kind  = cdl.Iast.coercion_list_kind;}
      
and ren_list_concat (l1:((ident*ident) list)) (l2:((ident*ident) list)):((ident*ident) list) = 
  let fl2 = fst (List.split l2) in
  let nl1 = List.filter (fun (c1,c2)-> not (List.mem c1 fl2)) l1 in (nl1@l2)

and subid (ren:(ident*ident) list) (i:ident) :ident = 
  let nl = List.filter (fun (c1,c2)-> (String.compare c1 i)==0) ren in
  if (List.length nl )> 0 then let _,l2 = List.hd nl in l2
  else i            
    
and rename_exp (ren:(ident*ident) list) (f:Iast.exp):Iast.exp =
  let pr1 = pr_list (pr_pair pr_id pr_id) in
  let pr2 = Iprinter.string_of_exp in
  Debug.no_2 "rename_exp" pr1 pr2 pr2 rename_exp_x ren f

and rename_exp_x (ren:(ident*ident) list) (f:Iast.exp):Iast.exp = 
  
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
              Iast.exp_assert_type = b.I.exp_assert_type;
              Iast.exp_assert_path_id = b.Iast.exp_assert_path_id} (*in
                                                                     let () = print_string (" before ren assert: "^(Iprinter.string_of_exp f)^"\n") in 
                                                                     let () = print_string (" after ren assert: "^(Iprinter.string_of_exp r)^"\n") in 
                                                                     r*)
    | Iast.ArrayAt b->
          Iast.ArrayAt  {  Iast.exp_arrayat_array_base = helper ren b.Iast.exp_arrayat_array_base; (* substitute the new name for array name if it is in ren *)
          Iast.exp_arrayat_index = List.map (helper ren) b.Iast.exp_arrayat_index;
          Iast.exp_arrayat_pos = b.Iast.exp_arrayat_pos}
    | Iast.Assign b->
          Iast.Assign   {  Iast.exp_assign_op = b.Iast.exp_assign_op;
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
    | Iast.CallNRecv b -> 
      let subst_list = List.fold_left (fun a (c1, c2) -> 
        ((c1, Unprimed), (c2, Unprimed))::((c1, Primed), (c2, Primed))::a) [] ren in
      let ho_arg = match b.Iast.exp_call_nrecv_ho_arg with
        | None -> None
        | Some f -> Some (IF.subst subst_list f) 
     in Iast.CallNRecv{ b with 
        Iast.exp_call_nrecv_arguments = List.map (helper ren) b.Iast.exp_call_nrecv_arguments;
        Iast.exp_call_nrecv_ho_arg = ho_arg; }
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
              Iast.exp_member_base = helper ren b.Iast.exp_member_base}
              (* bug introduced by WN *)
              (* Iast.exp_member_fields = List.map (subid ren ) b.Iast.exp_member_fields *)
              (* An Hoa *)
    | Iast.ArrayAlloc b-> 
          Iast.ArrayAlloc {b with Iast.exp_aalloc_dimensions = List.map (helper ren) b.Iast.exp_aalloc_dimensions}
    | Iast.New b-> 
          Iast.New {b with Iast.exp_new_arguments = List.map (helper ren) b.Iast.exp_new_arguments}
    | Iast.Return b ->  Iast.Return {b with Iast.exp_return_val = match b.Iast.exp_return_val with
        | None -> None
        | Some f -> Some (x_add rename_exp ren f)}
    | Iast.Seq b -> Iast.Seq 
          { Iast.exp_seq_exp1 = x_add rename_exp ren b.Iast.exp_seq_exp1;
          Iast.exp_seq_exp2 = x_add rename_exp ren b.Iast.exp_seq_exp2;
          Iast.exp_seq_pos = b.Iast.exp_seq_pos }         
    | Iast.Unary b-> Iast.Unary {b with Iast.exp_unary_exp = x_add rename_exp ren b.Iast.exp_unary_exp}
    | Iast.Unfold b-> Iast.Unfold{b with Iast.exp_unfold_var = ((subid ren (fst b.Iast.exp_unfold_var)),(snd b.Iast.exp_unfold_var))}
    | Iast.Var b -> Iast.Var{b with Iast.exp_var_name = subid ren b.Iast.exp_var_name}
    | Iast.While b-> 
          let nw = match b.Iast.exp_while_wrappings with
            | None -> None
            | Some (e,l) -> Some ((x_add rename_exp ren e),l)  in
          Iast.While{
              Iast.exp_while_condition = x_add rename_exp ren b.Iast.exp_while_condition;
              Iast.exp_while_body = x_add rename_exp ren b.Iast.exp_while_body;
              Iast.exp_while_addr_vars = [];
              Iast.exp_while_jump_label = b.Iast.exp_while_jump_label;
              Iast.exp_while_f_name = b.Iast.exp_while_f_name;
              Iast.exp_while_wrappings = nw;
              Iast.exp_while_specs = IF.subst_struc (List.fold_left(fun a (c1,c2)-> ((c1,Unprimed),(c2,Unprimed))::((c1,Primed),(c2,Primed))::a) [] ren) b.Iast.exp_while_specs;
              Iast.exp_while_path_id = b.Iast.exp_while_path_id;
              Iast.exp_while_pos = b.Iast.exp_while_pos;}
    | Iast.Time _ ->f
    | Iast.Try b -> 
          Iast.Try { b with
              Iast.exp_try_block = x_add rename_exp ren b.Iast.exp_try_block;
              Iast.exp_catch_clauses = List.map (x_add rename_exp ren) b.Iast.exp_catch_clauses;
              Iast.exp_finally_clause = List.map (x_add rename_exp ren) b.Iast.exp_finally_clause;}
    | Iast.Raise b-> 
          Iast.Raise {b with
              Iast.exp_raise_val = (match b.Iast.exp_raise_val with 
                | None -> None 
                | Some e -> Some (x_add rename_exp ren e));
              Iast.exp_raise_type = (match b.Iast.exp_raise_type with
                | Iast.Const_flow _ -> b.Iast.exp_raise_type
                | Iast.Var_flow vf -> Iast.Var_flow (subid ren vf))}
    | I.Par p ->
      let sst = List.fold_left (fun a (c1, c2) ->
        ((c1, Unprimed), (c2, Unprimed))::((c1, Primed), (c2, Primed))::a) [] ren 
      in
      let subst_ren ren (id, primed) = (subid ren id, primed) in
      let rename_par_case c = 
        let body = x_add rename_exp ren c.I.exp_par_case_body in
        let cond = map_opt (fun f -> IF.subst sst f) c.I.exp_par_case_cond in
        let vp = IVP.subst_f subst_ren ren c.I.exp_par_case_vperm in
        { I.exp_par_case_cond = cond;
          I.exp_par_case_vperm = vp;
          I.exp_par_case_else = c.I.exp_par_case_else;
          I.exp_par_case_body = body; 
          I.exp_par_case_pos = c.I.exp_par_case_pos; }
      in
      I.Par {
        I.exp_par_vperm = IVP.subst_f subst_ren ren p.I.exp_par_vperm; 
        I.exp_par_lend_heap = IF.subst sst p.I.exp_par_lend_heap;
        I.exp_par_cases = List.map rename_par_case p.I.exp_par_cases; 
        I.exp_par_pos = p.I.exp_par_pos; }
  in helper ren f 

and case_rename_var_decls_init (f:Iast.exp) : (Iast.exp * ((ident*ident) list)) =  
  let pr = Iprinter.string_of_exp in
  let pr_subs = pr_list (pr_pair pr_id pr_id) in
  Debug.no_1 "case_rename_var_decls" pr (pr_pair pr pr_subs) case_rename_var_decls f

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
            Iast.exp_catch_body = fst (case_rename_var_decls (x_add rename_exp ren b.Iast.exp_catch_body));},[])
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
        let l2 = x_add rename_exp ren l2 in      
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
  | I.Par p ->
    (I.Par { p with
      I.exp_par_cases = List.map (fun c -> { c with 
          I.exp_par_case_body = fst (case_rename_var_decls c.I.exp_par_case_body); }) 
        p.I.exp_par_cases; }, [])


and err_prim_l_vars s l pos= 
  List.iter (fun (c1,c2)-> match c2 with
    | Primed  ->
        (*LOCKSET: ignore "ghost" parameter ls*)
        if (c1 = Globals.ls_name || c1 = Globals.lsmu_name || c1 = Globals.waitlevel_name) then () else
        Error.report_error { 
          Error.error_loc = pos;
          Error.error_text = c1^"' "^s}
    | Unprimed -> () ) l
      
and check_eprim_in_formula s f = match f with
  | IF.Or o -> (check_eprim_in_formula s o.IF.formula_or_f1; check_eprim_in_formula s o.IF.formula_or_f2 )
  | IF.Base b-> ()
  | IF.Exists e-> err_prim_l_vars s e.IF.formula_exists_qvars e.IF.formula_exists_pos

and check_eprim_in_struc_formula s f =
  let pr2 = Iprinter.string_of_struc_formula in
  Debug.no_2 "check_eprim_in_struc_formula" 
      pr_id pr2 pr_none check_eprim_in_struc_formula_x s f

and check_eprim_in_struc_formula_x s f = match f with
  | IF.ECase b-> List.iter (fun (_,c2)-> check_eprim_in_struc_formula_x s c2) b.IF.formula_case_branches
  | IF.EBase b-> 
        (err_prim_l_vars s b.IF.formula_struc_exists b.IF.formula_struc_pos; 
        check_eprim_in_formula s b.IF.formula_struc_base;
        match b.IF.formula_struc_continuation with | None-> () | Some l-> check_eprim_in_struc_formula_x s l)
  | IF.EAssume b -> check_eprim_in_formula " is not a ref param " b.IF.formula_assume_simpl
  | IF.EInfer b -> check_eprim_in_struc_formula_x s b.IF.formula_inf_continuation
  | IF.EList b -> List.iter (fun (_,c)-> check_eprim_in_struc_formula_x s c) b

and case_normalize_exp prog (h: (ident*primed) list) (p: (ident*primed) list)(f:Iast.exp) :
      Iast.exp*((ident*primed) list)*((ident*primed) list) =  match f with
        | Iast.Assert b->
              let asrt_nf,nh = match b.Iast.exp_assert_asserted_formula with
                | None -> (None,h)
                | Some asserted_f -> 
                      let r, _ = case_normalize_struc_formula 3 prog h p (fst asserted_f) true 
                        false (*allow_post_vars*) false [] in
                      let () = check_eprim_in_struc_formula " is not a valid program variable " r in
                      (Some (r,(snd asserted_f)),h) in
              let assm_nf  = match b.Iast.exp_assert_assumed_formula with
                | None-> None 
                | Some f -> 
                      let r = case_normalize_formula prog nh f in 
                      let () = check_eprim_in_formula " is not a valid program variable " r in
                      Some r in
              let rez_assert = Iast.Assert { Iast.exp_assert_asserted_formula = asrt_nf;
              Iast.exp_assert_assumed_formula = assm_nf;
              Iast.exp_assert_pos = b.Iast.exp_assert_pos;
              Iast.exp_assert_type = b.I.exp_assert_type;
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
          let nl = List.map (fun c-> let r1, _, _ = case_normalize_exp prog h p c in r1) b.Iast.exp_call_nrecv_arguments in
          let ho_arg = match b.Iast.exp_call_nrecv_ho_arg with
            | None -> None
            | Some f ->
              let r = case_normalize_formula prog h f in
              let () = check_eprim_in_formula " is not a valid program variable " r in
              Some r 
          in 
          let nc = Iast.CallNRecv { b with 
              Iast.exp_call_nrecv_ho_arg = ho_arg;
              Iast.exp_call_nrecv_arguments = nl }
          in (nc, h, p) 
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
              (* let () = print_endline ("h = " ^ (pr_list (fun (id,pr) -> id^(string_of_primed pr)) h)) in *)
              (* let () = print_endline ("p = " ^ (pr_list (fun (id,pr) -> id^(string_of_primed pr)) p)) in *)
              (* let () = print_endline ("strad = " ^ (pr_list (fun (id,pr) -> id^(string_of_primed pr)) strad)) in *)
              let h = List. map (fun (id,_) -> (id,Unprimed)) h in (*TO CHECK: we may need to modify h for all in case_normalize_exp *)
              (*LOCKSET variable*********)
              let ls_pvar = (ls_name,Primed) in
              let ls_uvar = (ls_name,Unprimed) in
              let lsmu_pvar = (lsmu_name,Primed) in
              let lsmu_uvar = (lsmu_name,Unprimed) in
              let waitlevel_pvar = (waitlevel_name,Primed) in
              let waitlevel_uvar = (waitlevel_name,Unprimed) in
              let lock_vars = [waitlevel_uvar;waitlevel_pvar;lsmu_uvar;lsmu_pvar;ls_uvar;ls_pvar] in
              (**************************)
              let p = lock_vars@p in
              (*let ns,_ = case_normalize_struc_formula 4 prog h p b.Iast.exp_while_specs false false strad in*)
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
        | I.Par b ->
          let case_normalize_cond f =
            let r = case_normalize_formula prog h f in
            let () = check_eprim_in_formula " is not a valid program variable " r in
            r 
          in
          let case_normalize_par_case c =
            let cond = map_opt case_normalize_cond c.I.exp_par_case_cond in
            let body, _, _ = case_normalize_exp prog h p c.I.exp_par_case_body in
            { c with I.exp_par_case_cond = cond; I.exp_par_case_body = body; } 
          in
          (I.Par { b with 
            I.exp_par_cases = List.map (fun c -> case_normalize_par_case c) b.I.exp_par_cases; 
            I.exp_par_lend_heap = case_normalize_cond b.I.exp_par_lend_heap; },
          h, p)

and case_normalize_data prog (f:Iast.data_decl):Iast.data_decl =
  let h = List.map (fun f -> (I.get_field_name f,Unprimed) ) f.Iast.data_fields in  
  {f with Iast.data_invs = List.map (fun x -> case_normalize_formula prog h x) f.Iast.data_invs}

and case_normalize_proc prog (f:Iast.proc_decl):Iast.proc_decl =
  let pr = Iprinter.string_of_proc_decl in
  Debug.no_1 "case_normalize_proc" pr pr
      (fun _ -> case_normalize_proc_x prog f) f

and case_normalize_proc_x prog (f:Iast.proc_decl):Iast.proc_decl = 
  let gl_v_l = List.map (fun c-> List.map (fun (v,_,_)-> (c.I.exp_var_decl_type,v)) c.I.exp_var_decl_decls) prog.I.prog_global_var_decls in
  let gl_v =  List.map (fun (c1,c2)-> {I.param_type = c1; I.param_name = c2; I.param_mod = I.RefMod; I.param_loc = no_pos })(List.concat gl_v_l) in
  let gl_proc_args = gl_v @ f.Iast.proc_args in
  let gl_proc_args = gl_proc_args @ (match f.Iast.proc_ho_arg with | None -> [] | Some ha -> [ha]) in
  let h = (List.map (fun c1 -> (c1.Iast.param_name, Unprimed)) gl_proc_args) in
  let h_prm = (List.map (fun c1 -> (c1.Iast.param_name, Primed)) gl_proc_args) in
  (*LOCKSET variable*********)
  let ls_pvar = (ls_name,Primed) in
  let ls_uvar = (ls_name,Unprimed) in
  let lsmu_pvar = (lsmu_name,Primed) in
  let lsmu_uvar = (lsmu_name,Unprimed) in
  let waitlevel_pvar = (waitlevel_name,Primed) in
  let waitlevel_uvar = (waitlevel_name,Unprimed) in
  let lock_vars = [waitlevel_uvar;waitlevel_pvar;lsmu_uvar;lsmu_pvar;ls_uvar;ls_pvar] in
  (**************************)
  let p = lock_vars@((eres_name,Unprimed)::(res_name,Unprimed)::
         (List.map (fun c1-> (c1.Iast.param_name,Primed)) 
         (List.filter (fun c-> c.Iast.param_mod == Iast.RefMod) gl_proc_args))) in
  let strad_s = 
    let pr,pst = IF.struc_split_fv f.Iast.proc_static_specs false in
    Gen.BList.intersect_eq (=) pr pst in
  (* let () = print_endline ("h (proc) = " ^ (pr_list (fun (id,pr) -> id^(string_of_primed pr)) h)) in *)
  (* let () = print_endline ("p (proc)= " ^ (pr_list (fun (id,pr) -> id^(string_of_primed pr)) p)) in *)
  let nst,h11 = case_normalize_struc_formula 5 prog h p f.Iast.proc_static_specs false 
    false (*allow_post_vars*) false strad_s in
  (* let () = print_endline ("strad_s = " ^ (pr_list (fun (id,pr) -> id^(string_of_primed pr)) strad_s)) in *)
  let () = check_eprim_in_struc_formula " is not allowed in precond " nst in 
  let strad_d = 
    let pr,pst = IF.struc_split_fv f.Iast.proc_static_specs false in
    Gen.BList.intersect_eq (=) pr pst in
  let ndn, h12 = case_normalize_struc_formula 6 prog h p f.Iast.proc_dynamic_specs false 
    false (*allow_post_vars*) false strad_d in
  let () = check_eprim_in_struc_formula "is not allowed in precond " ndn in
  let h1 = Gen.BList.remove_dups_eq (=) (h11@h12) in 
  let h2 = Gen.BList.remove_dups_eq (=) (h@h_prm@(Gen.BList.difference_eq (=) h1 h)@ (IF.struc_free_vars true nst)) in
  let nb = match f.Iast.proc_body with 
      None -> None 
    | Some f->
          let f,_ = x_add_1 case_rename_var_decls_init f in
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
  let fct f = fst (case_normalize_struc_formula 7 prog u p f false 
      false (*allow_post_vars*) false []) in
  {bd with I.barrier_tr_list = List.map (fun (f,t,sp)-> (f,t,List.map fct sp)) bd.I.barrier_tr_list}
      
and case_normalize_barrier prog bd =    
  let pr_in = Iprinter.string_of_barrier_decl in
  Debug.no_1 "case_normalize_barrier " pr_in pr_in (case_normalize_barrier_x prog) bd
      
      
(* AN HOA : WHAT IS THIS FUNCTION SUPPOSED TO DO ? *)
and case_normalize_program (prog: Iast.prog_decl):Iast.prog_decl =
  Debug.no_1 "case_normalize_program" (Iprinter.string_of_program) (Iprinter.string_of_program) case_normalize_program_x prog
      
and case_normalize_program_x (prog: Iast.prog_decl):Iast.prog_decl=
  let tmp_views = (* order_views *) prog.I.prog_view_decls in
  x_tinfo_hp (add_str "case_normalize_prog(views)" pr_v_decls) tmp_views no_pos;
  (* let () = print_string ("case_normalize_program: view_b: " ^ (Iprinter.string_of_view_decl_list tmp_views)) in *)
  let tmp_views = List.map (fun c-> 
      let h = (self,Unprimed)::(eres_name,Unprimed)::(res_name,Unprimed)::(List.map (fun c-> (c,Unprimed)) c.Iast.view_vars ) in
      let p = (self,Primed)::(eres_name,Primed)::(res_name,Primed)::(List.map (fun c-> (c,Primed)) c.Iast.view_vars ) in
      let wf = case_normalize_struc_formula_view 8 prog h p c.Iast.view_formula false 
        false (*allow_post_vars*) false [] in
      let inv_lock = c.Iast.view_inv_lock in
      let inv_lock =
        (match inv_lock with
          | None -> None
          | Some f ->
                let new_f = case_normalize_formula prog p f in (* it has to be p to maintain self in the invariant*)
                Some new_f)
      in
      { c with Iast.view_formula =  wf; Iast.view_inv_lock = inv_lock}) tmp_views in
  (* let () = print_string ("case_normalize_program: view_a: " ^ (Iprinter.string_of_view_decl_list tmp_views)) in *)
  let prog = {prog with Iast.prog_view_decls = tmp_views} in
  let cdata = List.map (case_normalize_data prog) prog.I.prog_data_decls in
  let prog = {prog with Iast.prog_data_decls = cdata} in
  x_tinfo_hp (add_str "trans_prog 2 (prog views)" (pr_list Iprinter.string_of_view_decl))  prog.I.prog_view_decls  no_pos;
  x_tinfo_hp (add_str "trans_prog 2 (temp views)" (pr_list Iprinter.string_of_view_decl))  tmp_views  no_pos;
  (* andreeac: to check if moving Iast.set_check_fixpt at this point (earlier than previously) influences subsequent computions *)
  let () = x_add Iast.set_check_fixpt prog  prog.I.prog_data_decls tmp_views in
  let todo_unk = List.map (fun v -> (* if v.I.view_kind = I.View_NORM then *)
    v.I.view_imm_map <- Immutable.icollect_imm v.I.view_formula v.I.view_vars v.I.view_data_name  prog.I.prog_data_decls )  prog.I.prog_view_decls  in
  let procs1 = List.map (case_normalize_proc prog) prog.I.prog_proc_decls in
  let prog = {prog with Iast.prog_proc_decls = procs1} in
  (* let coer1 = List.map (case_normalize_coerc_list prog) prog.Iast.prog_coercion_decls in   *)
  { prog with 
      Iast.prog_data_decls = cdata;
      Iast.prog_view_decls = tmp_views;
      Iast.prog_proc_decls = procs1;
      (* Iast.prog_coercion_decls = coer1; *)
      Iast.prog_barrier_decls = List.map (case_normalize_barrier prog) prog.Iast.prog_barrier_decls;
  }

and prune_inv_inference_formula (cp:C.prog_decl) (v_l : CP.spec_var list) 
      (init_form_lst: (CF.formula*formula_label) list) u_baga u_inv pos:
      ((Cpure.b_formula * (formula_label list)) list)* (C.ba_prun_cond list) *
      ((formula_label list * (Gen.Baga(CP.PtrSV).baga * Cpure.b_formula list) ) list)
      = 
  let pr_lbl = Globals.string_of_formula_label in
  let pr_b_f =  Cprinter.string_of_b_formula in 
  let pr_svl = Cprinter.string_of_spec_var_list in
  let pr1 = pr_list (fun (bf,fl) -> (pr_b_f bf)^"->"^(pr_list pr_lbl fl)) in
  let pr2 = pr_list (pr_pair pr_svl pr_lbl) in
  let pr = pr_list (pr_pair Cprinter.string_of_formula pr_lbl) in
  let pr3 = Cprinter.string_of_prune_invariants 
  (*pr_list (pr_pair (pr_list pr_lbl) (pr_pair pr_svl (pr_list pr_b_f)))*) in 
  let pr_out (lb,cond,r) = (pr1 lb) ^ " || " ^ (pr2 cond)^" || "^(pr3 r) in
  Debug.no_3 "prune_inv_inference_formula" pr_svl pr pr_svl pr_out
      (fun _ _ _ -> prune_inv_inference_formula_x cp v_l init_form_lst u_baga u_inv pos) v_l init_form_lst u_baga

and prune_inv_inference_formula_x (cp:C.prog_decl) (v_l : CP.spec_var list) (init_form_lst: (CF.formula*formula_label) list) u_baga u_inv pos: 
      ((Cpure.b_formula * (formula_label list)) list)* (C.ba_prun_cond list) *
      ((formula_label list * (Gen.Baga(CP.PtrSV).baga * Cpure.b_formula list)) list) = 
  (*print_string ("sent to case inf: "^(Cprinter.string_of_formula init_form)^"\n");*)
  (*aux functions for case inference*)
  (* let rec get_or_list (f: CF.formula):CF.formula list = match f with *)
  (*   | CF.Base _ *)
  (*   | CF.Exists _ -> [f] *)
  (*   | CF.Or o -> (get_or_list o.CF.formula_or_f1)@(get_or_list o.CF.formula_or_f2) in *)
  
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
            (*let () = print_string ("\n pures:: "^(Cprinter.string_of_pure_formula (CP.mkExists acc f None no_pos))^"\n") in*)
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
              let tpi = fun f1 f2 -> TP.imply_one 7 f1 f2 "" false None in
              if ((fun (c,_,_)-> c) (tpi f1r f2r)) then f2r
              else if ((fun (c,_,_)-> c) (tpi f2r f1r)) then f1r
              else  CP.mkOr f1r f2r None no_pos in
      (*let () = print_string ("before hull: "^(Cprinter.string_of_pure_formula lr)^"\n") in*)
      let lr = hull_invs v_l lr in
      (*let () = print_string ("after hull: "^(String.concat " - " (List.map Cprinter.string_of_pure_formula lr))^"\n") in*)
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
    (* let () = print_endline ("all: "^(Cprinter.string_of_prune_invariants [all])) in *)
    let rec comp i (crt_lst: (formula_label list * (CP.baga_sv * CP.b_formula list))list) (last_lst: (formula_label list * (CP.baga_sv * CP.b_formula list))list) =
      if i>l then [all] (* crt_lst   *)(* in case l=1, we just return one answer; not twice*)
      else
        if i>=l then all :: crt_lst
        else 
          let n_list1 = List.map (
              fun  (c1,(b1,c2)) -> 
                  let h = (List.hd c1) in
                  let rem = List.filter (fun (d1,_)-> 
                      (not (List.exists (fun x-> (fst x)=(fst d1)) c1)) &&
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
    let pr0 = pr_list CP.SV.string_of in
    let pr2 = Cprinter.string_of_prune_invariants  in
	let pr1 inp = pr2 (List.map (fun (a,b)-> [a],b) inp) in
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
    let h,p,_,_,_,_ = CF.split_components b0 in
    let cm,ba = x_add Cvutil.xpure_heap_symbolic_i cp h p 0 in
    let ms = x_add_1 Cvutil.formula_2_mem b0 cp in
    let ba = match ms.CF.mem_formula_mset with | [] -> [] | h::_ -> h in
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
          let (b,_,_) = x_add TP.imply_one 8 f (CP.BForm (c,None)) "" false None in
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
        let r,_,_ = x_add TP.imply_one 9 all_r (CP.BForm (c,None)) "" false None in
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
    (*     let r,_,_ = x_add TP.imply_one 10 all_r (CP.BForm (c,None)) "" false None in *)
    (*     not r) uinvl in *)
    (* let uinv2 = imply_by_all all_r uinvl in *)
    let n_inv = List.map (add_needed_inv uinvl) rlist
    in (rlist,n_inv,p_ls) 
  in

  let pick_pures (lst:(CF.formula * formula_label) list) (vl:CP.spec_var list) (uinv:memo_pure) =
    let pr0 = Gen.BList.string_of_f (CP.SV.string_of) in
    (* let pr x = Gen.BList.string_of_f Cprinter.string_of_b_formula x in *)
    let pr_fl x = (Cprinter.string_of_formula_label) x "" in
    let pr1 (inp,_,_) = Cprinter.string_of_prune_invariants (List.map (fun (a,b)-> ([a],b)) inp) 
		(*let l= List.map (fun (f,(_,a)) -> (f,a)) inp in Gen.BList.string_of_f (Gen.string_of_pair pr_fl pr ) l*) in
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
                      in (x_add TP.is_sat 2 new_f "get_safe_prune_conds" false)
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
  if ((List.length f_branches) == 1) && (CF.isAnyConstFalse (fst (List.hd f_branches))) then
    let def_lbl = snd (List.hd f_branches) in
    { vd with  
      C.view_complex_inv =  Some ( MCP.mkMFalse no_pos) ; 
      C.view_prune_branches = [def_lbl]; 
      C.view_prune_conditions = [] ; 
      C.view_prune_conditions_baga = [];
      C.view_prune_invariants = [([def_lbl],([],[(CP.mkFalse_b no_pos)]))];}
  else (
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
  )

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

and coerc_spec prog c = 
  (* if not !Globals.allow_pred_spec then [c] *)
  if !Globals.dis_ps then [c]
  else 
    let prun_f = x_add Cvutil.prune_preds prog true  in
    [{c with C.coercion_head = prun_f c.C.coercion_head; 
        C.coercion_body = prun_f c.C.coercion_body
        ; C.coercion_body_norm = x_add Cvutil.prune_pred_struc prog true c.C.coercion_body_norm
    }]
        

and pred_prune_inference (cp:C.prog_decl):C.prog_decl = 
  Debug.no_1 "pred_prune_inference" pr_no pr_no pred_prune_inference_x cp 

and pred_prune_inference_x (cp:C.prog_decl):C.prog_decl =      
  Gen.Profiling.push_time "pred_inference";
    let preds = List.map (fun c-> view_prune_inv_inference cp c) cp.C.prog_view_decls in
    let bars = List.map (barrier_prune_inv_inference cp) cp.C.prog_barrier_decls in
    let prog_views_inf = {cp with C.prog_view_decls  = preds;C.prog_barrier_decls = bars} in
    let preds = List.map (fun c-> 
        let unstruc = List.map (fun (c1,c2) ->
            (Cvutil.prune_preds(*_debug*) prog_views_inf true c1,c2))c.C.view_un_struc_formula in
        {c with 
            C.view_formula =  CF.erase_propagated (Cvutil.prune_pred_struc prog_views_inf true c.C.view_formula) ;
            C.view_un_struc_formula = unstruc;}) preds in
    let prog_views_pruned = { prog_views_inf with C.prog_view_decls  = preds;} in
    let prune_bar c = { c with 
        C.barrier_tr_list = List.map (fun (a1,a2,c)-> a1,a2,List.map (Cvutil.prune_pred_struc prog_views_pruned true) c) c.C.barrier_tr_list;
        C.barrier_def= CF.erase_propagated (Cvutil.prune_pred_struc prog_views_pruned true c.C.barrier_def)} in
    let prune_bar c = Debug.no_1 "prune_bar" Cprinter.string_of_barrier_decl Cprinter.string_of_barrier_decl prune_bar c in
    let bars = List.map prune_bar bars in
    
    let prog_barriers_pruned ={prog_views_pruned with C.prog_barrier_decls = bars} in
    let proc_spec f = 
      let simp_b = not ((String.compare f.C.proc_file "primitives")==0 || (f.C.proc_file="")) in
      {f with 
          C.proc_static_specs= x_add Cvutil.prune_pred_struc prog_barriers_pruned simp_b f.C.proc_static_specs;
          C.proc_dynamic_specs= x_add Cvutil.prune_pred_struc prog_barriers_pruned simp_b f.C.proc_dynamic_specs;
      } in
    let procs = C.proc_decls_map proc_spec prog_barriers_pruned.C.new_proc_decls in 
    let l_coerc = List.concat (List.map (coerc_spec prog_barriers_pruned ) (Lem_store.all_lemma # get_left_coercion) (*prog_barriers_pruned.C.prog_left_coercions*)) in
    let r_coerc = List.concat (List.map (coerc_spec prog_barriers_pruned ) (Lem_store.all_lemma # get_right_coercion)(*prog_barriers_pruned.C.prog_right_coercions*)) in
    let () = Lem_store.all_lemma # set_coercion l_coerc r_coerc in
    let r = { prog_barriers_pruned with 
        C.new_proc_decls = procs;
        (* WN_all_lemma - is this overriding of lemmas? *)
        (*C.prog_left_coercions  = l_coerc;
          C.prog_right_coercions = r_coerc;*)} in
    Gen.Profiling.pop_time "pred_inference" ;r


(****************DER VIEW**************)
and mark_rec_and_der_order_x (views: I.view_decl list) : I.view_decl list =
  let sort_fn (n1,_) (n2,_) = n1- n2 in
  let cg = I.derivegraph_of_views views in
  let scc_arr = I.IGC.scc_array cg in
  let scc_list = Array.to_list scc_arr in
  (*todo: detect mutual recursion *)
  (* let cp = mark_recursive_call cp scc_list cg in *)
  let pair_views = mark_der_order views scc_list cg in
  (*sort on pair_views*)
  let sorted_views = List.sort sort_fn pair_views in
  snd (List.split sorted_views)

and mark_rec_and_der_order (views: I.view_decl list) : (I.view_decl) list =
  let pr1 v= pr_id v.I.view_name in
  let pr = pr_list pr1 in
  Debug.no_1 "mark_rec_and_der_order" pr pr mark_rec_and_der_order_x views

and mark_der_order_x (views: I.view_decl list) scc_list cg : (int*I.view_decl) list=
  let _, fscc = I.IGC.scc cg in
  let odered_views = List.map (fun v -> (fscc v.I.view_name, v)) views in
  odered_views

and mark_der_order (views: I.view_decl list) scc_list cg : (int*I.view_decl) list =
  let pr1 v= pr_id v.I.view_name in
  let pr2 scc_list = pr_list (fun scc -> (pr_list (fun s -> s) scc) ^ "\n") scc_list in
  let pr3 = pr_list pr1 in
  let pr4 = pr_list (pr_pair string_of_int pr1) in
  Debug.no_2 "mark_der_order" pr3 pr2 pr4
      (fun _ _ -> mark_der_order_x views scc_list cg) views scc_list

(************ENF DER VIEW**************)


and pr_proc_call_order p = 
  let n = p.Cast.proc_name in
  let c = p.Cast.proc_call_order in
  pr_pair pr_id string_of_int (n,c)

(* Termination *)             
(* Recursive call and call order detection *)
(* irf = is_rec_field *)
and mark_rec_and_call_order_x (cp: C.prog_decl) : C.prog_decl =
  let cg = C.callgraph_of_prog cp in
  (* let scc_list = List.rev (C.IGC.scc_list cg) in *)
  let scc_arr = C.IGC.scc_array cg in
  let scc_list = Array.to_list scc_arr in
  let cp = mark_recursive_call cp scc_list cg in
  let cp = mark_call_order cp scc_list cg in
  let (prims, mutual_grps) = C.re_proc_mutual (C.sort_proc_decls (C.list_of_procs cp)) in
  x_tinfo_hp (add_str "mutual scc" (pr_list (pr_list pr_proc_call_order))) mutual_grps no_pos;
  cp

and mark_rec_and_call_order (cp: C.prog_decl) : C.prog_decl =
  let pr p = pr_list (pr_proc_call_order) 
    (List.filter (fun x -> not (x.C.proc_body == None)) (C.list_of_procs p)) in
  Debug.no_1 "mark_rec_and_call_order" pr pr mark_rec_and_call_order_x cp

and mark_recursive_call (cp: C.prog_decl) scc_list cg : C.prog_decl =
  irf_traverse_prog cp scc_list

and mark_call_order_x (cp: C.prog_decl) scc_list cg : C.prog_decl =
  (* let proc_top, proc_base = List.partition (fun proc -> proc.C.proc_is_main) (C.list_of_procs cp) in      *)
  (* let proc_top_names = List.map (fun p -> p.C.proc_name) proc_top in                                      *)
  (* let scc_list = List.filter (fun scc -> Gen.BList.overlap_eq (=) scc proc_top_names) scc_list in         *)
  (* (* let scc_list = scc_sort scc_list cg in *)                                                            *)
  (* let _, scc_list = List.fold_left (fun (index, acc) scc ->                                               *)
  (*   (index+1, acc @ [(index, scc)])) (0, []) scc_list in                                                  *)
  (* let call_hierarchy = List.concat (List.map (fun (i, scc) -> List.map (fun m -> (m,i)) scc) scc_list) in *)
  (* let cal_index name lst = try List.assoc name lst with _ -> 0 in                                         *)
  (* let tbl = C.proc_decls_map (fun p ->                                                                    *)
  (*     { p with C.proc_call_order = cal_index p.C.proc_name call_hierarchy }                               *)
  (* ) cp.C.new_proc_decls in                                                                                *)
  (* { cp with C.new_proc_decls = tbl }                                                                      *)
  
  (* The following code stuff runs faster than above *)
  let _, fscc = C.IGC.scc cg in
  let tbl = C.proc_decls_map (fun p ->
      { p with C.proc_call_order = fscc p.C.proc_name }
  ) cp.C.new_proc_decls in
  { cp with C.new_proc_decls = tbl }

and mark_call_order (cp: C.prog_decl) scc_list cg : C.prog_decl =
  let pr1 p = pr_list (fun c -> (pr_proc_call_order c) ^ "\n") 
    (List.filter (fun x -> x.C.proc_is_main) (C.list_of_procs p)) in
  let pr2 scc_list = pr_list (fun scc -> (pr_list (fun s -> s) scc) ^ "\n") scc_list in
  Debug.no_2 "mark_call_order" pr1 pr2 pr1
      (fun _ _ -> mark_call_order_x cp scc_list cg) cp scc_list

and is_found (cp: C.prog_decl) (pname: Globals.ident) (scc: C.IG.V.t list) : bool =
  List.exists (fun m ->
      let mn = (C.look_up_proc_def_raw cp.C.new_proc_decls m).C.proc_name in
      mn = pname) scc
      
and find_scc_group (cp: C.prog_decl) (pname: Globals.ident) (scc_list: C.IG.V.t list list) : (C.IG.V.t list) =
  try List.find (fun scc -> is_found cp pname scc) scc_list
  with _ -> []
      
(* and neighbors_of_scc (scc: C.IG.V.t list) (scc_list: C.IG.V.t list list) cg : C.IG.V.t list list =        *)
(*   let neighbors = List.filter (fun m -> not (List.mem m scc)) (C.IGN.list_from_vertices cg scc) in        *)
(*   let scc_neighbors = List.find_all (fun s -> List.exists (fun m -> List.mem m neighbors) s) scc_list in  *)
(*   scc_neighbors                                                                                           *)

(* Warning: This method might have problem with OCaml 4.0 *)  
(* and scc_sort (scc_list: C.IG.V.t list list) cg : C.IG.V.t list list = *)
(*   let compare_scc scc1 scc2 =                                         *)
(*  if (List.mem scc2 (neighbors_of_scc scc1 scc_list cg)) then 1       *)
(*  else if (List.mem scc1 (neighbors_of_scc scc2 scc_list cg)) then -1 *)
(*  else 0                                                              *)
(*   in List.fast_sort (fun s1 s2 -> compare_scc s1 s2) scc_list         *)

(* and scc_sort (scc_list: C.IG.V.t list list) cg : C.IG.V.t list list =                            *)
(*   let topo_order = snd (C.IGT.fold (fun v (index, a) -> (index+1, (v, index)::a)) cg (0, [])) in *)
(*   let compare_scc scc1 scc2 =                                                                    *)
(*     try                                                                                          *)
(*       let i1 = List.assoc (List.hd scc1) topo_order in                                           *)
(*       let i2 = List.assoc (List.hd scc2) topo_order in                                           *)
(*       i2-i1                                                                                      *)
(*     with _ -> 0                                                                                  *)
(*   in List.fast_sort (fun s1 s2 -> compare_scc s1 s2) scc_list                                    *)

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
    | C.Par e ->
      let cl, ill = List.split (List.map (fun c ->  
        let ce, il = irf_traverse_exp cp c.C.exp_par_case_body scc in
        { c with C.exp_par_case_body = ce }, il) e.C.exp_par_cases)
      in
      (C.Par { e with C.exp_par_cases = cl }, List.concat ill)
              

and slicing_label_inference_program (prog: I.prog_decl) : I.prog_decl =
  {prog with
      I.prog_view_decls = List.map (fun v -> slicing_label_inference_view v) prog.I.prog_view_decls;}
      
and slicing_label_inference_view (view : I.view_decl) : I.view_decl =
  let v_inv = IP.break_pure_formula view.I.view_invariant in
  let v_form = IF.break_struc_formula view.I.view_formula in

  let str_inv = pr_list (Iprinter.string_of_b_formula) v_inv in
  let str_form = pr_list (pr_list Iprinter.string_of_b_formula) v_form in

  let () = print_string ("\nslicing_label_inference_view: inv: " ^ str_inv ^ "\n") in
  let () = print_string ("\nslicing_label_inference_view: form: " ^ str_form ^ "\n") in

  let lg = List.map (fun v -> trans_view_to_graph v) v_form in

  let str_lg = pr_list (pr_list (pr_list Iprinter.string_of_var)) lg in

  let () = print_string ("\nslicing_label_inference_view: graph: " ^ str_lg ^ "\n") in

  let () = List.iter (
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
        CF.h_formula_data_imm = CP.ConstAnn Mutable;
                        CF.h_formula_data_param_imm = [];
        CF.h_formula_data_perm = Some (Cpure.Var (v,no_pos));
        CF.h_formula_data_arguments = st_v::List.tl bd.C.barrier_shared_vars;
        CF.h_formula_data_label = None; 
        CF.h_formula_data_remaining_branches = None ;
        CF.h_formula_data_pruning_conditions = [] ;
        CF.h_formula_data_origins = [] ;
        CF.h_formula_data_original = true;
        CF.h_formula_data_holes =[];
        CF.h_formula_data_derv = false;
        CF.h_formula_data_split = SPLIT0;
        CF.h_formula_data_pos = no_pos } in
    let p2 = CP.mkEqVarInt st_v st no_pos in
    let p = x_add_1 Mcpure.mix_of_pure (CP.mkAnd p2 perm no_pos) in
    CF.mkExists [v;st_v] h p CVP.empty_vperm_sets CF.TypeTrue (CF.mkTrueFlow ()) [] no_pos in
  let f_gen_base st v perm = Debug.no_1 "f_gen_base" Cprinter.string_of_pure_formula Cprinter.string_of_formula (f_gen_base st v) perm in
  let f_gen st = f_gen_base st (CP.fresh_perm_var ()) (CP.mkTrue no_pos) in
  let f_gen_tot st = 
    let v = CP.fresh_perm_var () in
    let pf = CP.mkEq (CP.Var (v,no_pos)) (CP.Tsconst (Tree_shares.Ts.top,no_pos)) no_pos  in
    f_gen_base st v (CP.BForm ((pf,None),None)) in
  
  let one_entail f1 f2 = 
    let ctx = CF.build_context (CF.empty_ctx (CF.mkTrueFlow ()) Lab2_List.unlabelled no_pos) f1 no_pos in
    (*let () = if !Globals.print_core then print_string ("\n"^(Cprinter.string_of_formula f1)^" |- "^(Cprinter.string_of_formula f2)^"\n") else () in*)
    Gen.Profiling.inc_counter "barrier_proofs";
    let rs1, _ = x_add Solver.heap_entail_init prog false (CF.SuccCtx[ctx]) f2 no_pos in
    CF.transform_list_context (Solver.elim_ante_evars,(fun c->c)) rs1 in
  
  let one_entail f1 f2  = Debug.no_2 "one_entail" Cprinter.string_of_formula Cprinter.string_of_formula Cprinter.string_of_list_context one_entail f1 f2 in
  
  let one_ctx_entail c1 c2 =
    let r = 
      Gen.Profiling.inc_counter "barrier_proofs"; 
      let c1 = CF.set_context_formula (CF.Ctx empty_es) c1 in
      (*let f2 = (CF.context_to_formula c2) in*)
      (*let () = print_string ("entail: "^(Cprinter.string_of_list_context c1) ^" \n entails : "^(Cprinter.string_of_formula f2)^"\n") in*)
      (*print_string "cica start\n";*)
      let he_res = x_add Solver.heap_entail_init prog false (CF.SuccCtx[c1]) (*wrapp_frac_fv*) c2 no_pos in
      fst (he_res) in
    match r with
      | CF.SuccCtx l ->  List.for_all  (fun c-> (CF.isAnyFalseCtx c || CF.ctx_no_heap c)) l
      | CF.FailCtx _ -> ((*print_string "result : failed \n";*) false) in
  (*end auxes*)
  
  let one_ctx_entail c1 c2 = Debug.no_2(* _loop *) "one_ctx_entail" Cprinter.string_of_formula Cprinter.string_of_formula string_of_bool one_ctx_entail c1 c2 in
  
  let prep_t (fs,ts,fl) = 
    let t_str = "("^(string_of_int fs)^"->"^(string_of_int ts)^")" in
    (*  print_string ("transition: "^t_str^"\n"); flush stdout;*)
    let pres, posts = List.split (List.map (fun f-> match CF.split_struc_formula f with
      | (p1,p2)::[] -> 
            (* if Solver1.unsat_base_nth "0" prog (ref 0) p1 then raise  (Err.Malformed_barrier (" unsat pre for transition "^t_str ))
               else if Solver1.unsat_base_nth "0" prog (ref 0) p2 then raise  (Err.Malformed_barrier (" unsat post for transition  "^t_str))
               else*) (*checks: each contain a barrier fs in pre and ts in post*)
            if (CF.isFailCtx (one_entail p1 (f_gen fs))) then raise (Err.Malformed_barrier ("a precondition does not contain a barrier share for transition "^t_str))
            else if (CF.isFailCtx (one_entail p2 (f_gen ts))) then raise (Err.Malformed_barrier ("a postcondition does not contain a barrier share for transition "^t_str))
            else (*check precision P * P = false , shold be redundant at this point*)
              let f = (*Solver.normalize_frac_formula prog*) (CF.mkStar p1 p1 CF.Flow_combine no_pos) in
              (* WN_all_lemma *)
              let f = x_add Solver.normalize_formula_w_coers 8 prog empty_es f (Lem_store.all_lemma # get_left_coercion) (*prog.C.prog_left_coercions*) in
              Gen.Profiling.inc_counter "barrier_proofs";
              if Solver.unsat_base_nth 3 prog (ref 0) f then (p1,p2)
              else raise  (Err.Malformed_barrier "imprecise specification, this should not occur as long as the prev check is correct")
      | _ -> raise  (Err.Malformed_barrier " disjunctive specification?")) fl) in
    (*the pre sum totals full barrier fs get residue F1*)
    let tot_pre = List.fold_left (fun a c-> CF.mkStar a c CF.Flow_combine no_pos) (CF.mkTrue_nf no_pos) pres in
    (* WN_all_lemma *)
    let tot_pre = x_add Solver.normalize_formula_w_coers 9 prog empty_es tot_pre (Lem_store.all_lemma # get_left_coercion) (*prog.C.prog_left_coercions*) in
    (*let tot_pre = Solver.normalize_frac_formula prog tot_pre in*)
    (*let () = print_string (Cprinter.string_of_formula tot_pre) in *)
    Gen.Profiling.inc_counter "barrier_proofs";
    if Solver.unsat_base_nth 4 prog (ref 0) tot_pre then raise  (Err.Malformed_barrier (" contradiction in pres for transition "^t_str ))
    else
      let tot_pre_bar = f_gen_tot fs in
      let () = x_dinfo_zp (lazy ("check_barriers: whole pre:  "^ (Cprinter.string_of_formula tot_pre))) no_pos in
      let () = x_dinfo_zp (lazy ("check_barriers: whole pre barr: "^ (Cprinter.string_of_formula tot_pre_bar))) no_pos in
      let fpre = one_entail tot_pre tot_pre_bar in
      if CF.isFailCtx fpre then  raise  (Err.Malformed_barrier (" preconditions do not contain the entire barrier in transition "^t_str ))
      else (*the post sum totals full barrier ts get residue F2*)
        let tot_post = List.fold_left (fun a c-> CF.mkStar a c CF.Flow_combine no_pos) (CF.mkTrue_nf no_pos) posts in
        (* WN_all_lemma - is this overriding of lemmas? *)
        let tot_post = x_add Solver.normalize_formula_w_coers 10 prog empty_es tot_post (Lem_store.all_lemma # get_left_coercion) (*prog.C.prog_left_coercions*) in
        (*let tot_post = Solver.normalize_frac_formula prog tot_post in*)
        Gen.Profiling.inc_counter "barrier_proofs";
        if Solver.unsat_base_nth 5 prog (ref 0) tot_post then raise (Err.Malformed_barrier (" contradiction in post for transition "^t_str ))
        else
          let tot_post_bar = f_gen_tot ts in
          let () = x_dinfo_zp (lazy ("check_barriers: whole post:  "^ (Cprinter.string_of_formula tot_post))) no_pos in
          let () = x_dinfo_zp (lazy ("check_barriers: whole post barr: "^ (Cprinter.string_of_formula tot_post_bar))) no_pos in
          let fpost = one_entail tot_post tot_post_bar in
          if CF.isFailCtx fpost then  raise  (Err.Malformed_barrier (" postconditions do not contain the entire barrier in transition "^t_str ))
          else (*show F1 = F2*)
            let () = x_dinfo_zp (lazy ("check_barriers: pre: "^ (Cprinter.string_of_list_context fpre))) no_pos in
            let () = x_dinfo_zp (lazy ("check_barriers: post: "^ (Cprinter.string_of_list_context fpost))) no_pos in
            
            
            let fpre,fpost  =   (*add existential quantif for pure vars that do not appear on the other side*)
              
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
        let nf = CF.mkStar f1 f2 CF.Flow_combine no_pos in
        (* WN_all_lemma - is this overriding of lemmas? *)
        let nf = x_add Solver.normalize_formula_w_coers 11 prog empty_es nf (Lem_store.all_lemma # get_left_coercion)(*prog.C.prog_left_coercions*) in
      if  Solver.unsat_base_nth 6 prog (ref 0) nf then ()
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
    let n_tl = [] in
    let n_tl = type_list_add self { sv_info_kind = (Named bd.I.barrier_name);id = fresh_int () } n_tl in
    let n_tl = List.fold_left (fun tl (t,c)-> type_list_add c {sv_info_kind = t;id = fresh_int ()} tl) n_tl bd.I.barrier_shared_vars in
    (*let vl = self::(List.map snd bd.I.barrier_shared_vars) in*)
    let vl = [self] in
    let rec aux1 (tl:spec_var_type_list) (il:Iformula.struc_formula list) = (
      match il with 
      | []->tl,[]
      | hd::tail ->
          let (n_tl,sf) = trans_I2C_struc_formula 7 prog false true vl hd tl false true in
          let (n_tl,n_il) = aux1 n_tl tail in
          (n_tl, (sf::n_il))
    ) in
    let rec aux2 (tl:spec_var_type_list) (bl:(int*int* Iformula.struc_formula list) list) = (
      match bl with 
      | [] -> tl,[]
      | (f,t,sp)::tail ->
              let (n_tl,n_il) = aux1 tl sp in
              let (n_tl,n_bl) = aux2 n_tl tail in
              (n_tl, (f,t,n_il)::n_bl)
    ) in
    let (n_tl,l) = aux2 n_tl bd.I.barrier_tr_list in
    let bdef = let fct a l = match l with 
      | CF.EList l -> a@l 
      | _ -> (empty_spec_label_def, l)::a in
    CF.mkEList_no_flatten (List.fold_left (fun a (_,_,l)-> List.fold_left fct a l) [] l) in
    { C.barrier_thc = bd.I.barrier_thc;
    C.barrier_name = bd.I.barrier_name;
    C.barrier_shared_vars = List.map (fun (_,c)-> trans_var (c,Unprimed) n_tl no_pos) bd.I.barrier_shared_vars;
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
      
and trans_field_layout (iann : IP.ann list) : CP.ann list = List.map Immutable.iformula_ann_to_cformula_ann iann

and trans_mem_formula (imem : IF.mem_formula) (tlist:spec_var_type_list) : CF.mem_perm_formula = 
    let mem_exp = trans_pure_exp imem.IF.mem_formula_exp tlist in 
    let helpl1, helpl2 = List.split imem.IF.mem_formula_field_layout in
    let helpl2 = List.map trans_field_layout helpl2 in
    let guards = List.map (fun c -> trans_pure_formula c tlist) imem.IF.mem_formula_guards in 
    let field_values = List.map (fun c -> (fst c), 
      (List.map (fun a -> match a with
        | IP.Var ((ve, pe), pos_e) -> CP.Var(trans_var_safe (ve, pe) UNK tlist pos_e,pos_e)
        | IP.IConst(i,pos) -> CP.IConst(i,pos)
        | _ -> raise Not_found
       ) (snd c))) imem.IF.mem_formula_field_values in
    let meml = List.combine helpl1 helpl2 in
            {CF.mem_formula_exp  = mem_exp;
            CF.mem_formula_exact = imem.IF.mem_formula_exact;
            CF.mem_formula_field_values = field_values;
            CF.mem_formula_field_layout =  meml;
            CF.mem_formula_guards = guards}
            
and trans_view_mem (vmem : IF.mem_formula option) (tlist:spec_var_type_list) : CF.mem_perm_formula option = 
    match vmem with
    | Some a -> Some(trans_mem_formula a tlist)
    | None -> None
    
and compute_mem_spec (prog : C.prog_decl) (lhs : CF.formula) (rhs : CF.formula) (pos: loc) = 
    let formula1 = lhs in
    (*let () = print_string("LHS :"^(Cprinter.string_of_formula formula1) ^"\n") in*)
    let ctx = CF.build_context (CF.true_ctx ( CF.mkTrueFlow ()) Lab2_List.unlabelled pos) formula1 pos in
    let formula = rhs in
    (*let () = print_string("RHS :" ^(Cprinter.string_of_formula formula)^"\n") in*)
    let (rs, _) = x_add Solver.heap_entail_init prog false (CF.SuccCtx [ctx]) formula pos in
    if not(CF.isFailCtx rs) then ()
    else Err.report_error {Err.error_loc = pos;
    Err.error_text = "[astsimp.ml] : view formula does not entail supplied Memory Spec";}

and check_mem_formula_guards_disjoint (fl: CP.formula list) : bool = 
    let sat_subno = ref 0 in
    let f = CP.join_disjunctions fl in
    Tpdispatcher.is_sat_sub_no 14 (Cpure.Not (f,None,no_pos)) sat_subno

and validate_mem_spec (prog : C.prog_decl) (vdef: C.view_decl) = 
    if not(!Globals.allow_mem) then () else
    match vdef.C.view_mem with
    | Some a -> let pos = CF.pos_of_struc_formula vdef.C.view_formula in 
            let list_of_disjuncts = fst (List.split vdef.C.view_un_struc_formula) in 
                let list_of_calcmem = 
                List.map (fun c -> CF.formula_of_mix_formula (Mem.xmem c prog.C.prog_view_decls a) pos) list_of_disjuncts in
                let combined_list = List.combine list_of_disjuncts list_of_calcmem in
                let todo_unk = List.map (fun c-> compute_mem_spec prog (fst c) (snd c) pos) combined_list in 
                let flag = List.for_all 
                (fun c-> let x_fvs = CP.fv c in
            let relevant_slice = CP.join_conjunctions (List.filter 
            (fun c -> if (CP.disjoint x_fvs (CP.fv c)) then false else true)
            (CP.split_conjunctions (MCP.pure_of_mix vdef.C.view_user_inv))) in
                Solver.simple_imply c relevant_slice) a.CF.mem_formula_guards
                in
                if flag then if not (check_mem_formula_guards_disjoint a.CF.mem_formula_guards) then () 
              else Err.report_error {
            Err.error_loc = pos;
			Err.error_text = "[astsimp.ml] : Memory Guards of "^ vdef.C.view_name ^" are not exhaustive ";} 
                else 
            Err.report_error {Err.error_loc = pos;
            Err.error_text = "[astsimp.ml] : Mem Spec for "^vdef.C.view_name^" does not entail supplied invariant";}
            (*let calcmem = 
            MCP.simpl_memo_pure_formula Solver.simpl_b_formula Solver.simpl_pure_formula calcmem (x_add TP.simplify_a 10) in 
            let lhs = CF.formula_of_mix_formula vdef.C.view_x_formula pos in
            let rhs = CF.formula_of_mix_formula calcmem pos in*)     
    | None -> ()
    
(******trans_test_components**********)
and trans_test_comps prog tcomps =        
  match tcomps with
    | None -> None
    | Some t ->
          Some  {
              C.expected_ass = trans_expected_ass prog t.Iast.expected_ass;
              C.expected_hpdefs = trans_expected_ass prog t.Iast.expected_hpdefs;
          }

and trans_expected_ass prog ass =
  let trans_constr prog constr = 
    let if1, if2 = constr in
    let if1 = case_normalize_formula prog [] if1 in
    let n_tl = gather_type_info_formula prog if1 [] false in
    let (n_tl,f1) = trans_formula prog false [] false if1 n_tl false in
    let if2 = case_normalize_formula prog [] if2 in
    let n_tl = gather_type_info_formula prog if2 n_tl false in
    let (n_tl,f2) = trans_formula prog false [] false if2 n_tl false in
    (f1,f2)
  in
  let helper assl = List.map (fun one_ass -> trans_constr prog (one_ass.Iast.ass_lhs,one_ass.Iast.ass_rhs)) assl in         
  match ass with
    | None -> None 
    | Some (il,sl,assl) -> Some(il,sl,helper assl)

(******end trans_test_components**********)


(*translates cformulas to iformulas, with some simplifications*)

(* let rev_trans_spec_var v = match v with CP.SpecVar (t,v,p)-> (v,p)  *)
(* let sv_n = CP.name_of_spec_var  *)

(* let rec rev_trans_exp e = match e with *)
(*   | CP.Null p -> IP.Null p  *)
(*   (\* | CP.Var (v,p) -> IP.Var (rev_trans_spec_var v, p) *\) *)
(*   | CP.Var (v,p) -> let t =  CP.type_of_spec_var v in *)
(*     (\* let () = print_endline ((!CP.print_sv v)^ ": " ^ (string_of_typ t)) in *\) *)
(*     IP.Ann_Exp (IP.Var (rev_trans_spec_var v, p), t, p) (\*L2: added annotated sv instead sv here*\) *)
(*   | CP.Bptriple ((c,t,a),p) -> *)
(*       let nc = IP.Var (rev_trans_spec_var c, p) in *)
(*       let nt = IP.Var (rev_trans_spec_var t, p) in *)
(*       let na = IP.Var (rev_trans_spec_var a, p) in *)
(*       IP.Bptriple ((nc,nt,na),p) *)
(*   | CP.IConst b -> IP.IConst b *)
(*   | CP.FConst b -> IP.FConst b *)
(*   | CP.AConst b -> IP.AConst b *)
(*   | CP.Tsconst b -> IP.Tsconst b *)
(*   | CP.Add (e1,e2,p)      -> IP.Add (rev_trans_exp e1, rev_trans_exp e2, p) *)
(*   | CP.Subtract (e1,e2,p) -> IP.Subtract (rev_trans_exp e1, rev_trans_exp e2, p) *)
(*   | CP.Mult (e1,e2,p)     -> IP.Mult (rev_trans_exp e1, rev_trans_exp e2, p) *)
(*   | CP.Div (e1,e2,p)      -> IP.Div (rev_trans_exp e1, rev_trans_exp e2, p) *)
(*   | CP.Max (e1,e2,p)      -> IP.Max (rev_trans_exp e1, rev_trans_exp e2, p) *)
(*   | CP.Min (e1,e2,p)      -> IP.Min (rev_trans_exp e1, rev_trans_exp e2, p) *)
(*   | CP.TypeCast (ty,e1,p) -> IP.TypeCast (ty, rev_trans_exp e1, p) *)
(*   | CP.Bag (l,p)          -> IP.Bag (List.map rev_trans_exp l, p) *)
(*   | CP.BagUnion (l,p)     -> IP.BagUnion (List.map rev_trans_exp l, p) *)
(*   | CP.BagIntersect (l,p) -> IP.BagIntersect (List.map rev_trans_exp l, p) *)
(*   | CP.BagDiff (e1,e2,p)  -> IP.BagDiff (rev_trans_exp e1, rev_trans_exp e2, p) *)
(*   | CP.List (l,p)         -> IP.List (List.map rev_trans_exp l, p) *)
(*   | CP.ListCons (e1,e2,p) -> IP.ListCons (rev_trans_exp e1, rev_trans_exp e2, p) *)
(*   | CP.ListHead (e1,p) -> IP.ListHead (rev_trans_exp e1, p) *)
(*   | CP.ListTail (e,p)     -> IP.ListTail (rev_trans_exp e, p) *)
(*   | CP.ListLength (e,p)   -> IP.ListLength (rev_trans_exp e, p) *)
(*   | CP.ListAppend (l,p)   -> IP.ListAppend (List.map rev_trans_exp l, p) *)
(*   | CP.ListReverse (e,p)  -> IP.ListReverse (rev_trans_exp e, p) *)
(*   | CP.ArrayAt (v,el,p)   -> IP.ArrayAt (rev_trans_spec_var v, List.map rev_trans_exp el, p) *)
(*   | CP.Func (v,el,p)      -> IP.Func (sv_n v, List.map rev_trans_exp el, p) *)
(*   | CP.Level _| CP.InfConst _ -> report_error no_pos "AS.rev_trans_exp: not handle yet" *)

(* let rec rev_trans_pf f = match f with *)
(*   | CP.XPure b -> IP.XPure{   *)
(* 		IP.xpure_view_node = map_opt sv_n b.CP.xpure_view_node; *)
(* 		IP.xpure_view_name = b.CP.xpure_view_name; *)
(* 		IP.xpure_view_arguments = List.map sv_n b.CP.xpure_view_arguments; *)
(* 		IP.xpure_view_remaining_branches = None; *)
(* 		IP.xpure_view_pos = b.CP.xpure_view_pos} *)
(*   | CP.LexVar _ -> failwith "rev_trans_pure: unexpected lexvar, if you want support for it , implement this case\n" *)
(*   | CP.BConst b -> IP.BConst b  *)
(*   | CP.BVar (v,p) -> IP.BVar ( rev_trans_spec_var v, p) *)
(*   | CP.Lt (e1,e2,p) -> IP.Lt (rev_trans_exp e1, rev_trans_exp e2, p) *)
(*   | CP.Lte (e1,e2,p) -> IP.Lte (rev_trans_exp e1, rev_trans_exp e2, p) *)
(*   | CP.Gt (e1,e2,p) -> IP.Gt (rev_trans_exp e1, rev_trans_exp e2, p) *)
(*   | CP.Gte (e1,e2,p) -> IP.Gte (rev_trans_exp e1, rev_trans_exp e2, p) *)
(*   | CP.SubAnn (e1,e2,p) -> IP.SubAnn (rev_trans_exp e1, rev_trans_exp e2, p) *)
(*   | CP.Eq (e1,e2,p) -> IP.Eq (rev_trans_exp e1, rev_trans_exp e2, p) *)
(*   | CP.Neq (e1,e2,p) -> IP.Neq (rev_trans_exp e1, rev_trans_exp e2, p)   *)
(*   | CP.EqMax (e1,e2,e3,p) -> IP.EqMax (rev_trans_exp e1, rev_trans_exp e2, rev_trans_exp e3, p) *)
(*   | CP.EqMin (e1,e2,e3,p) -> IP.EqMin (rev_trans_exp e1, rev_trans_exp e2, rev_trans_exp e3, p)   *)
(*   | CP.BagIn (v,e,p) -> IP.BagIn (rev_trans_spec_var v, rev_trans_exp e, p) *)
(*   | CP.BagNotIn (v,e,p) -> IP.BagNotIn (rev_trans_spec_var v, rev_trans_exp e, p) *)
(*   | CP.BagSub (e1,e2,p) -> IP.BagSub (rev_trans_exp e1, rev_trans_exp e2, p) *)
(*   | CP.BagMin (v1,v2,p) -> IP.BagMin (rev_trans_spec_var v1, rev_trans_spec_var v2, p) *)
(*   | CP.BagMax  (v1,v2,p) -> IP.BagMax (rev_trans_spec_var v1, rev_trans_spec_var v2, p) *)
(*   | CP.VarPerm _ -> failwith "rev_trans_pure: unexpected VarPerm, if you want support for it , implement this case\n"  *)
(*   | CP.RelForm (v,el,p)-> IP.RelForm (sv_n v, List.map rev_trans_exp el, p) *)
(*   | CP.ListIn (e1,e2,p) -> IP.ListIn (rev_trans_exp e1, rev_trans_exp e2, p) *)
(*   | CP.ListNotIn (e1,e2,p) -> IP.ListNotIn (rev_trans_exp e1, rev_trans_exp e2, p) *)
(*   | CP.ListAllN (e1,e2,p) -> IP.ListAllN (rev_trans_exp e1, rev_trans_exp e2, p) *)
(*   | CP.ListPerm (e1,e2,p) -> IP.ListPerm (rev_trans_exp e1, rev_trans_exp e2, p) *)

(* let rec rev_trans_pure f = match f with *)
(*   | CP.BForm ((b1,_),b2)  -> IP.BForm ((rev_trans_pf b1,None), b2) *)
(*   | CP.And (b1,b2,b3) -> IP.And (rev_trans_pure b1, rev_trans_pure b2, b3) *)
(*   | CP.AndList l -> IP.AndList (map_l_snd rev_trans_pure l) *)
(*   | CP.Or (f1,f2,lbl,pos) -> IP.Or (rev_trans_pure f1, rev_trans_pure f2, lbl, pos) *)
(*   | CP.Not (f,lbl,pos)-> IP.Not (rev_trans_pure f, lbl, pos) *)
(*   | CP.Forall (v,f,lbl,pos)->  IP.Forall (rev_trans_spec_var v,rev_trans_pure f, lbl, pos) *)
(*   | CP.Exists (v,f,lbl,pos)->  IP.Exists (rev_trans_spec_var v,rev_trans_pure f, lbl, pos) *)
  
(* let rec rev_trans_mix f = rev_trans_pure(MCP.pure_of_mix f) *)
  
(* let rec rev_trans_heap f = match f with  *)
(*   | CF.HTrue  -> IF.HTrue *)
(*   | CF.HFalse -> IF.HFalse *)
(*   | CF.HEmp   -> IF.HEmp   *)
 (* | CF.ThreadNode b ->
      IF.mkThreadNode (rev_trans_spec_var b.CF.h_formula_thread_node) 
                    b.CF.h_formula_thread_name
                    (rev_trans_formula b.CF.h_formula_thread_resource)
                    (rev_trans_pure b.CF.h_formula_thread_delayed)
                    (Perm.rev_trans_perm b.CF.h_formula_thread_perm)
                    None
                    b.CF.h_formula_thread_pos *)
(*   | CF.DataNode b -> *)
(*       IF.mkHeapNode (rev_trans_spec_var b.CF.h_formula_data_node)  *)
(*                     b.CF.h_formula_data_name *)
(*                     0 *)
(*                     b.CF.h_formula_data_derv  *)
(*                     (IP.ConstAnn(Mutable)) *)
(*                     true false false None (List.map (fun c-> IP.Var ((rev_trans_spec_var c),no_pos)) b.CF.h_formula_data_arguments) [] *)
(*                     None b.CF.h_formula_data_pos          *)
(*   | CF.ViewNode b -> *)
(*       IF.mkHeapNode (rev_trans_spec_var b.CF.h_formula_view_node)  *)
(*                     b.CF.h_formula_view_name *)
(*                     0 *)
(*                     b.CF.h_formula_view_derv  *)
(*                     (IP.ConstAnn(Mutable)) *)
(*                     true false false None (List.map (fun c-> IP.Var ((rev_trans_spec_var c),no_pos)) b.CF.h_formula_view_arguments) (List.map (fun _ -> None) b.CF.h_formula_view_arguments) *)
(*                     None b.CF.h_formula_view_pos *)
(*   | CF.Hole _ -> failwith "holes should not have been here" *)
(*   | CF.HRel  (sv,el,p)  -> IF.HRel (sv_n sv, List.map rev_trans_exp el, p) *)
(*   | CF.Phase b  -> IF.mkPhase (rev_trans_heap b.CF.h_formula_phase_rd) (rev_trans_heap b.CF.h_formula_phase_rw) b.CF.h_formula_phase_pos *)
(*   | CF.Conj  b  -> IF.mkConj  (rev_trans_heap b.CF.h_formula_conj_h1) (rev_trans_heap b.CF.h_formula_conj_h2) b.CF.h_formula_conj_pos *)
(*   | CF.Star  b  -> IF.mkStar  (rev_trans_heap b.CF.h_formula_star_h1) (rev_trans_heap b.CF.h_formula_star_h2) b.CF.h_formula_star_pos *)
(*   | CF.StarMinus _| CF.ConjStar _|CF.ConjConj _ -> report_error no_pos "AS.rev_trans_heap: not handle yet" *)
                    (* (Perm.rev_trans_perm b.CF.h_formula_view_perm) *)
                    (* (List.map (fun c-> IP.Var ((rev_trans_spec_var c),no_pos)) b.CF.h_formula_view_arguments) (List.map (fun _ -> None) b.CF.h_formula_view_arguments) *)
 
(* let rec rev_trans_formula f = match f with  *)
(* 	| CF.Base b-> IF.Base  {  *)
(* 					 IF.formula_base_heap = rev_trans_heap b.CF.formula_base_heap; *)
(*                      IF.formula_base_pure = rev_trans_mix b.CF.formula_base_pure; *)
(*                      IF.formula_base_flow = (exlist # get_closest b.CF.formula_base_flow.CF.formula_flow_interval); *)
(*                      IF.formula_base_and = []; *)
(*                      IF.formula_base_pos = b.CF.formula_base_pos } *)
(* 	| CF.Exists b-> IF.Exists{ *)
(* 					   IF.formula_exists_qvars = List.map rev_trans_spec_var b.CF.formula_exists_qvars; *)
(*                        IF.formula_exists_heap = rev_trans_heap b.CF.formula_exists_heap; *)
(*                        IF.formula_exists_pure = rev_trans_mix b.CF.formula_exists_pure; *)
(*                        IF.formula_exists_flow = (exlist # get_closest b.CF.formula_exists_flow.CF.formula_flow_interval); *)
(*                        IF.formula_exists_and = []; *)
(*                        IF.formula_exists_pos =b.CF.formula_exists_pos} *)
(* 	| CF.Or b-> IF.Or { *)
(* 					IF.formula_or_f1 =rev_trans_formula b.CF.formula_or_f1;  *)
(* 					IF.formula_or_f2 =rev_trans_formula b.CF.formula_or_f2;  *)
(* 					IF.formula_or_pos = b.CF.formula_or_pos;} *)

(* let rev_trans_formula f= *)
(*   let pr1 = Cprinter.prtt_string_of_formula in *)
(*   let pr2 = Iprinter.string_of_formula in *)
(*   Debug.no_1 "rev_trans_formula" pr1 pr2 *)
(*       (fun _ -> rev_trans_formula f) f *)

(* let transform_hp_rels_to_iviews (hp_rels:(ident* CF.hp_rel_def) list):(ident*ident*I.view_decl) list =  *)
(* (\*CP.rel_cat * h_formula * formula*\) *)

(*   List.fold_left (fun acc (proc_id,(\* (rel_cat, hf,_,f_body) *\) def)-> *)
(*       let f_body = CF.disj_of_list (List.map fst def.CF.def_rhs) no_pos in *)
(* 	match def.CF.def_cat with *)
(* 	  | CP.HPRelDefn (v,r,paras)-> *)
(* 		let vname = sv_n v in *)
(* 		let slf, vars, tvars = match def.CF.def_lhs with *)
(* 		  | CF.HRel (v1,el,_)-> *)
(* 			if ((String.compare (sv_n v1) vname)!=0) then failwith "hrel name inconsistency\n" *)
(* 			else  ( *)
(*                             (\*LOC changed here.*\) *)
(* 			    (\* let tvars = List.map (fun c-> match c with CP.Var (CP.SpecVar (t, v, _),_)-> (t,v) | _ -> failwith "unexpected expr") el in *\) *)
(* 			    (\* let vars  = List.map (fun c-> *\) *)
(*                             (\*     match c with *\) *)
(*                             (\*       |  CP.Var (CP.SpecVar (_, v, p),_)-> (v^(match p with Primed -> "PRM"| _ -> "")) *\) *)
(*                             (\*       | _ -> failwith "unexpected expr" *\) *)
(*                             (\* ) el in *\) *)
(*                             let tvars = List.map (fun (CP.SpecVar (t, v, _))-> (t,v)) (r::paras) in *)
(* 			    let vars  = List.map (fun (CP.SpecVar (_, v, p))-> (v^(match p with Primed -> "PRM"| _ -> "")) *)
(*                             ) (r::paras) in *)
(* 			    match vars with *)
(* 			      | h::t -> h,t, (List.tl tvars) *)
(* 			      | []   -> failwith "unexpected number of arguments in inferred predicates\n" *)
(*                         ) *)
(* 		  | _ -> failwith "unexpected heap formula instead of hrel node \n" *)
(*                 in *)
(* 		let no_prm_body = CF.elim_prm f_body in *)
(* 		let new_body = CF.set_flow_in_formula_override {CF.formula_flow_interval = !top_flow_int; CF.formula_flow_link =None} no_prm_body in *)
(* 		let i_body = rev_trans_formula new_body in *)
(* 		let i_body = IF.subst [((slf,Unprimed),(self,Unprimed))] i_body in *)
(* 		let struc_body = IF.mkEBase [] [] [] i_body None (\* false *\) no_pos in *)
(*                 let n_iview = {  I.view_name = vname; *)
(*                                          I.view_pos = no_pos; *)
(* 		I.view_data_name = ""; *)
(* 		I.view_vars = vars; *)
(*                 I.view_imm_map = []; *)
(*                 I.view_parent_name = None; *)
(*                 I.view_derv = false; *)
(* 		I.view_labels = List.map (fun _ -> LO.unlabelled) vars, false; *)
(* 		I.view_modes = List.map (fun _ -> ModeOut) vars ; *)
(* 		I.view_typed_vars =  tvars; *)
(*                 I.view_kind = I.View_NORM; *)
(*                 I.view_prop_extns = []; *)
(*                 I.view_derv_info = []; *)
(* 		I.view_pt_by_self  = []; *)
(* 		I.view_formula = struc_body; *)
(* 		I.view_inv_lock = None; *)
(* 		I.view_is_prim = false; *)
(* 		I.view_invariant = IP.mkTrue no_pos; *)
(*                 I.view_mem = None; *)
(* 		I.view_materialized_vars = []; *)
(* 		I.try_case_inference = false; } *)
(*                 in *)
(* 		(proc_id,vname, n_iview)::acc *)
(* 	  | _ -> acc) [] hp_rels *)

(* let transform_hp_rels_to_iviews hp_rels = *)
(*   let pr1 = pr_list (pr_pair pr_id Cprinter.string_of_hp_rel_def) in *)
(*   let pr2 = pr_list (pr_triple pr_id pr_id Iprinter.string_of_view_decl) in *)
(*   Debug.no_1 "transform_hp_rels_to_iviews" pr1 pr2 transform_hp_rels_to_iviews hp_rels *)

(* let plugin_inferred_iviews views iprog = *)
(*   let vnames = List.map (fun (p,n,_)-> p,n) views in *)
(*   let vdecls = List.map (fun (pname,_,prd)-> { prd with  *)
(*       I.view_name = prd.I.view_name^"_"^pname; *)
(*       I.view_formula = IF.struc_formula_trans_heap_node (hn_trans pname vnames) prd.I.view_formula}) views in *)
(* 	let plug_views_proc proc =  *)
(* 	 let vnames = List.filter (fun (p,_)-> (String.compare p proc.I.proc_name)==0) vnames in *)
(* 	 (\* let () = print_string ("gugu: "^proc.I.proc_name^" "^(pr_list (pr_pair pr_id pr_id) vnames)^"\n") in *\) *)
(* 	 let hn_trans = hn_trans proc.I.proc_name vnames in *)
(* 	 {proc with  I.proc_static_specs= IF.struc_formula_trans_heap_node hn_trans (IF.struc_formula_drop_infer proc.I.proc_static_specs); *)
(* 				 I.proc_dynamic_specs= IF.struc_formula_trans_heap_node hn_trans (IF.struc_formula_drop_infer proc.I.proc_dynamic_specs)} in *)
(* 	{iprog with  *)
(* 		I.prog_view_decls= iprog.I.prog_view_decls@vdecls;  *)
(* 		I.prog_proc_decls= List.map plug_views_proc iprog.I.prog_proc_decls; *)
(* 		I.prog_hp_ids = [];  *)
(* 		I.prog_hp_decls=[];}  *)

(* let plugin_inferred_iviews views iprog = *)
(*   let pr1 = pr_list (pr_triple pr_id pr_id pr_none) in *)
(* Debug.no_1 "plugin_inferred_iviews" pr1 Iprinter.string_of_program (fun _ -> plugin_inferred_iviews views iprog) views *)

let check_data_pred_name iprog name : bool =
  try
    let todo_unk = I.look_up_data_def_raw iprog.I.prog_data_decls name in false
  with | Not_found -> begin
 	  try
	    let todo_unk = I.look_up_view_def_raw 3 iprog.I.prog_view_decls name in false
	  with | Not_found -> begin
      try
        let todo_unk = I.look_up_rel_def_raw iprog.I.prog_rel_decls name in false
      with | Not_found -> begin
        try
		      let todo_unk = I.look_up_func_def_raw iprog.I.prog_func_decls name in false
		    with | Not_found -> begin
          try
			      let todo_unk = I.look_up_hp_def_raw iprog.I.prog_hp_decls name in false
          with | Not_found -> begin
            try
              let todo_unk = I.look_up_templ_def_raw iprog.I.prog_templ_decls name in false 
            with | Not_found -> begin
              try
                let todo_unk = I.look_up_ut_def_raw iprog.I.prog_ut_decls name in false 
              with | Not_found -> true
              end
		        end
          end
        end
      end
    end

(* let check_data_pred_name iprog name : bool = *)
(*   let pr1 x = x in *)
(*   let pr2 = string_of_bool in *)
(*   Debug.no_1 "check_data_pred_name" pr1 pr2 (fun _ -> check_data_pred_name iprog name) name *)

(* let process_pred_def_4_iast iprog pdef =  *)
(*   (\* if check_data_pred_name iprog pdef.I.view_name then *\) *)
(*     let curr_view_decls = iprog.I.prog_view_decls in *)
(*     try *)
(*       let h = (self,Unprimed)::(res_name,Unprimed)::(List.map (fun c-> (c,Unprimed)) pdef.Iast.view_vars ) in *)
(*       let p = (self,Primed)::(res_name,Primed)::(List.map (fun c-> (c,Primed)) pdef.Iast.view_vars ) in *)
(*       iprog.I.prog_view_decls <- pdef :: curr_view_decls; *)
(*       let wf = case_normalize_struc_formula_view 11 iprog h p pdef.Iast.view_formula false  *)
(*         false (\*allow_post_vars*\) false [] in *)
(*       let inv_lock = pdef.I.view_inv_lock in *)
(*       let inv_lock = *)
(*         (match inv_lock with *)
(*           | None -> None *)
(*           | Some f -> *)
(*                 let new_f = case_normalize_formula iprog h f None in (\*TO CHECK: h or p*\) *)
(*                 Some new_f) *)
(*         in *)
(*       let new_pdef = {pdef with Iast.view_formula = wf;Iast.view_inv_lock = inv_lock} in *)
(*       iprog.I.prog_view_decls <- ( new_pdef :: curr_view_decls); *)
(*     with *)
(*       | _ ->  dummy_exception() ; iprog.I.prog_view_decls <- curr_view_decls *)
(*     (\* else *\) *)
(*     (\*   print_string (pdef.I.view_name ^ " is already defined.\n") *\) *)

(* let process_pred_def_4_iast iprog pdef = *)
(*   let pr = Iprinter.string_of_view_decl in *)
(*   Debug.no_1 "process_pred_def_4_iast" pr pr_no *)
(*       (fun _ -> process_pred_def_4_iast iprog pdef) pdef *)

let process_pred_def_4_iast_x iprog check_exists pdef=
  if not check_exists || check_data_pred_name iprog pdef.I.view_name then
    let curr_view_decls = iprog.I.prog_view_decls in
    iprog.I.prog_view_decls <- pdef :: curr_view_decls;
  else
    report_error pdef.I.view_pos (pdef.I.view_name ^ " is already defined.")

let process_pred_def_4_iast iprog check_exists pdef=
  let pr = Iprinter.string_of_view_decl in
  Debug.no_1 "process_pred_def_4_iast" pr pr_none
      (fun _ -> process_pred_def_4_iast_x iprog check_exists pdef) pdef

(*L2: todo: merge with SLEEKEN.convert_data_and_pred_to_cast*)
let convert_pred_to_cast_x ls_pr_new_view_tis is_add_pre iprog cprog do_pure_extn=
  let rec look_up_view ls_pair_view_name_tis vn0=
    match ls_pair_view_name_tis with
      | [] -> None
      | (vn,tis)::rest -> if String.compare vn vn0 = 0 then Some tis
        else look_up_view rest vn0
  in
  let new_views = List.map fst ls_pr_new_view_tis in
  let tmp_views, ls_mut_rec_views = (order_views (iprog.I.prog_view_decls)) in
  let () = x_add Iast.set_check_fixpt iprog iprog.I.prog_data_decls tmp_views in
  iprog.I.prog_view_decls <- tmp_views;
  let tmp_views_derv,tmp_views= List.partition (fun v -> v.I.view_derv) tmp_views in
  (* let tmp_new_views = List.filter (fun vdcl -> *)
  (*     List.exists (fun vn1 -> *)
  (*     String.compare vdcl.I.view_name vn1 = 0) new_views) tmp_views in *)
  let tmp_new_views = List.fold_left (fun res vdcl ->
      let otis = look_up_view ls_pr_new_view_tis vdcl.I.view_name in
      match otis with
        | None -> res
        | Some tis -> res@[(vdcl,tis)]
  ) [] tmp_views in
  (* let cviews0b = List.fold_left (fun transed_views (vdecl,tis) -> *)
  (*     let nview = trans_view iprog (List.concat ls_mut_rec_views) *)
  (*       transed_views tis vdecl in *)
  (*     transed_views@[nview] *)
  (* ) [] tmp_new_views in *)
  (* (\* Loc: to compute invs for mut-rec views *\) *)
  (* let () = Debug.ninfo_hprint (add_str "ls_mut_rec_views" (pr_list (pr_list pr_id))) ls_mut_rec_views no_pos in *)
  (* let cviews0a = Fixcalc.compute_inv_mutrec ls_mut_rec_views cviews0b in *)
  let cviews0a =  trans_views iprog ls_mut_rec_views tmp_new_views in
  (*derv and spec views*)
  let cviews0 = if do_pure_extn then
    let tmp_views_derv1 = mark_rec_and_der_order tmp_views_derv in
    let cviews_derv = List.fold_left (fun norm_views v ->
        let der_view = x_add_1 Derive.trans_view_dervs iprog Rev_ast.rev_trans_formula trans_view norm_views v in
        (cviews0a@[der_view])
    ) cviews0a tmp_views_derv1 in
    let cviews0 = (* cviews0a@ *)cviews_derv in
    cviews0
  else cviews0a
  in
  let pr2 = pr_list_ln Cprinter.string_of_view_decl in
  let cviews =
    if !Globals.norm_elim_useless (* !Globals.pred_elim_useless  *)then
      Norm.norm_elim_useless cviews0 (List.map (fun vdef -> vdef.C.view_name) cviews0)
    else cviews0
  in
  let cviews1 =
    if !Globals.norm_extract then
      Norm.norm_extract_common iprog cprog cviews (List.map (fun vdef -> vdef.C.view_name) cviews)
    else cviews
  in
  let () = Debug.ninfo_zprint (lazy (( "cviews1: " ^ (pr2 cviews1)))) no_pos in
  let cviews2 = x_add_1 Norm.cont_para_analysis cprog cviews1 in
  let () = cprog.C.prog_view_decls <- cprog.C.prog_view_decls@cviews2 in
  let todo_unk =  (List.map (fun vdef -> compute_view_x_formula cprog vdef !Globals.n_xpure) cviews2) in
  let todo_unk = (List.map (fun vdef -> set_materialized_prop vdef) cprog.C.prog_view_decls) in
  let cprog1 = fill_base_case cprog in
  let cprog2 = sat_warnings cprog1 in
  (*detect predicates for graph optimization*)
  let cprog2 =
     if !Globals.norm_cont_analysis then
     let is_need_seg_opz, cviews3a = x_add_1 Norm.norm_ann_seg_opz iprog cprog2 cprog2.Cast.prog_view_decls in
     let () = if is_need_seg_opz then
       let () = Frame.seg_opz := true in
       ()
     else
       let () = Frame.seg_opz := false in
       ()
     in
     let cprog2a = {cprog2 with Cast.prog_view_decls = cviews3a} in
     cprog2a
     else cprog2
  in
  let cprog3 = if (!Globals.enable_case_inference || (not !Globals.dis_ps)(* !Globals.allow_pred_spec *))
    then pred_prune_inference cprog2 else cprog2 in
  let cprog4 = if is_add_pre then (add_pre_to_cprog cprog3) else cprog3 in
  let () = cprog.C.prog_view_decls <- cprog4.C.prog_view_decls in
  List.filter (fun vdcl ->
      List.exists (fun vn1 ->
          String.compare vdcl.C.view_name vn1 = 0) new_views
  ) cprog.C.prog_view_decls

let convert_pred_to_cast new_views is_add_pre iprog cprog do_pure_extn=
  let pr1 = pr_list (pr_pair pr_id string_of_tlist) in
  let pr2 = pr_list_ln ( Cprinter.string_of_view_decl) in
  Debug.no_1 "convert_pred_to_cast" pr1 pr2
      ( fun _ -> convert_pred_to_cast_x new_views is_add_pre iprog cprog do_pure_extn) new_views

(*LOC: this transformation is not quite correct. please improve*)
let plugin_inferred_iviews views iprog cprog=
  let hn_trans pname vnames hn = match hn with 
    | IF.HRel (id,eargs, pos)-> 
        if (List.exists (fun (_,n)-> (String.compare n id)==0) vnames) then 
          let hvar,tl =
            let er, args = C.get_root_args_hprel cprog.C.prog_hp_decls id eargs in
            let r = match er with
              | (IP.Var (v,_))-> v
              | IP.Ann_Exp (IP.Var (sv, _), _, _) -> sv (*annotated self*)
              | _ -> failwith "reverification failure due to too complex predicate arguments \n" in
            (r, args)
          in
          IF.HeapNode { 
              IF.h_formula_heap_node = hvar;
              IF.h_formula_heap_name = id^"_"^pname;
              IF.h_formula_heap_deref = 0;
              IF.h_formula_heap_derv = false;
              IF.h_formula_heap_split = SPLIT0;
              IF.h_formula_heap_imm = IP.ConstAnn(Mutable);
              IF.h_formula_heap_imm_param = [];
              IF.h_formula_heap_full = false;
              IF.h_formula_heap_with_inv = false;
              IF.h_formula_heap_perm = None;
              IF.h_formula_heap_arguments = tl;
              IF.h_formula_heap_ho_arguments = []; (* TODO:HO *)
              IF.h_formula_heap_pseudo_data = false;
              IF.h_formula_heap_label = None;
              IF.h_formula_heap_pos = pos}
        else hn
    | _ -> hn
  in
  let vnames = List.map (fun (p,n,_)-> p,n) views in
  let vdecls = List.map (fun (pname,_,prd)-> { prd with 
        I.view_name = prd.I.view_name^"_"^pname;
        I.view_formula = IF.struc_formula_trans_heap_node (hn_trans pname vnames) prd.I.view_formula}
  ) views in
  let plug_views_proc proc = 
    let vnames = List.filter (fun (p,_)-> (String.compare p proc.I.proc_name)==0) vnames in
	 (* let () = print_string ("gugu: "^proc.I.proc_name^" "^(pr_list (pr_pair pr_id pr_id) vnames)^"\n") in *)
    let hn_trans = hn_trans proc.I.proc_name vnames in
    {proc with  I.proc_static_specs= IF.struc_formula_trans_heap_node hn_trans (IF.struc_formula_drop_infer proc.I.proc_static_specs);
                I.proc_dynamic_specs= IF.struc_formula_trans_heap_node hn_trans (IF.struc_formula_drop_infer proc.I.proc_dynamic_specs)} in
  {iprog with 
    I.prog_view_decls= iprog.I.prog_view_decls@vdecls; 
    I.prog_proc_decls= List.map plug_views_proc iprog.I.prog_proc_decls;
    I.prog_hp_ids = []; 
    I.prog_hp_decls=[];} 

let plugin_inferred_iviews views iprog cprog=
  let pr1 = pr_list (pr_triple pr_id pr_id pr_none) in
  Debug.no_1 "plugin_inferred_iviews" pr1 Iprinter.string_of_program (fun _ -> plugin_inferred_iviews views iprog cprog) views


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
