#include "xdebug.cppo"
(*
  Created 21-Feb-2006

  Formula
*)

module DD = Debug
open Globals
open VarGen
open Gen
open Exc.GTable
open Perm
open Label_only
open Label
open Cpure

module Err = Error
module CP = Cpure
module MCP = Mcpure
module CVP = CvpermUtils

let pre_subst_flag = ref false

(* type ann = ConstAnn of heap_ann | PolyAnn of CP.spec_var | *)
(*         TempAnn of ann | TempRes of (ann * ann) (\* lhs_ann * rhs_ann *\) *)
(* CP.TempAnn  -> to what is lent  *)

(* type view_arg = SVArg of CP.spec_var | AnnArg of ann *)

type ann = CP.ann

type cond_path_type = int list

(* let string_of_cond_path c = "(" ^(String.concat ", " (List.map string_of_int c)) ^ ")" *)
let string_of_cond_path c = pr_list_round string_of_int c

(* WN: mutable data is bad idea *)
(* type cond_path_type_stk = int Gen.stack *)
(* let string_of_cond_path_stk stk = *)
(*   let lst = stk # get_stk in *)
(*   string_of_cond_path lst *)


let string_of_ann a = CP.string_of_ann a
(* match a with *)
(*   | CP.ConstAnn h -> string_of_heap_ann h *)
(*   | CP.PolyAnn v -> "PolyAnn" *)
(*   | CP.TempAnn v -> "TempAnn" *)
(*   | CP.TempRes _ -> "TempRes" *)

let string_of_ann_list xs = pr_list string_of_ann xs

let view_prim_lst = new Gen.stack_pr "view-prim" pr_id (=)
let view_ptr_arith_lst = new Gen.stack_pr "view-ptr-arith" pr_id (=)

(* moved to globals.ml *)
(* type typed_ident = (typ * ident) *)

type mem_perm_formula = {mem_formula_exp : CP.exp;
                        mem_formula_exact : bool;
                        mem_formula_field_values : (ident * (CP.exp list)) list;
                        mem_formula_field_layout : (ident * (ann list)) list;
                        mem_formula_guards : CP.formula list;
                       }

let string_of_typed_ident = pr_pair string_of_typ pr_id

(* and formula_type = *)
(*   | Simple *)
(*   | Complex *)
(* (\*later, type of formula, based on #nodes ....*\) *)

type t_formula = (* type constraint *)
  (* commented out on 09.06.08 : we have decided to remove for now the type information related to the OO extension
     	   | TypeExact of t_formula_sub_type (* for t = C *)
     	   | TypeSub of t_formula_sub_type (* for t <: C *)
     	   | TypeSuper of t_formula_sub_type (* for t < C *)
     	*)

  | TypeAnd of t_formula_and
  | TypeTrue
  | TypeFalse
  | TypeEmpty

and t_formula_sub_type = { t_formula_sub_type_var : Cpure.spec_var;
                           t_formula_sub_type_type : ident }

and t_formula_and = { t_formula_and_f1 : t_formula;
                      t_formula_and_f2 : t_formula }


(*and struc_formula = (formula_label*ext_formula) list*)

and struc_formula =
  | EList of (spec_label_def * struc_formula) list
  | ECase of struc_case_formula
  | EBase of struc_base_formula
  | EAssume of assume_formula (*((Cpure.spec_var list) * formula * formula_label * ensures_type)*)
  | EInfer of struc_infer_formula

and assume_formula =
  {
    formula_assume_simpl : formula; (* this is added after pre-checking *)
    formula_assume_struc : struc_formula; (* this is used for proving post of methods *)
    formula_assume_lbl : formula_label;
    formula_assume_ensures_type : ensures_type;
    formula_assume_vars : Cpure.spec_var list;
  }

and struc_infer_formula =
  {
    (* formula_inf_tnt: bool; (\* true if termination to be inferred *\) *)
    formula_inf_obj: Globals.inf_obj_sub; (* local infer object *)
    formula_inf_post : bool; (* true if post to be inferred *)
    formula_inf_xpost : bool option; (* None -> no auto-var; Some _ -> true if post to be inferred *)
    formula_inf_transpec : (ident * ident) option;
    formula_inf_vars : Cpure.spec_var list;
    formula_inf_continuation : struc_formula;
    (* TODO : can we change this to struc_formula instead *)
    (* formula_inf_continuation : struc_formula; *)
    formula_inf_pos : loc
  }

and struc_case_formula =
  {
    formula_case_branches : (Cpure.formula * struc_formula ) list;
    (* formula_case_exists : Cpure.spec_var list; *) (*should be absolete, to be removed *)
    formula_case_pos : loc
  }

and struc_base_formula =
  {
    formula_struc_explicit_inst : Cpure.spec_var list;
    formula_struc_implicit_inst : Cpure.spec_var list;
        (*
           vars_free, vars_linking, vars_extracted
        *)
    formula_struc_exists : Cpure.spec_var list;
    formula_struc_base : formula;
    (* formula_struc_is_strict_seq: bool; *)
    formula_struc_is_requires: bool;
    formula_struc_continuation : struc_formula option;
    formula_struc_pos : loc
  }

and formula =
  | Base of formula_base
  | Or of formula_or
  | Exists of formula_exists

and rflow_formula = {
  rflow_kind: ho_flow_kind;
  rflow_base: (* struc_ *)formula;
  (* rflow_global_vars: CP.spec_var list; *)
}

and rflow_struc_formula = {
  (* rflow_kind: ho_flow_kind; *)
  rflow_struc_base: struc_formula;
  (* rflow_global_vars: CP.spec_var list; *)
}

and list_formula = formula list

and formula_sig = ident list

and formula_base = {
  formula_base_heap : h_formula;
  formula_base_vperm : CVP.vperm_sets;
  formula_base_pure : MCP.mix_formula;
  formula_base_type : t_formula; (* a collection ot subtype information *)
  formula_base_and : one_formula list; (*to capture concurrent flows*)
  formula_base_flow : flow_formula;
  formula_base_label : formula_label option;
  formula_base_pos : loc }

and mem_formula = {
  mem_formula_mset : CP.DisjSetSV.dpart ; (* list of disjoint vars *)
}

and formula_or = {
  formula_or_f1 : formula;
  formula_or_f2 : formula;
  formula_or_pos : loc }

and formula_exists = {
  formula_exists_qvars : CP.spec_var list;
  formula_exists_heap : h_formula;
  formula_exists_vperm : CVP.vperm_sets;
  formula_exists_pure : MCP.mix_formula;
  formula_exists_type : t_formula;
  formula_exists_and : one_formula list;
  formula_exists_flow : flow_formula;
  formula_exists_label : formula_label option;
  formula_exists_pos : loc }

and flow_formula = {  formula_flow_interval : nflow;
                      formula_flow_link : (ident option)}
and flow_store = {
  formula_store_name : ident;
  formula_store_value : flow_formula;
}

and one_formula = {
  formula_heap : h_formula;
  formula_pure : MCP.mix_formula;
  formula_thread : CP.spec_var; (*thread identifier*)
  formula_delayed : MCP.mix_formula;
  formula_ref_vars : CP.spec_var list; (*to update ref vars when join*)
  formula_label : formula_label option;
  formula_pos : loc
}

and flow_treatment =
  | Flow_combine
  | Flow_replace

and h_formula = (* heap formula *)
  | Star of h_formula_star
  (* guard as magic wand? *)
  (* | Wand of h_formula * h_formula *)
  | StarMinus of h_formula_starminus
  | Conj of h_formula_conj
  | ConjStar of h_formula_conjstar
  | ConjConj of h_formula_conjconj
  | Phase of h_formula_phase
  | DataNode of h_formula_data
  | ViewNode of h_formula_view
  | ThreadNode of h_formula_thread
  | Hole of int | FrmHole of int
  (* | TempHole of int * h_formula *)
  | HRel of (CP.spec_var * ((CP.exp) list) * loc) (*place holder for unknown heap predicates*)
  (* | HRel of ((CP.spec_var * cond_path_type) * ((CP.exp) list) * loc) (\*placeh older for heap predicates*\) *)
  | HTrue
  | HFalse
  | HEmp (* emp for classical logic *)
  | HVar of CP.spec_var * (CP.spec_var list)

and h_formula_star = {  h_formula_star_h1 : h_formula;
                        h_formula_star_h2 : h_formula;
                        h_formula_star_pos : loc }

and h_formula_starminus = {  h_formula_starminus_h1 : h_formula;
                             h_formula_starminus_h2 : h_formula;
                             h_formula_starminus_aliasing : aliasing_scenario;
                             h_formula_starminus_pos : loc }

and h_formula_conj = { h_formula_conj_h1 : h_formula;
                       h_formula_conj_h2 : h_formula;
                       h_formula_conj_pos : loc }

and h_formula_conjstar = { h_formula_conjstar_h1 : h_formula;
                           h_formula_conjstar_h2 : h_formula;
                           h_formula_conjstar_pos : loc }

and h_formula_conjconj = { h_formula_conjconj_h1 : h_formula;
                           h_formula_conjconj_h2 : h_formula;
                           h_formula_conjconj_pos : loc }


and h_formula_phase = { h_formula_phase_rd : h_formula;
                        h_formula_phase_rw : h_formula;
                        h_formula_phase_pos : loc }

(*Added in 2014-02-18: Thread node carrying a resource
  e.g. t::thread(0.5)<x::node<>> *)
and h_formula_thread = {  h_formula_thread_node : CP.spec_var;
                          h_formula_thread_name : ident;
                          h_formula_thread_derv : bool;
                          h_formula_thread_split : split_ann;
                          h_formula_thread_perm : cperm; (* option; *) (*LDK: permission*)
                          (*added to support fractional splitting of thread nodes*)
                          h_formula_thread_origins : ident list;
                          h_formula_thread_original : bool;
                          h_formula_thread_resource : formula;
                          h_formula_thread_delayed : CP.formula;
                          h_formula_thread_label : formula_label option;
                          h_formula_thread_pos : loc }

and h_formula_data = {  h_formula_data_node : CP.spec_var;
                        h_formula_data_name : ident;
                        h_formula_data_derv : bool;
                        h_formula_data_split : split_ann;
                        h_formula_data_imm : ann;
                        h_formula_data_param_imm : ann list;
                        h_formula_data_perm : cperm; (* option; *) (*LDK: permission*)
                        (*added to support fractional splitting of data nodes*)
                        h_formula_data_origins : ident list;
                        h_formula_data_original : bool;
                        (*h_formula_data_abstract_type : CP.spec_var option;  asankhs: keep track of the mathematical object that is associated with this points to *)
                        h_formula_data_arguments : CP.spec_var list;
                        h_formula_data_holes : int list; (* An Hoa : list of fields not to be considered for partial structures *) (*store positions*)
                        h_formula_data_label : formula_label option;
                        h_formula_data_remaining_branches :  (formula_label list) option;
                        h_formula_data_pruning_conditions :  (CP.b_formula * formula_label list ) list;
                        h_formula_data_pos : loc }

and h_formula_view = {  h_formula_view_node : CP.spec_var;
                        h_formula_view_name : ident;
                        h_formula_view_derv : bool;
                        h_formula_view_split : split_ann;
                        h_formula_view_imm : ann;
                        (* h_formula_view_primitive : bool; (\* indicates if it is primitive view? *\) *)
                        h_formula_view_perm : cperm; (*LDK: permission*)
                        h_formula_view_arguments : CP.spec_var list;
                        h_formula_view_ho_arguments : rflow_formula list;
                        (* h_formula_view_ho_arguments : rflow_struc_formula list; *)
                        h_formula_view_annot_arg : (CP.annot_arg * int) list;
                        h_formula_view_args_orig : (CP.view_arg  * int) list; (* serves as a map for view_arguments and view_annot_arg (their initial position) *)
                        h_formula_view_modes : mode list;
                        h_formula_view_coercible : bool;
                        (* if this view is generated by a coercion from another view c,
                           then c is in h_formula_view_origins. Used to avoid loopy coercions *)
                        h_formula_view_origins : ident list;
                        h_formula_view_original : bool;
                        h_formula_view_lhs_case : bool; (* to allow LHS case analysis prior to unfolding and lemma *)
                        (* WN : why is this lhs_case analysis needed?? *)
                        h_formula_view_unfold_num : int; (* to prevent infinite unfolding *)
                        (* h_formula_view_orig_fold_num : int; (\* depth of originality for folding *\) *)
                        (* used to indicate a specialised view *)
                        h_formula_view_remaining_branches :  (formula_label list) option;
                        h_formula_view_pruning_conditions :  (CP.b_formula * formula_label list ) list;
                        h_formula_view_label : formula_label option;
                        h_formula_view_pos : loc ;
                     }
and approx_disj =
  | ApproxBase of approx_disj_base
  | ApproxOr of approx_disj_or

and approx_formula =
  | ApproxCon of approx_disj
  | ApproxAnd of approx_formula_and

and approx_disj_base = { approx_disj_base_vars : CP.spec_var list;
                         (* list of variables that _must_ point to objects *)
                         approx_disj_base_formula : CP.formula }

and approx_disj_or = { approx_disj_or_d1 : approx_disj;
                       approx_disj_or_d2 : approx_disj }

and approx_formula_and = { approx_formula_and_a1 : approx_formula;
                           approx_formula_and_a2 : approx_formula }

(* this will be set to TPdispatcher.simplify_omega later *)
let simplify_omega = ref(fun (c:Cpure.formula) -> c)
let print_formula = ref(fun (c:formula) -> "printer not initialized")
let print_formula_label = ref(fun (c:formula_label) -> "printer not initialized")
let print_formula_type = ref(fun (c:formula_type) -> "printer not initialized")
let print_one_formula = ref(fun (c:one_formula) -> "printer not initialized")
let print_pure_f = ref(fun (c:CP.formula) -> "printer not initialized")
let print_formula_base = ref(fun (c:formula_base) -> "printer not initialized")
let print_h_formula = ref(fun (c:h_formula) -> "printer not initialized")
let print_h_formula_for_spec = ref(fun (c:h_formula) -> "printer not initialized")
let print_t_formula = ref(fun (c:t_formula) -> "printer not initialized")
let print_mix_f = ref(fun (c:MCP.mix_formula) -> "printer not initialized")
let print_mix_formula = print_mix_f
let print_ident_list = ref(fun (c:ident list) -> "printer not initialized")
let print_svl = ref(fun (c:CP.spec_var list) -> "printer not initialized")
let print_sv = ref(fun (c:CP.spec_var) -> "printer not initialized")
let print_struc_formula = ref(fun (c:struc_formula) -> "printer not initialized")
let print_flow_formula = ref(fun (c:flow_formula) -> "printer not initialized")
let print_spec_var = print_sv
let print_spec_var_list = print_svl
let print_vperm_sets = ref(fun (c:CVP.vperm_sets) -> "printer not yet initialized")
let print_infer_rel(l,r) = (!print_pure_f l)^" --> "^(!print_pure_f r)
let print_mem_formula = ref (fun (c:mem_formula) -> "printer has not been initialized")
let print_imm = ref (fun (c:ann) -> "printer has not been initialized")

(* !!! **cformula.ml#335:HPRel(n):H *)
(* !!! **cformula.ml#336:HPRel(args):[ p, q] *)
let mk_HRel_as_view n args loc =
  let () = x_tinfo_hp (add_str "HPRel(n)" !CP.print_sv) n no_pos in
  let vn = name_of_spec_var n in
  let hd,tails = match args with
      n::ns -> (n,ns)
    | _ -> x_report_error loc "HREL -> View : need at least one parameter"
  in
  ViewNode {
    (* HRel *)
    h_formula_view_name = vn;
    h_formula_view_node = hd; (* root *)
    h_formula_view_arguments = tails; (* rest of argument *) (* 220 *)
    h_formula_view_pos = loc; (* 57 *)
    h_formula_view_label = None; (* 29*)

    (* prim_view *)
    h_formula_view_split = SPLIT0; (*21*)
    h_formula_view_imm = CP.NoAnn; (* 87 *)
    h_formula_view_perm = None; (* 60*)
    h_formula_view_ho_arguments = []; (* 29 *)
    h_formula_view_annot_arg = []; (* 49 *)
    h_formula_view_modes = []; (* 17 *)
    h_formula_view_coercible = false; (* 14 *)

    (* view with defn *)
    h_formula_view_unfold_num = 0; (* to prevent infinite unfolding *) (* 20*)
    h_formula_view_remaining_branches =  None; (*48*)
    h_formula_view_pruning_conditions =  [];
    h_formula_view_derv = false; (* 36 *)
    h_formula_view_args_orig = []; (* 24 *)
    h_formula_view_origins = [];
    h_formula_view_original = false;
    h_formula_view_lhs_case = false; (* to allow LHS case analysis prior to unfolding and lemma *)

  }

let mk_HRel_as_view_w_root n root args loc =
  mk_HRel_as_view n (root::args) loc

let mk_HRel_as_view_w_root n root args loc =
  let pr1 = !CP.print_sv in
  let pr2 = !CP.print_svl in
  let pr3 = !print_h_formula in
  Debug.no_3 "mk_HRel_as_view_w_root" pr1 pr1 pr2 pr3
    (fun _ _ _ -> mk_HRel_as_view_w_root n root args loc) n root args

let sat_stk = new Gen.stack_pr "sat-stk"  !print_formula  (=)

(* let print_failesc = ref (fun (c:failesc) -> "printer has not been initialized") *)

let get_formula_base f =
  match f with
  | Base fb -> fb
  | _ -> failwith "not a formula_base"

let trans_rflow_formula f ff = { ff with rflow_base = f ff.rflow_base; }

let apply_rflow_formula f ff = f ff.rflow_base

let mkThreadNode c n derv split perm origins original rsr dl lbl pos =
  ThreadNode { h_formula_thread_node = c;
               h_formula_thread_name = n;
               h_formula_thread_derv = derv;
               h_formula_thread_split = split;
               h_formula_thread_perm = perm;
               h_formula_thread_origins = origins;
               h_formula_thread_original = original;
               h_formula_thread_resource = rsr;
               h_formula_thread_delayed = dl;
               h_formula_thread_label = lbl;
               h_formula_thread_pos = pos }

let mkFalseLbl (flowt: flow_formula) lbl pos =
  Base ({
      formula_base_heap = HFalse;
      formula_base_vperm = CVP.empty_vperm_sets;
      formula_base_pure = MCP.mkMFalse pos;
      formula_base_type = TypeFalse;
      formula_base_and = [];
      formula_base_flow = flowt (*mkFalseFlow*); (*Cpure.flow_eqs any_flow pos;*)
      formula_base_label = lbl;
      formula_base_pos = pos })

let dummy_lbl n = None
(* Some (-n,"")  *)

(* added a dummy_label for --eps *)
let mkFalse (flowt: flow_formula) pos = mkFalseLbl flowt (dummy_lbl 1) pos


let mkEFalse flowt pos = EBase({
    formula_struc_explicit_inst = [];
    formula_struc_implicit_inst = [];
    formula_struc_exists = [];
    formula_struc_base = mkFalse flowt pos;
    formula_struc_is_requires = false;
    formula_struc_continuation = None;
    formula_struc_pos = pos})

let mkTrueFlow () =
  {formula_flow_interval = !top_flow_int; formula_flow_link = None;}

let mkFalseFlow = {formula_flow_interval = false_flow_int; formula_flow_link = None;}
(* let mkFalseFlow () = mkTrueFlow () *)

let mkFlow i1 i2 =
  {formula_flow_interval = exlist # mk_nflow_from_min_max i1 i2; formula_flow_link = None;}

let mkFlow il =
  match il with
  | i1::i2::[] -> mkFlow i1 i2
  | _ -> mkTrueFlow ()

let mkTrue_b (flowt:flow_formula) pos = {
  formula_base_heap = HEmp;
  formula_base_vperm = CVP.empty_vperm_sets;
  formula_base_pure = MCP.mkMTrue pos;
  formula_base_type = TypeTrue;
  formula_base_and = [];
  formula_base_flow = flowt (*(mkTrueFlow ())*);
  formula_base_label = dummy_lbl 2;
  formula_base_pos = pos }

let mkTrue (flowt: flow_formula) pos = Base (mkTrue_b flowt pos)

let mkETrue flowt pos = EBase({
    formula_struc_explicit_inst = [];
    formula_struc_implicit_inst = [];
    formula_struc_exists = [];
    formula_struc_base = mkTrue flowt pos;
    formula_struc_is_requires = false;
    formula_struc_continuation = None;
    formula_struc_pos = pos})

(* Do we need emp? *)
let mkE_ensures_True flowt pos = EAssume {
    formula_assume_simpl = mkTrue flowt pos;
    formula_assume_struc = mkETrue flowt pos;
    formula_assume_lbl = (0,"no label");
    formula_assume_ensures_type = None;
    formula_assume_vars = [];
  }

let mkE_ensures_f f flowt pos = EAssume {
    formula_assume_simpl = f;
    formula_assume_struc = mkETrue flowt pos;
    formula_assume_lbl = (0,"no label");
    formula_assume_ensures_type = None;
    formula_assume_vars = [];
  }


let mkETrue_ensures_True flowt pos = EBase({
    formula_struc_explicit_inst = [];
    formula_struc_implicit_inst = [];
    formula_struc_exists = [];
    formula_struc_base = mkTrue flowt pos;
    formula_struc_is_requires = true;
    formula_struc_continuation = Some (mkE_ensures_True flowt pos);
    formula_struc_pos = pos})

let mkE_ensures_False flowt pos = EAssume {
    formula_assume_simpl = mkFalse flowt pos;
    formula_assume_struc = mkEFalse flowt pos;
    formula_assume_lbl = (0,"no label");
    formula_assume_ensures_type = None;
    formula_assume_vars = [];
  }

let mkETrue_ensures_False flowt pos = EBase({
    formula_struc_explicit_inst = [];
    formula_struc_implicit_inst = [];
    formula_struc_exists = [];
    formula_struc_base = mkTrue flowt pos;
    formula_struc_is_requires = true;
    formula_struc_continuation = Some (mkE_ensures_False flowt pos);
    formula_struc_pos = pos})

let isAnyConstFalse f = match f with
  | Exists ({
      formula_exists_heap = h;
      formula_exists_vperm = vp;
      formula_exists_pure = p;
      formula_exists_flow = fl; })
  | Base ({
        formula_base_heap = h;
        formula_base_vperm = vp;
        formula_base_pure = p;
        formula_base_flow = fl; }) ->
    h = HFalse || MCP.isConstMFalse p ||
    is_false_flow fl.formula_flow_interval || CVP.is_false_vperm_sets vp
  | _ -> false
(* TODO:WN : could we ensure vperm is normalized *)

(* let isAnyConstFalse f = *)
(*   let pr1 = !print_formula in *)
(*   Debug.no_1 "isAnyConstFalse" pr1 string_of_bool *)
(*     (fun _ -> isAnyConstFalse f) f *)

let isAnyConstFalse_struc sf= match sf with
  | EBase {formula_struc_base = f} -> isAnyConstFalse f
  | _ -> false

let isAllConstFalse f = match f with
  | Exists ({formula_exists_heap = h;
             formula_exists_pure = p;
             formula_exists_flow = fl;})
  | Base ({formula_base_heap = h;
           formula_base_pure = p;
           formula_base_flow = fl;}) -> (h = HFalse || MCP.isConstMFalse p)||(is_false_flow fl.formula_flow_interval)
  | _ -> false

let equal_flow_interval t1 t2 : bool =   is_eq_flow t1 t2

let is_top_flow p :bool = (equal_flow_interval !top_flow_int p)

let isStrictConstTrue_wo_flow f = match f with
  | Exists ({ formula_exists_heap = h;
              formula_exists_pure = p;
              formula_exists_flow = fl; })
  | Base ({formula_base_heap = h;
           formula_base_pure = p;
           formula_base_flow = fl;}) ->
    (h==HEmp || h==HTrue) && MCP.isConstMTrue p
  (* don't need to care about formula_base_type  *)
  | _ -> false

let isStrictConstTrue2 f = match f with
  | Exists ({ formula_exists_heap = h;
              formula_exists_pure = p;
              formula_exists_flow = fl; })
  | Base ({formula_base_heap = h;
           formula_base_pure = p;
           formula_base_flow = fl;}) ->
    (h==HTrue) && MCP.isConstMTrue p && is_top_flow fl.formula_flow_interval
  | _ -> false

let isStrictConstTrue f = match f with
  | Exists ({ formula_exists_heap = h;
              formula_exists_pure = p;
              formula_exists_flow = fl; })
  | Base ({formula_base_heap = h;
           formula_base_pure = p;
           formula_base_flow = fl;}) ->
    (*Loc: why h = HEmp is considered as ConstrTrue*)
    (h==HEmp || h==HTrue) && MCP.isConstMTrue p && is_top_flow fl.formula_flow_interval
  (* don't need to care about formula_base_type  *)
  | _ -> false

let  isStrictConstTrue (f:formula) =
  Debug.no_1 "isStrictConstTrue" !print_formula string_of_bool isStrictConstTrue f

let isStrictConstHTrue f = match f with
  | Exists ({ formula_exists_heap = h;
              formula_exists_pure = p;
              formula_exists_flow = fl; })
  | Base ({formula_base_heap = h;
           formula_base_pure = p;
           formula_base_flow = fl;}) ->
    ( h==HTrue) && MCP.isConstMTrue p && is_top_flow fl.formula_flow_interval
  (* don't need to care about formula_base_type  *)
  | _ -> false

let rec isConstDFalse f =
  match f with
  | EBase b -> isAnyConstFalse b.formula_struc_base
  | EList x-> List.for_all (fun (_,c)-> isConstDFalse c) x
  | _ -> false

let rec isConstDTrue f =
  match f with
  | EBase b -> (isStrictConstTrue b.formula_struc_base) &&(b.formula_struc_continuation==None)
  | EList x -> List.exists (fun (_,c)-> isConstDTrue c) x
  | _ -> false

let rec isConstDTrue2 f =
  match f with
  | EBase b -> (isStrictConstTrue2 b.formula_struc_base) &&(b.formula_struc_continuation==None)
  | EList x -> List.exists (fun (_,c)-> isConstDTrue2 c) x
  | _ -> false

let isConstETrue f = (*List.exists*) isConstDTrue2 f

let isConstETrue2 f = (*List.exists*) isConstDTrue2 f

let isConstEFalse f = (*List.for_all*) isConstDFalse f

let chg_assume_forms b f1 f2 = { b with
                                 formula_assume_simpl = f1;
                                 formula_assume_struc = f2;}

let mkEList_no_flatten_x l =
  (* if isConstETrue (EList l) then *)
  (*   mkETrue (mkTrueFlow ()) no_pos *)
  (* else *) if isConstEFalse (EList l) then mkEFalse (mkFalseFlow) no_pos
  else
    let l = List.filter (fun (c1,c2)-> not (isConstEFalse c2)) l in
    if l=[] then mkEFalse (mkFalseFlow) no_pos
    else EList l

let mkEList_no_flatten2 l =
  (* if isConstETrue2 (EList l) then *)
  (*   mkETrue (mkTrueFlow ()) no_pos *)
  (* else *) if isConstEFalse (EList l) then mkEFalse (mkFalseFlow) no_pos
  else
    let l = List.filter (fun (c1,c2)-> not (isConstEFalse c2)) l in
    if l=[] then mkEFalse (mkFalseFlow) no_pos
    else EList l

let mkEList_no_flatten l =
  let pr1 (_,cf) = !print_struc_formula cf in
  let pr2 = pr_list_ln pr1 in
  Debug.no_1 "mkEList_no_flatten" pr2 !print_struc_formula
    (fun _ -> mkEList_no_flatten_x l) l

let mkSingle f = (empty_spec_label_def,f)

let mkEList_flatten l =
  let l = List.map (fun c -> match c with | EList l->l | _ -> [mkSingle c]) l in
  mkEList_no_flatten (List.concat l)

let is_or_formula f = match f with
  | Or _ -> true
  | _ -> false

module Exp_Heap =
struct
  type e = h_formula
  let comb x y = Star
      { h_formula_star_h1 = x;
        h_formula_star_h2 = y;
        h_formula_star_pos = no_pos
      }
  let string_of = !print_h_formula
  let ref_string_of = print_h_formula
end;;

module Exp_Spec =
struct
  type e = struc_formula
  let comb x y = mkEList_flatten [x;y]
  let string_of = !print_struc_formula
  let ref_string_of = print_struc_formula
end;;

module Label_Heap = LabelExpr(Lab_List)(Exp_Heap);;
module Label_Spec = LabelExpr(Lab2_List)(Exp_Spec);;

(* generalized to data and view *)
let get_ptr_from_data h =
  match h with
  | DataNode f -> f.h_formula_data_node
  | ViewNode f -> f.h_formula_view_node
  | _ -> report_error no_pos "get_ptr_from_data : data expected"

(*if is hrel: return true and its name
  if a node or a view: return false and its name
*)
let get_ptr_from_data_w_hrel h =
  match h with
  | DataNode f -> false,f.h_formula_data_node
  | ViewNode f -> false, f.h_formula_view_node
  | HRel (hp,_,_) -> true,hp
  | _ -> report_error no_pos "get_ptr_from_data : data expected"

let print_path_trace = ref(fun (pt: path_trace) -> "printer not initialized")
let print_list_int = ref(fun (ll: int list) -> "printer not initialized")
(*--- 09.05.2000 *)
(* pretty printing for a spec_var list *)
let rec string_of_spec_var_list l = match l with
  | []               -> ""
  | h::[]            -> string_of_spec_var h
  | h::t             -> (string_of_spec_var h) ^ "," ^ (string_of_spec_var_list t)

and string_of_spec_var = function
  | CP.SpecVar (_, id, p) -> id ^ (match p with
      | Primed   -> "'"
      | Unprimed -> "")
(*09.05.2000 ---*)

let consistent_formula f : bool =
  let rec helper f = match f with
    | Base {formula_base_pure = mf}
    | Exists {formula_exists_pure = mf} ->
      MCP.consistent_mix_formula mf
    | Or {formula_or_f1 = f1; formula_or_f2 =f2} ->
      (helper f1) && (helper f2)
  in helper f

(* WN : what is the purpose of this "consistency" checking? *)
let must_consistent_formula (s:string) (l:formula) : unit =
  if !consistency_checking then
    let b = consistent_formula l in
    if b then  print_endline_quiet ("\nSuccessfully Tested Consistency at "^s)
    else report_error no_pos ("ERROR at "^s^": formula inconsistent")

let extr_formula_base e = match e with
    {formula_base_heap = h;
     formula_base_pure = p;
     formula_base_vperm = vp;
     formula_base_type = t;
     formula_base_flow = fl;
     formula_base_and = a} -> (h,p,vp,t,fl,a)

let is_eq_node_name a b = String.compare a b==0

let is_eq_data_name a b =
  match a,b with
  | {h_formula_data_name = c1;}, {h_formula_data_name = c2;}-> c1=c2

let is_eq_view_name a b =
  match a,b with
  | {h_formula_view_name = c1;}, {h_formula_view_name = c2;}-> String.compare c1 c2==0

let is_eq_view_name a b =
  Debug.no_2 "is_eq_view_name" (fun x->x) (fun x->x) string_of_bool (fun _ _ ->  is_eq_view_name a b)
    a.h_formula_view_name b.h_formula_view_name

let is_eq_data_ann a b = (a = b)
let is_eq_view_ann a b =
  match a,b with
  | {h_formula_view_imm = c1;}, {h_formula_view_imm = c2;}-> c1=c2

let br_match br1 br2 = match br1,br2 with
  | None,None -> true
  | Some br1,Some br2 ->(Gen.BList.list_setequal_eq (=) br1 br2)
  | _ ->   Err.report_error { Err.error_loc = no_pos; Err.error_text ="mix of specialised and unspecialised view"}

let is_eq_view_spec a b =
  (is_eq_view_name a b) &&
  (match a,b with
   | {h_formula_view_remaining_branches = c1;}, {h_formula_view_remaining_branches = c2;}-> br_match c1 c2)

let is_eq_view_spec a b =
  Debug.no_2 "is_eq_view_spec" (fun x->x) (fun x->x) string_of_bool (fun _ _ ->  is_eq_view_spec a b)
    a.h_formula_view_name b.h_formula_view_name

let mk_mem_formula vs =
  { mem_formula_mset = CP.DisjSetSV.one_list_dset vs}

(* returns false if unsatisfiable *)
let is_sat_mem_formula_x (mf:mem_formula) : bool =
  let d = mf.mem_formula_mset in
  (CP.DisjSetSV.is_sat_dset d)

let is_sat_mem_formula (mf:mem_formula) : bool =
  Debug.no_1 "is_sat_mem_formula"
    !print_mem_formula string_of_bool
    is_sat_mem_formula_x mf

let is_mem_mem_formula_x (e:CP.spec_var) (mf:mem_formula) : bool =
  let d = mf.mem_formula_mset in
  (CP.DisjSetSV.is_mem_dset e d)

(*check whether a spec var is a member of mem_formula*)
let is_mem_mem_formula (e:CP.spec_var) (mf:mem_formula) : bool =
  Debug.no_2 "is_mem_mem_formula"
    !print_spec_var !print_mem_formula string_of_bool
    is_mem_mem_formula_x e mf

(* returns all the disjoint pairs from a mem formula *)
let generate_disj_pairs_from_memf (mf:mem_formula):(CP.spec_var * CP.spec_var) list  =
  let m = mf.mem_formula_mset in
  let rec helper l =
    match l with
    | h::r ->
      if (r!=[]) then (List.fold_left (fun x y -> (h,y)::x) [] r) @ (helper r)
      else []
    | [] -> []
  in
  List.fold_left (fun x y -> x@(helper y)) [] m


let find_close svl0 eqs0 =
  let rec find_match svl ls_eqs rem_eqs=
    match ls_eqs with
    | [] -> svl,rem_eqs
    | (sv1,sv2)::ss->
      let b1 = CP.mem_svl sv1 svl in
      let b2 = CP.mem_svl sv2 svl in
      let new_m,new_rem_eqs=
        match b1,b2 with
        | false,false -> [],[(sv1,sv2)]
        | true,false -> ([sv2],[])
        | false,true -> ([sv1],[])
        | true,true -> ([],[])
      in
      find_match (svl@new_m) ss (rem_eqs@new_rem_eqs)
  in
  let rec loop_helper svl eqs=
    let new_svl,rem_eqs = find_match svl eqs [] in
    if List.length new_svl > List.length svl then
      loop_helper new_svl rem_eqs
    else new_svl
  in
  loop_helper svl0 eqs0

let rec formula_of_heap h pos =
  mkBase h (MCP.mkMTrue pos) CVP.empty_vperm_sets TypeTrue (mkTrueFlow ()) [] pos

and formula_base_of_heap h pos = {
  formula_base_heap = h;
  formula_base_vperm = CVP.empty_vperm_sets;
  formula_base_pure = (MCP.mkMTrue pos);
  formula_base_type = TypeTrue;
  formula_base_flow = (mkTrueFlow ());
  formula_base_and = [];
  formula_base_label = None;
  formula_base_pos = pos }

and formula_base_of_pure mf pos = {
  formula_base_heap = HEmp;
  formula_base_vperm = CVP.empty_vperm_sets;
  formula_base_pure = mf;
  formula_base_type = TypeTrue;
  formula_base_flow = (mkTrueFlow ());
  formula_base_and = [];
  formula_base_label = None;
  formula_base_pos = pos }

and formula_of_heap_w_normal_flow h pos =
  mkBase h (MCP.mkMTrue pos) CVP.empty_vperm_sets TypeTrue (mkNormalFlow ()) [] pos

and formula_of_heap_fl h fl pos =
  mkBase h (MCP.mkMTrue pos) CVP.empty_vperm_sets TypeTrue fl [] pos

and struc_formula_of_heap h pos =
  EBase {
    formula_struc_explicit_inst = [];
    formula_struc_implicit_inst = [];
    formula_struc_exists = [];
    formula_struc_base = formula_of_heap h pos;
    formula_struc_is_requires = false;
    formula_struc_continuation = None;
    formula_struc_pos = pos }

and struc_formula_of_heap_fl h fl pos = EBase {
    formula_struc_explicit_inst = [];
    formula_struc_implicit_inst = [];
    formula_struc_exists = [];
    formula_struc_base = formula_of_heap_fl h fl pos;
    formula_struc_is_requires = false;
    formula_struc_continuation = None;
    formula_struc_pos = pos}

and struc_formula_of_formula f pos = EBase {
    formula_struc_explicit_inst = [];
    formula_struc_implicit_inst = [];
    formula_struc_exists = [];
    formula_struc_base = f;
    formula_struc_is_requires = false;
    formula_struc_continuation = None;
    formula_struc_pos = pos}

and mkNormalFlow () = { formula_flow_interval = !norm_flow_int; formula_flow_link = None;}

and mkErrorFlow () = { formula_flow_interval = !error_flow_int; formula_flow_link = None;}

and formula_of_mix_formula (p: MCP.mix_formula) (pos:loc) : formula =
  mkBase HEmp p CVP.empty_vperm_sets TypeTrue (mkTrueFlow ()) [] pos

and formula_of_pure_formula (p:CP.formula) (pos:loc) :formula =
  let mix_f = (*MCP.OnePF*) MCP.mix_of_pure p in
  formula_of_mix_formula mix_f pos

and mkBase_simp (h : h_formula) (p : MCP.mix_formula) : formula =
  mkBase_w_lbl h p CVP.empty_vperm_sets TypeTrue (mkNormalFlow()) [] no_pos None

and mkEBase_w_vars ee ei ii f ct pos = EBase{
    formula_struc_explicit_inst = ei;
    formula_struc_implicit_inst = ii;
    formula_struc_exists =ee;
    formula_struc_base = f;
    formula_struc_is_requires = ct!=None;
    formula_struc_continuation = ct;
    formula_struc_pos = pos;
  }
and mkBase_rec f ct pos = {
  formula_struc_explicit_inst =[];
  formula_struc_implicit_inst =[];
  formula_struc_exists =[];
  formula_struc_base = f;
  formula_struc_is_requires = ct!=None;
  formula_struc_continuation = ct;
  formula_struc_pos = pos;
}

and mkEBase f ct pos = EBase (mkBase_rec f ct pos)

and mkEAssume vars post struc_post lbl ensure = EAssume {
    formula_assume_simpl = post;
    formula_assume_struc = struc_post;
    formula_assume_lbl = lbl;
    formula_assume_ensures_type = ensure;
    formula_assume_vars = vars;}

and mkEAssume_simp vars post struc_post lbl = EAssume {
    formula_assume_simpl = post;
    formula_assume_struc = struc_post;
    formula_assume_lbl = lbl;
    formula_assume_ensures_type = None;
    formula_assume_vars = vars;}

and mk_ebase_inferred_pre (h:h_formula) (p:CP.formula) ct = mkEBase (mkBase_simp h (MCP.mix_of_pure p)) ct no_pos

and formula_of_pure_aux (p:CP.formula) (status:int) (pos:loc) :formula=
  let mp = if (status > 0) then MCP.memoise_add_pure_N (MCP.mkMTrue pos) p
    else MCP.memoise_add_pure_P (MCP.mkMTrue pos) p
  in mkBase HEmp mp CVP.empty_vperm_sets TypeTrue (mkTrueFlow ()) [] pos

and formula_of_pure_P (p:CP.formula) (pos:loc) :formula = formula_of_pure_aux p (-1) pos

and formula_of_pure_N (p:CP.formula) (pos:loc) :formula = formula_of_pure_aux p 1 pos

(* and formula_of_pure_with_branches_aux p br status pos =                                                    *)
(*   let mp = if status>0 then MCP.memoise_add_pure_N (MCP.mkMTrue pos) p                                     *)
(*   else MCP.memoise_add_pure_P (MCP.mkMTrue pos) p in                                                       *)
(*   mkBase HTrue mp TypeTrue (mkTrueFlow ()) br [] pos                                                       *)

(* and formula_of_pure_with_branches_N p br pos = formula_of_pure_with_branches_aux p br 1 pos                *)

(* and formula_of_pure_with_branches_P p br pos = formula_of_pure_with_branches_aux p br (-1) pos             *)

(* and formula_of_mix_formula_with_branches p br pos = mkBase HTrue p TypeTrue (mkTrueFlow ()) br pos         *)

(* and formula_of_pure_with_branches_fl_aux p br fl status pos =                                              *)
(*   let mp = if status>0 then MCP.memoise_add_pure_N (MCP.mkMTrue pos) p                                     *)
(*   else MCP.memoise_add_pure_P (MCP.mkMTrue pos) p in                                                       *)
(*   mkBase HTrue mp TypeTrue fl br [] pos                                                                    *)

(* and formula_of_pure_with_branches_fl_N p br fl pos = formula_of_pure_with_branches_fl_aux p br fl 1 pos    *)

(* and formula_of_pure_with_branches_fl_P p br fl pos = formula_of_pure_with_branches_fl_aux p br fl (-1) pos *)

and formula_of_mix_formula_with_fl (p:MCP.mix_formula) fl pos =
  mkBase HEmp p CVP.empty_vperm_sets TypeTrue fl pos

and formula_of_base base = Base(base)

and data_of_h_formula h = match h with
  | DataNode d -> d
  | _ -> failwith ("data_of_h_formula: input is not a data node")

(*not strict, no need for empty pure*)
and isConstTrueFormula2 f =
  match f with
  | Base ({formula_base_heap = h})
  | Exists ({formula_exists_heap = h}) -> (h==HTrue)
  | Or ({formula_or_f1 = f1; formula_or_f2 = f2}) ->
    (isConstTrueFormula2 f1) && (isConstTrueFormula2 f2)

(*not strict, no need for empty pure*)
and isConstEmpFormula f =
  match f with
  | Base ({formula_base_heap = h})
  | Exists ({formula_exists_heap = h}) -> (h==HEmp)
  | Or ({formula_or_f1 = f1; formula_or_f2 = f2}) ->
    (isConstEmpFormula f1) && (isConstEmpFormula f2)

(* TRUNG TODO: should change name to isConstEmpFormula ? *)
and isConstTrueFormula f =
  match f with
  | Base b -> (b.formula_base_heap==HEmp) &&
              (MCP.isConstMTrue b.formula_base_pure)
  | Exists _ -> false
  | Or b -> false

and isConstETrueSpecs f = match f with
  | EBase b
  | EList ((_,EBase b)::[])-> isStrictConstTrue b.formula_struc_base &&
                              (match b.formula_struc_continuation with
                               | Some EAssume b-> isStrictConstTrue b.formula_assume_simpl
                               | None -> true
                               | _-> false)
  | _ -> false

(* TRUNG TODO: should change name to isStrictConstEmp_x ? *)
and isStrictConstEmp f = match f with
  | Exists ({ formula_exists_heap = HEmp;
              formula_exists_pure = p;
              formula_exists_flow = fl; })
  | Base ({formula_base_heap = HEmp;
           formula_base_pure = p;
           formula_base_flow = fl;}) ->
    MCP.isConstMTrue p && is_top_flow fl.formula_flow_interval
  (* don't need to care about formula_base_type  *)
  | _ -> false

and isStrictConstHTrue f = match f with
  | Exists ({ formula_exists_heap = HTrue;
              formula_exists_pure = p;
              formula_exists_flow = fl; })
  | Base ({formula_base_heap = HTrue;
           formula_base_pure = p;
           formula_base_flow = fl;}) ->
    MCP.isConstMTrue p && is_top_flow fl.formula_flow_interval
  (* don't need to care about formula_base_type  *)
  | _ -> false

and isEmpFormula f =
  match f with
  | Base ({formula_base_heap = HEmp}) -> true
  | Exists ({formula_exists_heap = HEmp}) -> true
  | Or ({formula_or_f1 = f1; formula_or_f2 = f2}) ->
    (isEmpFormula f1) && (isEmpFormula f2)
  | _ -> false

and is_trivial_h_formula h =
  match h with
  | HTrue | HFalse | HEmp -> true
  | _ -> false

and is_trivial_heap_formula f =
  match f with
  | Base ({formula_base_heap = h})
  | Exists ({formula_exists_heap = h})
    -> is_trivial_h_formula h
  | _ -> false

and is_trivial_formula f =
  match f with
  | Base {formula_base_heap = h;
          formula_base_pure = p;
         } ->
    ( is_trivial_h_formula h) && ((MCP.isConstMTrue p) ||  MCP.isTrivMTerm p)
  | Exists ({formula_exists_heap = h})
    -> let _,base = split_quantifiers f in
    is_trivial_formula base
  | _ -> false

(* allow explicit false to be considered trivial formula *)
and is_trivial_f f =
  match f with
  | Base {formula_base_heap = h;
          formula_base_pure = p;
         } ->   ( is_trivial_h_formula h ||  MCP.isTrivMTerm p)
  | Exists ({formula_exists_heap = h})
    -> let _,base = split_quantifiers f in
    is_trivial_f base
  | _ -> false

and isTrivTerm_x f = match f with
  | Base ({formula_base_heap = HEmp;formula_base_pure = p; formula_base_flow = fl;})
  | Exists ({formula_exists_heap = HEmp;formula_exists_pure = p; formula_exists_flow = fl;}) ->
    MCP.isTrivMTerm p && is_top_flow fl.formula_flow_interval
  (* don't need to care about formula_base_type  *)
  | _ -> false

and isTrivTerm (f:formula) =
  Debug.no_1 "isTrivTerm" !print_formula string_of_bool isTrivTerm_x f

(* TRUNG TODO: should change name to isAnyConstEmp ? *)
and isAnyConstTrue f = match f with
  | Exists ({formula_exists_heap = HEmp;
             formula_exists_pure = p;
             formula_exists_flow = fl; })
  | Base ({formula_base_heap = HEmp;
           formula_base_pure = p;
           formula_base_flow = fl;}) ->
    MCP.isConstMTrue p (* don't need to care about formula_base_type  *)
  | _ -> false

and is_complex_heap (h : h_formula) : bool = match h with
  | HFalse | HEmp-> false
  | _ -> true

and is_coercible_x (h : h_formula) : bool = match h with
  | ViewNode ({h_formula_view_coercible = c}) -> c
  | DataNode _ -> true (*LDK: assume that all data nodes are coercible*)
  | _ -> false

and is_coercible (h : h_formula) : bool =
  Debug.no_1 "is_coercible" !print_h_formula string_of_bool is_coercible_x h


(*
  for immutability
*)
and drop_read_phase (f : h_formula) : h_formula = match f with
  | Phase(f1) -> f1.h_formula_phase_rw
  | _ -> f

and drop_read_phase1 (f : h_formula) p : h_formula = match f with
  | Phase(f1) ->
    if contains_spec_var f1.h_formula_phase_rw p
    then f1.h_formula_phase_rw
    else f
  | Star({h_formula_star_h1 = h1;
          h_formula_star_h2 = h2;
          h_formula_star_pos = pos;}) ->
    let new_f1 = drop_read_phase1 h1 p in
    let new_f2 = drop_read_phase1 h2 p in
    mkStarH new_f1 new_f2 pos
  | Conj({h_formula_conj_h1 = h1;
          h_formula_conj_h2 = h2;
          h_formula_conj_pos = pos;}) ->
    let new_f1 = drop_read_phase1 h1 p in
    let new_f2 = drop_read_phase1 h2 p in
    mkConjH new_f1 new_f2 pos
  | ConjStar({h_formula_conjstar_h1 = h1;
              h_formula_conjstar_h2 = h2;
              h_formula_conjstar_pos = pos;}) ->
    let new_f1 = drop_read_phase1 h1 p in
    let new_f2 = drop_read_phase1 h2 p in
    mkConjStarH new_f1 new_f2 pos
  | ConjConj({h_formula_conjconj_h1 = h1;
              h_formula_conjconj_h2 = h2;
              h_formula_conjconj_pos = pos;}) ->
    let new_f1 = drop_read_phase1 h1 p in
    let new_f2 = drop_read_phase1 h2 p in
    mkConjConjH new_f1 new_f2 pos
  | _ -> f

and contains_spec_var (f : h_formula) p : bool = match f with
  | DataNode (h1) -> Cpure.eq_spec_var p h1.h_formula_data_node
  | ViewNode (h1) -> Cpure.eq_spec_var p h1.h_formula_view_node
  | Phase ({h_formula_phase_rd = h1;
            h_formula_phase_rw = h2;}) ->
    (contains_spec_var h1 p) || (contains_spec_var h2 p)
  | Conj ({h_formula_conj_h1 = h1;
           h_formula_conj_h2 = h2;})
  | ConjStar ({h_formula_conjstar_h1 = h1;
               h_formula_conjstar_h2 = h2;})
  | ConjConj ({h_formula_conjconj_h1 = h1;
               h_formula_conjconj_h2 = h2;}) ->
    (contains_spec_var h1 p) || (contains_spec_var h2 p)
  | Star ({h_formula_star_h1 = h1;
           h_formula_star_h2 = h2;}) ->
    (contains_spec_var h1 p) || (contains_spec_var h2 p)
  | HRel (_, expl, _) -> let svl = CP.afv_list expl in (*List.exists (fun e -> CP.eq_spec_var e p) svl*)
    (* let () = print_endline (!print_sv (List.hd svl)) in *)
    CP.eq_spec_var (List.hd svl) p
  | _ -> false



(*
  perform simplification incrementally
*)

and mkAndType f1 f2 = match f1 with
  | TypeTrue -> f2
  | TypeFalse -> TypeFalse
  | _ -> begin
      match f2 with
      | TypeTrue -> f1
      | TypeFalse -> TypeFalse
      | _ -> TypeAnd ({t_formula_and_f1 = f1; t_formula_and_f2 = f2})
    end

(*assume none is invalid*)
(* and non_overlapping (n1,n2) (p1,p2) : bool = n1>p2 || p1>n2 *)
and non_overlapping t1 t2 : bool = not(is_overlap_flow t1 t2)

and overlapping n p : bool = is_overlap_flow n p

(* and intersect_flow (n1,n2)(p1,p2) : (int*int)= ((if (n1<p1) then p1 else n1),(if (n2<p2) then n2 else p2)) *)

(* and is_false_flow (p1,p2) :bool = (p2==0)&&(p1==0) || p1>p2 *)


and is_sleek_mustbug_flow p: bool = (equal_flow_interval !error_flow_int p)
and is_sleek_mustbug_flow_ff ff: bool = is_sleek_mustbug_flow ff.formula_flow_interval

(* and equal_flow_interval (t1:nflow) (t2:nflow) : bool =  *)
(*   is_eq_flow t1 t2 *)

(*first subsumes the second*)
(* and subsume_flow_x (n1,n2)(p1,p2) : bool = *)
(* if (is_false_flow (p1,p2)) then true else (n1<=p1)&&(p2<=n2) *)

(* and subsume_flow (t1:nflow) (t2:nflow) : bool = *)
(*   is_subsume_flow t1 t2 *)

and subsume_flow t1 t2 : bool =
  is_subsume_flow t1 t2

(* and subsume_flow n p : bool =  *)
(*   let pr1 = pr_pair string_of_int  string_of_int in *)
(*   Debug.no_2 "subsume_flow" pr1 pr1 string_of_bool subsume_flow_x n p  *)

(* and overlap_flow t1 t2 : bool = (subsume_flow t1 t2) || (subsume_flow t2 t1) *)


and overlap_flow t1 t2 : bool = is_overlap_flow t1 t2

and subtract_flow_list t1 t2  (* : (nflow list) *) =
  subtract_flow_l t1 t2
(* if n1<p1 then (n1,p1-1)::(subtract_flow_list (p1,n2) (p1,p2)) *)
(* else if n2>p2 then [(p2+1,n2)] *)
(* else [] *)

and disjoint_flow t1 t2 : bool = not(overlap_flow t1 t2)

and subsume_flow_f t1 f :bool = subsume_flow t1 f.formula_flow_interval

and subsume_flow_ff f1 f2 :bool = subsume_flow f1.formula_flow_interval f2.formula_flow_interval

(* (==solver.ml#7135==) *)
(* subsume_flow_ff@2 *)
(* subsume_flow_ff inp1 :{FLOW,(1,26)=__flow#E} *)
(* subsume_flow_ff inp2 :{FLOW,(4,5)=__norm#E} *)
(* subsume_flow_ff@2 EXIT:true *)

(* subsume_flow_ff@3 *)
(* subsume_flow_ff inp1 :{FLOW,(4,5)=__norm#E} *)
(* subsume_flow_ff inp2 :{FLOW,(1,26)=__flow#E} *)
(* subsume_flow_ff@3 EXIT:false *)

(* and subsume_flow_ff f1 f2 :bool = *)
(*   let pr = !print_flow_formula in *)
(*   Debug.no_2 "subsume_flow_ff" pr pr string_of_bool subsume_flow_ff_x f1 f2 *)

and overlap_flow_ff f1 f2 :bool = overlap_flow f1.formula_flow_interval f2.formula_flow_interval

(* and overlap_flow_ff f1 f2 :bool =  *)
(*   let pr = !print_flow_formula in *)
(*   Debug.no_2 "subsume_flow_ff" pr pr string_of_bool overlap_flow_ff_x f1 f2 *)

and get_flow_from_stack c l pos =
  try
    let r = List.find (fun h-> ((String.compare h.formula_store_name c)==0)) l in
    r.formula_store_value
  with Not_found -> Err.report_error {
      Err.error_loc = pos;
      Err.error_text = "the flow var stack \n "^
                       (String.concat " " (List.map (fun h-> (h.formula_store_name^"= "^
                                                              (string_of_flow (h.formula_store_value.formula_flow_interval) ^" "))) l))^
                       "\n does not contain "^c
    }

and set_flow_in_formula_override (n:flow_formula) (f:formula):formula = match f with
  | Base b-> Base {b with formula_base_flow = n}
  | Exists b-> Exists {b with formula_exists_flow = n}
  | Or b-> Or {formula_or_f1 = set_flow_in_formula_override n b.formula_or_f1;
               formula_or_f2 = set_flow_in_formula_override n b.formula_or_f2;
               formula_or_pos = b.formula_or_pos}

and set_flow_in_formula (n:flow_formula) (f:formula):formula = match f with
  | Base b-> Base {b with formula_base_flow = if (subsume_flow_f !norm_flow_int b.formula_base_flow) then n else b.formula_base_flow}
  | Exists b-> Exists {b with formula_exists_flow = if (subsume_flow_f !norm_flow_int b.formula_exists_flow) then n else b.formula_exists_flow}
  | Or b-> Or {formula_or_f1 = set_flow_in_formula_override n b.formula_or_f1;
               formula_or_f2 = set_flow_in_formula_override n b.formula_or_f2;
               formula_or_pos = b.formula_or_pos}


and set_flow_to_link_f flow_store f pos = match f with
  | Base b-> Base {b with formula_base_flow =
                            if (equal_flow_interval b.formula_base_flow.formula_flow_interval false_flow_int) then b.formula_base_flow
                            else
                            if (subsume_flow !norm_flow_int b.formula_base_flow.formula_flow_interval ) then
                              match b.formula_base_flow.formula_flow_link with
                              | None -> Error.report_error { Error.error_loc = pos;Error.error_text = "simple flow where link required"}
                              | Some v -> get_flow_from_stack v flow_store pos
                            else b.formula_base_flow}
  | Exists b-> Exists {b with formula_exists_flow =
                                if (equal_flow_interval b.formula_exists_flow.formula_flow_interval false_flow_int) then b.formula_exists_flow
                                else
                                if (subsume_flow !norm_flow_int b.formula_exists_flow.formula_flow_interval ) then
                                  match b.formula_exists_flow.formula_flow_link with
                                  | None -> Error.report_error { Error.error_loc = pos;Error.error_text = "simple flow where link required"}
                                  | Some v -> get_flow_from_stack v flow_store pos
                                else b.formula_exists_flow}
  | Or b-> Or {formula_or_f1 = set_flow_to_link_f flow_store b.formula_or_f1 pos;
               formula_or_f2 = set_flow_to_link_f flow_store b.formula_or_f2 pos;
               formula_or_pos = b.formula_or_pos}


and formula_is_eq_flow  (f:formula) ff   : bool =
  let is_eq f = equal_flow_interval ff (f.formula_flow_interval) in
  match f with
  | Base b-> is_eq b.formula_base_flow
  | Exists b-> is_eq b.formula_exists_flow
  | Or b ->  (formula_is_eq_flow b.formula_or_f1 ff) &&  (formula_is_eq_flow b.formula_or_f2 ff)

and struc_formula_is_eq_flow (f:struc_formula) ff : bool = match f with
  | EList l ->List.for_all (fun (_,c)-> struc_formula_is_eq_flow c ff)l
  | EBase b -> (formula_is_eq_flow b.formula_struc_base ff) && (match b.formula_struc_continuation with Some f -> struc_formula_is_eq_flow f ff | None-> true)
  | ECase b -> List.for_all (fun (_,c) -> struc_formula_is_eq_flow c ff) b.formula_case_branches
  | EAssume b -> formula_is_eq_flow b.formula_assume_simpl ff
  | EInfer b -> struc_formula_is_eq_flow b.formula_inf_continuation ff

and formula_subst_flow (f:formula) ff : formula =
  match f with
  | Base b-> Base {b with formula_base_flow = ff}
  | Exists b-> Exists{b with formula_exists_flow = ff}
  | Or b -> Or {b with formula_or_f1 = formula_subst_flow b.formula_or_f1 ff;
                       formula_or_f2 = formula_subst_flow b.formula_or_f2 ff}

and struc_formula_subst_flow (f:struc_formula) ff : struc_formula = match f with
  | EList l -> EList (map_l_snd (fun c-> struc_formula_subst_flow c ff) l)
  | EBase b -> EBase {b with
                      formula_struc_base = formula_subst_flow b.formula_struc_base ff ;
                      formula_struc_continuation = map_opt (fun c-> struc_formula_subst_flow c ff) b.formula_struc_continuation
                     }
  | ECase b -> ECase {b with formula_case_branches =
                               List.map (fun (c1,c2) -> (c1,(struc_formula_subst_flow c2 ff))) b.formula_case_branches;}
  | EAssume b -> EAssume {b with
                          formula_assume_simpl = formula_subst_flow b.formula_assume_simpl ff;
                          formula_assume_struc = struc_formula_subst_flow b.formula_assume_struc ff;}
  | EInfer b -> EInfer {b with formula_inf_continuation = struc_formula_subst_flow b.formula_inf_continuation ff}

and split_one_formula (f : one_formula) = f.formula_heap, f.formula_pure,  f.formula_thread, f.formula_delayed, f.formula_label, f.formula_pos

and one_formula_of_formula (f : formula) (tid: CP.spec_var) (delayed_f:MCP.mix_formula) : one_formula =
  (match f with
   | Base {formula_base_heap = h;
           formula_base_pure = p;
           formula_base_label = lbl;
           formula_base_pos = pos;
          } ->
     mkOneFormula h p tid delayed_f lbl pos
   | Exists {
       formula_exists_heap = h;
       formula_exists_pure = p;
       formula_exists_label = lbl;
       formula_exists_pos = pos;
     } ->
     mkOneFormula h p tid delayed_f lbl pos
   | _ -> Error.report_error {Error.error_loc = no_pos; Error.error_text = "one_formula_of_formula: disjunctive form"} )

and add_formula_and (a: one_formula list) (f:formula) : formula =
  match f with
  | Or o -> mkOr (add_formula_and a o.formula_or_f1) (add_formula_and a o.formula_or_f2) o.formula_or_pos
  | Base b -> Base { b with formula_base_and = b.formula_base_and@a}
  | Exists e -> Exists {e with formula_exists_and = e.formula_exists_and@a}

and replace_formula_and (a: one_formula list) (f:formula) : formula =
  match f with
  | Or o -> mkOr (add_formula_and a o.formula_or_f1) (add_formula_and a o.formula_or_f2) o.formula_or_pos
  | Base b -> Base { b with formula_base_and = a}
  | Exists e -> Exists {e with formula_exists_and = a}


and formula_of_one_formula (f : one_formula) : formula =
  Base {
    formula_base_heap = f.formula_heap;
    formula_base_vperm = CVP.empty_vperm_sets;
    formula_base_pure = f.formula_pure;
    formula_base_type = TypeTrue;
    formula_base_and = [];
    formula_base_flow = mkTrueFlow ();
    formula_base_label = f.formula_label;
    formula_base_pos = f.formula_pos; }

and formula_and_of_formula (f:formula) : one_formula list =
  match f with
  | Base b-> b.formula_base_and
  | Exists b-> b.formula_exists_and
  | Or b ->
    (*need normalization or error*)
    Err.report_error { Err.error_loc = no_pos;
                       Err.error_text = "formula_and_of_formula: disjunctive formula"}

and flow_formula_of_formula (f:formula) (*pos*) : flow_formula =
  match f with
  | Base b-> b.formula_base_flow
  | Exists b-> b.formula_exists_flow
  | Or b ->
    let fl1 = flow_formula_of_formula b.formula_or_f1 in
    let fl2 = flow_formula_of_formula b.formula_or_f2 in
    if (equal_flow_interval fl1.formula_flow_interval fl2.formula_flow_interval) then fl1
    else (*TO CHECK: temporarily return !top_flow_int*)
      mkTrueFlow ()
(* else Err.report_error { Err.error_loc = no_pos; *)
(* Err.error_text = "flow_formula_of_formula: disjunctive formula"} *)

and flow_formula_of_struc_formula (f:struc_formula):flow_formula=
  let compare_flow ffi1 ffi2 =
    if (equal_flow_interval ffi1.formula_flow_interval ffi2.formula_flow_interval) then ffi1
    else Err.report_error { Err.error_loc = no_pos;
                            Err.error_text = "flow_formula_of_struc_formula: need to handle here"}
  in
  let fold_left_compare_flows flow_list=
    match flow_list with
    | [] -> report_error no_pos "Cformula.flow_formula_of_struc_formula"
    | fl::[] -> fl
    | _ ->  List.fold_left compare_flow (List.hd flow_list) (List.tl flow_list)
  in
  let rec helper (f:struc_formula) = match f with
    | EList b -> fold_left_compare_flows (List.map (fun (_,c)-> helper c) b)
    | EBase b -> flow_formula_of_formula b.formula_struc_base
    | ECase b -> fold_left_compare_flows (List.map (fun (_,c)-> helper c) b.formula_case_branches)
    | EAssume b -> flow_formula_of_formula b.formula_assume_simpl
    | EInfer b -> helper b.formula_inf_continuation
  in
  helper f

and substitute_flow_in_f to_flow from_flow (f:formula):formula =
  Debug.no_3 "substitute_flow_in_f" string_of_flow string_of_flow !print_formula !print_formula (fun _ _ _ -> substitute_flow_in_f_x to_flow from_flow f) to_flow from_flow f

and substitute_flow_in_f_x to_flow from_flow (f:formula):formula = match f with
  | Base b-> Base {b with formula_base_flow =
                            if (equal_flow_interval from_flow b.formula_base_flow.formula_flow_interval) then
                              {formula_flow_interval = to_flow; formula_flow_link = b.formula_base_flow.formula_flow_link}
                            else b.formula_base_flow;}
  | Exists b-> Exists{b with formula_exists_flow =
                               if (equal_flow_interval from_flow b.formula_exists_flow.formula_flow_interval) then
                                 {formula_flow_interval = to_flow; formula_flow_link = b.formula_exists_flow.formula_flow_link}
                               else b.formula_exists_flow;}
  | Or b-> Or {formula_or_f1 = substitute_flow_in_f_x to_flow from_flow b.formula_or_f1;
               formula_or_f2 = substitute_flow_in_f_x to_flow from_flow b.formula_or_f2;
               formula_or_pos = b.formula_or_pos}

and substitute_flow_into_f to_flow (f:formula):formula = match f with
  | Base b-> Base {b with formula_base_flow =
                            {formula_flow_interval = to_flow; formula_flow_link = b.formula_base_flow.formula_flow_link}}
  | Exists b-> Exists{b with formula_exists_flow =
                               {formula_flow_interval = to_flow; formula_flow_link = b.formula_exists_flow.formula_flow_link}}
  | Or b-> Or {formula_or_f1 = substitute_flow_into_f to_flow b.formula_or_f1;
               formula_or_f2 = substitute_flow_into_f to_flow b.formula_or_f2;
               formula_or_pos = b.formula_or_pos}

and substitute_flow_in_struc_f to_flow from_flow (f:struc_formula):struc_formula = match f with
  | EList b -> EList (map_l_snd (substitute_flow_in_struc_f to_flow from_flow) b)
  | EBase b -> EBase {b with formula_struc_base = substitute_flow_in_f to_flow from_flow b.formula_struc_base ;
                             formula_struc_continuation = map_opt (substitute_flow_in_struc_f to_flow from_flow)  b.formula_struc_continuation}
  | ECase b -> ECase {b with formula_case_branches = List.map (fun (c1,c2) -> (c1,(substitute_flow_in_struc_f to_flow from_flow  c2))) b.formula_case_branches;}
  | EAssume b -> EAssume {b with
                          formula_assume_simpl = substitute_flow_in_f to_flow from_flow  b.formula_assume_simpl;
                          formula_assume_struc = substitute_flow_in_struc_f to_flow from_flow b.formula_assume_struc;}
  | EInfer b -> EInfer {b with formula_inf_continuation =substitute_flow_in_struc_f to_flow from_flow b.formula_inf_continuation}

and change_flow f = match f with
  | Base fb ->
    if formula_is_eq_flow f !top_flow_int then
      Base {fb with
            formula_base_flow = mkNormalFlow ()}
    else f
  | Or fo -> Or {fo with
                 formula_or_f1 = change_flow fo.formula_or_f1;
                 formula_or_f2 = change_flow fo.formula_or_f2}
  | Exists fe ->
    if formula_is_eq_flow f !top_flow_int then
      Exists {fe with
              formula_exists_flow = mkNormalFlow ()}
    else f

and change_spec_flow spec =
  match spec with
  | EList el -> EList (List.map (fun (lbl,sf) -> (lbl,change_spec_flow sf)) el)
  | ECase ec -> ECase {ec with
                       formula_case_branches = List.map (fun (pf,sf) -> (pf,change_spec_flow sf)) ec.formula_case_branches}
  | EBase eb -> (match eb.formula_struc_continuation with
      | None ->
        let f = eb.formula_struc_base in
        let new_f = change_flow f in
        EBase {eb with
               formula_struc_base = new_f}
      | Some sf -> EBase {eb with
                          formula_struc_continuation = Some (change_spec_flow sf)}
    )
  | EAssume ea -> EAssume {ea with
                           formula_assume_simpl = change_flow ea.formula_assume_simpl;
                           formula_assume_struc = change_spec_flow ea.formula_assume_struc}
  | EInfer ei -> EInfer {ei with
                         formula_inf_continuation = change_spec_flow ei.formula_inf_continuation}

and mkAndFlow (fl1:flow_formula) (fl2:flow_formula) flow_tr :flow_formula =
  let pr = !print_flow_formula in
  let pr2 x = match x with Flow_combine -> "Combine" | Flow_replace -> "Replace"  in
  Debug.no_3 "mkAndFlow" pr pr pr2 pr (fun _ _ _ -> mkAndFlow_x fl1 fl2 flow_tr) fl1 fl2 flow_tr

(*this is used for adding formulas, links will be ignored since the only place where links can appear is in the context, the first one will be kept*)
and mkAndFlow_x (fl1:flow_formula) (fl2:flow_formula) flow_tr :flow_formula =  let int1 = fl1.formula_flow_interval in
  let int2 = fl2.formula_flow_interval in
  let r = if (is_top_flow int1) then fl2
    else if (is_top_flow int2) then fl1 (*Loc: why?, at least with Flow_replace, we should use int2 anyway?*)
    else
      match flow_tr with
      | Flow_replace ->
        {	formula_flow_interval = int2;
          formula_flow_link = match (fl1.formula_flow_link,fl2.formula_flow_link)with
            | None,None -> None
            | Some s,None-> Some s
            | None, Some s -> Some s
            | Some _, Some s -> Some s
                              (* | _ ->  Err.report_error { Err.error_loc = no_pos; Err.error_text = "mkAndFlow: cannot and two flows with two links"} *)
                              ;}
      | Flow_combine ->
        if (overlapping int1 int2) then
          {	formula_flow_interval = intersect_flow (* union_flow *) int1 int2;
            formula_flow_link = match (fl1.formula_flow_link,fl2.formula_flow_link)with
              | None,None -> None
              | Some s,None-> Some s
              | None, Some s -> Some s
              | Some s1, Some s2 -> Some (s1^"AND"^s2)
                                  (* | _ ->  Err.report_error { Err.error_loc = no_pos; Err.error_text = "mkAndFlow: cannot and two flows with two links"} *)
                                  ;}
        else {formula_flow_interval = false_flow_int; formula_flow_link = None}
  in
  r

and get_case_guard_list lbl (lst:(Cpure.b_formula * formula_label list) list) :  CP.b_formula list=
  List.fold_left (fun a (cond,lbl_lst) -> if (List.mem lbl lbl_lst) then cond::a else a) [] lst

(* TRUNG TODO: should change name to mkEmp_b ? *)

and mkTrue_b_nf pos = mkTrue_b (mkTrueFlow ()) pos

and mkTrue_nf pos = Base (mkTrue_b_nf pos)

and mkHTrue_b (flowt:flow_formula) pos = {
  formula_base_heap = HTrue;
  formula_base_vperm = CVP.empty_vperm_sets;
  formula_base_pure = MCP.mkMTrue pos;
  formula_base_type = TypeTrue;
  formula_base_and = [];
  formula_base_flow = flowt (*(mkTrueFlow ())*);
  formula_base_label = None;
  formula_base_pos = pos}

and mkHTrue_b_nf pos = mkHTrue_b (mkTrueFlow ()) pos

and mkHTrue (flowt: flow_formula) pos = Base (mkHTrue_b flowt pos)

and mkHTrue_nf pos = Base (mkHTrue_b_nf pos)

and mkFalse_nf pos = mkFalse (mkTrueFlow ()) pos

(*no flow*)
and mkETrue_nf pos = mkETrue (mkTrueFlow ()) pos

and mkOr f1 f2 pos =
  (* let rec liniarize_or c = match c with *)
  (*       | Or f ->  *)
  (*       	  let p11,p12,p13 = liniarize_or f.formula_or_f1 in *)
  (*       	  let p21,p22,p23 = liniarize_or f.formula_or_f2 in *)
  (*       	  (p11@p21, p12@p22, p13@p23) *)
  (*       | Exists _ -> ([],[],[c])  *)
  (*       | Base f ->  *)
  (*       	  if (isAnyConstFalse c) then ([],[c],[]) *)
  (*       	  else if (isAnyConstTrue c) then ([c],[],[]) *)
  (*       	  else ([],[],[c]) in *)
  (* if isStrictConstTrue f1 || isStrictConstTrue f2 then *)
  (*       mkTrue (mkTrueFlow ()) pos *)
  (* else  *)if isAnyConstFalse f1 then f2
  else if isAnyConstFalse f2 then f1
  else
    Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos})

and mkOr_n f1 f2 pos =
  (* if isStrictConstHTrue f1 then f2 else *)
  (*   if isStrictConstHTrue f2 then f1 *)
  (* else *) if isAnyConstFalse f1 then f2
  else if isAnyConstFalse f2 then f1
  else
    Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos})

and list_of_disjs (f0 : formula) : formula list =
  let rec helper f disjs = match f with
    | Or {formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos} ->
      let tmp1 = helper f2 disjs in
      let tmp2 = helper f1 tmp1 in
      tmp2
    | _ -> f :: disjs
  in
  helper f0 []

and disj_of_list (xs : formula list) pos : formula =
  let rec helper xs r = match xs with
    | [] -> r
    | x::xs -> mkOr x (helper xs r) pos
  in
  match xs with
  | [] -> mkTrue (mkTrueFlow ()) pos
  | x::xs -> helper xs x


and mkBase_w_lbl (h : h_formula) (p : MCP.mix_formula) (vp: CVP.vperm_sets)
    (t : t_formula) (fl : flow_formula) (a : one_formula list) (pos : loc) lbl: formula=
  if MCP.isConstMFalse p || h = HFalse || (is_false_flow fl.formula_flow_interval) then mkFalse fl pos
  else
    Base ({
        formula_base_heap = h;
        formula_base_vperm = vp;
        formula_base_pure = p;
        formula_base_type = t;
        formula_base_flow = fl;
        formula_base_and = a;
        formula_base_label = lbl;
        formula_base_pos = pos })

and mkBase (h : h_formula) (p : MCP.mix_formula) (vp: CVP.vperm_sets)
    (t : t_formula) (fl : flow_formula) (a: one_formula list) (pos : loc) : formula=
  mkBase_w_lbl h p vp t fl a pos None

and mkOneFormula (h : h_formula) (p : MCP.mix_formula) (tid : CP.spec_var) (dl : MCP.mix_formula) lbl (pos : loc) : one_formula=
  {formula_heap = h;
   formula_pure = p;
   formula_thread = tid;
   formula_delayed = dl;
   formula_ref_vars = [];
   formula_label = lbl;
   formula_pos = pos;
  }


and mkStarH (f1 : h_formula) (f2 : h_formula) (pos : loc) = match f1 with
  | HFalse -> HFalse
  | HEmp -> f2
  | _ -> match f2 with
    | HFalse -> HFalse
    | HEmp -> f1
    | _ -> if (f1 = HTrue) && (f2 = HTrue) then HTrue
      else Star { h_formula_star_h1 = f1;
                  h_formula_star_h2 = f2;
                  h_formula_star_pos = pos }

and mkStarMinusH (f1 : h_formula) (f2 : h_formula) (al: aliasing_scenario) (pos : loc) (no: int) =
  let pr = !print_h_formula in
  Debug.no_3 "mkStarMinusH" string_of_int pr pr pr (fun _ _ _ -> mkStarMinusH_x f1 f2 al pos) no f1 f2

and mkStarMinusH_x (f1 : h_formula) (f2 : h_formula) (al: aliasing_scenario) (pos : loc) = match f1 with
  | HFalse -> HFalse
  | HEmp -> f2
  | _ -> match f2 with
    | HFalse -> HFalse
    | HEmp -> f1
    | _ -> if (f1 = HTrue) && (f2 = HTrue) then HTrue
      else StarMinus { h_formula_starminus_h1 = f1;
                       h_formula_starminus_h2 = f2;
                       h_formula_starminus_aliasing = al;
                       h_formula_starminus_pos = pos }

and mkConjH (f1 : h_formula) (f2 : h_formula) (pos : loc) =
  if (f1 = HFalse) || (f2 = HFalse) then HFalse
  else if (f1 = HTrue) && (f2 = HTrue) then HTrue
  else if (f1 = HEmp) && (f2 = HEmp) then HEmp
  else if (f1 = HEmp) then f2
  else if (f2 = HEmp) then f1
  else Conj ({h_formula_conj_h1 = f1;
              h_formula_conj_h2 = f2;
              h_formula_conj_pos = pos})

and mkConjStarH (f1 : h_formula) (f2 : h_formula) (pos : loc) =
  if (f1 = HFalse) || (f2 = HFalse) then HFalse
  else if (f1 = HTrue) && (f2 = HTrue) then HTrue
  else if (f1 = HEmp) && (f2 = HEmp) then HEmp
  else if (f1 = HEmp) then f2
  else if (f2 = HEmp) then f1
  else ConjStar ({h_formula_conjstar_h1 = f1;
                  h_formula_conjstar_h2 = f2;
                  h_formula_conjstar_pos = pos})

and mkConjConjH (f1 : h_formula) (f2 : h_formula) (pos : loc) =
  if (f1 = HFalse) || (f2 = HFalse) then HFalse
  else if (f1 = HTrue) && (f2 = HTrue) then HTrue
  else if (f1 = HEmp) && (f2 = HEmp) then HEmp
  else if (f1 = HEmp) then f2
  else if (f2 = HEmp) then f1
  else ConjConj ({h_formula_conjconj_h1 = f1;
                  h_formula_conjconj_h2 = f2;
                  h_formula_conjconj_pos = pos})

and mkPhaseH (f1 : h_formula) (f2 : h_formula) (pos : loc) =
  match f1 with
  | HFalse -> HFalse
  | _ -> match f2 with
    | HFalse -> HFalse
    | _ -> Phase ({h_formula_phase_rd = f1;
                   h_formula_phase_rw = f2;
                   h_formula_phase_pos = pos})

and is_simple_formula (f:formula) =
  let h, _, _, _, _, _ = split_components f in
  match h with
  | HTrue | HFalse
  | HEmp
  | DataNode _ -> true
  | ViewNode _ -> true
  | _ -> false

and is_emp_formula (f:formula) =
  let h, _, _, _, _, _ = split_components f in
  match h with
  | HTrue | HEmp -> true
  (* | DataNode _ -> true *)
  (* | ViewNode _ -> true *)
  | _ -> false

(*TO CHECK: formula_*_and *)
(* WN : free var should not need to depend on flags *)
and fv_simple_formula (f:formula) =
  let h, _, _, _, _, _ = split_components f in
  match h with
  | HTrue -> []                       (*TRUNG TODO: should be [perm_of_htrue]*)
  | HFalse | HEmp -> []
  | DataNode h ->
    let perm = h.h_formula_data_perm in
    let perm_vars = fv_cperm perm in
    let ann_vars = (* if (!Globals.allow_imm) || (!Globals.allow_field_ann) then ( *) CP.fv_ann (h.h_formula_data_imm)(* ) else []  *) in
    let ann_vars = if true (* (!Globals.allow_field_ann) *) then ann_vars @ (CP.fv_ann_lst h.h_formula_data_param_imm) else ann_vars  in
    perm_vars@ann_vars@(h.h_formula_data_node::h.h_formula_data_arguments)
  | ViewNode h ->
    let perm = h.h_formula_view_perm in
    let perm_vars = fv_cperm perm in
    let ann_vars =  (* if ((!Globals.allow_imm) || (!Globals.allow_field_ann)) then *) (CP.fv_ann (h.h_formula_view_imm))@(CP.fv_annot_arg h.h_formula_view_annot_arg)   (* else [] *) in
    perm_vars@ann_vars@(h.h_formula_view_node::h.h_formula_view_arguments)
  | _ -> []

(*LDK: don't count perm var as free vars in a coercion*)
and fv_simple_formula_coerc (f:formula) =
  let h, _, _, _, _, _ = split_components f in
  match h with
  | HTrue | HFalse | HEmp -> []
  | DataNode h ->  h.h_formula_data_node::h.h_formula_data_arguments
  | ViewNode h ->  h.h_formula_view_node::h.h_formula_view_arguments
  | _ -> []

and mkStar (f1 : formula) (f2 : formula) flow_tr (pos : loc) =
  let h1, p1, vp1, fl1, t1, a1 = split_components f1 in
  let h2, p2, vp2, fl2, t2, a2 = split_components f2 in
  let h = mkStarH h1 h2 pos in
  let p = x_add MCP.merge_mems p1 p2 true in
  let vp = CVP.merge_vperm_sets [vp1; vp2] in
  let vp = CVP.norm_vperm_sets vp in
  let t = mkAndType t1 t2 in
  let fl = mkAndFlow fl1 fl2 flow_tr in
  let a = a1@a2 in (* assuming merging a1 and a2 *)
  mkBase h p vp t fl a pos (*TO CHECK: how about a1,a2: DONE*)
(* TODO *)


and combine_and_pure (f1:formula) (p:MCP.mix_formula) (f2:MCP.mix_formula): MCP.mix_formula*bool =
  if (isAnyConstFalse f1) then (MCP.mkMFalse no_pos, false)
  else if (isAnyConstTrue f1) then (f2, true)
  else
    let r = Gen.Profiling.no_1 "6_combine_mm" (x_add MCP.merge_mems p f2) true in
    if (MCP.isConstMFalse r) then (r, false)
    else if (MCP.isConstMTrue r) then (r, false)
    else (r, true)

(*and combine_and_pure (f1:formula)(p:MCP.mix_formula)(f2:MCP.mix_formula):MCP.mix_formula*bool =
  let pr = pr_pair !print_mix_formula  (string_of_bool) in
  Debug.no_3 "combine_and_pure" (!print_formula) (!print_mix_formula) (!print_mix_formula) pr
  combine_and_pure_x f1 p f2 *)

and sintactic_search (f:formula)(p:Cpure.formula):bool = match f with
  | Or b-> false
  | Base _
  | Exists _->
    let _, pl, _, _, _, _ = split_components f in
    (MCP.memo_is_member_pure p pl)

and mkStar_combine (f1 : formula) (f2 : formula) flow_tr (pos : loc) =
  Debug.no_2 "mkstar_combine"
    (!print_formula)
    (!print_formula)
    (!print_formula)
    (fun f1 f2 -> mkStar_combine_x f1 f2 flow_tr pos) f1 f2

and mkStar_combine_heap (f1 : formula) (f2 : h_formula) flow_tr (pos : loc) =
  mkStar_combine f1 (formula_of_heap f2 pos) flow_tr pos

and mkStar_combine_x (f1 : formula) (f2 : formula) flow_tr (pos : loc) =
  let h1, p1, vp1, fl1, t1, a1 = split_components f1 in
  let h2, p2, vp2, fl2, t2, a2 = split_components f2 in

  (* i assume that at least one of the two formulae has only 1 phase *)
  let h =
    if not(contains_phase h1) then
      mkStarH h1 h2 pos
    else
    if not(contains_phase h2) then
      mkStarH h2 h1 pos
    else
      report_error no_pos "[cformula.ml, mkstar_combine]: at least one of the formulae combined should not contain phases"
  in
  (* let h = mkStarH h1 h2 pos in *)
  let p, _ = combine_and_pure f1 p1 p2 in
  let vp = CVP.merge_vperm_sets [vp1; vp2] in
  let vp_2 = CVP.combine_vperm_sets [vp1; vp2] in
  let t = mkAndType t1 t2 in
  let fl = mkAndFlow fl1 fl2 flow_tr in
  let a = a1@a2 in (*combine a1 and a2: assuming merging a1 and a2*)
  mkBase h p vp t fl a pos (*TO CHECK: how about a1,a2: DONE*)

and contains_phase (f : h_formula) : bool =  match f with
  | DataNode (h1) -> false
  | ViewNode (h1) -> false
  | Conj({h_formula_conj_h1 = h1;
          h_formula_conj_h2 = h2;
          h_formula_conj_pos = pos})
  | ConjStar({h_formula_conjstar_h1 = h1;
              h_formula_conjstar_h2 = h2;
              h_formula_conjstar_pos = pos})
  | ConjConj({h_formula_conjconj_h1 = h1;
              h_formula_conjconj_h2 = h2;
              h_formula_conjconj_pos = pos})
  | Star({h_formula_star_h1 = h1;
          h_formula_star_h2 = h2;
          h_formula_star_pos = pos}) -> (contains_phase h1) || (contains_phase h2)
  | Phase({h_formula_phase_rd = h1;
           h_formula_phase_rw = h2;
           h_formula_phase_pos = pos}) -> true
  | _ -> false


and mkStarMinus_combine (f1 : formula) (f2 : formula) flow_tr al (pos : loc) =
  let h1, p1, vp1, fl1, t1, a1 = split_components f1 in
  let h2, p2, vp2, fl2, t2, a2 = split_components f2 in
  let h = mkStarMinusH h1 h2 al pos 9 in
  let p, _ = combine_and_pure f1 p1 p2 in
  let vp = CVP.merge_vperm_sets [vp1; vp2] in
  let t = mkAndType t1 t2 in
  let fl =  mkAndFlow fl1 fl2 flow_tr in
  let a = a1@a2 in (*assume merging a1 and a2*)
  mkBase h p vp t fl a pos (*TO CHECK: how about a1,a2: DONE*)

and mkConj_combine (f1 : formula) (f2 : formula) flow_tr (pos : loc) =
  let h1, p1, vp1, fl1, t1, a1 = split_components f1 in
  let h2, p2, vp2, fl2, t2, a2 = split_components f2 in
  let h = mkConjH h1 h2 pos in
  let p,_ = combine_and_pure f1 p1 p2 in
  let vp = CVP.merge_vperm_sets [vp1; vp2] in
  let t = mkAndType t1 t2 in
  let fl =  mkAndFlow fl1 fl2 flow_tr in
  let a = a1@a2 in (*assume merging a1 and a2*)
  mkBase h p vp t fl a pos (*TO CHECK: how about a1,a2: DONE*)

and mkConjStar_combine (f1 : formula) (f2 : formula) flow_tr (pos : loc) =
  let h1, p1, vp1, fl1, t1, a1 = split_components f1 in
  let h2, p2, vp2, fl2, t2, a2 = split_components f2 in
  let h = mkConjStarH h1 h2 pos in
  let p,_ = combine_and_pure f1 p1 p2 in
  let vp = CVP.merge_vperm_sets [vp1; vp2] in
  let t = mkAndType t1 t2 in
  let fl =  mkAndFlow fl1 fl2 flow_tr in
  let a = a1@a2 in (*assume merging a1 and a2*)
  mkBase h p vp t fl a pos (*TO CHECK: how about a1,a2: DONE*)

and mkConjConj_combine (f1 : formula) (f2 : formula) flow_tr (pos : loc) =
  let h1, p1, vp1, fl1, t1, a1 = split_components f1 in
  let h2, p2, vp2, fl2, t2, a2 = split_components f2 in
  let h = mkConjConjH h1 h2 pos in
  let p,_ = combine_and_pure f1 p1 p2 in
  let vp = CVP.merge_vperm_sets [vp1; vp2] in
  let t = mkAndType t1 t2 in
  let fl =  mkAndFlow fl1 fl2 flow_tr in
  let a = a1@a2 in (*assume merging a1 and a2*)
  mkBase h p vp t fl a pos (*TO CHECK: how about a1,a2: DONE*)

and mkPhase_combine (f1 : formula) (f2 : formula) flow_tr (pos : loc) =
  let h1, p1, vp1, fl1, t1, a1 = split_components f1 in
  let h2, p2, vp2, fl2, t2, a2 = split_components f2 in
  let h = mkPhaseH h1 h2 pos in
  let p,_ = combine_and_pure f1 p1 p2 in
  let vp = CVP.merge_vperm_sets [vp1; vp2] in
  let t = mkAndType t1 t2 in
  let fl =  mkAndFlow fl1 fl2 flow_tr in
  let a = a1@a2 in (*assume merging a1 and a2*)
  mkBase h p vp t fl a pos (*TO CHECK: how about a1,a2: DONE*)

(* and mkAnd_pure_x (f1 : formula) (p2 : MCP.mix_formula) (pos : loc):formula = *)
(*   if (isAnyConstFalse f1) then f1                                            *)
(*   else                                                                       *)
(* 	let h1, p1, fl1, t1, a1 = split_components f1 in		                        *)
(*     if (MCP.isConstMTrue p1) then mkBase h1 p2 t1 fl1 a1 pos                 *)
(* 	  else                                                                      *)
(*       mkBase h1 (x_add MCP.merge_mems p1 p2 true) t1 fl1 a1 pos                    *)

and mkAnd_base_pure (fb: formula_base) (p2: MCP.mix_formula) (pos: loc): formula_base =
  if (MCP.isConstMTrue p2) then fb
  else
    { fb with formula_base_pure = x_add MCP.merge_mems fb.formula_base_pure  p2 true; }

and mkAnd_pure_x (f1: formula) (p2: MCP.mix_formula) (pos: loc): formula =
  if (isAnyConstFalse f1) then f1
  else if (MCP.isConstMTrue p2) then f1
  else
    match f1 with
    | Base ({ formula_base_pure = p; } as b) ->
      Base { b with formula_base_pure = x_add MCP.merge_mems p p2 true; }
    | Exists ({ formula_exists_pure = p; } as e) ->
      Exists { e with formula_exists_pure = x_add MCP.merge_mems p p2 true; }
    | Or ({ formula_or_f1 = f1; formula_or_f2 = f2; } as o) ->
      Or { o with
           formula_or_f1 = mkAnd_pure f1 p2 pos;
           formula_or_f2 = mkAnd_pure f2 p2 pos }

and mkAnd_pure (f1 : formula) (p2 : MCP.mix_formula) (pos : loc):formula =
  Debug.no_2 "mkAnd_pure" !print_formula !print_mix_f !print_formula
    (fun _ _ -> mkAnd_pure_x f1 p2 pos) f1 p2

and mkExists_w_lbl (svs : CP.spec_var list) (h : h_formula) (p : MCP.mix_formula) (vp: CVP.vperm_sets)
    (t : t_formula) (fl:flow_formula) a (pos : loc) lbl=
  let tmp_b = {
    formula_base_heap = h;
    formula_base_vperm = vp;
    formula_base_pure = p;
    formula_base_type = t;
    formula_base_flow = fl;
    formula_base_and = a;
    formula_base_label = lbl;
    formula_base_pos = pos } in
  let fvars = fv (Base tmp_b) in
  let qvars = Gen.BList.intersect_eq (CP.eq_spec_var) svs fvars in (* used only these for the quantified formula *)
  if Gen.is_empty qvars then Base tmp_b
  else
    Exists ({
        formula_exists_qvars = qvars;
        formula_exists_heap =  h;
        formula_exists_vperm = vp;
        formula_exists_pure = p;
        formula_exists_type = t;
        formula_exists_and = a;
        formula_exists_flow = fl;
        formula_exists_label = lbl;
        formula_exists_pos = pos })

and is_empty_heap (h : h_formula) = match h with
  | HEmp -> true
  | HFalse -> true
  | _ -> false

and is_unknown_heap (h : h_formula) = match h with
  | HTrue -> true
  | _ -> false

and is_empty_f f0=
  let rec helper f=
    match f with
    | Base fb ->
      (is_empty_heap fb.formula_base_heap) &&
      (CP.isConstTrue (MCP.pure_of_mix fb.formula_base_pure))
    | Exists _ -> let _, base_f = split_quantifiers f in
      is_empty_f base_f
    | Or orf -> (helper orf.formula_or_f1) && (helper orf.formula_or_f2)
  in
  helper f0

and mkExists (svs : CP.spec_var list) (h : h_formula) (p : MCP.mix_formula) (vp: CVP.vperm_sets)
    (t : t_formula) (fl:flow_formula) a (pos : loc) =
  mkExists_w_lbl svs h p vp t fl a pos None

and ex_formula_of_heap svl h pos =
  mkExists svl h (MCP.mkMTrue pos) CVP.empty_vperm_sets TypeTrue (mkTrueFlow ()) [] pos

and is_view (h : h_formula) = match h with
  | ViewNode _ -> true
  | _ -> false

and is_view_primitive (h : h_formula) = match h with
  | ViewNode v -> view_prim_lst # mem (v.h_formula_view_name)
  | _ -> false

and is_view_user (h : h_formula) = match h with
  | ViewNode v -> not(view_prim_lst # mem (v.h_formula_view_name))
  | _ -> false

and is_view_user_dupl_ptr_unfold_x (h : h_formula) = match h with
  | ViewNode v -> let vn = v.h_formula_view_name in
    let b1 = view_prim_lst # mem vn in
    let b2 = view_ptr_arith_lst # mem vn in
    let () = y_dinfo_hp (add_str "b1" string_of_bool) b1 in
    let () = y_dinfo_hp (add_str "b2" string_of_bool) b2 in
    not( b1 || b2)
  | _ -> false

and is_view_user_dupl_ptr_unfold (h : h_formula) =
  let pr = !print_h_formula in
  Debug.no_1 "is_view_user_dupl_ptr_unfold" pr string_of_bool is_view_user_dupl_ptr_unfold_x h

and is_data (h : h_formula) = match h with
  | DataNode _ -> true
  | _ -> false

and is_thread (h : h_formula) = match h with
  | ThreadNode _ -> true
  | _ -> false

and is_hole (h : h_formula) = match h with
  | Hole _ -> true
  | _ -> false

and is_hrel (h: h_formula) =
  match h with
  | HRel _ -> true
  | _ -> false

and is_hformula_contain_htrue (h: h_formula) : bool =
  match h with
  | Star { h_formula_star_h1 = h1;
           h_formula_star_h2 = h2; }
  | StarMinus { h_formula_starminus_h1 = h1;
                h_formula_starminus_h2 = h2; }
    -> (is_hformula_contain_htrue h1) || (is_hformula_contain_htrue h2)
  | Conj { h_formula_conj_h1 = h1;
           h_formula_conj_h2 = h2; }
  | ConjStar { h_formula_conjstar_h1 = h1;
               h_formula_conjstar_h2 = h2; }
  | ConjConj { h_formula_conjconj_h1 = h1;
               h_formula_conjconj_h2 = h2; } -> (is_hformula_contain_htrue h1) || (is_hformula_contain_htrue h2)
  | Phase { h_formula_phase_rd = h1;
            h_formula_phase_rw = h2; } -> (is_hformula_contain_htrue h1) || (is_hformula_contain_htrue h2)
  | HTrue -> true
  | HRel _
  | DataNode _
  | ViewNode _
  | ThreadNode _
  | Hole _ | FrmHole _
  | HFalse
  | HEmp | HVar _ -> false

and is_formula_contain_htrue (h: formula) : bool =
  match h with
  | Base { formula_base_heap = h1; } -> is_hformula_contain_htrue h1
  | Exists { formula_exists_heap = h1; } -> is_hformula_contain_htrue h1
  | Or { formula_or_f1 = f1;
         formula_or_f2 = f2 } -> (is_formula_contain_htrue f1) || (is_formula_contain_htrue f2)

and get_node_derv (h : h_formula) = match h with
  | ThreadNode ({h_formula_thread_derv = c})
  | ViewNode ({h_formula_view_derv = c})
  | DataNode ({h_formula_data_derv = c}) -> c
  | _ -> failwith ("get_node_derv: invalid argument")

and get_node_split (h : h_formula) = match h with
  | ThreadNode ({h_formula_thread_split = c})
  | ViewNode ({h_formula_view_split = c})
  | DataNode ({h_formula_data_split = c}) -> c
  | _ -> failwith ("get_node_split: invalid argument")

and get_node_pos (h : h_formula) = match h with
  | ThreadNode ({h_formula_thread_pos = c})
  | ViewNode ({h_formula_view_pos = c})
  | DataNode ({h_formula_data_pos = c}) -> c
  | Hole i -> no_pos
  | HRel (_, _, pos) -> pos
  | _ -> failwith ("get_node_pos: invalid argument")

and get_node_name_x (h : h_formula) = match h with
  | ThreadNode ({h_formula_thread_name = c})
  | ViewNode ({h_formula_view_name = c})
  | DataNode ({h_formula_data_name = c}) -> c
  | HRel (hp, _, _) -> CP.name_of_spec_var hp
  | Hole i -> "Hole_"^(string_of_int i)
  | HVar _ -> ""
  | _ ->
    let pr = !print_h_formula in
    failwith ("get_node_name: invalid argument: " ^ (pr h))

and get_node_name i (h : h_formula) =
  Debug.no_1_num i "get_node_name" !print_h_formula idf get_node_name_x h

and get_node_perm (h : h_formula) = match h with
  | ThreadNode ({h_formula_thread_perm = c})
  | ViewNode ({h_formula_view_perm = c})
  | DataNode ({h_formula_data_perm = c}) -> c
  | _ -> failwith ("get_node_perm: invalid argument. Expected ViewNode/DataNode/ThreadNode")

and get_node_original (h : h_formula) = match h with
  | ThreadNode ({h_formula_thread_original = c})
  | ViewNode ({h_formula_view_original = c})
  | DataNode ({h_formula_data_original = c}) -> c
  | _ -> false (* default? *)
(* failwith ("get_node_original: invalid argument. Expected ViewNode/DataNode/ThreadNode") *)

and get_node_origins (h : h_formula) = match h with
  | ThreadNode ({h_formula_thread_origins = c})
  | ViewNode ({h_formula_view_origins = c})
  | DataNode ({h_formula_data_origins = c}) -> c
  | _ -> [] (* default *)
(* | _ -> failwith ("get_node_origins: invalid argument. Expected ViewNode/DataNode/ThreadNode") *)

and set_node_perm (h : h_formula) p= match h with
  | ThreadNode b -> ThreadNode {b with h_formula_thread_perm = p}
  | ViewNode b -> ViewNode {b with h_formula_view_perm = p}
  | DataNode b -> DataNode {b with h_formula_data_perm = p}
  | _ -> failwith ("set_node_perm: invalid argument")

(* (* To distinguish with later get_node_args *)                                           *)
(* and get_node_args_inner (h : h_formula) = match h with                                  *)
(*   | ViewNode ({h_formula_view_arguments = c})                                           *)
(*   | DataNode ({h_formula_data_arguments = c}) -> c                                      *)
(*   | ThreadNode _ -> failwith ("get_node_args: invalid argument. Unexpected ThreadNode") *)
(*   | _ -> failwith ("get_node_args: invalid argument. Expected ViewNode/DataNode")       *)

and get_node_ho_args (h : h_formula) = match h with
  | ViewNode ({h_formula_view_ho_arguments = c}) -> c
  | DataNode _ -> []
  | HRel _ -> []
  | ThreadNode _ -> failwith ("get_node_args: invalid argument. Unexpected ThreadNode")
  | _ -> failwith ("get_node_args: invalid argument. Expected ViewNode/DataNode, got:"^(!print_h_formula h))

and get_node_annot_args_x (h : h_formula) = match h with
  | ViewNode ({h_formula_view_annot_arg = c}) -> List.map fst c
  | DataNode _ -> []
  | HRel _ -> []
  | _ -> failwith ("get_node_args: invalid argument"^(!print_h_formula h))

and get_node_annot_args (h : h_formula) =
  Debug.no_1 "get_node_annot_args" !print_h_formula CP.string_of_annot_arg_list get_node_annot_args_x h

and get_node_annot_args_w_pos (h : h_formula) = match h with
  | ViewNode ({h_formula_view_annot_arg = c}) -> c
  | DataNode _ -> []
  | HRel _ -> []
  | _ -> failwith ("get_node_args: invalid argument"^(!print_h_formula h))

and get_node_args_orig (h : h_formula) = match h with
  | ViewNode ({h_formula_view_args_orig = c}) -> List.map fst c
  | DataNode _ -> []
  | _ -> failwith ("get_node_args: invalid argument"^(!print_h_formula h))

and get_node_args_orig_w_pos (h : h_formula) = match h with
  | ViewNode ({h_formula_view_args_orig = c}) -> c
  | DataNode _ -> []
  | _ -> failwith ("get_node_args: invalid argument"^(!print_h_formula h))

and get_node_label (h : h_formula) = match h with
  | ThreadNode ({h_formula_thread_label = c})
  | ViewNode ({h_formula_view_label = c})
  | DataNode ({h_formula_data_label = c}) -> c
  | _ -> failwith ("get_node_args: invalid argument"^(!print_h_formula h))

(* TODO:WN:HVar *)
and get_node_var_x (h : h_formula) = match h with
  | ThreadNode ({h_formula_thread_node = c})
  | ViewNode ({h_formula_view_node = c})
  | DataNode ({h_formula_data_node = c}) -> c
  | HVar (v,hvar_vs) -> v
  | HRel (hrel, el, _) ->
    (match el with
    | (CP.Var (sv, _))::_ -> sv
    | _ -> failwith ("Cannot find suitable root node of the HRel " ^ (CP.name_of_spec_var hrel))
    )
  | _ -> CP.null_var
           (* failwith ("get_node_var: invalid argument"^(!print_h_formula h)) *)

and get_node_var (h : h_formula) =
  Debug.no_1 "get_node_var" !print_h_formula !print_sv
    get_node_var_x h

and set_node_var newc (h : h_formula) = match h with
  | ThreadNode w -> ThreadNode {w with h_formula_thread_node = newc;}
  | ViewNode w -> ViewNode {w with h_formula_view_node = newc;}
  | DataNode w -> DataNode {w with h_formula_data_node = newc;}
  | _ -> failwith ("set_node_var: invalid argument "^(!print_h_formula h))

and get_node_imm (h : h_formula) = match h with
  | ViewNode ({h_formula_view_imm = imm})
  | DataNode ({h_formula_data_imm = imm}) -> imm
  | _ -> failwith ("get_node_imm: invalid argument "^(!print_h_formula h))

and get_node_param_imm (h : h_formula) = match h with
  | DataNode ({h_formula_data_param_imm = param_imm}) -> param_imm
  | ViewNode ({h_formula_view_annot_arg = field_imm}) -> (CP.annot_arg_to_imm_ann_list (List.map fst field_imm))
  | _ -> failwith ("get_node_param_imm: invalid argument "^(!print_h_formula h))

and get_view_origins (h : h_formula) = match h with
  | ViewNode ({h_formula_view_origins = origs}) -> origs
  | _ -> [] (* failwith ("get_view_origins: not a view") *)

and get_view_original (h : h_formula) = match h with
  | ViewNode ({h_formula_view_original = original}) -> original
  | _ -> true (* failwith ("get_view_original: not a view") *)

and get_view_unfold_num (h : h_formula) = match h with
  | ViewNode ({h_formula_view_unfold_num = i}) -> i
  | _ -> 0

and get_view_modes_x (h : h_formula) = match h with
  | ViewNode ({h_formula_view_modes = modes}) -> modes
  | _ -> failwith ("get_view_modes: not a view "^(!print_h_formula h))

and get_view_modes (h : h_formula) =
  let pr l = string_of_int (List.length l) in
  Debug.no_1 "get_view_modes" !print_h_formula pr (fun _ -> get_view_modes_x h) h

and get_view_imm (h : h_formula) = match h with
  | ViewNode ({h_formula_view_imm = imm}) -> imm
  | _ -> failwith ("get_view_imm: not a view " ^(!print_h_formula h))

and get_view_derv (h : h_formula) = match h with
  | ViewNode ({h_formula_view_derv = dr}) -> dr
  | _ -> failwith ("get_view_derv: not a view "^(!print_h_formula h))

and get_view_split (h : h_formula) = match h with
  | ViewNode ({h_formula_view_split = dr}) -> dr
  | _ -> failwith ("get_view_split: not a view "^(!print_h_formula h))

and get_data_derv (h : h_formula) = match h with
  | DataNode ({h_formula_data_derv = dr}) -> dr
  | _ -> failwith ("get_data_derv not a data "^(!print_h_formula h))

and get_data_split (h : h_formula) = match h with
  | DataNode ({h_formula_data_split = dr}) -> dr
  | _ -> failwith ("get_data_split not a data "^(!print_h_formula h))

and h_add_origins (h : h_formula) origs =
  let pr = !print_h_formula in
  let pr2 = !print_ident_list in
  Debug.no_2 "h_add_origins" pr pr2 pr h_add_origins_a h origs

and h_add_origins_a (h : h_formula) origs =
  let rec helper h = match h with
    | Star ({h_formula_star_h1 = h1;
             h_formula_star_h2 = h2;
             h_formula_star_pos = pos}) ->
      Star ({h_formula_star_h1 = helper h1;
             h_formula_star_h2 = helper h2;
             h_formula_star_pos = pos})
    | ViewNode vn -> ViewNode {vn with h_formula_view_origins = origs @ vn.h_formula_view_origins}
    | DataNode dn -> DataNode {dn with h_formula_data_origins = origs @ dn.h_formula_data_origins}
    | _ -> h
  in helper h

and h_add_perm (h : h_formula) (permvar:cperm_var) : h_formula =
  let pr = !print_h_formula in
  let pr2 = !print_spec_var in
  Debug.no_2 "h_add_perm" pr pr2 pr h_add_perm_a h permvar

and h_add_perm_a (h : h_formula) (permvar:cperm_var) : h_formula=
  let rec helper h = match h with
    | Star ({h_formula_star_h1 = h1;
             h_formula_star_h2 = h2;
             h_formula_star_pos = pos}) ->
      Star ({h_formula_star_h1 = helper h1;
             h_formula_star_h2 = helper h2;
             h_formula_star_pos = pos})
    | ViewNode vn -> ViewNode {vn with h_formula_view_perm = Some (Cpure.Var (permvar,no_pos))}
    | DataNode vn -> DataNode {vn with h_formula_data_perm = Some (Cpure.Var (permvar,no_pos))}
    | _ -> h
  in helper h

and h_add_original (h : h_formula) original =
  let rec helper h = match h with
    | Star ({h_formula_star_h1 = h1;
             h_formula_star_h2 = h2;
             h_formula_star_pos = pos}) ->
      Star ({h_formula_star_h1 = helper h1;
             h_formula_star_h2 = helper h2;
             h_formula_star_pos = pos})
    | ViewNode vn -> ViewNode {vn with h_formula_view_original = original}
    | DataNode dn -> DataNode {dn with h_formula_data_original = original}
    | _ -> h
  in helper h

and h_set_lhs_case (h : h_formula) flag =
  let rec helper h = match h with
    | Star ({h_formula_star_h1 = h1;
             h_formula_star_h2 = h2;
             h_formula_star_pos = pos}) ->
      Star ({h_formula_star_h1 = helper h1;
             h_formula_star_h2 = helper h2;
             h_formula_star_pos = pos})
    | ViewNode vn -> ViewNode {vn with h_formula_view_lhs_case = flag}
    | _ -> h
  in helper h

and h_set_lhs_case_of_a_view (h : h_formula) (v_name:ident) flag: h_formula =
  let rec helper h = match h with
    | Star ({h_formula_star_h1 = h1;
             h_formula_star_h2 = h2;
             h_formula_star_pos = pos}) ->
      Star ({h_formula_star_h1 = helper h1;
             h_formula_star_h2 = helper h2;
             h_formula_star_pos = pos})
    | ViewNode vn ->
      let name = get_node_name 5 h in
      if (name=v_name) then
        ViewNode {vn with h_formula_view_lhs_case = flag}
      else h
    | _ -> h
  in helper h

and h_add_unfold_num (h : h_formula) i =
  let rec helper h = match h with
    | Star ({h_formula_star_h1 = h1;
             h_formula_star_h2 = h2;
             h_formula_star_pos = pos}) ->
      Star ({h_formula_star_h1 = helper h1;
             h_formula_star_h2 = helper h2;
             h_formula_star_pos = pos})
    | ViewNode vn -> ViewNode {vn with h_formula_view_unfold_num = i}
    | _ -> h
  in helper h

(* WN : below is marking node as @D? *)
and h_add_origs_to_node (v : string) (h : h_formula) origs =
  let rec helper h = match h with
    | Star ({h_formula_star_h1 = h1;
             h_formula_star_h2 = h2;
             h_formula_star_pos = pos}) ->
      Star ({h_formula_star_h1 = helper h1;
             h_formula_star_h2 = helper h2;
             h_formula_star_pos = pos})
    | ViewNode vn -> if not((CP.name_of_spec_var vn.h_formula_view_node) = v) then
        ViewNode {vn with
                  h_formula_view_origins = origs @ vn.h_formula_view_origins;
                  h_formula_view_original = false}
      else
        ViewNode {vn with
                  h_formula_view_origins = origs @ vn.h_formula_view_origins;
                  (* set the view to be derived *)
                  h_formula_view_original = false}
    | DataNode dn -> if not((CP.name_of_spec_var dn.h_formula_data_node) = v) then
        DataNode {dn with
                  h_formula_data_origins = origs @ dn.h_formula_data_origins;
                  h_formula_data_original = false}
      else
        DataNode {dn with
                  h_formula_data_origins = origs @ dn.h_formula_data_origins;
                  (* set the view to be derived *)
                  h_formula_data_original = false}
    | _ -> h
  in helper h

and add_origs_to_node (v:string) (f : formula) origs =
  let rec helper f = match f with
    | Or ({formula_or_f1 = f1;
           formula_or_f2 = f2;
           formula_or_pos = pos}) ->
      Or ({formula_or_f1 = helper f1;
           formula_or_f2 = helper f2;
           formula_or_pos = pos})
    | Base b -> Base ({b with formula_base_heap = h_add_origs_to_node v b.formula_base_heap origs})
    | Exists e -> Exists ({e with formula_exists_heap = h_add_origs_to_node v e.formula_exists_heap origs})
  in helper f

(* the first matched node has orgins and its view_original=false *)
(* , other nodes have their view_original=original *)
(*ln: lhs name: name of heap node in the head of an coercion*)
(* origs: origs to add to the first node *)
(* orignal: "orignal" for other nodes *)
and h_add_origs_to_first_node (v : string) (ln:string) (h : h_formula) origs original =
  (*return a pair (is_first,h_formula), where is_first indicates
    whether the first matched node is in the h_formula*)
  let rec helper h found_first: (bool * h_formula)= match h with
    | Star ({h_formula_star_h1 = h1;
             h_formula_star_h2 = h2;
             h_formula_star_pos = pos}) ->
      let  (is_first1,star_h1) = helper h1 found_first in
      let is_first2,star_h2 =
        if ((not is_first1) && (not (found_first))) then
          let is_first2, star_h2 =  helper h2 false in
          (is_first2,star_h2)
        else
          (*first node found somewhere*)
          let _,star_h2 =  helper h2 true in
          (true,star_h2)
      in
      is_first2, Star ({
          h_formula_star_h1 = star_h1;
          h_formula_star_h2 = star_h2;
          h_formula_star_pos = pos})
    | ViewNode vn ->
      if (((CP.name_of_spec_var vn.h_formula_view_node) = v) && (not found_first) && vn.h_formula_view_name=ln) then
        (*if it is the first matched node (same pointer name,
          same view name and first_node not found):
          - add origs to its view_origins
          - set view_original= false*)
        (true,
         ViewNode {vn with
                   h_formula_view_origins = origs @ vn.h_formula_view_origins;
                   (* set the view to be derived *)
                   h_formula_view_original = false})

      else
        (*otherwise, its origins unchange but its view_original=true*)
        (false, ViewNode {vn with h_formula_view_original = original})
    (* (false, ViewNode {vn with *)
    (*     h_formula_view_origins = origs @ vn.h_formula_view_origins; *)
    (*     h_formula_view_original = true}) *)
    | DataNode dn ->
      if (((CP.name_of_spec_var dn.h_formula_data_node) = v) && (not found_first) && dn.h_formula_data_name=ln) then
        (*if it is the first matched node (same pointer name,
          same view name and first_node not found):
          - add origs to its view_origins
          - set view_original= false*)
        (true,
         DataNode {dn with
                   h_formula_data_origins = origs @ dn.h_formula_data_origins;
                   (* set the view to be derived *)
                   h_formula_data_original = false})

      else
        (*otherwise, its origins unchange but its view_original=true*)
        (false, DataNode {dn with h_formula_data_original = original})
    (* (false, DataNode {dn with  *)
    (*     h_formula_data_origins = origs @ dn.h_formula_data_origins; *)
    (*     h_formula_data_original = true}) *)
    | _ -> (false,h)
  in
  let _, h1 = helper h false in
  h1

(*
  ln: lhs name: name of heap node in the head of an coercion
  origs: origs to add to the first node
  orignal: "orignal" for other nodes
*)
and add_origs_to_first_node_x (v:string) (ln:string)(f : formula) origs original =
  let rec helper f = match f with
    | Or ({formula_or_f1 = f1;
           formula_or_f2 = f2;
           formula_or_pos = pos}) ->
      Or ({formula_or_f1 = helper f1;
           formula_or_f2 = helper f2;
           formula_or_pos = pos})
    | Base b -> Base ({b with formula_base_heap = h_add_origs_to_first_node v ln b.formula_base_heap origs original})
    | Exists e -> Exists ({e with formula_exists_heap = h_add_origs_to_first_node v ln e.formula_exists_heap origs original})
  in helper f

and add_origs_to_first_node (v:string) (ln:string)(f : formula) origs original =
  Debug.no_3 "add_origs_to_first_node"
    pr_id pr_id !print_formula !print_formula
    (fun _ _ _ -> add_origs_to_first_node_x v ln f origs original) v ln f

and struc_add_origs_to_first_node (v:string) (ln:string)(f : struc_formula) origs original =
  let rec helper f = match f with
    | EList b-> EList (map_l_snd  helper b)
    | ECase b -> ECase {b with formula_case_branches = map_l_snd helper b.formula_case_branches;}
    | EBase b -> EBase {b with formula_struc_base =  add_origs_to_first_node v ln b.formula_struc_base origs original;
                               formula_struc_continuation = map_opt helper b.formula_struc_continuation}
    | EAssume b ->  EAssume {b with
                             formula_assume_simpl = add_origs_to_first_node v ln b.formula_assume_simpl origs original;
                             formula_assume_struc = helper b.formula_assume_struc;}
    | EInfer b -> EInfer {b with formula_inf_continuation = helper b.formula_inf_continuation}
  in helper f

and add_origins (f : formula) origs =
  let pr = !print_formula in
  let pr2 = !print_ident_list in
  Debug.no_2 "add_origins" pr pr2 pr add_origins_a f origs

and add_origins_a (f : formula) origs =
  let rec helper f = match f with
    | Or ({formula_or_f1 = f1;
           formula_or_f2 = f2;
           formula_or_pos = pos}) ->
      Or ({formula_or_f1 = helper f1;
           formula_or_f2 = helper f2;
           formula_or_pos = pos})
    | Base b -> Base ({b with formula_base_heap = h_add_origins b.formula_base_heap origs})
    | Exists e -> Exists ({e with formula_exists_heap = h_add_origins e.formula_exists_heap origs})
  in helper f

and add_perm (f : formula) (permvar:cperm_var):formula =
  let rec helper f = match f with
    | Or ({formula_or_f1 = f1;
           formula_or_f2 = f2;
           formula_or_pos = pos}) ->
      Or ({formula_or_f1 = helper f1;
           formula_or_f2 = helper f2;
           formula_or_pos = pos})
    | Base b -> Base ({b with formula_base_heap = h_add_perm b.formula_base_heap permvar})
    | Exists e -> Exists ({e with formula_exists_heap = h_add_perm e.formula_exists_heap permvar})
  in helper f

and h_reset_origins (h : h_formula) =
  let rec helper h = match h with
    | Star ({h_formula_star_h1 = h1;
             h_formula_star_h2 = h2;
             h_formula_star_pos = pos}) ->
      Star ({h_formula_star_h1 = helper h1;
             h_formula_star_h2 = helper h2;
             h_formula_star_pos = pos})
    | ViewNode vn -> ViewNode {vn with h_formula_view_origins = []}
    | _ -> h
  in helper h

and reset_origins (f : formula) =
  let rec helper f = match f with
    | Or ({formula_or_f1 = f1;
           formula_or_f2 = f2;
           formula_or_pos = pos}) ->
      Or ({formula_or_f1 = helper f1;
           formula_or_f2 = helper f2;
           formula_or_pos = pos})
    | Base b -> Base ({b with formula_base_heap = h_reset_origins b.formula_base_heap})
    | Exists e -> Exists ({e with formula_exists_heap = h_reset_origins e.formula_exists_heap})
  in helper f

and reset_struc_origins (f : struc_formula) = match f with
  | EList b-> EList (map_l_snd reset_struc_origins b)
  | ECase b -> ECase {b with formula_case_branches = map_l_snd reset_struc_origins b.formula_case_branches;}
  | EBase b -> EBase {b with formula_struc_base = reset_origins b.formula_struc_base ;
                             formula_struc_continuation = map_opt reset_struc_origins b.formula_struc_continuation}
  | EAssume b ->  EAssume {b with
                           formula_assume_simpl = reset_origins b.formula_assume_simpl;
                           formula_assume_struc = reset_struc_origins b.formula_assume_struc;}
  | EInfer b -> EInfer {b with formula_inf_continuation = reset_struc_origins b.formula_inf_continuation}

and add_original (f : formula) original =
  let rec helper f = match f with
    | Or ({formula_or_f1 = f1;
           formula_or_f2 = f2;
           formula_or_pos = pos}) ->
      Or ({formula_or_f1 = helper f1;
           formula_or_f2 = helper f2;
           formula_or_pos = pos})
    | Base b -> Base ({b with formula_base_heap = h_add_original b.formula_base_heap original})
    | Exists e -> Exists ({e with formula_exists_heap = h_add_original e.formula_exists_heap original})
  in helper f

and add_struc_original original (f : struc_formula) = match f with
  | ECase b -> ECase {b with formula_case_branches = map_l_snd (add_struc_original original) b.formula_case_branches;}
  | EList b -> EList (map_l_snd (add_struc_original original) b)
  | EBase b -> EBase {b with formula_struc_base = add_original b.formula_struc_base original ;
                             formula_struc_continuation = map_opt (add_struc_original original) b.formula_struc_continuation}
  | EAssume b ->  EAssume {b with
                           formula_assume_simpl = add_original b.formula_assume_simpl original;
                           formula_assume_struc = add_struc_original original b.formula_assume_struc;}
  (*| EVariance b -> EVariance {b with formula_var_continuation = ext_f b.formula_var_continuation}*)
  | EInfer b -> EInfer {b with formula_inf_continuation = add_struc_original original b.formula_inf_continuation}

and set_lhs_case_x (f : formula) flag =
  let rec helper f = match f with
    | Or ({formula_or_f1 = f1;
           formula_or_f2 = f2;
           formula_or_pos = pos}) ->
      Or ({formula_or_f1 = helper f1;
           formula_or_f2 = helper f2;
           formula_or_pos = pos})
    | Base b -> Base ({b with formula_base_heap = h_set_lhs_case b.formula_base_heap flag})
    | Exists e -> Exists ({e with formula_exists_heap = h_set_lhs_case e.formula_exists_heap flag})
  in helper f

and set_lhs_case (f : formula) flag =
  let pr = !print_formula in
  Debug.no_2 "set_lhs_case" pr string_of_bool pr set_lhs_case_x f flag

and set_lhs_case_of_a_view (f : formula) (v_name:ident) flag : formula =
  let rec helper f = match f with
    | Or ({formula_or_f1 = f1;
           formula_or_f2 = f2;
           formula_or_pos = pos}) ->
      Or ({formula_or_f1 = helper f1;
           formula_or_f2 = helper f2;
           formula_or_pos = pos})
    | Base b -> Base ({b with formula_base_heap = h_set_lhs_case_of_a_view b.formula_base_heap v_name flag})
    | Exists e -> Exists ({e with formula_exists_heap = h_set_lhs_case_of_a_view e.formula_exists_heap v_name flag})
  in helper f

and struc_formula_set_lhs_case (flag:bool) (f:struc_formula) : struc_formula = match f with
  | EBase b -> EBase {b with formula_struc_base = set_lhs_case b.formula_struc_base flag ;
                             formula_struc_continuation = map_opt (struc_formula_set_lhs_case flag) b.formula_struc_continuation}
  | EList b -> EList (map_l_snd (struc_formula_set_lhs_case flag) b)
  | ECase b -> ECase {b with formula_case_branches = map_l_snd (struc_formula_set_lhs_case flag) b.formula_case_branches;}
  | EAssume b -> EAssume {b with
                          formula_assume_simpl = set_lhs_case b.formula_assume_simpl flag;
                          formula_assume_struc = struc_formula_set_lhs_case flag b.formula_assume_struc;}
  | EInfer b -> EInfer {b with formula_inf_continuation = struc_formula_set_lhs_case flag b.formula_inf_continuation}

and add_unfold_num (f : formula) uf =
  let rec helper f = match f with
    | Or ({formula_or_f1 = f1;
           formula_or_f2 = f2;
           formula_or_pos = pos}) ->
      Or ({formula_or_f1 = helper f1;
           formula_or_f2 = helper f2;
           formula_or_pos = pos})
    | Base b -> Base ({b with formula_base_heap = h_add_unfold_num b.formula_base_heap uf})
    | Exists e -> Exists ({e with formula_exists_heap = h_add_unfold_num e.formula_exists_heap uf})
  in helper f

and add_struc_origins origs (f:struc_formula) = match f with
  | ECase b -> ECase {b with formula_case_branches = map_l_snd (add_struc_origins origs) b.formula_case_branches;}
  | EBase b -> EBase {b with formula_struc_base = add_origins b.formula_struc_base origs ;
                             formula_struc_continuation = map_opt (add_struc_origins origs) b.formula_struc_continuation}
  | EAssume b ->  EAssume {b with
                           formula_assume_simpl = add_origins b.formula_assume_simpl origs;
                           formula_assume_struc = add_struc_origins origs b.formula_assume_struc;}
  | EList b -> EList (map_l_snd (add_struc_origins origs) b)
  | EInfer b -> EInfer {b with formula_inf_continuation = add_struc_origins origs b.formula_inf_continuation}

and no_change (svars : CP.spec_var list) (pos : loc) : CP.formula = match svars with
  | sv :: rest ->
    let f = CP.mkEqVar (CP.to_primed sv) (CP.to_unprimed sv) pos in
    let restf = no_change rest pos in
    CP.mkAnd f restf pos
  | [] -> CP.mkTrue pos

(* and mkEq fr_svl to_svl pos: CP.formula= *)
(*   let ss = List.combine to_svl fr_svl in *)
(*   let fs = List.map (fun (sv1, sv2) -> CP.mkEqVar sv1 sv2 pos) ss in *)
(*   List.fold_left (fun p1 p2 -> CP.mkAnd p1 p2 pos) (CP.mkTrue pos) fs *)

and pos_of_struc_formula (f:struc_formula): loc =match f with
  | ECase b -> b.formula_case_pos
  | EBase b -> b.formula_struc_pos
  | EAssume b-> pos_of_formula b.formula_assume_simpl
  | EInfer b -> b.formula_inf_pos
  | EList b-> match b with | x::_ -> pos_of_struc_formula (snd x) |_-> no_pos

and base_formula_of_struc_formula_x sf=
  match sf with
  | EBase b ->  true, b.formula_struc_base
  | _ -> false, mkTrue (mkTrueFlow()) no_pos

and base_formula_of_struc_formula sf=
  let pr1 = !print_struc_formula in
  let pr2 = !print_formula in
  Debug.no_1 "base_formula_of_struc_formula" pr1 (pr_pair string_of_bool pr2)
    (fun _ -> base_formula_of_struc_formula_x sf) sf

and pos_of_formula (f : formula) : loc = match f with
  | Base ({formula_base_pos = pos}) -> pos
  | Or ({formula_or_f1 = f1;
         formula_or_f2 = f2;
         formula_or_pos = pos}) -> pos_of_formula f1
  | Exists ({formula_exists_pos = pos}) -> pos

and pos_of_h_formula (hf: h_formula) : loc = match hf with
  | Star {h_formula_star_pos = pos}
  | StarMinus {h_formula_starminus_pos = pos}
  | Conj {h_formula_conj_pos = pos}
  | ConjStar {h_formula_conjstar_pos = pos}
  | ConjConj {h_formula_conjconj_pos = pos}
  | Phase {h_formula_phase_pos = pos}
  | DataNode {h_formula_data_pos = pos}
  | ViewNode {h_formula_view_pos = pos}
  | ThreadNode {h_formula_thread_pos = pos}
  | HRel (_,_,pos) -> pos
  | Hole _ | FrmHole _ -> no_pos
  | HTrue | HFalse | HEmp | HVar _ -> no_pos

and list_pos_of_formula (f : formula) : (loc list)= match f with
  | Base ({formula_base_heap = h;
           formula_base_pure = mf;
           formula_base_pos = pos}) -> (list_pos_of_heap_formula h) @ (MCP.list_pos_of_mix_formula mf) @ [pos]
  | Or ({formula_or_f1 = f1;
         formula_or_f2 = f2;
         formula_or_pos = pos}) -> (list_pos_of_formula f1) @ (list_pos_of_formula f2) @ [pos]
  | Exists ({formula_exists_heap = h;
             formula_exists_pure = mf;
             formula_exists_pos = pos}) -> (list_pos_of_heap_formula h) @ (MCP.list_pos_of_mix_formula mf) @ [pos]

and list_pos_of_heap_formula (h: h_formula): (loc list)= match h with
  | Star {h_formula_star_pos = pos} -> [pos]
  | ConjStar {h_formula_conjstar_pos = pos} -> [pos]
  | ConjConj {h_formula_conjconj_pos = pos} -> [pos]
  | _ -> []

and get_lines (ll: loc list): (int list)=
  Gen.Basic.remove_dups (List.map (fun x -> x.start_pos.Lexing.pos_lnum) ll)

and subst_pos_struc_formula (p:loc) (f:struc_formula): struc_formula=
  match f with
  | ECase b ->
    let helper (pre, post)= (CP.subst_pos_formula p pre, subst_pos_struc_formula p post) in
    ECase {formula_case_branches = List.map helper b.formula_case_branches; formula_case_pos = p}
  | EBase b-> EBase { b with formula_struc_base = subst_pos_formula p b.formula_struc_base;
                             formula_struc_continuation = map_opt (subst_pos_struc_formula p) b.formula_struc_continuation;
                             formula_struc_pos = p}
  | EAssume b-> EAssume {b with
                         formula_assume_simpl = subst_pos_formula p b.formula_assume_simpl;
                         formula_assume_struc = subst_pos_struc_formula p b.formula_assume_struc;}
  | EInfer ei -> EInfer {ei with formula_inf_continuation = subst_pos_struc_formula p ei.formula_inf_continuation; formula_inf_pos=p}
  | EList b -> EList (map_l_snd (subst_pos_struc_formula p) b)

and subst_pos_formula (p:loc) (f: formula): formula=
  match f with
  | Base b -> Base {b with formula_base_pure = MCP.subst_pos_mix_formula p b.formula_base_pure;formula_base_pos = p }
  | Or b -> Or {formula_or_f1 = subst_pos_formula p b.formula_or_f1;
                formula_or_f2 = subst_pos_formula p b.formula_or_f2;
                formula_or_pos = p}
  | Exists ef -> Exists {ef with formula_exists_pos =  p}

and struc_fv ?(vartype=Vartypes.var_with_none) (f: struc_formula) : CP.spec_var list =
  let rdv = Gen.BList.remove_dups_eq CP.eq_spec_var in
  let dsvl l1 l2 = Gen.BList.difference_eq CP.eq_spec_var (rdv l1) l2 in
  let rec aux f =
    match f with
    | ECase b -> (* dsvl *)
      (List.concat (List.map (fun (c1,c2) ->
           let vars = if vartype # is_heap_only then [] else CP.fv c1 in
           vars@(aux c2) ) b.formula_case_branches)) (* b.formula_case_exists *)
    | EBase b ->
      let impl_vs = if vartype # is_implicit then [] else b.formula_struc_implicit_inst in
      let expl_vs = if vartype # is_explicit then [] else b.formula_struc_explicit_inst in
      let exists_vs = if vartype # is_exists then [] else b.formula_struc_exists in
      dsvl ((fold_opt aux b.formula_struc_continuation)@(fv ~vartype:vartype b.formula_struc_base))
        (impl_vs @ expl_vs @ exists_vs)
    | EAssume b -> fv ~vartype:vartype b.formula_assume_simpl
    | EInfer b -> Gen.BList.remove_dups_eq CP.eq_spec_var (aux b.formula_inf_continuation)
    | EList b -> rdv (fold_l_snd aux b)
  in aux f

and struc_implicit_vars (f: struc_formula): CP.spec_var list =
  match f with
  | EList el -> List.concat (List.map (fun (_, sf) -> struc_implicit_vars sf) el)
  | ECase ec -> List.concat (List.map (fun (_, sf) -> struc_implicit_vars sf) ec.formula_case_branches)
  | EBase eb -> eb.formula_struc_implicit_inst
  | EAssume ae -> []
  | EInfer ei -> struc_implicit_vars ei.formula_inf_continuation

and struc_fv_infer (f: struc_formula) : CP.spec_var list =
  let rdv = Gen.BList.remove_dups_eq CP.eq_spec_var in
  let dsvl l1 l2 = Gen.BList.difference_eq CP.eq_spec_var (rdv l1) l2 in
  match f with
  | ECase b -> (* dsvl *) (List.concat (List.map (fun (c1,c2) -> (CP.fv c1)@(struc_fv_infer c2) ) b.formula_case_branches)) (* b.formula_case_exists *)
  | EBase b -> dsvl ((fold_opt struc_fv_infer b.formula_struc_continuation)@(fv b.formula_struc_base))
                 (b.formula_struc_explicit_inst @ b.formula_struc_implicit_inst@ b.formula_struc_exists)
  | EAssume b -> fv b.formula_assume_simpl
  | EInfer b -> dsvl (struc_fv_infer b.formula_inf_continuation) b.formula_inf_vars
  | EList b -> rdv (fold_l_snd struc_fv_infer b)

and struc_infer_relation (f: struc_formula) : CP.spec_var list =
  let rdv = Gen.BList.remove_dups_eq CP.eq_spec_var in
  match f with
  | ECase b -> List.concat (List.map (fun (_,c) -> struc_infer_relation c) b.formula_case_branches)
  | EBase b -> fold_opt struc_infer_relation b.formula_struc_continuation
  | EAssume b -> []
  | EInfer b -> b.formula_inf_vars
  | EList b -> rdv (fold_l_snd struc_infer_relation b)

and struc_post_fv (f:struc_formula):Cpure.spec_var list =
  let rdv = Gen.BList.remove_dups_eq CP.eq_spec_var in
  match f with
  | ECase b-> rdv (fold_l_snd struc_post_fv b.formula_case_branches)
  | EBase b->	fold_opt struc_post_fv b.formula_struc_continuation
  | EAssume b-> CP.remove_dups_svl ((fv b.formula_assume_simpl)(* @(struc_post_fv b.formula_assume_struc) *))
  | EInfer b -> struc_post_fv b.formula_inf_continuation
  | EList b -> rdv (fold_l_snd struc_post_fv b)

and all_vars (f:formula): Cpure.spec_var list = match f with
  | Or ({
      formula_or_f1 = f1;
      formula_or_f2 = f2 }) ->
    CP.remove_dups_svl (fv f1 @ fv f2)
  | Base ({
      formula_base_heap = h;
      formula_base_pure = p;
      formula_base_vperm = vp;
      formula_base_and = a;
      formula_base_type = t }) ->
    let vars = CP.remove_dups_svl (List.concat (List.map one_formula_fv a)) in
    CP.remove_dups_svl (h_fv h @ MCP.mfv p @ (CVP.fv vp) @ vars)
  | Exists ({
      formula_exists_qvars = qvars;
      formula_exists_heap = h;
      formula_exists_pure = p;
      formula_exists_vperm = vp;
      formula_exists_type = t;
      formula_exists_and = a;
      formula_exists_flow = fl;
      formula_exists_label = lbl;
      formula_exists_pos = pos }) ->
    let fvars = fv (Base ({
        formula_base_heap = h;
        formula_base_pure = p;
        formula_base_vperm = vp;
        formula_base_type = t;
        formula_base_and = a;
        formula_base_flow = fl;
        formula_base_label = lbl;
        formula_base_pos = pos }))
    in
    let vars = List.concat (List.map one_formula_fv a) in
    let fvars = CP.remove_dups_svl (vars@fvars) in
    (* let res = Gen.BList.difference_eq CP.eq_spec_var fvars qvars in *)
    fvars

and struc_all_vars (f:struc_formula): Cpure.spec_var list =
  let rdv = Gen.BList.remove_dups_eq CP.eq_typed_spec_var in
  match f with
  | ECase b -> (List.concat (List.map (fun (c1,c2) -> (CP.fv c1)@(struc_all_vars c2)) b.formula_case_branches)) (* rdv (fold_l_snd struc_all_vars b.formula_case_branches) *)
  | EBase b -> (fold_opt struc_all_vars b.formula_struc_continuation)@(all_vars b.formula_struc_base) (* rdv (fold_opt struc_all_vars b.formula_struc_continuation) *)
  | EAssume b -> all_vars b.formula_assume_simpl
  | EInfer b -> rdv (struc_all_vars b.formula_inf_continuation)
  | EList b -> rdv (fold_l_snd struc_all_vars b)

and struc_all_vars_except_post (f:struc_formula): Cpure.spec_var list =
  let rdv = Gen.BList.remove_dups_eq CP.eq_typed_spec_var in
  match f with
  | ECase b -> (List.concat (List.map (fun (c1,c2) -> (CP.fv c1)@(struc_all_vars_except_post c2)) b.formula_case_branches)) (* rdv (fold_l_snd struc_all_vars_except_post b.formula_case_branches) *)
  | EBase b -> (fold_opt struc_all_vars_except_post b.formula_struc_continuation)@(all_vars b.formula_struc_base) (* rdv ((fold_opt struc_fv b.formula_struc_continuation)@(fv b.formula_struc_base)) *)
  | EAssume b -> []
  | EInfer b -> rdv (struc_all_vars_except_post b.formula_inf_continuation)
  | EList b -> rdv (fold_l_snd struc_all_vars_except_post b)

and heap_of (f:formula) : h_formula list = match f with
  | Or ({formula_or_f1 = f1;
         formula_or_f2 = f2}) -> (heap_of f1)@(heap_of f2)
  | Base b-> [b.formula_base_heap]
  | Exists b-> [b.formula_exists_heap]

and fv_heap_of (f:formula) =
  let hl= heap_of f in
  List.concat (List.map h_fv hl)

and fv_heap_of_one_formula (f:one_formula) =  (h_fv f.formula_heap)

and mk_Star f1 f2 pos = match f1 with
  | HFalse -> HFalse
  | HEmp -> f2
  | _ -> match f2 with
    | HFalse -> HFalse
    | HEmp -> f1
    | _ -> if (f1 = HTrue) && (f2 = HTrue) then HTrue
      else Star { h_formula_star_h1 = f1;
                  h_formula_star_h2 = f2;
                  h_formula_star_pos = pos }

and mk_Conj f1 f2 p =
  if (f1 = HFalse) || (f2 = HFalse) then HFalse
  else if (f1 = HTrue) && (f2 = HTrue) then HTrue
  else if (f1 = HEmp) && (f2 = HEmp) then HEmp
  else Conj ({h_formula_conj_h1 = f1;
              h_formula_conj_h2 = f2;
              h_formula_conj_pos = p})

and mk_ConjStar f1 f2 p =
  if (f1 = HFalse) || (f2 = HFalse) then HFalse
  else if (f1 = HTrue) && (f2 = HTrue) then HTrue
  else if (f1 = HEmp) && (f2 = HEmp) then HEmp
  else ConjStar ({h_formula_conjstar_h1 = f1;
                  h_formula_conjstar_h2 = f2;
                  h_formula_conjstar_pos = p})

and mk_ConjConj f1 f2 p =
  if (f1 = HFalse) || (f2 = HFalse) then HFalse
  else if (f1 = HTrue) && (f2 = HTrue) then HTrue
  else if (f1 = HEmp) && (f2 = HEmp) then HEmp
  else ConjConj ({h_formula_conjconj_h1 = f1;
                  h_formula_conjconj_h2 = f2;
                  h_formula_conjconj_pos = p})

and remove_h_lend (f:h_formula) : h_formula =
  match f with
  | Star b ->
    let new_f1 = remove_h_lend b.h_formula_star_h1 in
    let new_f2 = remove_h_lend b.h_formula_star_h2 in
    let pos = b.h_formula_star_pos in
    mk_Star new_f1 new_f2 pos
  | Conj b ->
    let new_f1 = remove_h_lend b.h_formula_conj_h1 in
    let new_f2 = remove_h_lend b.h_formula_conj_h2 in
    let pos = b.h_formula_conj_pos in
    mk_Conj new_f1 new_f2 pos
  | DataNode {h_formula_data_imm = i}
  | ViewNode {h_formula_view_imm = i} ->
    if CP.isLend i then HEmp else f
  | _ -> f

and remove_lend (f:formula) : formula = match f with
  | Or b ->
    let new_f1 = remove_lend b.formula_or_f1 in
    let new_f2 = remove_lend b.formula_or_f2 in
    Or {b with formula_or_f1=new_f1; formula_or_f2=new_f2}
  | Base b ->
    let old_h = b.formula_base_heap in
    Base {b with formula_base_heap = remove_h_lend old_h}
  | Exists b ->
    let old_h = b.formula_exists_heap in
    Exists {b with formula_exists_heap = remove_h_lend old_h}

and remove_h_ann (f:h_formula) (annot : ann) : h_formula =
  match f with
  | Star b ->
    let new_f1 = remove_h_ann b.h_formula_star_h1 annot in
    let new_f2 = remove_h_ann b.h_formula_star_h2 annot in
    let pos = b.h_formula_star_pos in
    mk_Star new_f1 new_f2 pos
  | Conj b ->
    let new_f1 = remove_h_ann b.h_formula_conj_h1 annot in
    let new_f2 = remove_h_ann b.h_formula_conj_h2 annot in
    let pos = b.h_formula_conj_pos in
    mk_Conj new_f1 new_f2 pos
  | ConjStar b ->
    let new_f1 = remove_h_ann b.h_formula_conjstar_h1 annot in
    let new_f2 = remove_h_ann b.h_formula_conjstar_h2 annot in
    let pos = b.h_formula_conjstar_pos in
    mk_ConjStar new_f1 new_f2 pos
  | ConjConj b ->
    let new_f1 = remove_h_ann b.h_formula_conjconj_h1 annot in
    let new_f2 = remove_h_ann b.h_formula_conjconj_h2 annot in
    let pos = b.h_formula_conjconj_pos in
    mk_ConjConj new_f1 new_f2 pos
  | DataNode {h_formula_data_imm = i}
  | ViewNode {h_formula_view_imm = i} ->
    if (CP.eq_ann i annot) then HTrue else f
  | _ -> f

and remove_one_ann (f:formula) (annot : ann) : formula =
  match f with
  | Or b ->
    let new_f1 = remove_one_ann b.formula_or_f1 annot in
    let new_f2 = remove_one_ann b.formula_or_f2 annot in
    Or {b with formula_or_f1=new_f1; formula_or_f2=new_f2}
  | Base b ->
    let old_h = b.formula_base_heap in
    Base {b with formula_base_heap = remove_h_ann old_h annot}
  | Exists b ->
    let old_h = b.formula_exists_heap in
    Exists {b with formula_exists_heap = remove_h_ann old_h annot}

and remove_ann  (f:formula) (annot_lst : ann list) : formula =
  match annot_lst with
  | []       -> f
  | annot::r -> remove_ann (remove_one_ann f annot) r

and one_formula_fv ?(vartype=Vartypes.var_with_none) (f:one_formula) : CP.spec_var list =
  let base = formula_of_one_formula f in
  let vars = fv ~vartype base in
  let tid = f.formula_thread in
  (tid::vars)

and fv' ?(vartype=Vartypes.var_with_none) (f : formula) : CP.spec_var list =
  let rec aux f =
    match f with
    | Or ({
        formula_or_f1 = f1;
        formula_or_f2 = f2 }) ->
      CP.remove_dups_svl (aux f1 @ aux f2)
    | Base ({
        formula_base_heap = h;
        formula_base_pure = p;
        formula_base_vperm = vp;
        formula_base_and = a;
        formula_base_type = t }) ->
      let vars = if vartype # is_heap_only then []
        else List.concat (List.map (one_formula_fv ~vartype) a) @ (MCP.mfv ~vartype p)
      in
      CP.remove_dups_svl ((h_fv ~vartype:vartype h) @ vars)
    | Exists ({
        formula_exists_qvars = qvars;
        formula_exists_heap = h;
        formula_exists_pure = p;
        formula_exists_vperm = vp;
        formula_exists_type = t;
        formula_exists_and = a;
        formula_exists_flow = fl;
        formula_exists_label = lbl;
        formula_exists_pos = pos }) ->
      let qvars = if vartype # is_exists then [] else qvars in
      let fvars = aux (Base ({
          formula_base_heap = h;
          formula_base_pure = p;
          formula_base_vperm = vp;
          formula_base_type = t;
          formula_base_and = a;
          formula_base_flow = fl;
          formula_base_label = lbl;
          formula_base_pos = pos }))
      in
      (* let vars = List.concat (List.map one_formula_fv a) in *)
      let fvars = CP.remove_dups_svl ((* vars@ *)fvars) in
      let res = Gen.BList.difference_eq CP.eq_spec_var fvars qvars in
      res
  in aux f

and fv ?(vartype=Vartypes.var_with_none) (f : formula) =
  Debug.no_1
    "Cformula.fv"
    !print_formula
    !print_svl
    (fv' ~vartype)
    f

(* and is_absent imm = *)
(*   match imm with *)
(*   | CP.ConstAnn(Accs) -> true *)
(*   | _ -> false *)

and remove_absent ann vs =
  if List.length ann = List.length vs then
    let com_ls = List.combine ann vs in
    let res_ls = List.filter (fun (a,_) -> not((* CP.is_absent_ann *)Immutils.is_abs a)) com_ls in
    List.split res_ls
  else (ann,vs)

and h_fv_node ?(vartype=Vartypes.var_with_none) v perm ann param_ann vs ho_vs annot_args =
  let (param_ann,vs) = remove_absent param_ann vs in
  Debug.no_2 "h_fv_node" string_of_ann_list !print_svl !print_svl
    (fun _ _ -> h_fv_node_x ~vartype:vartype v perm ann param_ann vs ho_vs annot_args) param_ann vs

and h_fv_node_x ?(vartype=Vartypes.var_with_none) vv perm ann param_ann
    vs ho_vs annot_args =
  let pvars = fv_cperm perm in
  let avars = (CP.fv_ann ann) in
  (* WN : free var should not need to depend on flags *)
  let avars = if true (* (!Globals.allow_field_ann) *) then avars @ (CP.fv_ann_lst param_ann)  else avars in
  let avars = avars @ (CP.fv_annot_arg annot_args ) in
  let pvars =
    match pvars with
    | [] ->  []
    | p::ps ->
      (* WN: previously List.mem was used *)
      if (CP.mem_svl p vs)
      then []
      else
        if !Globals.warn_nonempty_perm_vars then
          let msg = "NON-EMPTY PERM VARS"^(!CP.print_svl pvars) in
          failwith msg
        else
          pvars
  in
  let hvars = Gen.BList.remove_dups_eq CP.eq_spec_var (List.concat (List.map rf_fv ho_vs)) in
  let vs = vs@pvars in
  let other_vs = avars@hvars in
  (* WN : is_heap_only excludes ann_vars and higher-order vars for now *)
  let () = y_ninfo_hp (add_str "vv" !CP.print_sv) vv in
  let () = y_ninfo_hp (add_str "vs" !CP.print_svl) vs in
  if vartype # is_heap_only then
    begin
      (* if other_vs!=[] then x_winfo_pp ((add_str "other free vars?" !CP.print_svl) other_vs) no_pos; *)
      (* let () = x_tinfo_hp (add_str "vs" !CP.print_svl) vs no_pos in *)
      (* let () = x_tinfo_hp (add_str "v" !CP.print_sv) vv no_pos in *)
      vs
    end
  else if vartype # is_heap_ptr_only then [vv]
  else (if CP.mem_svl vv vs then vs else vv :: vs)@other_vs

and rf_fv (f: rflow_formula) = fv f.rflow_base

and f_h_fv (f : formula) : CP.spec_var list =
  (* let rec helper h = match h with *)
  (*   | Star b ->  Gen.BList.remove_dups_eq (=) (helper b.h_formula_star_h1 @ helper b.h_formula_star_h2) *)
  (*   | Conj b ->  Gen.BList.remove_dups_eq (=) (helper b.h_formula_conj_h1 @ helper b.h_formula_conj_h2) *)
  (*   | Phase b ->  Gen.BList.remove_dups_eq (=) (helper b.h_formula_phase_rd @ helper b.h_formula_phase_rw) *)
  (*   | DataNode b -> [b.h_formula_data_node] *)
  (*   | ViewNode b -> [b.h_formula_view_node] *)
  (*   | HRel (r, args, pos) -> [r] (\*vp*\) *)
  (*   | HTrue | HFalse | HEmp | Hole _ -> [] in *)
  match f with
  | Or b -> CP.remove_dups_svl (fv b.formula_or_f1 @ fv b.formula_or_f2)
  | Base b -> h_fv b.formula_base_heap
  | Exists b -> Gen.BList.difference_eq CP.eq_spec_var (h_fv b.formula_exists_heap) b.formula_exists_qvars

and h_fv ?(vartype=Vartypes.var_with_none) (h : h_formula) : CP.spec_var list =
  (* Debug.no_1 "h_fv" !print_h_formula !print_svl *) (h_fv_x ~vartype:vartype) h

and h_fv_x ?(vartype=Vartypes.var_with_none) (h : h_formula) : CP.spec_var list =
  let rec aux h =
    match h with
    | Star ({h_formula_star_h1 = h1;
             h_formula_star_h2 = h2;
             h_formula_star_pos = pos})
    | StarMinus ({h_formula_starminus_h1 = h1;
                  h_formula_starminus_h2 = h2;
                  h_formula_starminus_pos = pos}) -> CP.remove_dups_svl (aux h1 @ aux h2)
    | Conj ({h_formula_conj_h1 = h1;
             h_formula_conj_h2 = h2;
             h_formula_conj_pos = pos})
    | ConjStar ({h_formula_conjstar_h1 = h1;
                 h_formula_conjstar_h2 = h2;
                 h_formula_conjstar_pos = pos})
    | ConjConj ({h_formula_conjconj_h1 = h1;
                 h_formula_conjconj_h2 = h2;
                 h_formula_conjconj_pos = pos}) -> Gen.BList.remove_dups_eq (=) (aux h1 @ aux h2)
    | Phase ({h_formula_phase_rd = h1;
              h_formula_phase_rw = h2;
              h_formula_phase_pos = pos}) -> Gen.BList.remove_dups_eq (=) (aux h1 @ aux h2)
    | DataNode ({h_formula_data_node = v;
                 h_formula_data_perm = perm;
                 h_formula_data_imm = ann;
                 h_formula_data_param_imm = param_ann;
                 h_formula_data_arguments = vs}) ->
      h_fv_node ~vartype:vartype v perm ann param_ann vs [] []
    | ViewNode ({h_formula_view_node = v;
                 h_formula_view_name = i;
                 h_formula_view_perm = perm;
                 h_formula_view_imm = ann;
                 h_formula_view_ho_arguments = ho_vs;
                 h_formula_view_annot_arg = ann_args;
                 h_formula_view_arguments = vs}) ->
      if vartype # is_view_only then [CP.mk_spec_var i]
      else
        h_fv_node ~vartype:vartype v perm ann [] vs ho_vs ann_args
    | ThreadNode ({h_formula_thread_node = v;
                   h_formula_thread_perm = perm;
                   h_formula_thread_delayed = dl;
                   h_formula_thread_resource = rsr;
                  }) ->
      let perm_vars = fv_cperm perm in
      let rsr_vars = fv rsr in
      let dl_vars = CP.fv dl in
      let old_vs = Gen.BList.remove_dups_eq (=) (v::(perm_vars@rsr_vars@dl_vars)) in
      if vartype # is_heap_only || vartype # is_heap_ptr_only  then []
      else old_vs
    | HRel (r, args, _) ->
      let vid = r in
      let old_vs = vid::CP.remove_dups_svl (List.fold_left List.append [] (List.map CP.afv args)) in
      let () = x_tinfo_hp (add_str "HRel(vs)" !CP.print_svl) old_vs no_pos in
      if vartype # is_heap_only || vartype # is_heap_ptr_only  then []
      else old_vs
    | HTrue | HFalse | HEmp | Hole _ | FrmHole _ -> []
    | HVar (v,ls) -> v::ls
  in aux h

(*and br_fv br init_l: CP.spec_var list =
  CP.remove_dups_svl (List.fold_left (fun a (c1,c2)-> (CP.fv c2)@a) init_l br)*)

and f_top_level_vars_struc (f:struc_formula) : CP.spec_var list =
  let pr1 = !print_struc_formula in
  let pr2 = !print_svl in
  Debug.no_1 "f_top_level_vars_struc" pr1 pr2 f_top_level_vars_struc_x f

and f_top_level_vars_struc_x (f:struc_formula) : CP.spec_var list = match f with
  | ECase c-> fold_l_snd f_top_level_vars_struc_x c.formula_case_branches
  | EBase b -> 	(f_top_level_vars b.formula_struc_base) @ (fold_opt f_top_level_vars_struc_x b.formula_struc_continuation)
  | EAssume _ -> []
  | EInfer b -> f_top_level_vars_struc_x b.formula_inf_continuation
  | EList b -> fold_l_snd f_top_level_vars_struc_x b

and f_top_level_vars_x (f : formula) : CP.spec_var list = match f with
  | Base ({formula_base_heap = h}) -> (top_level_vars h)
  | Or ({ formula_or_f1 = f1;
          formula_or_f2 = f2}) -> (f_top_level_vars_x f1) @ (f_top_level_vars_x f2)
  | Exists ({formula_exists_heap = h}) -> (top_level_vars h)

and f_top_level_vars (f : formula) : CP.spec_var list =
  let pr1 = !print_formula in
  let pr2 = !print_svl in
  Debug.no_1 "f_top_level_vars" pr1 pr2 f_top_level_vars_x f


and top_level_vars (h : h_formula) : CP.spec_var list = match h with
  | Star ({h_formula_star_h1 = h1;
           h_formula_star_h2 = h2})
  | StarMinus ({h_formula_starminus_h1 = h1;
                h_formula_starminus_h2 = h2}) -> (top_level_vars h1) @ (top_level_vars h2)
  | Conj ({h_formula_conj_h1 = h1;
           h_formula_conj_h2 = h2})
  | ConjStar ({h_formula_conjstar_h1 = h1;
               h_formula_conjstar_h2 = h2})
  | ConjConj ({h_formula_conjconj_h1 = h1;
               h_formula_conjconj_h2 = h2}) -> (top_level_vars h1) @ (top_level_vars h2)
  | Phase ({h_formula_phase_rd = h1;
            h_formula_phase_rw = h2}) -> (top_level_vars h1) @ (top_level_vars h2)
  | ThreadNode ({h_formula_thread_node = v})
  | DataNode ({h_formula_data_node = v})
  | ViewNode ({h_formula_view_node = v}) -> [v]
  | HRel (r, agrs,  pos) -> [r] (*vp*)
  | HTrue | HFalse | HEmp | Hole _ | FrmHole _ | HVar _ -> []

and get_formula_pos (f : formula) = match f with
  | Base ({formula_base_pos = p}) -> p
  | Or ({formula_or_pos = p}) -> p
  | Exists ({formula_exists_pos = p}) -> p


(* substitution *)

and subst_avoid_capture (fr : CP.spec_var list) (t : CP.spec_var list) (f : formula) =
  Debug.no_3 "subst_avoid_capture"
    (add_str "from vars:" !print_svl)
    (add_str "to vars:" !print_svl)
    !print_formula
    !print_formula
    (fun _ _ _ -> subst_avoid_capture_x fr t f) fr t f

and subst_avoid_capture_x (fr : CP.spec_var list) (t : CP.spec_var list) (f : formula) =
  let fresh_fr = CP.fresh_spec_vars fr in
  (*--- 09.05.2000 *)
  (*let () = (print_string ("\n[cformula.ml, line 307]: fresh name = " ^ (string_of_spec_var_list fresh_fr) ^ "!!!!!!!!!!!\n")) in*)
  (*09.05.2000 ---*)
  let st1 = List.combine fr fresh_fr in
  let st2 = List.combine fresh_fr t in
  let f1 = subst_one_by_one st1 f in
  let f2 = subst_one_by_one st2 f1 in
  f2

(*subst in pure formula only*)
and subst_avoid_capture_pure (fr : CP.spec_var list) (t : CP.spec_var list) (f : formula) =
  Debug.no_3 "subst_avoid_capture_pure"
    (add_str "from vars:" !print_svl)
    (add_str "to vars:" !print_svl)
    !print_formula
    !print_formula
    (fun _ _ _ -> subst_avoid_capture_pure_x fr t f) fr t f

and subst_avoid_capture_pure_x (fr : CP.spec_var list) (t : CP.spec_var list) (f : formula) =
  let fresh_fr = CP.fresh_spec_vars fr in
  (*--- 09.05.2000 *)
  (*let () = (print_string ("\n[cformula.ml, line 307]: fresh name = " ^ (string_of_spec_var_list fresh_fr) ^ "!!!!!!!!!!!\n")) in*)
  (*09.05.2000 ---*)
  let st1 = List.combine fr fresh_fr in
  let st2 = List.combine fresh_fr t in
  let f1 = subst_one_by_one_pure st1 f in
  let f2 = subst_one_by_one_pure st2 f1 in
  f2

and subst_avoid_capture_h (fr : CP.spec_var list) (t : CP.spec_var list) (f : h_formula) : h_formula =
  Debug.no_3 "subst_avoid_capture_h" !print_svl !print_svl !print_h_formula !print_h_formula
    (fun _ _ _ -> subst_avoid_capture_h_x fr t f) fr t f

and subst_avoid_capture_h_x (fr : CP.spec_var list) (t : CP.spec_var list) (f : h_formula) : h_formula =
  let fresh_fr = CP.fresh_spec_vars fr in
  let st1 = List.combine fr fresh_fr in
  let st2 = List.combine fresh_fr t in
  let f1 = subst_one_by_one_h st1 f in
  let f2 = subst_one_by_one_h st2 f1 in
  f2

and subst_var_list sst (svs : Cpure.spec_var list) = match svs with
  | [] -> []
  | sv :: rest ->
    let new_vars = subst_var_list sst rest in
    let new_sv = match List.filter (fun st -> fst st = sv) sst with
      | [(fr, t)] -> t
      | _ -> sv in
    new_sv :: new_vars

and subst_struc_avoid_capture (fr : CP.spec_var list) (t : CP.spec_var list) (f : struc_formula):struc_formula =
  let pr1 = !CP.print_svl in
  let pr2 = !print_struc_formula in
  Debug.no_3 "subst_struc_avoid_capture" pr1 pr1 pr2 pr2
    subst_struc_avoid_capture_x fr t f

(*LDK: substitue variales (t) in formula (f) by variables (fr)*)
and subst_struc_avoid_capture_x (fr : CP.spec_var list) (t : CP.spec_var list) (f : struc_formula):struc_formula =
  let fresh_fr = CP.fresh_spec_vars fr in
  let st1 = List.combine fr fresh_fr in
  let st2 = List.combine fresh_fr t in
  let f1 = subst_struc_x st1 f in
  let f2 = subst_struc_x st2 f1 in
  f2

and subst_struc sst (f : struc_formula) =
  let pr1 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
  let pr2 = !print_struc_formula in
  Debug.no_2 "subst_struc" pr1 pr2 pr2 subst_struc_x sst f

and subst_struc_x sst (f : struc_formula) = match sst with
  | s :: rest -> subst_struc_x rest (apply_one_struc s f)
  | [] -> f

and subst_struc_pre sst (f : struc_formula) =
  (* apply_par_struc_pre s f *)
  match sst with
  | s :: rest -> subst_struc_pre rest (apply_one_struc_pre s f)
  | [] -> f


and apply_one_struc_pre  ((fr, t) as s : (CP.spec_var * CP.spec_var)) (f : struc_formula):struc_formula = match f with
  | ECase b -> ECase {b with
                      formula_case_branches = List.map (fun (c1,c2)-> ((CP.apply_one s c1),(apply_one_struc_pre s c2)) ) b.formula_case_branches;}
  | EBase b -> EBase {
      formula_struc_explicit_inst = List.map (subst_var s)  b.formula_struc_explicit_inst;
      formula_struc_implicit_inst = List.map (subst_var s)  b.formula_struc_implicit_inst;
      formula_struc_exists = List.map (subst_var s)  b.formula_struc_exists;
      formula_struc_base = apply_one s  b.formula_struc_base;
      formula_struc_is_requires = b.formula_struc_is_requires;
      formula_struc_continuation = map_opt (apply_one_struc_pre s) b.formula_struc_continuation;
      formula_struc_pos = b.formula_struc_pos
    }
  | EAssume b-> if (List.mem fr b.formula_assume_vars) then f
    else EAssume { b with
                   formula_assume_simpl = apply_one s b.formula_assume_simpl;
                   formula_assume_struc = apply_one_struc_pre s b.formula_assume_struc;}
  | EInfer b -> EInfer {b with formula_inf_continuation = apply_one_struc_pre s b.formula_inf_continuation}
  | EList b-> EList (map_l_snd (apply_one_struc_pre s) b)


and apply_one_struc  ((fr, t) as s : (CP.spec_var * CP.spec_var)) (f : struc_formula):struc_formula =  match f with
  | ECase b -> ECase {b with formula_case_branches = List.map (fun (c1,c2)-> ((CP.apply_one s c1),(apply_one_struc s c2)) ) b.formula_case_branches;}
  | EBase b -> EBase {b with
                      formula_struc_explicit_inst = List.map (subst_var s)  b.formula_struc_explicit_inst;
                      formula_struc_implicit_inst = List.map (subst_var s)  b.formula_struc_implicit_inst;
                      formula_struc_exists = List.map (subst_var s)  b.formula_struc_exists;
                      formula_struc_base = apply_one s  b.formula_struc_base;
                      formula_struc_continuation = map_opt (apply_one_struc s) b.formula_struc_continuation;
                      formula_struc_pos = b.formula_struc_pos }
  | EAssume b-> EAssume{ b with
                         formula_assume_vars = subst_var_list [s] b.formula_assume_vars;
                         formula_assume_simpl = apply_one s b.formula_assume_simpl;
                         formula_assume_struc = apply_one_struc s b.formula_assume_struc;}
  | EInfer b -> EInfer {b with  formula_inf_continuation = apply_one_struc s b.formula_inf_continuation}
  | EList b-> EList (map_l_snd (apply_one_struc s) b)

(*LDK: add a constraint formula between perm spec var of datanode to fresh spec var of a view decl  *)
and add_mix_formula_to_struc_formula  (rhs_p: MCP.mix_formula) (f : struc_formula): struc_formula =
  Debug.no_2 "add_mix_formula_to_struc_formula"
    !print_mix_formula !print_struc_formula !print_struc_formula
    add_mix_formula_to_struc_formula_x rhs_p f

(*LDK: only heap need fractional permision spec var (perm) *)
and add_mix_formula_to_struc_formula_x (rhs_p: MCP.mix_formula) (f : struc_formula) : struc_formula = match f with
  | ECase b -> f
  | EBase b -> EBase {b with  formula_struc_base = add_mix_formula_to_formula rhs_p b.formula_struc_base ;
                              formula_struc_continuation = map_opt (add_mix_formula_to_struc_formula_x rhs_p) b.formula_struc_continuation;}
  | EAssume _ -> f
  | EInfer b -> EInfer { b with formula_inf_continuation = add_mix_formula_to_struc_formula_x rhs_p b.formula_inf_continuation;}
  | EList b -> EList (map_l_snd (add_mix_formula_to_struc_formula_x rhs_p) b)

and add_pure_formula_to_struc_formula f1 (f2:struc_formula): struc_formula =
  add_mix_formula_to_struc_formula (MCP.mix_of_pure f1) f2

and add_pure_formula_to_formula (f1_pure: CP.formula) (f2_f:formula)  : formula =
  add_mix_formula_to_formula (MCP.mix_of_pure f1_pure) f2_f

(*LDK : add a constraint formula between perm spec var of datanode to fresh spec var of a view decl  *)
and add_mix_formula_to_formula  (f1_mix: MCP.mix_formula) (f2_f:formula) : formula =
  Debug.no_2 "add_mix_formula_to_formula_x" !print_mix_formula !print_formula
    !print_formula
    add_mix_formula_to_formula_x f1_mix f2_f

and add_mix_formula_to_formula_x (f1_mix: MCP.mix_formula) (f2_f:formula)  : formula=
  match f2_f with
  | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) ->
    Or ({formula_or_f1 = add_mix_formula_to_formula_x f1_mix f1 ; formula_or_f2 =  add_mix_formula_to_formula_x f1_mix f2 ; formula_or_pos = pos})
  | Base b -> Base { b with formula_base_pure = add_mix_formula_to_mix_formula f1_mix b.formula_base_pure;}
  | Exists b -> Exists {b with  formula_exists_pure = add_mix_formula_to_mix_formula f1_mix b.formula_exists_pure;}

(*add f1 into p*)
and add_mix_formula_to_mix_formula (f1: MCP.mix_formula) (f2: MCP.mix_formula) :MCP.mix_formula =
  (x_add MCP.merge_mems f1 f2 true)

and one_formula_subst sst (f : one_formula) =
  let sst = List.filter (fun (fr,t) ->
      if ((CP.name_of_spec_var fr)=Globals.ls_name || (CP.name_of_spec_var fr)=Globals.lsmu_name) then false
      else true
    ) sst in (*donot rename ghost LOCKSET name*)
  let df = f.formula_delayed in
  let ndf = MCP.m_apply_par sst df in
  let base = formula_of_one_formula f in
  let rs = x_add subst sst base in
  let ref_vars = (List.map (CP.subst_var_par sst) f.formula_ref_vars) in
  let tid = CP.subst_var_par sst f.formula_thread in
  let one_f = (one_formula_of_formula rs tid ndf) in
  {one_f with formula_ref_vars = ref_vars}


(** An Hoa : replace the function subst above by substituting f in parallel **)

and subst sst (f : formula) =
  let pr1 = pr_list (pr_pair !print_sv !print_sv) in
  let pr2 = !print_formula in
  Debug.no_2 "subst" pr1 pr2 pr2 subst_x sst f

and subst_x sst (f : formula) =
  let rec helper f =
    match f with
    | Or ({ formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos }) ->
      Or ({ formula_or_f1 = helper f1; formula_or_f2 =  helper f2; formula_or_pos = pos })
    | Base b -> Base ({ b with
                        formula_base_heap = h_subst sst b.formula_base_heap;
                        formula_base_pure = MCP.regroup_memo_group (MCP.m_apply_par sst b.formula_base_pure);
                        (* formula_base_vperm = CVP.subst_par sst b.formula_base_vperm; *)
                        formula_base_and = (List.map (fun f -> one_formula_subst sst f) b.formula_base_and);})
    | Exists ({
        formula_exists_qvars = qsv;
        formula_exists_heap = qh;
        formula_exists_vperm = vp;
        formula_exists_pure = qp;
        formula_exists_type = tconstr;
        formula_exists_and = a; (*TO CHECK*)
        formula_exists_flow = fl;
        formula_exists_label = lbl;
        formula_exists_pos = pos }) ->
      (* Variable under this existential quantification should NOT be substituted! *)
      (* Thus, we need to filter out replacements (fr |-> t) in sst where fr is in qsv *)
      let qsvnames = (List.map CP.name_of_spec_var qsv) in
      let sst = List.filter (fun (fr,_) -> not (List.mem (CP.name_of_spec_var fr) qsvnames)) sst in
      if sst = [] then f
      else Exists ({
          formula_exists_qvars = qsv;
          formula_exists_heap =  h_subst sst qh;
          formula_exists_vperm = (* CVP.subst_par sst *) vp;
          formula_exists_pure = MCP.regroup_memo_group (MCP.m_apply_par sst qp);
          formula_exists_type = tconstr;
          formula_exists_and = (List.map (fun f -> one_formula_subst sst f) a);
          formula_exists_flow = fl;
          formula_exists_label = lbl;
          formula_exists_pos = pos })
  in helper f

and subst_all sst (f : formula) =
  let pr1 = pr_list (pr_pair !print_sv !print_sv) in
  let pr2 = !print_formula in
  let loc = VarGen.last_posn # get "subst_all" in
  let () = y_winfo_pp (loc ^ ": You are using an unsafe substitution; should use subst_avoid_capture instead.") in
  Debug.no_2 "subst_all" pr1 pr2 pr2
    (fun _ _ -> subst_all_x sst f) sst f

and subst_all_x sst (f : formula) =
  let rec helper f = match f with
    | Or ({ formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos }) ->
      Or ({ formula_or_f1 = helper f1; formula_or_f2 =  helper f2; formula_or_pos = pos })
    | Base b -> Base ({ b with
                        formula_base_heap = h_subst sst b.formula_base_heap;
                        formula_base_pure = MCP.regroup_memo_group (MCP.m_apply_par sst b.formula_base_pure);
                        formula_base_vperm = CVP.subst_par sst b.formula_base_vperm;
                        formula_base_and = (List.map (fun f -> one_formula_subst sst f) b.formula_base_and); })
    | Exists ({
        formula_exists_qvars = qsv;
        formula_exists_heap = qh;
        formula_exists_vperm = vp;
        formula_exists_pure = qp;
        formula_exists_type = tconstr;
        formula_exists_and = a; (*TO CHECK*)
        formula_exists_flow = fl;
        formula_exists_label = lbl;
        formula_exists_pos = pos }) ->
      Exists ({
          formula_exists_qvars = CP.subst_var_list_par sst qsv;
          formula_exists_heap = h_subst sst qh;
          formula_exists_vperm = CVP.subst_par sst vp;
          formula_exists_pure = MCP.regroup_memo_group (MCP.m_apply_par sst qp);
          formula_exists_type = tconstr;
          formula_exists_and = (List.map (fun f -> one_formula_subst sst f) a);
          formula_exists_flow = fl;
          formula_exists_label = lbl;
          formula_exists_pos = pos })
  in helper f

and subst_b_x sst (b:formula_base): formula_base =
  { b with
    formula_base_heap = h_subst sst b.formula_base_heap;
    formula_base_vperm = CVP.subst_par sst b.formula_base_vperm;
    formula_base_pure = MCP.regroup_memo_group (MCP.m_apply_par sst b.formula_base_pure);
    formula_base_and = (List.map (fun f -> one_formula_subst sst f) b.formula_base_and); }

and subst_b sst (f : formula_base) =
  let pr1 = pr_list (pr_pair !print_sv !print_sv) in
  let pr2 = !print_formula_base in
  Debug.no_2 "subst_b" pr1 pr2 pr2 subst_b_x sst f
(** An Hoa : End of formula substitution **)


(** An Hoa: Function to substitute variables in a heap formula in parallel **)
and dn_subst sst dn=
  ({ dn with
     h_formula_data_node = CP.subst_var_par sst dn.h_formula_data_node;
     h_formula_data_perm = map_opt (CP.e_apply_subs sst) dn.h_formula_data_perm;
     h_formula_data_arguments = List.map (CP.subst_var_par sst) dn.h_formula_data_arguments;
     (* h_formula_data_imm =  *) (*andreeac TODO add sebst for ann*)
     (* h_formula_data_param_ann =  *)
     h_formula_data_pruning_conditions = List.map (fun (c,c2)-> (CP.b_apply_subs sst c,c2)) dn.h_formula_data_pruning_conditions;
   })

and vn_subst sst vn=
  let n_hf = h_subst sst (ViewNode vn) in
  match n_hf with
  | ViewNode vn -> vn
  | _ -> report_error no_pos "CF.vn_subst"

and rf_subst sst (f: rflow_formula) =
  { f with rflow_base = (* subst sst *) f.rflow_base; }

and h_subst sst (f : h_formula) =
  match f with
  | Star ({h_formula_star_h1 = f1;
           h_formula_star_h2 = f2;
           h_formula_star_pos = pos}) ->
    Star ({h_formula_star_h1 = h_subst sst f1;
           h_formula_star_h2 = h_subst sst f2;
           h_formula_star_pos = pos})
  | StarMinus ({h_formula_starminus_h1 = f1;
                h_formula_starminus_h2 = f2;
                h_formula_starminus_aliasing = al;
                h_formula_starminus_pos = pos}) ->
    StarMinus ({h_formula_starminus_h1 = h_subst sst f1;
                h_formula_starminus_h2 = h_subst sst f2;
                h_formula_starminus_aliasing =  al;
                h_formula_starminus_pos = pos})
  | Phase ({h_formula_phase_rd = f1;
            h_formula_phase_rw = f2;
            h_formula_phase_pos = pos}) ->
    Phase ({h_formula_phase_rd = h_subst sst f1;
            h_formula_phase_rw = h_subst sst f2;
            h_formula_phase_pos = pos})
  | Conj ({h_formula_conj_h1 = f1;
           h_formula_conj_h2 = f2;
           h_formula_conj_pos = pos}) ->
    Conj ({h_formula_conj_h1 = h_subst sst f1;
           h_formula_conj_h2 = h_subst sst f2;
           h_formula_conj_pos = pos})
  | ConjStar ({h_formula_conjstar_h1 = f1;
               h_formula_conjstar_h2 = f2;
               h_formula_conjstar_pos = pos}) ->
    ConjStar ({h_formula_conjstar_h1 = h_subst sst f1;
               h_formula_conjstar_h2 = h_subst sst f2;
               h_formula_conjstar_pos = pos})
  | ConjConj ({h_formula_conjconj_h1 = f1;
               h_formula_conjconj_h2 = f2;
               h_formula_conjconj_pos = pos}) ->
    ConjConj ({h_formula_conjconj_h1 = h_subst sst f1;
               h_formula_conjconj_h2 = h_subst sst f2;
               h_formula_conjconj_pos = pos})
  | ViewNode ({h_formula_view_node = x;
               h_formula_view_name = c;
               h_formula_view_imm = imm;
               h_formula_view_perm = perm; (*LDK*)
               h_formula_view_arguments = svs;
               h_formula_view_ho_arguments = ho_svs;
               h_formula_view_annot_arg = anns;
               h_formula_view_modes = modes;
               h_formula_view_coercible = coble;
               h_formula_view_origins = orgs;
               h_formula_view_original = original;
               h_formula_view_unfold_num = i;
               h_formula_view_label = lbl;
               h_formula_view_remaining_branches = ann;
               h_formula_view_pruning_conditions = pcond;
               h_formula_view_pos = pos} as g) ->
    ViewNode { g with
               h_formula_view_imm = subs_imm_par sst imm;
               h_formula_view_node = CP.subst_var_par sst x;
               h_formula_view_perm = map_opt (CP.e_apply_subs sst) perm;
               h_formula_view_arguments = List.map (CP.subst_var_par sst) svs;
               h_formula_view_ho_arguments = List.map (rf_subst sst) ho_svs;
               h_formula_view_annot_arg = CP.subst_annot_arg sst anns;
               h_formula_view_pruning_conditions = List.map (fun (c,c2)-> (CP.b_apply_subs sst c,c2)) pcond
             }
  | DataNode ({h_formula_data_node = x;
               h_formula_data_name = c;
               h_formula_data_derv = dr;
               h_formula_data_split = split;
               h_formula_data_imm = imm;
               h_formula_data_param_imm = ann_param;
               h_formula_data_perm = perm; (*LDK*)
               h_formula_data_arguments = svs;
               h_formula_data_origins = orgs;
               h_formula_data_original = original;
               h_formula_data_holes = hs; (* An Hoa 16/8/2011 Holes added *)
               h_formula_data_label = lbl;
               h_formula_data_remaining_branches = ann;
               h_formula_data_pruning_conditions = pcond;
               h_formula_data_pos = pos}) ->
    DataNode ({h_formula_data_node = CP.subst_var_par sst x;
               h_formula_data_name = c;
               h_formula_data_derv = dr;
               h_formula_data_split = split;
               h_formula_data_imm = subs_imm_par sst imm;
               h_formula_data_param_imm = List.map (subs_imm_par sst) ann_param;
               h_formula_data_perm = map_opt (CP.e_apply_subs sst) perm;   (*LDK*)
               h_formula_data_arguments = List.map (CP.subst_var_par sst) svs;
               h_formula_data_holes = hs; (* An Hoa 16/8/2011 Holes added *)
               h_formula_data_origins = orgs;
               h_formula_data_original = original;
               h_formula_data_label = lbl;
               h_formula_data_remaining_branches = ann;
               h_formula_data_pruning_conditions = List.map (fun (c,c2)-> (CP.b_apply_subs sst c,c2)) pcond;
               h_formula_data_pos = pos})
  | ThreadNode ({h_formula_thread_node = x;
                 h_formula_thread_name = c;
                 h_formula_thread_derv = dr;
                 h_formula_thread_split = split;
                 h_formula_thread_perm = perm; (*LDK*)
                 h_formula_thread_delayed = dl;
                 h_formula_thread_resource = rsr;
                 h_formula_thread_origins = orgs;
                 h_formula_thread_original = original;
                 h_formula_thread_label = lbl;
                 h_formula_thread_pos = pos} ) ->
    let new_sst = List.filter (fun (fr,t) ->
        if ((CP.name_of_spec_var fr)=Globals.ls_name || (CP.name_of_spec_var fr)=Globals.lsmu_name) then false
        else true
      ) sst in (*donot rename ghost LOCKSET name*)
    let ndl = CP.apply_subs new_sst dl in
    ThreadNode ({h_formula_thread_node = CP.subst_var_par sst x;
                 h_formula_thread_name = c;
                 h_formula_thread_derv = dr;
                 h_formula_thread_split = split;
                 h_formula_thread_perm = map_opt (CP.e_apply_subs sst) perm;   (*LDK*)
                 h_formula_thread_delayed = ndl;
                 h_formula_thread_resource = x_add subst sst rsr;
                 h_formula_thread_origins = orgs;
                 h_formula_thread_original = original;
                 h_formula_thread_label = lbl;
                 h_formula_thread_pos = pos})
  | HRel (r, args, pos) ->
    HRel (CP.subst_var_par sst r, List.map (CP.e_apply_subs sst) args, pos)
  | HVar (v,ls) -> HVar ((CP.subst_var_par sst v),(List.map (CP.subst_var_par sst) ls))
  | HTrue -> f
  | HFalse -> f
  | HEmp -> f
  | Hole _ | FrmHole _ -> f
(** An Hoa : End of heap formula substitution **)

(* and subst_var_par sst v = try *)
(* 			List.assoc v sst *)
(* 	with Not_found -> v *)

and subst_one_by_one sst (f : formula) =
  let pr1 = pr_list (pr_pair !print_sv !print_sv) in
  let pr2 = !print_formula in
  Debug.no_2 "subst_one_by_one" pr1 pr2 pr2 subst_one_by_one_x sst f

and subst_one_by_one_x sst (f : formula) = match sst with
  | s :: rest -> subst_one_by_one_x rest (apply_one s f)
  | [] -> f

and subst_one_by_one_pure sst (f : formula) =
  let pr1 = pr_list (pr_pair !print_sv !print_sv) in
  let pr2 = !print_formula in
  Debug.no_2 "subst_one_by_one_pure" pr1 pr2 pr2 subst_one_by_one_pure_x sst f

and subst_one_by_one_pure_x sst (f : formula) = match sst with
  | s :: rest -> subst_one_by_one_pure_x rest (apply_one_pure s f)
  | [] -> f

and subst_one_by_one_h sst (f : h_formula) =
  let pr1 = pr_list (pr_pair !print_sv !print_sv) in
  let pr2 = !print_h_formula in
  Debug.no_2 "subst_one_by_one_h" pr1 pr2 pr2 subst_one_by_one_h_x sst f

and subst_one_by_one_h_x sst (f : h_formula) = match sst with
  | s :: rest -> subst_one_by_one_h_x rest (h_apply_one s f)
  | [] -> f

and subst_one_by_one_var sst (v : CP.spec_var) =
  match sst with
  | s :: rest -> subst_one_by_one_var rest (subst_var s v)
  | [] -> v

and subst_var (fr, t) (o : CP.spec_var) =
  if CP.eq_spec_var fr o then t else o

and apply_one_one_formula ((fr, t) as s : (CP.spec_var * CP.spec_var)) (f : one_formula) =
  let df = f.formula_delayed in
  let ndf = MCP.m_apply_one (fr, t) df in
  let base = formula_of_one_formula f in
  let rs = apply_one s base in
  let tid = subst_var s f.formula_thread in
  let ref_vars = List.map (subst_var s) f.formula_ref_vars in
  let one_f = (one_formula_of_formula rs tid ndf) in
  {one_f with formula_ref_vars = ref_vars}

and apply_one ((fr, t) as s : (CP.spec_var * CP.spec_var)) (f : formula) = match f with
  | Or ({ formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos }) ->
    Or ({ formula_or_f1 = apply_one s f1; formula_or_f2 =  apply_one s f2; formula_or_pos = pos })
  | Base ({
      formula_base_heap = h;
      formula_base_vperm = vp;
      formula_base_pure = p;
      formula_base_type = t;
      formula_base_and = a;
      formula_base_flow = fl;
      formula_base_label = lbl;
      formula_base_pos = pos }) ->
    Base ({
        formula_base_heap = h_apply_one s h;
        (* WN:subs_pre *)
        formula_base_vperm =
          if !pre_subst_flag then vp
          else CVP.subst_one s vp;
        formula_base_pure = MCP.regroup_memo_group (MCP.m_apply_one s p);
        formula_base_type = t;
        formula_base_and = List.map (apply_one_one_formula s) a;
        formula_base_flow = fl;
        formula_base_label = lbl;
        formula_base_pos = pos })
  | Exists ({
      formula_exists_qvars = qsv;
      formula_exists_heap = qh;
      formula_exists_vperm = vp;
      formula_exists_pure = qp;
      formula_exists_type = tconstr;
      formula_exists_and = a;
      formula_exists_flow = fl;
      formula_exists_label = lbl;
      formula_exists_pos = pos }) ->
    if List.mem (CP.name_of_spec_var fr) (List.map CP.name_of_spec_var qsv) then f
    else if List.mem (CP.name_of_spec_var t) (List.map CP.name_of_spec_var qsv) then
      (* !! needed as it might be the case that a free variable is renamed  *)
      (*   such that the new name clashes with an existential               *)
      let qvars, base_f = split_quantifiers f in
      let new_qvar = CP.fresh_spec_var t in
      let new_qvars = List.filter (fun c -> not (CP.eq_spec_var t c)) qsv in
      add_quantifiers (new_qvar::new_qvars) (apply_one s (apply_one (t,new_qvar) base_f))
    else Exists ({
        formula_exists_qvars = qsv;
        formula_exists_heap =  h_apply_one s qh;
        formula_exists_vperm =
          (if !pre_subst_flag then vp
           else CVP.subst_one s vp);
        formula_exists_pure = MCP.regroup_memo_group (MCP.m_apply_one s qp);
        formula_exists_type = tconstr;
        formula_exists_and = List.map (apply_one_one_formula s) a;
        formula_exists_flow = fl;
        formula_exists_label = lbl;
        formula_exists_pos = pos })

(*Only substitute pure formula*)
and apply_one_pure ((fr, t) as s : (CP.spec_var * CP.spec_var)) (f : formula) = match f with
  | Or ({ formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos }) ->
    Or ({ formula_or_f1 = apply_one s f1; formula_or_f2 =  apply_one s f2; formula_or_pos = pos })
  | Base ({
      formula_base_heap = h;
      formula_base_vperm = vp;
      formula_base_pure = p;
      formula_base_type = t;
      formula_base_and = a;
      formula_base_flow = fl;
      formula_base_label = lbl;
      formula_base_pos = pos }) ->
    Base ({
        formula_base_heap = h;
        formula_base_vperm = CVP.subst_one s vp;
        formula_base_pure = MCP.regroup_memo_group (MCP.m_apply_one s p);
        formula_base_type = t;
        formula_base_and = List.map (apply_one_one_formula s) a;
        formula_base_flow = fl;
        formula_base_label = lbl;
        formula_base_pos = pos })
  | Exists ({
      formula_exists_qvars = qsv;
      formula_exists_heap = qh;
      formula_exists_vperm = vp;
      formula_exists_pure = qp;
      formula_exists_type = tconstr;
      formula_exists_and = a;
      formula_exists_flow = fl;
      formula_exists_label = lbl;
      formula_exists_pos = pos }) ->
    if List.mem (CP.name_of_spec_var fr) (List.map CP.name_of_spec_var qsv) then f
    else Exists ({
        formula_exists_qvars = qsv;
        formula_exists_heap = qh;
        formula_exists_vperm = CVP.subst_one s vp;
        formula_exists_pure = MCP.regroup_memo_group (MCP.m_apply_one s qp);
        formula_exists_type = tconstr;
        formula_exists_and = List.map (apply_one_one_formula s) a;
        formula_exists_flow = fl;
        formula_exists_label = lbl;
        formula_exists_pos = pos })

and h_apply_one ((fr, t) as s : (CP.spec_var * CP.spec_var)) (f : h_formula) = match f with
  | Star ({h_formula_star_h1 = f1;
           h_formula_star_h2 = f2;
           h_formula_star_pos = pos}) ->
    Star ({h_formula_star_h1 = h_apply_one s f1;
           h_formula_star_h2 = h_apply_one s f2;
           h_formula_star_pos = pos})
  | StarMinus ({h_formula_starminus_h1 = f1;
                h_formula_starminus_h2 = f2;
                h_formula_starminus_aliasing = al;
                h_formula_starminus_pos = pos}) ->
    StarMinus ({h_formula_starminus_h1 = h_apply_one s f1;
                h_formula_starminus_h2 = h_apply_one s f2;
                h_formula_starminus_aliasing =  al;
                h_formula_starminus_pos = pos})
  | Phase ({h_formula_phase_rd = f1;
            h_formula_phase_rw = f2;
            h_formula_phase_pos = pos}) ->
    Phase ({h_formula_phase_rd = h_apply_one s f1;
            h_formula_phase_rw = h_apply_one s f2;
            h_formula_phase_pos = pos})
  | Conj ({h_formula_conj_h1 = f1;
           h_formula_conj_h2 = f2;
           h_formula_conj_pos = pos}) ->
    Conj ({h_formula_conj_h1 = h_apply_one s f1;
           h_formula_conj_h2 = h_apply_one s f2;
           h_formula_conj_pos = pos})
  | ConjStar ({h_formula_conjstar_h1 = f1;
               h_formula_conjstar_h2 = f2;
               h_formula_conjstar_pos = pos}) ->
    ConjStar ({h_formula_conjstar_h1 = h_apply_one s f1;
               h_formula_conjstar_h2 = h_apply_one s f2;
               h_formula_conjstar_pos = pos})
  | ConjConj ({h_formula_conjconj_h1 = f1;
               h_formula_conjconj_h2 = f2;
               h_formula_conjconj_pos = pos}) ->
    ConjConj ({h_formula_conjconj_h1 = h_apply_one s f1;
               h_formula_conjconj_h2 = h_apply_one s f2;
               h_formula_conjconj_pos = pos})
  | ViewNode ({h_formula_view_node = x;
               h_formula_view_name = c;
               h_formula_view_imm = imm;
               h_formula_view_perm = perm; (*LDK*)
               h_formula_view_arguments = svs;
               h_formula_view_ho_arguments = ho_svs;
               h_formula_view_modes = modes;
               h_formula_view_coercible = coble;
               h_formula_view_origins = orgs;
               h_formula_view_original = original;
               h_formula_view_unfold_num = i;
               h_formula_view_label = lbl;
               h_formula_view_remaining_branches = ann;
               h_formula_view_pruning_conditions = pcond;
               h_formula_view_annot_arg = annot_args;
               h_formula_view_pos = pos} as g) ->
    ViewNode {g with h_formula_view_node = subst_var s x;
                     h_formula_view_perm = subst_var_perm () s perm;  (*LDK*)
                     h_formula_view_imm = apply_one_imm s imm;
                     (* WN:subs_pre *)
                     h_formula_view_ho_arguments =
                       if !pre_subst_flag then ho_svs
                       else List.map (trans_rflow_formula (apply_one s)) ho_svs;
                     h_formula_view_arguments = List.map (subst_var s) svs;
                     h_formula_view_annot_arg = apply_one_annot_arg s annot_args;
                     h_formula_view_pruning_conditions = List.map (fun (c,c2)-> (CP.b_apply_one s c,c2)) pcond
             }
  | DataNode ({h_formula_data_node = x;
               h_formula_data_name = c;
               h_formula_data_derv = dr;
               h_formula_data_split = split;
               h_formula_data_imm = imm;
               h_formula_data_param_imm = ann_param;
               h_formula_data_perm = perm; (*LDK*)
               h_formula_data_origins = orgs;
               h_formula_data_original = original;
               h_formula_data_arguments = svs;
               h_formula_data_holes = hs; (* An Hoa 16/8/2011 Holes added *)
               h_formula_data_label = lbl;
               h_formula_data_remaining_branches = ann;
               h_formula_data_pruning_conditions = pcond;
               h_formula_data_pos = pos}) ->
    DataNode ({h_formula_data_node = subst_var s x;
               h_formula_data_name = c;
               h_formula_data_derv = dr;
               h_formula_data_split = split;
               h_formula_data_perm = subst_var_perm () s perm; (*LDK*)
               h_formula_data_imm = apply_one_imm s imm;
               h_formula_data_param_imm = List.map (apply_one_imm s) ann_param;
               h_formula_data_origins = orgs;
               h_formula_data_original = original;
               h_formula_data_arguments = List.map (subst_var s) svs;
               h_formula_data_holes = hs;
               h_formula_data_label = lbl;
               h_formula_data_remaining_branches = ann;
               h_formula_data_pruning_conditions = List.map (fun (c,c2)-> (CP.b_apply_one s c,c2)) pcond;
               h_formula_data_pos = pos})
  | ThreadNode ({h_formula_thread_node = x;
                 h_formula_thread_resource = rsr;
                 h_formula_thread_delayed = dl;
                 h_formula_thread_perm = perm;} as t) ->
    ThreadNode ({t with h_formula_thread_node = subst_var s x;
                        h_formula_thread_perm = subst_var_perm () s perm; (*LDK*)
                        h_formula_thread_delayed = CP.apply_one s dl;
                        h_formula_thread_resource = apply_one s rsr;})
  | HRel (r, args, pos) -> HRel (r, List.map (CP.e_apply_one s ) args, pos)
  | HVar (v,ls) -> HVar (CP.subst_var s v, List.map (CP.subst_var s) ls)
  | HTrue -> f
  | HFalse -> f
  | HEmp -> f
  | Hole _ | FrmHole _ -> f

(* normalization *)
(* normalizes ( \/ (EX v* . /\ ) ) * ( \/ (EX v* . /\ ) ) *)
and normalize_keep_flow (f1 : formula) (f2 : formula) flow_tr (pos : loc) = match f1 with
  | Or ({formula_or_f1 = o11; formula_or_f2 = o12; formula_or_pos = _}) ->
    let eo1 = normalize_x o11 f2 pos in
    let eo2 = normalize_x o12 f2 pos in
    mkOr eo1 eo2 pos
  | _ -> begin
      match f2 with
      | Or ({formula_or_f1 = o21; formula_or_f2 = o22; formula_or_pos = _}) ->
        let eo1 = normalize_x f1 o21 pos in
        let eo2 = normalize_x f1 o22 pos in
        mkOr eo1 eo2 pos
      | _ -> begin
          let rf1 = rename_bound_vars f1 in
          let rf2 = rename_bound_vars f2 in
          let qvars1, base1 = split_quantifiers rf1 in
          let qvars2, base2 = split_quantifiers rf2 in
          let new_base = mkStar_combine base1 base2 flow_tr pos in
          let new_h, new_p, new_vp, new_fl, new_t, new_a = split_components new_base in
          let resform = mkExists (qvars1 @ qvars2) new_h new_p new_vp new_t new_fl new_a pos in (* qvars[1|2] are fresh vars, hence no duplications *)
          resform
        end
    end

and normalize i (f1 : formula) (f2 : formula) (pos : loc) =
  Debug.no_2 "normalizeB" (!print_formula) (!print_formula) (!print_formula) (fun _ _ -> normalize_x f1 f2 pos) f1 f2

and normalize_x (f1 : formula) (f2 : formula)
    (pos : loc) =
  normalize_keep_flow f1 f2 Flow_combine pos

(*the flow of f2*)
and normalize_replace (f1 : formula) (f2 : formula) (pos : loc) =
  Debug.no_2 "normalize_replace" !print_formula !print_formula !print_formula
    (fun _ _ -> normalize_replace_x f1 f2 pos) f1 f2

and normalize_replace_x (f1 : formula) (f2 : formula) (pos : loc) =
  normalize_keep_flow f1 f2 Flow_replace pos

and normalize_combine_heap (f1 : formula) (f2 : h_formula)
  = normalize_combine_star f1 (formula_of_heap f2 no_pos) no_pos

and normalize_combine (f1 : formula) (f2 : formula) (pos : loc) = normalize_combine_star f1 f2 pos

and normalize_combine_star_x (f1 : formula) (f2 : formula) (pos : loc) = match f1 with
  | Or ({formula_or_f1 = o11; formula_or_f2 = o12; formula_or_pos = _}) ->
    let eo1 = normalize_combine_star_x o11 f2 pos in
    let eo2 = normalize_combine_star_x o12 f2 pos in
    mkOr eo1 eo2 pos
  | _ -> begin
      match f2 with
      | Or ({formula_or_f1 = o21; formula_or_f2 = o22; formula_or_pos = _}) ->
        let eo1 = normalize_combine_star_x f1 o21 pos in
        let eo2 = normalize_combine_star_x f1 o22 pos in
        mkOr eo1 eo2 pos
      | _ -> begin
          let rf1 = Gen.Profiling.no_1 "7_ren_bound" rename_bound_vars f1 in
          let rf2 = Gen.Profiling.no_1 "7_ren_bound" rename_bound_vars f2 in
          let qvars1, base1 = split_quantifiers rf1 in
          let qvars2, base2 = split_quantifiers rf2 in
          let new_base = Gen.Profiling.no_1 "6_mkstar" (mkStar_combine base1 base2 Flow_combine) pos in
          (* let () = print_string("normalize 1\n") in *)
          let new_h, new_p, new_vp, new_fl, new_t, new_a = split_components new_base in
          let resform = mkExists (qvars1 @ qvars2) new_h new_p new_vp new_t new_fl new_a pos in (* qvars[1|2] are fresh vars, hence no duplications *)
          resform
        end
    end

and normalize_combine_star (f1 : formula) (f2 : formula) (pos : loc) =
  let pr = !print_formula in
  Debug.no_2 "normalize_combine_star" pr pr pr
    (fun _ _ -> Gen.Profiling.no_1 "10_norm_comb_st"(normalize_combine_star_x f1 f2) pos) f1 f2

and normalize_combine_starminus (f1 : formula) (f2 : formula) (al: aliasing_scenario) (pos : loc) = match f1 with
  | Or ({formula_or_f1 = o11; formula_or_f2 = o12; formula_or_pos = _}) ->
    let eo1 = normalize_combine_starminus o11 f2 al pos in
    let eo2 = normalize_combine_starminus o12 f2 al pos in
    mkOr eo1 eo2 pos
  | _ -> begin
      match f2 with
      | Or ({formula_or_f1 = o21; formula_or_f2 = o22; formula_or_pos = _}) ->
        let eo1 = normalize_combine_starminus f1 o21 al pos in
        let eo2 = normalize_combine_starminus f1 o22 al pos in
        mkOr eo1 eo2 pos
      | _ -> begin
          let rf1 = rename_bound_vars f1 in
          let rf2 = rename_bound_vars f2 in
          let qvars1, base1 = split_quantifiers rf1 in
          let qvars2, base2 = split_quantifiers rf2 in
          let new_base = mkStarMinus_combine base1 base2 Flow_combine al pos in
          let new_h, new_p, new_vp, new_fl, new_t, new_a = split_components new_base in
          let resform = mkExists (qvars1 @ qvars2) new_h new_p new_vp new_t new_fl new_a pos in (* qvars[1|2] are fresh vars, hence no duplications *)
          resform
        end
    end

and normalize_combine_conj (f1 : formula) (f2 : formula) (pos : loc) = match f1 with
  | Or ({formula_or_f1 = o11; formula_or_f2 = o12; formula_or_pos = _}) ->
    let eo1 = normalize_combine_conj o11 f2 pos in
    let eo2 = normalize_combine_conj o12 f2 pos in
    mkOr eo1 eo2 pos
  | _ -> begin
      match f2 with
      | Or ({formula_or_f1 = o21; formula_or_f2 = o22; formula_or_pos = _}) ->
        let eo1 = normalize_combine_conj f1 o21 pos in
        let eo2 = normalize_combine_conj f1 o22 pos in
        mkOr eo1 eo2 pos
      | _ -> begin
          let rf1 = rename_bound_vars f1 in
          let rf2 = rename_bound_vars f2 in
          let qvars1, base1 = split_quantifiers rf1 in
          let qvars2, base2 = split_quantifiers rf2 in
          let new_base = mkConj_combine base1 base2 Flow_combine pos in
          let new_h, new_p, new_vp, new_fl, new_t, new_a = split_components new_base in
          let resform = mkExists (qvars1 @ qvars2) new_h new_p new_vp new_t new_fl new_a pos in (* qvars[1|2] are fresh vars, hence no duplications *)
          resform
        end
    end

and normalize_combine_conjstar (f1 : formula) (f2 : formula) (pos : loc) = match f1 with
  | Or ({formula_or_f1 = o11; formula_or_f2 = o12; formula_or_pos = _}) ->
    let eo1 = normalize_combine_conjstar o11 f2 pos in
    let eo2 = normalize_combine_conjstar o12 f2 pos in
    mkOr eo1 eo2 pos
  | _ -> begin
      match f2 with
      | Or ({formula_or_f1 = o21; formula_or_f2 = o22; formula_or_pos = _}) ->
        let eo1 = normalize_combine_conjstar f1 o21 pos in
        let eo2 = normalize_combine_conjstar f1 o22 pos in
        mkOr eo1 eo2 pos
      | _ -> begin
          let rf1 = rename_bound_vars f1 in
          let rf2 = rename_bound_vars f2 in
          let qvars1, base1 = split_quantifiers rf1 in
          let qvars2, base2 = split_quantifiers rf2 in
          let new_base = mkConjStar_combine base1 base2 Flow_combine pos in
          let new_h, new_p, new_vp, new_fl, new_t, new_a = split_components new_base in
          let resform = mkExists (qvars1 @ qvars2) new_h new_p new_vp new_t new_fl new_a pos in (* qvars[1|2] are fresh vars, hence no duplications *)
          resform
        end
    end

and normalize_combine_conjconj (f1 : formula) (f2 : formula) (pos : loc) = match f1 with
  | Or ({formula_or_f1 = o11; formula_or_f2 = o12; formula_or_pos = _}) ->
    let eo1 = normalize_combine_conjconj o11 f2 pos in
    let eo2 = normalize_combine_conjconj o12 f2 pos in
    mkOr eo1 eo2 pos
  | _ -> begin
      match f2 with
      | Or ({formula_or_f1 = o21; formula_or_f2 = o22; formula_or_pos = _}) ->
        let eo1 = normalize_combine_conjconj f1 o21 pos in
        let eo2 = normalize_combine_conjconj f1 o22 pos in
        mkOr eo1 eo2 pos
      | _ -> begin
          let rf1 = rename_bound_vars f1 in
          let rf2 = rename_bound_vars f2 in
          let qvars1, base1 = split_quantifiers rf1 in
          let qvars2, base2 = split_quantifiers rf2 in
          let new_base = mkConjConj_combine base1 base2 Flow_combine pos in
          let new_h, new_p, new_vp, new_fl, new_t, new_a = split_components new_base in
          let resform = mkExists (qvars1 @ qvars2) new_h new_p new_vp new_t new_fl new_a pos in (* qvars[1|2] are fresh vars, hence no duplications *)
          resform
        end
    end

and normalize_combine_phase (f1 : formula) (f2 : formula) (pos : loc) = match f1 with
  | Or ({formula_or_f1 = o11; formula_or_f2 = o12; formula_or_pos = _}) ->
    let eo1 = normalize_combine_phase o11 f2 pos in
    let eo2 = normalize_combine_phase o12 f2 pos in
    mkOr eo1 eo2 pos
  | _ -> begin
      match f2 with
      | Or ({formula_or_f1 = o21; formula_or_f2 = o22; formula_or_pos = _}) ->
        let eo1 = normalize_combine_phase f1 o21 pos in
        let eo2 = normalize_combine_phase f1 o22 pos in
        mkOr eo1 eo2 pos
      | _ -> begin
          let rf1 = rename_bound_vars f1 in
          let rf2 = rename_bound_vars f2 in
          let qvars1, base1 = split_quantifiers rf1 in
          let qvars2, base2 = split_quantifiers rf2 in
          let new_base = mkPhase_combine base1 base2 Flow_combine pos in
          let new_h, new_p, new_vp, new_fl, new_t, new_a = split_components new_base in
          let resform = mkExists (qvars1 @ qvars2) new_h new_p new_vp new_t new_fl new_a pos in (* qvars[1|2] are fresh vars, hence no duplications *)
          resform
        end
    end

(* -- 13.05.2008 *)
(* normalizes but only renames the bound variables of f1 that clash with variables from fv(f2) *)

and normalize_only_clash_rename (f1 : formula) (f2 : formula) (pos : loc) =
  Debug.no_2 "normalize_only_clash_rename" (!print_formula) (!print_formula) (!print_formula) (fun _ _ -> normalize_only_clash_rename_x f1 f2 pos) f1 f2

and normalize_only_clash_rename_x (f1 : formula) (f2 : formula) (pos : loc) = match f1 with
  | Or ({formula_or_f1 = o11; formula_or_f2 = o12; formula_or_pos = _}) ->
    let eo1 = normalize_only_clash_rename_x o11 f2 pos in
    let eo2 = normalize_only_clash_rename_x o12 f2 pos in
    mkOr eo1 eo2 pos
  | _ -> begin
      match f2 with
      | Or ({formula_or_f1 = o21; formula_or_f2 = o22; formula_or_pos = _}) ->
        let eo1 = normalize_only_clash_rename_x f1 o21 pos in
        let eo2 = normalize_only_clash_rename_x f1 o22 pos in
        mkOr eo1 eo2 pos
      | _ -> begin
          let rf1 = (fst (rename_clash_bound_vars f1 f2)) in
          let rf2 = (*rename_bound_vars*) f2 in
          let qvars1, base1 = split_quantifiers rf1 in
          let qvars2, base2 = split_quantifiers rf2 in
          let new_base = mkStar_combine base1 base2 Flow_combine pos in
          (* let () = print_string("normalize 2\n") in *)
          let new_h, new_p, new_vp, new_fl, new_t, new_a = split_components new_base in
          let resform = mkExists (qvars1 @ qvars2) new_h new_p new_vp new_t new_fl new_a pos in (* qvars[1|2] are fresh vars, hence no duplications *)
          resform
        end
    end
(* 13.05.2008 -- *)

(* split a conjunction into heap constraints, pure pointer constraints, *)
(* and Presburger constraints *)
and split_components_x ?(rename_flag=false) (f: formula) =
  snd (split_components_exist ~rename_flag:rename_flag f)

and split_components ?(rename_flag=false) (f: formula) =
  let pr1 = !print_formula in
  let pr2 = (fun (h, p, _, _, _, _) -> pr_pair !print_h_formula !MCP.print_mix_f (h, p)) in
  Debug.no_1 "split_components" pr1 pr2
    (fun _ -> split_components_x ~rename_flag:rename_flag f) f

and split_components_all_exist ?(rename_flag=false) (f : formula) =
  let rec helper f =
    if (isAnyConstFalse f) then []
    (* (HFalse, (MCP.mkMFalse no_pos), CVP.empty_vperm_sets,  *)
    (* (flow_formula_of_formula f), TypeFalse, []) *)
    else
      match f with
      | Base ({
          formula_base_heap = h;
          formula_base_vperm = vp;
          formula_base_pure = p;
          formula_base_flow = fl;
          formula_base_and = a; (* TO CHECK: omit at the moment *)
          formula_base_type = t }) -> [([],(h, p, vp, fl, t, a))]
      | Exists ({
          (* need to do renaming here *)
          formula_exists_heap = h;
          formula_exists_qvars = qv;
          formula_exists_vperm = vp;
          formula_exists_pure = p;
          formula_exists_flow = fl;
          formula_exists_and = a; (* TO CHECK: omit at the moment *)
          formula_exists_type = t }) ->  [(qv,(h, p, vp, fl, t, a))]
      | Or ({ formula_or_f1 = f1;
              formula_or_f2 = f2}) ->
        (helper f1) @ (helper f2) in
  let f =
    if rename_flag then rename_bound_vars f
    else f
  in helper f

and split_components_all ?(rename_flag=false) (f : formula) =
  List.map snd (split_components_all_exist ~rename_flag:rename_flag f)

and split_components_exist ?(rename_flag=false) (f : formula) =
  let lst = split_components_all_exist ~rename_flag:rename_flag f in
  match lst with
  | [] -> ([],(HFalse, (MCP.mkMFalse no_pos), CVP.empty_vperm_sets,
           (flow_formula_of_formula f), TypeFalse, []))
  | [r] -> r
  | _ -> let () = x_tinfo_hp (add_str "f" !print_formula) f no_pos in
    Err.report_error {
      Err.error_loc = no_pos;
      Err.error_text = "split_components: don't expect OR" }

and get_rel_args f0=
  let rec helper f=
    match f with
    | Base ({formula_base_pure = p; }) ->
      (* let p1 = (MCP.pure_of_mix p) in *)
      (* let () =  Debug.info_zprint (lazy  ("XXXX p: " ^ (!CP.print_formula p1))) no_pos in *)
      CP.get_rel_args (MCP.pure_of_mix p)
    | Exists ({ formula_exists_pure = p;}) ->
      (* let p1 = (MCP.pure_of_mix p) in *)
      (* let () =  Debug.info_zprint (lazy  ("XXXX p: " ^ (!CP.print_formula p1))) no_pos in *)
      CP.get_rel_args (MCP.pure_of_mix p)
    | Or ({formula_or_f1 = of1;
           formula_or_f2 = of2;}) -> (helper of1)@(helper of2)
  in
  helper f0

and get_list_rel_args f0=
  let rec helper f=
    match f with
    | Base ({formula_base_pure = p; }) ->
      CP.get_list_rel_args (MCP.pure_of_mix p)
    | Exists ({ formula_exists_pure = p;}) ->
      CP.get_list_rel_args (MCP.pure_of_mix p)
    | Or ({formula_or_f1 = of1;
           formula_or_f2 = of2;}) -> (helper of1)@(helper of2)
  in
  helper f0

and check_rel_args_quan_clash args f0=
  let rec helper f=
    match f with
    | Base _ ->
      false
    | Exists ({ formula_exists_qvars = quans;}) ->
      CP.intersect_svl args quans <> []
    | Or ({formula_or_f1 = of1;
           formula_or_f2 = of2;}) -> (helper of1)||(helper of2)
  in
  helper f0

and all_components (f:formula) = (*the above misses some *)
  if (isAnyConstFalse f) then ([],HFalse,(MCP.mkMFalse no_pos),CVP.empty_vperm_sets,TypeFalse,(flow_formula_of_formula f),None,[],  no_pos)
  else match f with
    | Base b -> ([], b.formula_base_heap, b.formula_base_pure, b.formula_base_vperm,
                 b.formula_base_type, b.formula_base_flow, b.formula_base_label, b.formula_base_and, b.formula_base_pos)
    | Exists e -> (e.formula_exists_qvars, e.formula_exists_heap, e.formula_exists_pure, e.formula_exists_vperm,
                   e.formula_exists_type, e.formula_exists_flow, e.formula_exists_label, e.formula_exists_and, e.formula_exists_pos)
    | Or ({formula_or_pos = pos}) ->  Err.report_error {Err.error_loc = pos;Err.error_text = "all_components: don't expect OR"}

and split_quantifiers (f : formula) : (CP.spec_var list * formula) =
  match f with
  | Exists ({
      formula_exists_qvars = qvars;
      formula_exists_heap = h;
      formula_exists_vperm = vp;
      formula_exists_pure = p;
      formula_exists_type = t;
      formula_exists_flow = fl;
      formula_exists_and = a;
      formula_exists_label = lbl;
      formula_exists_pos = pos}) ->
    (qvars, mkBase_w_lbl h p vp t fl a pos lbl)
  | Base _ -> ([], f)
  | _ -> failwith ("split_quantifiers: invalid argument (formula_or)")

and add_quantifiers_x (qvars : CP.spec_var list) (f : formula) : formula =
  match f with
  | Base ({
      formula_base_heap = h;
      formula_base_vperm = vp;
      formula_base_pure = p;
      formula_base_type = t;
      formula_base_flow = fl;
      formula_base_and = a;
      formula_base_label = lbl;
      formula_base_pos = pos }) ->
    mkExists_w_lbl qvars h p vp t fl a pos lbl
  | Exists ({
      formula_exists_qvars = qvs;
      formula_exists_heap = h;
      formula_exists_vperm = vp;
      formula_exists_pure = p;
      formula_exists_type = t;
      formula_exists_flow = fl;
      formula_exists_and = a;
      formula_exists_label = lbl;
      formula_exists_pos = pos }) ->
    let new_qvars = CP.remove_dups_svl (qvs @ qvars) in
    mkExists_w_lbl new_qvars h p vp t fl a pos lbl
  | _ -> failwith ("add_quantifiers: invalid argument")

and add_quantifiers (qvars : CP.spec_var list) (f : formula) : formula =
  Debug.no_2 "add_quantifiers" !print_svl !print_formula !print_formula add_quantifiers_x qvars f

(* 19.05.2008 *)
and remove_quantifiers (qvars : CP.spec_var list) (f : formula) : formula =
  match f with
  | Base _ -> f
  | Exists ({
      formula_exists_qvars = qvs;
      formula_exists_heap = h;
      formula_exists_vperm = vp;
      formula_exists_pure = p;
      formula_exists_type = t;
      formula_exists_flow = fl;
      formula_exists_and = a;
      formula_exists_pos = pos }) ->
    (* let new_qvars = (List.filter (fun x -> not (List.exists (fun y -> CP.eq_spec_var x y) qvars)) qvs) in *)
    let new_qvars = Gen.BList.difference_eq CP.eq_spec_var qvs qvars in
    if (List.length new_qvars == 0) then mkBase h p vp t fl a pos
    else mkExists new_qvars h p vp t fl a pos
  | _ -> failwith ("remove_quantifiers: invalid argument")
(* 19.05.2008 *)

and push_struc_exists (qvars : CP.spec_var list) (f : struc_formula) =
  let pr = !print_struc_formula in
  Debug.no_2 "push_struc_exists" !print_svl pr pr push_struc_exists_x qvars f

and push_struc_exists_x (qvars : CP.spec_var list) (f : struc_formula) = match f with
  | EBase b ->
    (match b.formula_struc_continuation with
     | None -> EBase {b with formula_struc_base = push_exists qvars b.formula_struc_base}
     | _ -> EBase {b with formula_struc_exists = b.formula_struc_exists @ qvars})
  (* | ECase b -> ECase {b with formula_case_exists = b.formula_case_exists @ qvars} *)
  | ECase b -> ECase {b with formula_case_branches = List.map (fun (f,sf) -> (f,push_struc_exists_x qvars sf) ) b.formula_case_branches; }
  (* b with formula_case_exists = b.formula_case_exists @ qvars} *)
  | EAssume b -> EAssume {b with
                          formula_assume_simpl = push_exists qvars b.formula_assume_simpl;
                          formula_assume_struc = push_struc_exists_x qvars b.formula_assume_struc;}
  | EInfer b -> EInfer b
  | EList b -> EList (map_l_snd (push_struc_exists_x qvars) b)

and push_exists_x (qvars : CP.spec_var list) (f : formula) =
  match f with
  | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) ->
    let new_f1 = push_exists_x qvars f1 in
    let new_f2 = push_exists_x qvars f2 in
    let resform = mkOr new_f1 new_f2 pos in
    resform
  | _ -> add_quantifiers qvars f

and push_exists (qvars : CP.spec_var list) (f : formula) =
  if qvars==[] then f
  else Debug.no_2 "push_exists" !print_svl !print_formula !print_formula
      push_exists_x qvars f

(* 19.05.2008 *)
and pop_exists (qvars : CP.spec_var list) (f : formula) = match f with
  | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) ->
    let new_f1 = pop_exists qvars f1 in
    let new_f2 = pop_exists qvars f2 in
    let resform = mkOr new_f1 new_f2 pos in
    resform
  | _ -> remove_quantifiers qvars f
(* 19.05.2008 *)

and get_exists (f : formula) : CP.spec_var list =
  let rec helper f =
    match f with
    | Or ({formula_or_f1 = f1; formula_or_f2 = f2;}) ->
      let evars1 = helper f1 in
      let evars2 = helper f2 in
      (evars1@evars2)
    | Exists e -> e.formula_exists_qvars
    | Base b -> []
  in helper f

and elim_exists (f0 : formula) : formula =
  let pr =  !print_formula in
  (* Debug.no_1 "cformula.elim_exists" pr pr *) elim_exists_x f0

(* removing existentail using ex x. (x=y & P(x)) <=> P(y) *)
and elim_exists_x (f0 : formula) : formula = match f0 with
  | Or ({
      formula_or_f1 = f1;
      formula_or_f2 = f2;
      formula_or_pos = pos }) ->
    let ef1 = elim_exists_x f1 in
    let ef2 = elim_exists_x f2 in
    mkOr ef1 ef2 pos
  | Base _ -> f0
  | Exists ({
      formula_exists_qvars = qvar :: rest_qvars;
      formula_exists_heap = h;
      formula_exists_vperm = vp;
      formula_exists_pure = p;
      formula_exists_type = t;
      formula_exists_flow = fl;
      formula_exists_and = a;
      formula_exists_pos = pos }) ->
    let st, pp1 = MCP.get_subst_equation_memo_formula_vv p qvar in
    let r =
      if List.length st = 1 then
        let tmp = mkBase h pp1 vp t fl a pos in (*TO CHECK*) (* VP: no aliasing *)
        let new_baref = x_add subst st tmp in
        let tmp2 = add_quantifiers rest_qvars new_baref in
        let tmp3 = elim_exists_x tmp2 in
        tmp3
      else (* if qvar is not equated to any variables, try the next one *)
        let tmp1 = mkExists rest_qvars h p vp t fl a pos in (*TO CHECK*)
        let tmp2 = elim_exists_x tmp1 in
        let tmp3 = add_quantifiers [qvar] tmp2 in
        tmp3
    in r
  | Exists _ -> report_error no_pos ("Solver.elim_exists: Exists with an empty list of quantified variables")

(*
    WN : do the following
    (i) temp remove all non-linear stuff
    (ii) call simplify_omega
    (iii) add back removed stuff
    (iv) extend to disj form
*)
and simplify_aux_x f =
  if not(!Globals.oc_adv_simplify) then f
  else
    let disjs = CP.split_disjunctions f in
    List.fold_left (fun acc disj ->
        let conjs = CP.split_conjunctions disj in
        (* let null_svl = CP.get_null_ptrs disj in *)
        (* let eqs = List.filter (CP.is_eq_exp_ptrs null_svl) conjs in *)
        let eqs = [] in
        let lvs, non_lvs = List.partition CP.is_lexvar conjs in
        (* let vps, non_vps = List.partition CP.is_varperm non_lvs in *)
        let rels, non_rels = List.partition CP.is_RelForm non_lvs in
        let lins, non_lins = List.partition CP.is_linear_formula non_rels in
        let lin_f = List.fold_left (fun acc lin -> CP.mkAnd acc lin no_pos) (CP.mkTrue no_pos) lins in
        let lin_f = !simplify_omega lin_f in
        let new_disj = List.fold_left (fun acc non_lin -> CP.mkAnd acc non_lin no_pos) (lin_f) (eqs@non_lins) in
        let new_disj = List.fold_left (fun acc rel -> CP.mkAnd acc rel no_pos) new_disj rels in
        (* let new_disj = List.fold_left (fun acc vp -> CP.mkAnd acc vp no_pos) new_disj vps in *)
        let new_disj = List.fold_left (fun acc lv -> CP.mkAnd acc lv no_pos) new_disj lvs in
        CP.mkOr acc new_disj None no_pos
      ) (CP.mkFalse no_pos) disjs

and simplify_aux f =
  let pr = !print_pure_f in
  Debug.no_1 "simplify_aux" pr pr simplify_aux_x f

(* WN : can simplify ignore other type of pure ctrs? *)
and simplify_pure_f_x (f0:formula) =
  let simp f =
    let r1 = CP.remove_redundant f in
    let r2 = Wrapper.wrap_exception f simplify_aux r1 in
    let () = x_tinfo_hp (add_str "simp(f)" !print_pure_f) f no_pos in
    let () = x_tinfo_hp (add_str "simp(syn)" !print_pure_f) r1 no_pos in
    let () = x_tinfo_hp (add_str "simp(oc)" !print_pure_f) r2 no_pos in r2 in
  let rec helper f=
    match f with
    | Base b-> Base {b with formula_base_pure = MCP.mix_of_pure (simp (* CP.remove_redundant *) (MCP.pure_of_mix b.formula_base_pure));}
    | Exists e -> Exists {e with formula_exists_pure = MCP.mix_of_pure (simp (* CP.remove_redundant *) (MCP.pure_of_mix e.formula_exists_pure));}
    (* let quans, bare = split_quantifiers f in *)
    (* let simpl_bare = helper bare in *)
    (* add_quantifiers quans simpl_bare *)
    | Or orf -> Or {orf with formula_or_f1 = helper orf.formula_or_f1;
                             formula_or_f2 = helper orf.formula_or_f2}
  in
  helper f0

and simplify_pure_f (f0:formula) =
  let pr= !print_formula in
  Debug.no_1 "simplify_pure_f" pr pr
    (fun _ -> simplify_pure_f_x f0) f0

and simplify_pure_f_old_x (f0:formula) =
  let rec helper f=
    match f with
    | Base b-> Base {b with formula_base_pure = MCP.mix_of_pure (CP.remove_redundant (MCP.pure_of_mix b.formula_base_pure));}
    | Exists e -> Exists {e with formula_exists_pure = MCP.mix_of_pure (CP.remove_redundant (MCP.pure_of_mix e.formula_exists_pure));}
    | Or orf -> Or {orf with formula_or_f1 = helper orf.formula_or_f1;
                             formula_or_f2 = helper orf.formula_or_f2}
  in
  helper f0

and simplify_pure_f_old (f0:formula) =
  let pr= !print_formula in
  Debug.no_1 "simplify_pure_f_old" pr pr
    (fun _ -> simplify_pure_f_old_x f0) f0

and elim_exists_struc_preserve_pre_evars pre_evars0 (cf0: struc_formula) : struc_formula =
  let find_close_f svl0 f=
    let ( _,mf,_,_,_,_) = split_components f in
    let eqs = (MCP.ptr_equations_without_null mf)in
    find_close svl0 eqs
  in
  let rec helper pre_evars cf = match cf with
    | EList b  -> EList (map_l_snd (helper pre_evars) b)
    | ECase b  -> ECase {b with formula_case_branches = map_l_snd (helper pre_evars) b.formula_case_branches;}
    | EBase b  ->
      let qvars, base_f = split_quantifiers b.formula_struc_base in
      let cl_qvars = find_close_f qvars base_f in
      EBase {b with
             formula_struc_continuation = map_opt (helper (CP.remove_dups_svl  (pre_evars@cl_qvars)))
                 b.formula_struc_continuation; }
    | EAssume b ->
      let qvars, base_f = split_quantifiers b.formula_assume_simpl in
      let ( _,mf,_,_,_,_) = split_components base_f in
      let eqs = (MCP.ptr_equations_without_null mf) in
      let cl_qvars = find_close qvars eqs in
      let () = DD.ninfo_hprint (add_str "qvars" !CP.print_svl) qvars no_pos in
      let () = DD.ninfo_hprint (add_str "cl_qvars" !CP.print_svl) cl_qvars no_pos in
      let () = DD.ninfo_hprint (add_str "pre_evars" !CP.print_svl) pre_evars no_pos in
      let () = DD.ninfo_hprint (add_str "eqs" (pr_list (pr_pair !CP.print_sv !CP.print_sv))) eqs no_pos in
      let inter = CP.intersect_svl cl_qvars pre_evars in
      let sst = List.fold_left (fun r (sv1, sv2) ->
          if CP.mem_svl sv1 qvars && CP.mem_svl sv2 inter then r@[(sv1,sv2)] else r
        ) [] eqs in
      let n_qvars = CP.subst_var_list sst qvars in
      let n_base_f = simplify_pure_f (x_add subst sst base_f) in
      let () = DD.ninfo_hprint (add_str "n_qvars" !CP.print_svl) n_qvars no_pos in
      let () = DD.ninfo_hprint (add_str "n_base_f" !print_formula) n_base_f no_pos in
      EAssume {b with
               formula_assume_simpl = add_quantifiers  n_qvars n_base_f;
               formula_assume_struc = (helper pre_evars) b.formula_assume_struc;}
    | EInfer b -> EInfer {b with formula_inf_continuation = (helper pre_evars) b.formula_inf_continuation}
  in
  helper pre_evars0 cf0

and elim_exists_preserve (f0 : formula) rvars : formula = match f0 with
  | Or ({ formula_or_f1 = f1;
          formula_or_f2 = f2;
          formula_or_pos = pos}) ->
    let ef1 = elim_exists_preserve f1 rvars in
    let ef2 = elim_exists_preserve f2 rvars in
    mkOr ef1 ef2 pos
  | Base _ ->  f0
  | Exists ({
      formula_exists_qvars = qvar :: rest_qvars;
      formula_exists_heap = h;
      formula_exists_vperm = vps;
      formula_exists_pure = p;
      formula_exists_type = t;
      formula_exists_flow = fl;
      formula_exists_and = a;
      formula_exists_pos = pos }) ->
    let st, pp1 = MCP.get_subst_equation_memo_formula_vv p qvar in
    let r =
      let vp =
        if (List.length st = 1) then (
          let (sv1,sv2) = List.hd st in
          not (List.exists (fun sv ->
              (String.compare (CP.full_name_of_spec_var sv1) sv == 0) ||
              (String.compare (CP.full_name_of_spec_var sv2) sv == 0)) rvars))
        else false
      in
      if vp then
        let tmp = mkBase h pp1 vps t fl a pos in (*TO CHECK*)
        let new_baref = x_add subst st tmp in

        let tmp2 = add_quantifiers rest_qvars new_baref in

        let tmp3 = elim_exists_preserve tmp2 rvars in
        tmp3
      else (* if qvar is not equated to any variables, try the next one *)
        let tmp1 = mkExists rest_qvars h p vps t fl a pos in (*TO CHECK*)
        let tmp2 = elim_exists_preserve tmp1 rvars in
        let tmp3 = add_quantifiers [qvar] tmp2 in
        tmp3
    in r
  | Exists _ -> report_error no_pos ("Solver.elim_exists: Exists with an empty list of quantified variables")

and elim_exists_es_his_x (f0 : formula) (* (his:h_formula list) *) : formula(* *h_formula list *) =
  let rec helper f0 (* hfs *) (* ss_ref *)=
    match f0 with
    | Or ({
        formula_or_f1 = f1;
        formula_or_f2 = f2;
        formula_or_pos = pos }) ->
      let ef1(* , hfs1 *)(* ,ss_ref1 *) = helper f1 (* hfs *) (* ss_ref *) in
      let ef2(* ,hfs2 *) (* ,ss_ref2 *) = helper f2 (* hfs1 *) (* ss_ref1 *) in
      (mkOr ef1 ef2 pos (*, hfs2 *)(* ,ss_ref2 *))
    | Base _ -> (f0(* , hfs *))
    | Exists ({
        formula_exists_qvars = qvar :: rest_qvars;
        formula_exists_heap = h;
        formula_exists_vperm = vp;
        formula_exists_pure = p;
        formula_exists_type = t;
        formula_exists_flow = fl;
        formula_exists_and = a;
        formula_exists_pos = pos }) ->
      let st, pp1 = MCP.get_subst_equation_memo_formula_vv p qvar in
      let r(* ,n_hfs *) =
        if List.length st = 1 then
          let tmp = mkBase h pp1 vp t fl a pos in (*TO CHECK*)
          let new_baref = x_add subst st tmp in
          (* let new_hfs = List.map (h_subst st) hfs in *)
          (* let n_ss_ref = List.map (fun (sv1,sv2) -> (sv1, CP.subs_one st sv2)) ss_ref in *)
          let tmp2 = add_quantifiers rest_qvars new_baref in
          let tmp3(* ,new_hfs1 *)(* ,n_ss_ref1 *) = helper tmp2 (* new_hfs *) (* n_ss_ref *) in
          (tmp3(* ,new_hfs1 *)(* ,n_ss_ref1 *))
        else (* if qvar is not equated to any variables, try the next one *)
          let tmp1 = mkExists rest_qvars h p vp t fl a pos in (*TO CHECK*)
          let tmp2(* ,hfs1 *)(* ,ss_ref1 *) = helper tmp1 (* hfs *) (* ss_ref *) in
          let tmp3 = add_quantifiers [qvar] tmp2 in
          (tmp3(* ,hfs1 *)(* ,ss_ref1 *))
      in
      (r(* ,n_hfs *)(* ,n_ss_ref *))
    | Exists _ -> report_error no_pos ("Solver.elim_exists: Exists with an empty list of quantified variables")
  in
  helper f0 (* his *) (* subst_ref *)

and elim_exists_es_his (f0 : formula) (* (his:h_formula list) *) (* ss_ref *) : formula(* *h_formula list *) =
  let pr1 = pr_list !print_h_formula in
  (* let pr2 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in *)
  let pr_out = (* (pr_pair !print_formula pr1) *) !print_formula in
  Debug.no_1 "elim_exists_es_his"
    !print_formula  pr_out
    elim_exists_es_his_x f0

and formula_of_disjuncts (f:formula list) : formula=
  match f with
  | [] -> (mkTrue (mkTrueFlow()) no_pos)
  | x::xs -> List.fold_left (fun a c-> mkOr a c no_pos) x xs

and rename_struc_bound_vars ?(stk=None) (f:struc_formula):struc_formula = match f with
  | ECase b->
    (* let sst3 = List.map (fun v -> (v,(CP.fresh_spec_var v))) b.formula_case_exists in *)
    let f = ECase {b with (* formula_case_exists = (snd (List.split sst3)); *)
                   formula_case_branches = List.map (fun (c1,c2)-> ((Cpure.rename_top_level_bound_vars c1),(rename_struc_bound_vars ~stk:stk c2))) b.formula_case_branches;} in
    (* subst_struc  sst3  f *)
    f
  | EBase b->
    let sst1 = List.map (fun v -> (v,(CP.fresh_spec_var v))) b.formula_struc_explicit_inst in
    let sst2 = List.map (fun v -> (v,(CP.fresh_spec_var v))) b.formula_struc_implicit_inst in
    let sst3 = List.map (fun v -> (v,(CP.fresh_spec_var v))) b.formula_struc_exists in
    let () = match stk with
      | None -> ()
      | Some stk -> stk # push_list sst2 in
    let sst = sst1@sst2@sst3 in
    let f = EBase {b with
                   formula_struc_implicit_inst = (snd (List.split sst2));
                   formula_struc_explicit_inst = (snd (List.split sst1));
                   formula_struc_exists = (snd (List.split sst3));
                   formula_struc_base = rename_bound_vars b.formula_struc_base;
                   formula_struc_continuation = map_opt (rename_struc_bound_vars ~stk:stk) b.formula_struc_continuation; }in
    subst_struc sst f
  | EAssume b-> EAssume {b with
                         formula_assume_simpl = rename_bound_vars b.formula_assume_simpl;
                         formula_assume_struc = rename_struc_bound_vars ~stk:stk b.formula_assume_struc;}
  | EInfer b -> EInfer { b with formula_inf_continuation = rename_struc_bound_vars ~stk:stk b.formula_inf_continuation;}
  | EList b -> EList (map_l_snd (rename_struc_bound_vars ~stk:stk) b)

(* and rename_struc_bound_vars (f:struc_formula):struc_formula = *)
(*   let pr1 = !print_struc_formula in *)
(*   Debug.no_1 "rename_struc_bound_vars" pr1 pr1 *)
(*       (fun _ -> rename_struc_bound_vars_x f) f *)

and rename_bound_vars (f : formula) =
  let pr = !print_formula in
  let pr_out (f,_) = pr f in
  let res = Debug.no_1 "CF.rename_bound_vars" pr pr_out
      (fun _ -> rename_bound_vars_x f) f in
  fst res

and rename_bound_vars_with_subst (f : formula) = (rename_bound_vars_x f)

and rename_bound_vars_x (f : formula) = match f with
  | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) ->
    let rf1,l1 = rename_bound_vars_x f1 in
    let rf2,l2 = rename_bound_vars_x f2 in
    let resform = mkOr rf1 rf2 pos in
    resform,l1@l2
  | Base _ -> (f,[])
  | Exists _ ->
    let qvars, base_f = split_quantifiers f in
    (*filter out RelT and HpT*)
    let qvars = List.filter (fun sv -> not(CP.is_rel_all_var sv)) qvars in
    let new_qvars = CP.fresh_spec_vars qvars in
    (*--- 09.05.2000 *)
    (*let () = (print_string ("\n[cformula.ml, line 519]: fresh name = " ^ (string_of_spec_var_list new_qvars) ^ "!!!!!!!!!!!\n")) in*)
    (*09.05.2000 ---*)
    let rho = List.combine qvars new_qvars in
    let new_base_f = x_add subst rho base_f in (*TO CHECK*)
    let resform = add_quantifiers new_qvars new_base_f in
    (resform,rho)

and propagate_perm_formula (f : formula) (permvar:cperm_var) : formula =
  Debug.no_2 "propagate_perm_formula"
    !print_formula
    !print_spec_var
    !print_formula
    propagate_perm_formula_x f permvar

(*LDK: propagate permvar into view formula during UNFOLDING*)
and propagate_perm_formula_x (f : formula) (permvar:cperm_var) : formula = match f with
  | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) ->
    let rf1 = propagate_perm_formula_x f1 permvar in
    let rf2 = propagate_perm_formula_x f2 permvar in
    let resform = mkOr rf1 rf2 pos in
    resform
  | Base f1 ->
    let f1_heap,vars = propagate_perm_h_formula f1.formula_base_heap permvar in
    let base_p = f1.formula_base_pure in
    let mk_eq v = mkEq_cperm () v permvar no_pos in
    let mk_eqs = List.map mk_eq vars in
    let mk_BForm (b:CP.b_formula): CP.formula = CP.BForm (b,None) in
    let mk_eqs = List.map mk_BForm mk_eqs in
    let perm_p = List.fold_left (fun res v -> CP.mkAnd v res no_pos) (CP.mkTrue no_pos) mk_eqs in
    let perm_p = MCP.OnePF perm_p in
    let base_p = add_mix_formula_to_mix_formula perm_p base_p in
    Base({f1 with formula_base_heap = f1_heap; formula_base_pure = base_p})
  | Exists f1 ->
    let f1_heap,vars = propagate_perm_h_formula f1.formula_exists_heap permvar in
    let base_p = f1.formula_exists_pure in
    let mk_eq v = mkEq_cperm () v permvar no_pos in
    let mk_eqs = List.map mk_eq vars in
    let mk_BForm (b:CP.b_formula): CP.formula = CP.BForm (b,None) in
    let mk_eqs = List.map mk_BForm mk_eqs in
    let perm_p = List.fold_left (fun res v -> CP.mkAnd v res no_pos) (CP.mkTrue no_pos) mk_eqs in
    let perm_p = MCP.OnePF perm_p in
    let base_p = add_mix_formula_to_mix_formula perm_p base_p in
    Exists({f1 with
            formula_exists_qvars = List.append vars f1.formula_exists_qvars;
            formula_exists_heap = f1_heap;
            formula_exists_pure = base_p})

(*Spec_var list to creat pure constraints: freshvar = permvar*)
and propagate_perm_h_formula (f : h_formula) (permvar:cperm_var) : h_formula * (CP.spec_var list) =
  match f with
  | ViewNode f1 ->
    let fresh_var = fresh_cperm_var () permvar in
    let vn = ViewNode({f1 with h_formula_view_perm = Some (Cpure.Var (fresh_var,no_pos))}) in
    (vn,[fresh_var])
  | DataNode f1 ->
    let fresh_var = fresh_cperm_var () permvar in
    let dn = DataNode({f1 with h_formula_data_perm = Some (Cpure.Var (fresh_var,no_pos))}) in
    (dn,[fresh_var])
  | Star f1 ->
    let h1,xs1 = propagate_perm_h_formula f1.h_formula_star_h1 permvar in
    let h2,xs2 = propagate_perm_h_formula f1.h_formula_star_h2 permvar in
    let star = mkStarH h1 h2 f1.h_formula_star_pos in
    let xs = List.append xs1 xs2 in
    (star,xs)
  | Conj f1 ->
    let h1,xs1 = propagate_perm_h_formula f1.h_formula_conj_h1 permvar in
    let h2,xs2 = propagate_perm_h_formula f1.h_formula_conj_h2 permvar in
    let conj = mkConjH h1 h2 f1.h_formula_conj_pos in
    let xs = List.append xs1 xs2 in
    (conj,xs)
  | ConjStar f1 ->
    let h1,xs1 = propagate_perm_h_formula f1.h_formula_conjstar_h1 permvar in
    let h2,xs2 = propagate_perm_h_formula f1.h_formula_conjstar_h2 permvar in
    let conjstar = mkConjStarH h1 h2 f1.h_formula_conjstar_pos in
    let xs = List.append xs1 xs2 in
    (conjstar,xs)
  | ConjConj f1 ->
    let h1,xs1 = propagate_perm_h_formula f1.h_formula_conjconj_h1 permvar in
    let h2,xs2 = propagate_perm_h_formula f1.h_formula_conjconj_h2 permvar in
    let conjconj = mkConjConjH h1 h2 f1.h_formula_conjconj_pos in
    let xs = List.append xs1 xs2 in
    (conjconj,xs)
  | Phase f1 ->
    let h1,xs1 = propagate_perm_h_formula f1.h_formula_phase_rd permvar in
    let h2,xs2 = propagate_perm_h_formula f1.h_formula_phase_rw permvar in
    let phase = mkPhaseH h1 h2 f1.h_formula_phase_pos in
    let xs = List.append xs1 xs2 in
    (phase,xs)
  | _ -> (f,[])

(* type: struc_formula -> formula -> struc_formula *)
and rename_struc_clash_bound_vars (f1 : struc_formula) (f2 : formula) : struc_formula  =
  let pr1 = !print_struc_formula in
  let pr2 = !print_formula in
  Debug.no_2 "rename_struc_clash_bound_vars" pr1 pr2 pr1 rename_struc_clash_bound_vars_X f1 f2

(* -- 13.05.2008 *)
(* rename only those bound vars of f1 which clash with fv(f2) *)
(* return the new formula and the list of fresh names *)
and rename_struc_clash_bound_vars_X (f1 : struc_formula) (f2 : formula) : struc_formula  =  match f1 with
  | EAssume b -> EAssume {b with
                          formula_assume_simpl = fst (rename_clash_bound_vars b.formula_assume_simpl f2);
                          formula_assume_struc = rename_struc_clash_bound_vars b.formula_assume_struc f2;}
  | ECase b ->
    let r1 = List.map (fun (c1,c2) -> (c1,(rename_struc_clash_bound_vars c2 f2))) b.formula_case_branches in
    (* let new_exs = List.map (fun v -> (if (check_name_clash v f2) then (v,(CP.fresh_spec_var v)) else (v,v))) b.formula_case_exists in *)
    (* let rho = (List.filter (fun (v1,v2) -> (not (CP.eq_spec_var v1 v2))) new_exs) in *)
    ECase {(* formula_case_exists = (snd (List.split new_exs)); *)
      formula_case_branches = (* List.map (fun (c1,c2)-> ((Cpure.subst rho c1),(subst_struc rho c2))) *) r1;
      formula_case_pos = b.formula_case_pos}
  | EBase b ->
    (* let () = Debug.info_zprint (lazy  ("  b.formula_struc_implicit_inst " ^ (!CP.print_svl b.formula_struc_implicit_inst))) no_pos in *)
    (* let () = Debug.info_zprint (lazy  ("  b.formula_struc_explicit_inst " ^ (!CP.print_svl b.formula_struc_explicit_inst))) no_pos in *)
    let new_imp = List.map (fun v -> (if (check_name_clash v f2) &&
                                         not(CP.is_rel_all_var v) then (v,(CP.fresh_spec_var v)) else (v,v))) b.formula_struc_implicit_inst in
    let new_exp = List.map (fun v -> (if (check_name_clash v f2) then (v,(CP.fresh_spec_var v)) else (v,v))) b.formula_struc_explicit_inst in
    let new_exs = List.map (fun v -> (if (check_name_clash v f2) then (v,(CP.fresh_spec_var v)) else (v,v))) b.formula_struc_exists in
    (* fresh_qvars contains only the freshly generated names *)
    let rho_imp = (List.filter (fun (v1,v2) -> (not (CP.eq_spec_var v1 v2)))  new_imp) in
    let rho_exp = (List.filter (fun (v1,v2) -> (not (CP.eq_spec_var v1 v2)))  new_exp) in
    let rho_exs = (List.filter (fun (v1,v2) -> (not (CP.eq_spec_var v1 v2)))  new_exs) in
    let rho = rho_imp@rho_exp@rho_exs in
    EBase {b with
           formula_struc_implicit_inst = (snd (List.split new_imp));
           formula_struc_explicit_inst = (snd (List.split new_exp));
           formula_struc_exists = (snd (List.split new_exs));
           formula_struc_base = x_add subst rho (fst ( rename_clash_bound_vars b.formula_struc_base f2 ));
           formula_struc_continuation = map_opt (fun c-> rename_struc_clash_bound_vars (subst_struc rho c) f2) b.formula_struc_continuation;
          }
  | EInfer b -> EInfer {b with formula_inf_continuation = rename_struc_clash_bound_vars b.formula_inf_continuation f2}
  | EList b -> EList (map_l_snd (fun c->rename_struc_clash_bound_vars c f2) b)


and rename_clash_bound_vars (f1 : formula) (f2 : formula) : (formula * CP.spec_var list) = match f1 with
  | Or ({formula_or_f1 = or1; formula_or_f2 = or2; formula_or_pos = pos}) ->
    let (rf1, fvar1) = (rename_clash_bound_vars or1 f2) in
    let (rf2, fvar2) = (rename_clash_bound_vars or2 f2) in
    let resform = mkOr rf1 rf2 pos in
    (resform, fvar1@fvar2)
  | Base _ -> (f1, [])
  | Exists _ ->
    let qvars, base_f = split_quantifiers f1 in
    let new_qvars = (List.map (fun v -> (if (check_name_clash v f2) then (CP.fresh_spec_var v) else v)) qvars) in
    (* fresh_qvars contains only the freshly generated names *)
    let fresh_qvars = (List.filter (fun v1 -> (not (List.exists (fun v2 -> CP.eq_spec_var v1 v2) qvars)))  new_qvars) in
    let rho = List.combine qvars new_qvars in
    let new_base_f = x_add subst rho base_f in
    let resform = add_quantifiers new_qvars new_base_f in
    (resform, fresh_qvars)

and check_name_clash (v : CP.spec_var) (f : formula) : bool =
  let spec_vars = fv f in
  (*let () = print_string ("[cformula.ml, line 467]: Spec vars: " ^ (string_of_spec_var_list spec_vars) ^ "\n") in*)
  (List.exists (fun c -> (CP.eq_spec_var c v)) spec_vars)
(* 13.05.2008 -- *)

(* composition operator: it suffices to define composition in terms of  *)
(* the * operator, as the & operator is just a special case when one of *)
(* the term is pure                                                     *)

(* x+x' o[x'->fx] x'=x+1 --> x+fx & x'=fx+1 *)

(*transform history also*)
and compose_formula_new_x (delta : formula) (phi : formula) (x : CP.spec_var list) flow_tr (* history *) (pos : loc) =
  let rs = CP.fresh_spec_vars x in
  (*--- 09.05.2000 *)
  (*let () = (print_string ("\n[cformula.ml, line 533]: fresh name = " ^ (string_of_spec_var_list rs) ^ "!!!!!!!!!!!\n")) in*)
  (*09.05.2000 ---*)
  let rho1 = List.combine (List.map CP.to_unprimed x) rs in
  let rho2 = List.combine (List.map CP.to_primed x) rs in
  let new_delta = x_add subst rho2 delta in
  let new_phi = x_add subst rho1 phi in
  (* let new_history = List.map (h_subst rho2) history in *)
  let new_f = normalize_keep_flow new_delta new_phi flow_tr pos in
  let () = must_consistent_formula "compose_formula 1" new_f in
  let resform = push_exists rs new_f in
  let () = must_consistent_formula "compose_formula 2" resform in
  resform,(* new_history, *)rho2

and compose_formula_new (delta : formula) (phi : formula) (x : CP.spec_var list) flow_tr (* history *) (pos : loc) =
  let pr = !print_formula in
  let pr1 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
  Debug.no_3 "compose_formula_new" pr pr (!CP.print_svl) (pr_pair pr pr1)
    (fun _ _ _ -> compose_formula_new_x delta phi x flow_tr pos) delta phi x

and compose_formula_x (delta : formula) (phi : formula) (x : CP.spec_var list) flow_tr (pos : loc) =
  let rs = CP.fresh_spec_vars x in
  (*--- 09.05.2000 *)
  (*let () = (print_string ("\n[cformula.ml, line 533]: fresh name = " ^ (string_of_spec_var_list rs) ^ "!!!!!!!!!!!\n")) in*)
  (*09.05.2000 ---*)
  let rho1 = List.combine (List.map CP.to_unprimed x) rs in
  let rho2 = List.combine (List.map CP.to_primed x) rs in
  let new_delta = x_add subst rho2 delta in
  DD.info_zprint (lazy  ("   should not subst hprel old: " ^ (!print_formula phi))) pos;
  let new_phi = x_add subst rho1 phi in
  DD.info_zprint (lazy  ("   should not subst hprel new: " ^ (!print_formula new_phi))) pos;
  let new_f = normalize_keep_flow new_delta new_phi flow_tr pos in
  (* WN : this checking seems to be for debugging purpose of *)
  (*   MCP formulae  *)
  (* let () = must_consistent_formula "compose_formula 1" new_f in *)
  let resform = push_exists rs new_f in
  (* let () = must_consistent_formula "compose_formula 2" resform in *)
  resform

and compose_formula (delta : formula) (phi : formula) (x : CP.spec_var list) flow_tr (pos : loc) =
  let pr1 = !print_formula in
  let pr3 = !print_svl in
  Debug.no_3 "compose_formula" pr1 pr1 pr3 pr1 (fun _ _ _ -> compose_formula_x delta phi x flow_tr pos) delta phi x

(*compose formula when joined*)
and normalize_keep_flow_join (f1 : formula) (f2 : formula) flow_tr (pos : loc) = match f1 with
  | Or ({formula_or_f1 = o11; formula_or_f2 = o12; formula_or_pos = _}) ->
    let eo1 = normalize_x o11 f2 pos in
    let eo2 = normalize_x o12 f2 pos in
    mkOr eo1 eo2 pos
  | _ -> begin
      match f2 with
      | Or ({formula_or_f1 = o21; formula_or_f2 = o22; formula_or_pos = _}) ->
        let eo1 = normalize_x f1 o21 pos in
        let eo2 = normalize_x f1 o22 pos in
        mkOr eo1 eo2 pos
      | _ -> begin
          (*When join, need not rename exist vars*)
          (* let rf1 = rename_bound_vars f1 in *)
          (* let rf2 = rename_bound_vars f2 in *)
          let qvars1, base1 = split_quantifiers f1 in
          let qvars2, base2 = split_quantifiers f2 in
          let new_base = mkStar_combine base1 base2 flow_tr pos in
          let new_h, new_p, new_vp, new_fl, new_t, new_a = split_components new_base in
          (* let new_h = Immutable.normalize_field_ann_heap_node new_h in *)
          let resform = mkExists (qvars1 @ qvars2) new_h new_p new_vp new_t new_fl new_a pos in (* qvars[1|2] are fresh vars, hence no duplications *)
          resform
        end
    end

(*compose formula when joined*)
and compose_formula_join_x (delta : formula) (phi : formula) (x : CP.spec_var list) flow_tr (pos : loc) =
  let rs = CP.fresh_spec_vars x in
  (*--- 09.05.2000 *)
  (*let () = (print_string ("\n[cformula.ml, line 533]: fresh name = " ^ (string_of_spec_var_list rs) ^ "!!!!!!!!!!!\n")) in*)
  (*09.05.2000 ---*)
  let rho1 = List.combine (List.map CP.to_unprimed x) rs in
  let rho2 = List.combine (List.map CP.to_primed x) rs in
  let new_delta = x_add subst rho2 delta in
  let new_phi = x_add subst rho1 phi in
  let new_f = normalize_keep_flow_join new_delta new_phi flow_tr pos in
  let () = must_consistent_formula "compose_formula 1" new_f in
  let resform = push_exists rs new_f in
  let () = must_consistent_formula "compose_formula 2" resform in
  resform

(*compose formula when joined*)
(*Different from compose_formula
  due to the fact that do not rename
  existential variables because
  those variables belong to both
  formula*)
and compose_formula_join (delta : formula) (phi : formula) (x : CP.spec_var list) flow_tr (pos : loc) =
  let pr1 = !print_formula in
  let pr3 = !print_svl in
  Debug.no_3 "compose_formula" pr1 pr1 pr3 pr1 (fun _ _ _ -> compose_formula_join_x delta phi x flow_tr pos) delta phi x

and view_node_types (f:formula):ident list =
  let rec helper (f:h_formula):ident list =  match f with
    | Star b -> Gen.BList.remove_dups_eq (=) ((helper b.h_formula_star_h1)@(helper b.h_formula_star_h2))
    | ViewNode b -> [b.h_formula_view_name]
    | _ -> [] in
  match f with
  | Or b-> Gen.BList.remove_dups_eq (=) ((view_node_types b.formula_or_f1) @ (view_node_types b.formula_or_f2))
  | Base b -> helper b.formula_base_heap
  | Exists b -> helper b.formula_exists_heap

(*
  Other utilities.
*)

and get_var_type_x v (f: formula): (typ * bool) =
  let fv_list = fv f in
  let res_list = CP.remove_dups_svl (List.filter (fun c-> ((String.compare v (CP.name_of_spec_var c))==0)) fv_list) in
  match List.length res_list with
  | 0 -> (Void,false)
  | 1 -> (CP.type_of_spec_var (List.hd res_list),true)
  | _ -> Err.report_error { Err.error_loc = no_pos; Err.error_text = "could not find a coherent "^v^" type"}

and get_var_type v (f: formula): (typ * bool) =
  let pr2 = pr_pair string_of_typ string_of_bool in
  Debug.no_2 "get_var_type"
    pr_id !print_formula pr2
    (fun _ _ -> get_var_type_x v f) v f


and get_result_type (f: formula): (typ * bool) = get_var_type res_name f

and get_exc_result_type (f: formula): (typ * bool) = get_var_type eres_name f

and disj_count (f0 : formula) = match f0 with
  | Or ({formula_or_f1 = f1;
         formula_or_f2 = f2}) ->
    let c1 = disj_count f1 in
    let c2 = disj_count f2 in
    1 + c1 + c2

  | _ -> 1

let rec flatten_struc_formula sf =
  match sf with
  | EList el -> EList (List.map (fun (lbl,sf) -> (lbl, flatten_struc_formula sf)) el)
  | EBase eb1 -> (
      match eb1.formula_struc_continuation with
      | None -> sf
      | Some cont_f ->
        let new_cont_f = flatten_struc_formula cont_f in
        flatten_struc_formula_base eb1 new_cont_f
        (* match new_cont_f with                                                    *)
        (* | EBase eb2 ->                                                           *)
        (*   let f1 = eb1.formula_struc_base in                                     *)
        (*   let f2 = eb2.formula_struc_base in                                     *)
        (*   let h1, p1, vp1, fl1, t1, a1 = split_components f1 in                  *)
        (*   let h2, p2, vp2, fl2, t2, a2 = split_components f2 in                  *)
        (*   if ((is_empty_heap h1) || (is_empty_heap h2)) then                     *)
        (*     let h = if (is_empty_heap h1) then h2 else h1 in                     *)
        (*     let p,_ = combine_and_pure f1 p1 p2 in                               *)
        (*     let vp = CVP.merge_vperm_sets [vp1; vp2] in                          *)
        (*     let t = mkAndType t1 t2 in                                           *)
        (*     let fl = mkAndFlow fl1 fl2 Flow_combine in                           *)
        (*     let a = a1@a2 in                                                     *)
        (*     let new_base = mkBase h p vp t fl a no_pos in                        *)
        (*     EBase { eb1 with                                                     *)
        (*            formula_struc_base = new_base;                                *)
        (*            formula_struc_continuation = eb2.formula_struc_continuation } *)
        (*   else sf                                                                *)
        (* | _ -> EBase {eb1 with formula_struc_continuation = Some new_cont_f}     *)
    )
  | EInfer ei -> (* flatten_struc_formula ei.formula_inf_continuation *)
    (* Add back EInfer to prevent lost information after @post *)
    EInfer { ei with formula_inf_continuation = flatten_struc_formula ei.formula_inf_continuation }
  | ECase ec -> ECase { ec with
        formula_case_branches = List.map (fun (c, sf) -> (c, flatten_struc_formula sf)) ec.formula_case_branches }
  | EAssume _ -> sf

and flatten_struc_formula_base eb1 sf =
  match sf with
  | EBase eb2 ->
    let f1 = eb1.formula_struc_base in
    let f2 = eb2.formula_struc_base in
    let h1, p1, vp1, fl1, t1, a1 = split_components f1 in
    let h2, p2, vp2, fl2, t2, a2 = split_components f2 in
    if ((is_empty_heap h1) || (is_empty_heap h2)) then
      let h = if (is_empty_heap h1) then h2 else h1 in
      let p, _ = combine_and_pure f1 p1 p2 in
      let vp = CVP.merge_vperm_sets [vp1; vp2] in
      let t = mkAndType t1 t2 in
      let fl = mkAndFlow fl1 fl2 Flow_combine in
      let a = a1@a2 in
      let new_base = mkBase h p vp t fl a no_pos in
      flatten_struc_formula (EBase { eb1 with
             formula_struc_base = new_base;
             formula_struc_continuation = eb2.formula_struc_continuation })
    else EBase eb1
  | EInfer ei -> EInfer { ei with
        formula_inf_continuation = flatten_struc_formula_base eb1 ei.formula_inf_continuation }
  | _ -> EBase { eb1 with formula_struc_continuation = Some sf }

let flatten_struc_formula sf =
  Debug.no_1 "flatten_struc_formula"
    !print_struc_formula !print_struc_formula
    flatten_struc_formula sf

(***************INFER******************)
(*(*intermediary structure for heap predicate inference, stores a constraint on heap predicates*)
  (*    used in the context fields: es_infer_hp_rel and returned by various methods in particular*)
  (*	check_specs_infer*)*)

(* guard *)
type formula_guard = formula * (formula option)
type formula_guard_list = formula_guard list

type hprel_infer_type = INFER_UNKNOWN | INFER_UNFOLD | INFER_FOLD
                (* | I_FOLD_LARGE | I_UNFOLD_LARGE  *)
type hprel = {
  hprel_kind: CP.rel_cat;
  unk_svl: CP.spec_var list; (* unknown and dangling *)
  unk_hps:(CP.spec_var*CP.spec_var list) list; (* not needed *)
  predef_svl: CP.spec_var list; (* not needed *)
  hprel_lhs: formula;
  hprel_guard: formula option;
  (* capture the ctx when we want to capture relations *)
  (* of more than one field. ususally it is heap nodes *)
  (* guard is used in unfolding pre-preds              *)
  hprel_type: hprel_infer_type;
  hprel_unknown: CP.spec_var list; (* the unknown vars inferred *)
  hprel_rhs: formula;
  hprel_path: cond_path_type;
  hprel_proving_kind: Others.proving_kind;
  hprel_flow: nflow list;
  (* hprel_fold: bool; *)
}


(*seems to be finished inferred relations, used in the rel_def_stk structure*)
(*although that stack seems more internal to the inference than anything else, *)
(*the results are never picked from the stack, rather they are returned by the inference method*)
and hprel_def= {
  hprel_def_kind: CP.rel_cat;
  hprel_def_hrel: h_formula; (* LHS *)
  hprel_def_guard:  formula option;
  hprel_def_body: (cond_path_type * (formula option) * (nflow option)) list; (* RHS *)
  (* hprel_def_body: (cond_path_type * (formula_guard list)) list; (\* RHS *\) *)
  hprel_def_body_lib: (formula * (nflow option)) list; (* reuse of existing pred *)
  (* hprel_def_path: cond_path_type; *)
  hprel_def_flow: nflow option;
}

(*temporal: name * hrel * guard option * definition body*)
(*actually used to store the constraints on heap predicates inference*)
and hp_rel_def_old = CP.rel_cat * h_formula * (formula option) * formula

(* and hp_rel_def = CP.rel_cat * h_formula * (formula option) * (formula_guard list) *)

and hp_rel_def = {
  def_cat : CP.rel_cat;
  def_lhs : h_formula;
  def_rhs : ((* cond_path_type * *) formula_guard) list;
  def_flow: nflow option;
}
(*  SHAPE ANALYSIS stages *)
(* hprel --synthesis--> hp_rel_def --normalization-->  hprel_def *)
    (* hprel_def -trans--> view_decl *)

(* to convert to using hp_rel_def_new *)

(* and infer_rel_type =  (CP.rel_cat * CP.formula * CP.formula) *)
and infer_state = {
  is_constrs : hprel list; (*current processing*)
  is_all_constrs : hprel list;
  is_link_hpargs : (CP.spec_var * CP.spec_var list) list;
  is_dang_hpargs : (CP.spec_var * CP.spec_var list) list;
     (*dangling hps = link hps = unknown. to remove one of them*)
  is_unk_map: ((CP.spec_var * int list)  * CP.xpure_view) list ;
    (* unk_map : obsolete? *)
  is_sel_hps: CP.spec_var list;
  is_post_hps: CP.spec_var list;
  is_prefix_hps: CP.spec_var list;
  is_cond_path: cond_path_type;
  is_flow: nflow;
  is_hp_equivs: (CP.spec_var*CP.spec_var) list;
  is_hp_defs: hp_rel_def list;
}

let print_hprel_def_short = ref (fun (c: hprel_def) -> "printer has not been initialized")

let print_hprel_short = ref (fun (c: hprel) -> "printer has not been initialized")

let print_hprel_list_short = ref (fun (c: hprel list) -> "printer has not been initialized")

(* outcome from shape_infer *)
let rel_def_stk : hprel_def Gen.stack_pr = new Gen.stack_pr "rel_def (shape-infer)"
  !print_hprel_def_short (==)

let print_flow = ref(fun (c:nflow) -> "printer not initialized")

let partition_hprel_flow_x constrs0=
  let rec helper constrs res=
    match constrs with
    | [] -> res
    | rel::rest -> begin
        let (same_part), rest1 = List.partition (fun rel1 ->
            match rel.hprel_flow,rel1.hprel_flow with
            | [(fl1)],[fl2] -> equal_flow_interval fl1 fl2
            | _ -> true
          ) rest in
        let fl = match rel.hprel_flow with
          | [] -> !norm_flow_int
          | a::_ -> a
        in
        helper rest1 (res@[(rel::same_part,fl)])
      end
  in
  helper constrs0 []

let partition_hprel_flow constrs0=
  let pr1 = pr_list_ln !print_hprel_short in
  let pr2 = pr_list_ln (pr_pair pr1 !print_flow) in
  Debug.no_1 "partition_hprel_flow" pr1 pr2
    (fun _ -> partition_hprel_flow_x constrs0) constrs0

(*for drop non-selective subformulas*)
let check_hp_arg_eq (hp1, args1) (hp2, args2)=
  ((CP.eq_spec_var hp1 hp2) && (CP.eq_spec_var_order_list args1 args2))

(*check a data node does not belong to a set of data node name*)
let check_nbelongsto_dnode dn dn_names=
  List.for_all (fun dn_name -> not(CP.eq_spec_var dn.h_formula_data_node dn_name)) dn_names

(*check a view node does not belong to a set of view node name*)
let check_nbelongsto_vnode vn vn_names=
  List.for_all (fun vn_name -> not(CP.eq_spec_var vn.h_formula_view_node vn_name)) vn_names

let check_neq_hpargs id ls=
  not (Gen.BList.mem_eq check_hp_arg_eq id ls)


(*check a data node belongs to a list of data node names*)
let select_dnode dn1 dn_names=
  List.exists (CP.eq_spec_var dn1.h_formula_data_node) dn_names

(*check a view node belongs to a list of view node names*)
let select_vnode vn1 vn_names=
  (*return subst of args and add in lhs*)
  List.exists (CP.eq_spec_var vn1.h_formula_view_node) vn_names

let check_neq_hrelnode id ls=
  not (CP.mem_svl id ls)

let to_new_hp_rel_def (r,hf,g,f) =
  { def_cat = r;
    def_lhs = hf;
    def_rhs = [(f,g)];
    def_flow = None;
  }

let from_new_hp_rel_def d : hp_rel_def_old =
  match d with
    { def_cat = r;
      def_lhs = hf;
      def_rhs = rhs;
      def_flow = fl;
    } -> (r,hf,None,fst (List.hd rhs))

let flatten_hp_rel_def_wo_guard def=
  (def.def_cat, def.def_lhs, formula_of_disjuncts (List.map fst def.def_rhs))

let rec look_up_hpdef hpdefs hp0=
  match hpdefs with
  | [] -> raise Not_found
  | hpdef::rest -> begin
      match hpdef.hprel_def_kind with
      | CP.HPRelDefn (hp,_,_) -> if CP.eq_spec_var hp hp0 then (hpdef)
        else look_up_hpdef rest hp0
      | _ -> look_up_hpdef rest hp0
    end

let rec look_up_hpdef_with_remain hpdefs hp0 done_hpdefs=
  match hpdefs with
  | [] -> raise Not_found
  | hpdef::rest -> begin
      match hpdef.hprel_def_kind with
      | CP.HPRelDefn (hp,_,_) -> if CP.eq_spec_var hp hp0 then (hpdef,done_hpdefs@rest)
        else look_up_hpdef_with_remain rest hp0 (done_hpdefs@[hpdef])
      | _ -> look_up_hpdef_with_remain rest hp0 (done_hpdefs@[hpdef])
    end

let rec look_up_hp_def hp_defs hp0=
  match hp_defs with
  | [] -> raise Not_found
  | (hp_def)::rest -> begin
      match hp_def.def_cat with
      | CP.HPRelDefn (hp,_,_) -> if CP.eq_spec_var hp hp0 then hp_def
        else look_up_hp_def rest hp0
      | _ -> look_up_hp_def rest hp0
    end

let rec look_up_hp_def_with_remain hp_defs hp0 done_hpdefs=
  match hp_defs with
  | [] -> raise Not_found
  | (hp_def)::rest -> begin
      match hp_def.def_cat with
      | CP.HPRelDefn (hp,_,_) -> if CP.eq_spec_var hp hp0 then (hp_def,done_hpdefs@rest)
        else look_up_hp_def_with_remain rest hp0 (done_hpdefs@[hp_def])
      | _ -> look_up_hp_def_with_remain rest hp0 (done_hpdefs@[hp_def])
    end

let is_unknown_f_x f0=
  let rec helper f=  match f with
    | Base fb ->
      (is_unknown_heap fb.formula_base_heap) &&
      (CP.isConstTrue (MCP.pure_of_mix fb.formula_base_pure))
    | Exists _ -> let _, base1 = split_quantifiers f in
      helper base1
    | Or {formula_or_f1 = o11; formula_or_f2 = o12;} -> (helper o11) && (helper o12)
  in
  helper f0

let is_unknown_f f=
  let pr1 = !print_formula in
  Debug.no_1 "is_unknown_f" pr1 string_of_bool
    (fun _ -> is_unknown_f_x f) f

let is_htrue_or_unknown hf unk_hps=
  match hf with
    | HTrue -> true
    | HRel (hp,_,_) -> CP.mem_svl hp unk_hps
    | _ -> false

let is_htrue_or_unknown_x f0 unk_hps=
  let rec helper f=  match f with
    | Base fb ->
      (is_htrue_or_unknown fb.formula_base_heap unk_hps) &&
      (CP.isConstTrue (MCP.pure_of_mix fb.formula_base_pure))
    | Exists _ -> let _, base1 = split_quantifiers f in
      helper base1
    | Or {formula_or_f1 = o11; formula_or_f2 = o12;} -> (helper o11) && (helper o12)
  in
  helper f0

let is_htrue_or_unknown f0 unk_hps=
  let pr1 = !print_formula in
  let pr2 = !CP.print_svl in
  Debug.no_2 "is_htrue_or_unknown" pr1 pr2 string_of_bool
      (fun _ _ -> is_htrue_or_unknown_x f0 unk_hps) f0 unk_hps

let get_hpdef_name hpdef=
  match hpdef with
  | CP.HPRelDefn (hp,_,_) -> hp
  (* | CP.HPRelNDefn hp -> hp *)
  | _ -> report_error no_pos "sau.get_hpdef_name"

let get_hpdef_name_w_tupled hpdef=
  match hpdef with
  | CP.HPRelDefn (hp,_,_) -> [hp]
  | CP.HPRelLDefn hps -> hps
  | _ -> []

let subst_opt ss f_opt=
  match f_opt with
  | None -> None
  | Some f -> Some (x_add subst ss f)

let h_subst_opt ss hf_opt=
  match hf_opt with
  | None -> None
  | Some hf -> Some (h_subst ss hf)

let subst_hpdef ss hpdef=
  let n_guard = subst_opt ss hpdef.hprel_def_guard in
  let n_body = List.map (fun (p, f_opt, flow) -> (p, subst_opt ss f_opt, flow)) hpdef.hprel_def_body in
  { hpdef with
    hprel_def_guard = n_guard;
    hprel_def_body = n_body;
  }

let subst_hprel_constr sst hprel =
  let sst = List.filter (fun (fr, t) -> not (CP.eq_spec_var fr t)) sst in
  if is_empty sst then hprel
  else
    let fr, t = List.split sst in
    let all_fv = (fv hprel.hprel_lhs) @ (fv hprel.hprel_rhs) @
      (match hprel.hprel_guard with None -> [] | Some g -> fv g)
    in
    let subst_f f =
      (* Name clashing *)
      let clashed_svl = Gen.BList.intersect_eq CP.eq_spec_var t all_fv in
      if is_empty clashed_svl then subst sst f
      else
        let fresh_svl = CP.fresh_spec_vars clashed_svl in
        let avoid_clash_sst = List.combine clashed_svl fresh_svl in
        subst sst (subst avoid_clash_sst f)
    in
    let n_guard = map_opt subst_f hprel.hprel_guard in
    let n_lhs = subst_f hprel.hprel_lhs in
    let n_rhs = subst_f hprel.hprel_rhs in
    { hprel with
      hprel_lhs = n_lhs;
      hprel_rhs = n_rhs;
      hprel_guard = n_guard; }

let subst_hprel_constr sst hprel =
  let pr1 = !print_hprel_short in
  let pr2 = !CP.print_sv in
  let pr3 = pr_list (pr_pair pr2 pr2) in
  Debug.no_2 "subst_hprel_constr" pr1 pr3 pr1
    (fun _ _ -> subst_hprel_constr sst hprel) hprel sst

let hp_def_cmp (d1:hp_rel_def) (d2:hp_rel_def) =
  try
    let hp1 = get_hpdef_name d1.def_cat in
    try
      let hp2 = get_hpdef_name d2.def_cat in
      String.compare (CP.name_of_spec_var hp1) (CP.name_of_spec_var hp2)
    with _ -> 1
  with _ -> -1

let hpdef_cmp d1 d2 =
  try
    let hp1 = get_hpdef_name d1.hprel_def_kind in
    try
      let hp2 = get_hpdef_name d2.hprel_def_kind in
      String.compare (CP.name_of_spec_var hp1) (CP.name_of_spec_var hp2)
    with _ -> 1
  with _ -> -1

let mk_hp_rel_def hp (args, r, paras) (g: formula option) f ofl pos=
  let hf = HRel (hp, List.map (fun x -> CP.mkVar x no_pos) args, pos) in
  { def_cat= (CP.HPRelDefn (hp, r, paras));
    def_lhs =hf;
    def_rhs = [(f,g)];
    def_flow = ofl;
  }

let mk_hp_rel_def1 c lhs rhs ofl=
  { def_cat= c;
    def_lhs = lhs;
    def_rhs = rhs;
    def_flow = ofl;
  }

let mkHprel ?(fold_type=false) ?(infer_type=INFER_UNKNOWN) knd u_svl u_hps pd_svl hprel_l (hprel_g: formula option) hprel_r hprel_p=
  {  hprel_kind = knd;
     hprel_type = infer_type;
     hprel_unknown = [];
     unk_svl = u_svl;
     unk_hps = u_hps ;
     predef_svl = pd_svl;
     hprel_lhs = hprel_l;
     hprel_guard = hprel_g;
     hprel_rhs = hprel_r;
     hprel_path = hprel_p;
     hprel_proving_kind = Others.find_impt_proving_kind ();
     (* hprel_fold = fold_type; *)
     hprel_flow = [!norm_flow_int];
  }

let mkHprel_w_flow ?(fold_type=false) ?(infer_type=INFER_UNKNOWN) knd u_svl u_hps pd_svl hprel_l (hprel_g: formula option) hprel_r hprel_p nflow=
  {  hprel_kind = knd;
     hprel_type = infer_type;
     hprel_unknown = [];
     unk_svl = u_svl;
     unk_hps = u_hps ;
     predef_svl = pd_svl;
     hprel_lhs = hprel_l;
     hprel_guard = hprel_g;
     hprel_rhs = hprel_r;
     hprel_path = hprel_p;
     hprel_proving_kind = Others.find_impt_proving_kind ();
     (* hprel_fold = fold_type; *)
     hprel_flow = [nflow];
  }

let mkHprel_1 ?(fold_type=false) knd hprel_l hprel_g hprel_r hprel_p =
  mkHprel ~fold_type:fold_type knd [] [] [] hprel_l hprel_g hprel_r hprel_p

let mk_hprel_def kind hprel (guard_opt: formula option) path_opf opflib optflow_int=
  let libs = match opflib with
    | None -> []
    | Some f -> [(f, optflow_int)]
  in
  let body = List.map (fun (a,f) -> (a,f, optflow_int)) path_opf in
  {
    hprel_def_kind = kind;
    hprel_def_hrel = hprel;
    hprel_def_guard = guard_opt;
    hprel_def_body =  body;
    hprel_def_body_lib = libs;
    hprel_def_flow = optflow_int;
    (* hprel_fold = fold_type; *)
  }

(* let mk_hprel_fold kind hprel (guard_opt: formula option) path_opf opflib optflow_int = *)
(*   mk_hprel_def ~fold_type:true kind hprel (guard_opt: formula option) path_opf opflib optflow_int  *)

let pr_h_formula_opt og=
  match og with
  | None -> ""
  | Some hf -> !print_h_formula hf

let is_HRel hf=
  match hf with
  | HRel _ -> true
  | _ -> false

let is_HRel_f (f0:formula) =
  let rec helper f=
    match f with
    | Base ({ formula_base_heap = h1;})
    | Exists ({formula_exists_heap = h1;}) ->
      (
        is_HRel h1
      )
    | Or orf  ->
      (helper orf.formula_or_f1) && (helper orf.formula_or_f2)
  in
  helper f0


let struc_elim_exist_x (f0 : struc_formula): struc_formula =
  let rec helper f=
    match f with
    | ECase b -> let r1 = List.map (fun (c1,c2) -> (c1, helper c2)) b.formula_case_branches in
      ECase {b with formula_case_branches = r1}
    | EBase b -> EBase {b with  formula_struc_base = elim_exists b.formula_struc_base;
                                formula_struc_continuation = map_opt (helper) b.formula_struc_continuation;}
    | EAssume b -> EAssume {b with formula_assume_simpl = elim_exists b.formula_assume_simpl;
                                   formula_assume_struc = helper b.formula_assume_struc
                           }
    | EInfer b -> EInfer { b with formula_inf_continuation = helper b.formula_inf_continuation;}
    | EList b -> EList (map_l_snd (helper) b)
  in
  helper f0

let struc_elim_exist (f0 : struc_formula): struc_formula =
  let pr1 = !print_struc_formula in
  Debug.no_1 "struc_elim_exist" pr1 pr1
    (fun _ -> struc_elim_exist_x f0) f0

let map_heap_hf_1 fn hf0=
  let rec helper hf=
    match hf with
    | Star { h_formula_star_h1 = hf1;
             h_formula_star_h2 = hf2;}
    |  Conj { h_formula_conj_h1 = hf1;
              h_formula_conj_h2 = hf2;}
    | Phase { h_formula_phase_rd = hf1;
              h_formula_phase_rw = hf2;}
    | StarMinus { h_formula_starminus_h1 = hf1;
                  h_formula_starminus_h2 = hf2;}
    | ConjStar { h_formula_conjstar_h1 = hf1;
                 h_formula_conjstar_h2 = hf2;}
    | ConjConj { h_formula_conjconj_h1 = hf1;
                 h_formula_conjconj_h2 = hf2;} ->
      (helper hf1)@(helper hf2)
    | _ -> fn hf
  in
  helper hf0

let map_heap_1 fn f0=
  let rec helper f=
    match f with
    | Base ({ formula_base_heap = h1;})
    | Exists ({formula_exists_heap = h1;}) ->
      map_heap_hf_1 fn h1
    | Or orf  ->
      (helper orf.formula_or_f1) @ (helper orf.formula_or_f2)
  in
  helper f0


let trans_heap_hf fn hf0=
  let rec helper hf=
    match hf with
    | Star { h_formula_star_h1 = hf1;
             h_formula_star_h2 = hf2;
             h_formula_star_pos = pos} ->
      Star {h_formula_star_h1 = helper hf1;
            h_formula_star_h2 = helper hf2;
            h_formula_star_pos = pos}
    |  Conj { h_formula_conj_h1 = hf1;
              h_formula_conj_h2 = hf2;
              h_formula_conj_pos = pos} ->
      Conj { h_formula_conj_h1 = helper hf1;
             h_formula_conj_h2 = helper hf2;
             h_formula_conj_pos = pos}
    | Phase { h_formula_phase_rd = hf1;
              h_formula_phase_rw = hf2;
              h_formula_phase_pos = pos} ->
      Phase { h_formula_phase_rd = helper hf1;
              h_formula_phase_rw = helper hf2;
              h_formula_phase_pos = pos}
    | StarMinus { h_formula_starminus_h1 = hf1;
                  h_formula_starminus_h2 = hf2;
                  h_formula_starminus_aliasing = a;
                  h_formula_starminus_pos = pos} ->
      StarMinus { h_formula_starminus_h1 = helper hf1;
                  h_formula_starminus_h2 = helper hf2;
                  h_formula_starminus_aliasing = a;
                  h_formula_starminus_pos = pos}
    | ConjStar { h_formula_conjstar_h1 = hf1;
                 h_formula_conjstar_h2 = hf2;
                 h_formula_conjstar_pos =pos } ->
      ConjStar { h_formula_conjstar_h1 = helper hf1;
                 h_formula_conjstar_h2 = helper hf2;
                 h_formula_conjstar_pos =pos }
    | ConjConj { h_formula_conjconj_h1 = hf1;
                 h_formula_conjconj_h2 = hf2;
                 h_formula_conjconj_pos = pos } ->
      ConjConj { h_formula_conjconj_h1 = helper hf1;
                 h_formula_conjconj_h2 = helper hf2;
                 h_formula_conjconj_pos = pos }
    | _ -> fn hf
  in
  helper hf0

let trans_heap fn f0=
  let rec helper f=
    match f with
    | Base fb -> Base {fb with formula_base_heap = trans_heap_hf fn fb.formula_base_heap}
    | Exists fe -> Exists {fe with formula_exists_heap = trans_heap_hf fn fe.formula_exists_heap}
    | Or orf -> Or {orf with formula_or_f1 = helper orf.formula_or_f1;
                             formula_or_f2 = helper orf.formula_or_f2
                   }
  in
  helper f0

let get_HRel hf=
  match hf with
  | HRel (hp, eargs, _ ) -> Some (hp, List.concat (List.map CP.afv eargs))
  | _ -> None

let extract_HRel hf=
  match hf with
  | HRel (hp, eargs, _ ) -> (hp, List.concat (List.map CP.afv eargs))
  | _ -> raise SA_HP_NOT_PRED

let extract_HRel_f (f0:formula) =
  let rec helper f=
    match f with
    | Base ({ formula_base_heap = h1;})
    | Exists ({formula_exists_heap = h1;}) ->
      (
        extract_HRel h1
      )
    | _ -> raise SA_HP_NOT_PRED
  in
  helper f0

let extract_unk_hprel_x (f0:formula) =
  let rec helper f=
    match f with
    | Base ({ formula_base_pure = p1;
              formula_base_heap = h1;})
    | Exists ({ formula_exists_pure = p1;
                formula_exists_heap = h1;}) ->
      (
        if  not (is_unknown_heap h1) then
          let p2 = (MCP.pure_of_mix p1) in
          if (CP.isConstTrue p2 || CP.is_xpure p2) then
            match h1 with
            | HRel (hp, _, _ ) -> [hp]
            | _ -> report_error no_pos "CF.extract_unk_hprel_f: 1"
          else
            report_error no_pos "CF.extract_unk_hprel_f: 2"
        else []
      )
    | Or {formula_or_f1 = f1;
          formula_or_f2 = f2} ->
      (helper f1) @ (helper f2)
  in
  helper f0

let extract_unk_hprel (f0:formula) =
  let pr1 = !print_formula in
  let pr2 = !CP.print_svl in
  Debug.no_1 "extract_unk_hprel" pr1 pr2
    (fun _ ->  extract_unk_hprel_x f0) f0

(* WN : This needs to extract a list of hprel, and return its residue *)
let extract_hrel_head (f0:formula) =
  let rec helper f=
    match f with
    | Base ({ formula_base_pure = p1;
              formula_base_heap = h1;})
    | Exists ({ formula_exists_pure = p1;
                formula_exists_heap = h1;}) ->
      (
        (* Why the need to check for p2? *)
        (* let p2 = (MCP.pure_of_mix p1) in *)
        (* if (CP.isConstTrue p2 || CP.is_xpure p2) then *)
          match h1 with
          | HRel (hp, _, _ ) -> Some (hp)
          | _ -> None
        (* else *)
        (*   None *)
      )
    | Or _ -> None
  in
  helper f0

let extract_hrel_head (f0:formula) =
  Debug.no_1 "extract_hrel_head" !print_formula (pr_option !CP.print_sv) extract_hrel_head f0

let extract_hrel_head_w_args (f0:formula) =
  let rec helper f=
    match f with
    | Base ({ formula_base_pure = p1;
              formula_base_heap = h1;})
    | Exists ({ formula_exists_pure = p1;
                formula_exists_heap = h1;}) ->
      (
        let p2 = (MCP.pure_of_mix p1) in
        if (CP.isConstTrue p2 || CP.is_xpure p2) then
          match h1 with
          | HRel (hp, eargs, _ ) -> Some (hp,List.concat (List.map CP.afv eargs))
          | _ -> None
        else
          None
      )
    | Or _ -> None
  in
  helper f0

let extract_hrel_head_w_args (f0:formula) =
  let pr1 = !print_formula in
  let pr2 a = match a with None -> "None"
                         | Some (hp, args) -> let pr = pr_pair !CP.print_sv !CP.print_svl in
                           pr (hp,args)
  in
  Debug.no_1 "extract_hrel_head_w_args" pr1 pr2
    (fun _ ->  extract_hrel_head_w_args f0) f0

let is_top_guard rhs link_hps og=
  let hp_opt = extract_hrel_head rhs in
  match hp_opt with
  | None -> false
  | Some (hp) -> CP.mem_svl hp link_hps (*CF.isStrictConstHTrue cs.CF.hprel_rhs*)
                 && (og != None)

let is_only_viewnode_x acc_pure (f0:formula) =
  let rec helper f=
    match f with
    | Base ({ formula_base_pure = p1;
              formula_base_heap = h1;})
    | Exists ({ formula_exists_pure = p1;
                formula_exists_heap = h1;}) ->
      (
        let p2 = (MCP.pure_of_mix p1) in
        if acc_pure || (CP.isConstTrue p2 ) then
          match h1 with
          | ViewNode hv -> Some hv
          | _ -> None
        else
          None
      )
    | Or _ -> None
  in
  helper f0

let is_only_viewnode acc_pure (f0:formula) =
  let pr1 = !print_formula in
  let pr2 ovn = match ovn with
    | Some vn -> !print_h_formula (ViewNode vn)
    | None -> "None"
  in
  Debug.no_2 "is_only_viewnode" string_of_bool pr1 pr2
    (fun _ _ -> is_only_viewnode_x acc_pure f0)
    acc_pure f0

let extract_hprel_pure (f0:formula) =
  let rec helper f=
    match f with
    | Base ({ formula_base_pure = p1;
              formula_base_heap = h1;})
    | Exists ({ formula_exists_pure = p1;
                formula_exists_heap = h1;}) ->
      (
        let p2 = (MCP.pure_of_mix p1) in
        match h1 with
        | HRel (hp, eargs, _ ) -> Some (hp, List.concat (List.map CP.afv eargs), p2)
        | _ -> None
      )
    | Or _ -> report_error no_pos "CF.extract_hprel_pure 1"
  in
  helper f0

let get_xpure_view (f0:formula) =
  let rec helper f=
    match f with
    | Base ({ formula_base_pure = p1;})
    | Exists ({ formula_exists_pure = p1;}) ->
      (
        CP.get_xpure (MCP.pure_of_mix p1)
      )
    | Or {formula_or_f1 = f1;
          formula_or_f2 = f2} ->
      (helper f1) @ (helper f2)
  in
  helper f0

let rec look_up_ptr_args_data_node_x hd=
  List.filter CP.is_node_typ hd.h_formula_data_arguments
(*data nodes*)
(* let data_def =  C.look_up_data_def no_pos prog.C.prog_data_decls hd.CF.h_formula_data_name in *)
(* (\*get prototype of a node declaration*\) *)
(* let args = List.map (fun (t,_) -> t) data_def.C.data_fields in *)
(* (\*combine with actual areg*\) *)
(* let targs = List.combine args hd.CF.h_formula_data_arguments in *)
(* (\*get pointer*\) *)
(* snd (List.split (List.filter (fun (t, v) -> is_pointer t) targs)) *)

and look_up_ptr_args_data_node hd=
  let pr1 = fun dn -> dn.h_formula_data_name in
  Debug.no_1 " look_up_ptr_args_data_node" pr1 !CP.print_svl
    (fun _ ->  look_up_ptr_args_data_node_x hd) hd

(* let loop_up_ptr_args_view_node prog hv= *)
(*   (\*view node*\) *)
(*   let view_def = x_add Cast.look_up_view_def no_pos prog.Cast.prog_view_decls hv.CF.h_formula_view_name in *)
(*   (\*get prototype of a node declaration*\) *)
(*   let args = List.map (fun (t,_) -> t) view_def.Cast.view_fields in *)
(*   (\*combine with actual areg*\) *)
(*   let targs = List.combine args hd.CF.h_formula_view_arguments in *)
(*   (\*get pointer*\) *)
(*   snd (List.split (List.filter (fun (t, v) -> is_pointer t) targs)) *)
let rec look_up_data_node ls node_name=
  match ls with
  | [] -> []
  | dn::ds ->
    if CP.eq_spec_var node_name dn.h_formula_data_node then
      (* loop_up_ptr_args_data_node prog dn *)
      (* List.filter CP.is_node_typ *) dn.h_formula_data_arguments
    else
      (* let args =  List.filter CP.is_node_typ dn.CF.h_formula_data_arguments in *)
      (*     if (CP.intersect_svl args cur_ptrs) <> [] then *)
      (*       [dn.CF.h_formula_data_node] *)
      (*     else [] *)
      (* in *)
      look_up_data_node ds node_name

let rec look_up_rev_data_node ls node_name=
  match ls with
  | [] -> []
  | dn::ds ->
        let () = Debug.ninfo_hprint (add_str "node_name"  !CP.print_sv) node_name no_pos in
        let () = Debug.ninfo_hprint (add_str "dn"  (fun dn -> !print_h_formula (DataNode dn))) dn no_pos in
        if CP.mem_svl node_name dn.h_formula_data_arguments then
          [dn.h_formula_data_node]
        else
          look_up_rev_data_node ds node_name

let rec look_up_view_node ls node_name=
  match ls with
  | [] -> []
  | vn::vs -> if CP.eq_spec_var node_name vn.h_formula_view_node then
      (* List.filter CP.is_node_typ *) vn.h_formula_view_arguments
    else look_up_view_node vs node_name

let rec look_up_rev_view_node ls node_name=
  match ls with
  | [] -> []
  | vn::vs -> if CP.mem_svl node_name vn.h_formula_view_arguments then
      (* List.filter CP.is_node_typ *) [vn.h_formula_view_node]
    else look_up_rev_view_node vs node_name

let rec look_up_hrel_sig ls node_name =
  match ls with
  | [] -> []
  | (rn, rargs)::rs ->
    if CP.eq_spec_var node_name rn then rargs
    else look_up_hrel_sig rs node_name

let look_up_ptr_args_one_node prog hd_nodes hv_nodes ?(hr_sigs = []) node_name =
  let ptrs = look_up_data_node hd_nodes node_name in
  if ptrs = [] then
    (look_up_view_node hv_nodes node_name) @
    (look_up_hrel_sig hr_sigs node_name)
  else ptrs

let look_up_rev_ptr_node_one_node prog hd_nodes hv_nodes node_name =
  let ptrs = look_up_rev_data_node hd_nodes node_name in
  let () = Debug.ninfo_hprint (add_str "ptrs"  !CP.print_svl) ptrs no_pos in
  if ptrs = [] then look_up_rev_view_node hv_nodes node_name
  else ptrs

let look_up_rev_ptr_node_one_node prog hd_nodes hv_nodes node_name=
  let pr1 hv = !print_h_formula (ViewNode hv) in
  let pr2 hn = !print_h_formula (DataNode hn) in
  Debug.no_3 "look_up_rev_ptr_node_one_node" (pr_list pr2) (pr_list pr1) !CP.print_sv !CP.print_svl
      (fun _ _ _ -> look_up_rev_ptr_node_one_node prog hd_nodes hv_nodes node_name)
      hd_nodes hv_nodes node_name

(*should improve: should take care hrel also*)
let look_up_reachable_ptr_args prog hd_nodes hv_nodes ?(hr_sigs = []) node_names =
  let rec helper old_ptrs inc_ptrs =
    let new_ptrs = List.concat
        (List.map (look_up_ptr_args_one_node prog hd_nodes hv_nodes ~hr_sigs:hr_sigs)
           inc_ptrs) in
    let diff_ptrs = List.filter (fun id -> not (CP.mem_svl id old_ptrs)) new_ptrs in
    let diff_ptrs = Gen.BList.remove_dups_eq CP.eq_spec_var diff_ptrs in
    if diff_ptrs = [] then old_ptrs
    else (helper (old_ptrs@diff_ptrs) diff_ptrs)
  in
  helper node_names node_names

(* let look_up_last_reachable_ptr_args prog hd_nodes hv_nodes node_names= *)
(*   let rec helper old_ptrs inc_ptrs= *)
(*     let new_ptrs = List.concat *)
(*       (List.map (look_up_ptr_args_one_node prog hd_nodes hv_nodes) *)
(*            inc_ptrs) in *)
(*     let diff_ptrs = List.filter (fun id -> not (CP.mem_svl id old_ptrs)) new_ptrs in *)
(*     let diff_ptrs = Gen.BList.remove_dups_eq CP.eq_spec_var diff_ptrs in *)
(*     if diff_ptrs = [] then inc_ptrs *)
(*     else (helper (old_ptrs@diff_ptrs) diff_ptrs) *)
(*   in *)
(*   helper node_names node_names *)

let look_up_rev_reachable_ptr_args_x prog hd_nodes hv_nodes node_names=
  let rec helper old_ptrs inc_ptrs=
    let new_ptrs = List.concat
        (List.map (look_up_rev_ptr_node_one_node prog hd_nodes hv_nodes)
           inc_ptrs) in
    let () = Debug.ninfo_hprint (add_str "new_ptrs"  !CP.print_svl) new_ptrs no_pos in
    let diff_ptrs = List.filter (fun id -> not (CP.mem_svl id old_ptrs)) new_ptrs in
    let diff_ptrs = Gen.BList.remove_dups_eq CP.eq_spec_var diff_ptrs in
    if diff_ptrs = [] then old_ptrs
    else (helper (old_ptrs@diff_ptrs) diff_ptrs)
  in
  helper node_names node_names

let look_up_rev_reachable_ptr_args prog hd_nodes hv_nodes node_names=
  let pr1 hv = !print_h_formula (ViewNode hv) in
  let pr2 hn = !print_h_formula (DataNode hn) in
  Debug.no_3 "look_up_rev_reachable_ptr_args" (pr_list pr2) (pr_list pr1) !CP.print_svl !CP.print_svl
    (fun _ _ _ -> look_up_rev_reachable_ptr_args_x prog hd_nodes hv_nodes node_names)
    hd_nodes hv_nodes node_names

let look_up_reachable_ptrs_w_alias_helper prog hd_nodes hv_nodes eqset roots=
  let rec helper old_ptrs inc_ptrs=
    let new_ptrs = List.fold_left (fun r sv -> r@(look_up_ptr_args_one_node prog hd_nodes hv_nodes sv)) [] inc_ptrs in
    let diff_ptrs = List.filter (fun id -> not (CP.mem_svl id old_ptrs)) (find_close new_ptrs eqset) in
    let diff_ptrs = Gen.BList.remove_dups_eq CP.eq_spec_var diff_ptrs in
    if diff_ptrs = [] then old_ptrs
    else (helper (old_ptrs@diff_ptrs) diff_ptrs)
  in
  let cl_roots = find_close roots eqset in
  helper cl_roots cl_roots

let look_up_first_reachable_unfold_ptr prog hd_nodes hv_nodes ?(hr_sigs = []) roots =
  let is_unfold_ptr hv_nodes hr_sigs sv =
     (List.exists (fun vn -> CP.eq_spec_var vn.h_formula_view_node sv) hv_nodes) ||
     (List.exists (fun (hr_root, _) -> CP.eq_spec_var hr_root sv) hr_sigs)
  in

  let rec helper old_ptrs inc_ptrs =
    let new_ptrs = List.fold_left (fun r sv ->
        r@(look_up_ptr_args_one_node prog hd_nodes hv_nodes ~hr_sigs:hr_sigs sv)) [] inc_ptrs in
    let unfold_ptrs = List.filter (fun sv -> is_unfold_ptr hv_nodes hr_sigs sv) new_ptrs in
    if unfold_ptrs != [] then unfold_ptrs
    else
      let diff_ptrs = List.filter (fun id -> not (CP.mem_svl id old_ptrs)) new_ptrs in
      let diff_ptrs = Gen.BList.remove_dups_eq CP.eq_spec_var diff_ptrs in
      if diff_ptrs = [] then []
      else (helper (old_ptrs@diff_ptrs) diff_ptrs)
  in
  (*check onl_ptrs are unfold points - view*)
  if List.exists (fun sv -> is_unfold_ptr hv_nodes hr_sigs sv) roots
  then roots
  else helper roots roots

let extract_HRel_orig hf=
  match hf with
  | HRel (hp, eargs, p ) -> (hp, eargs,p)
  | _ -> raise SA_HP_TUPLED


let extract_HRel_orig_f (f0:formula) =
  let rec helper f=
    match f with
    | Base ({ formula_base_heap = h1;})
    | Exists ({formula_exists_heap = h1;}) ->
      (
        extract_HRel_orig h1
      )
    | _ -> report_error no_pos "CF.extract_HRel"
  in
  helper f0

let get_HRels hf=
  let rec helper h=
    match h with
    | HRel (hp, eargs, _ ) -> [(hp, List.concat (List.map CP.afv eargs))]
    | Conj {h_formula_conj_h1 = h1; h_formula_conj_h2 = h2}
    | Star {h_formula_star_h1 = h1; h_formula_star_h2 = h2}
    | Phase {h_formula_phase_rd = h1; h_formula_phase_rw = h2}
      -> (helper h1)@(helper h2)
    | _ -> []
  in
  helper hf

let rec get_HRels_f f=
  match f with
  | Base fb -> get_HRels fb.formula_base_heap
  | Exists fe -> get_HRels fe.formula_exists_heap
  | Or orf  ->
    let a1 = get_HRels_f orf.formula_or_f1 in
    let a2 = get_HRels_f orf.formula_or_f2 in
    (a1@a2)

let get_hp_rel_pre_struc_formula (sf0:struc_formula) =
  let rec helper sf= match sf with
    | ECase b-> List.fold_left (fun r (_,sc) -> r@(helper sc)) [] b.formula_case_branches
    | EBase b -> get_HRels_f b.formula_struc_base
    | EAssume _ -> []
    | EInfer b -> helper b.formula_inf_continuation
    | EList l -> List.fold_left (fun r (_,sc) -> r@(helper sc)) [] l
  in
  helper sf0


let check_and_get_one_hpargs f=
  let helper mf hf=
    if CP.isConstTrue (MCP.pure_of_mix mf) then
      match hf with
      | HRel (hp, eargs, p ) -> [(hp, List.concat (List.map CP.afv eargs),p)]
      | _ -> []
    else []
  in
  match f with
  | Base fb -> helper fb.formula_base_pure fb.formula_base_heap
  | Exists fe -> helper fe.formula_exists_pure fe.formula_exists_heap
  | Or _  -> []

let rec check_eq_hrel_node  (rl1, args1 ,_)  (rl2, args2,_)=
  let rec helper l1 l2=
    match l1,l2 with
    | [],[] -> true
    | (e1)::vs1,(e2)::vs2 ->
      let sv1 = CP.afv e1 in
      let sv2 = CP.afv e2 in
      if CP.diff_svl sv1 sv2 = [] then helper vs1 vs2
      else false
    | _ -> false
  in
  (*hp1 = hp2 and args1 = arg2*)
  (* let svs1 = List.concat (List.map CP.afv args1) in *)
  (* let svs2 = List.concat (List.map CP.afv args2) in *)
  (CP.eq_spec_var rl1 rl2) && (helper args1 args2)

and get_ptrs_f (f0: formula)=
  let rec helper f=
    match f with
    | Base fb ->
      get_ptrs fb.formula_base_heap
    | Exists fe -> get_ptrs fe.formula_exists_heap
    | Or orf -> (helper orf.formula_or_f1)@(helper orf.formula_or_f2)
  in
  helper f0

and get_pure (f0: formula)=
  let rec helper f=
    match f with
    | Base fb ->
      MCP.pure_of_mix fb.formula_base_pure
    | Exists fe ->
      let qvars, base1 = split_quantifiers f in
      let p = helper base1 in
      CP.mkExists qvars p None fe.formula_exists_pos
    | Or orf ->
      let p1 = helper orf.formula_or_f1 in
      let p2 = helper orf.formula_or_f2 in
      CP.Or (p1, p2, None , orf.formula_or_pos)
      (*use CP.mkOr will remove trueConst*)
      (* CP.mkOr p1 p2 None orf.formula_or_pos *)
  in
  helper f0

and get_pure_ignore_exists (f0: formula)=
  let rec helper f=
    match f with
    | Base fb   -> MCP.pure_of_mix fb.formula_base_pure
    | Exists fe -> MCP.pure_of_mix fe.formula_exists_pure
    | Or orf ->
      let p1 = helper orf.formula_or_f1 in
      let p2 = helper orf.formula_or_f2 in
      CP.Or (p1, p2, None , orf.formula_or_pos)
  in
  helper f0

and get_ptrs (f: h_formula): CP.spec_var list = match f with
  | DataNode {h_formula_data_node = c}
  | ViewNode {h_formula_view_node = c} -> [c]
  | Conj {h_formula_conj_h1 = h1; h_formula_conj_h2 = h2}
  | ConjStar {h_formula_conjstar_h1 = h1; h_formula_conjstar_h2 = h2}
  | ConjConj {h_formula_conjconj_h1 = h1; h_formula_conjconj_h2 = h2}
  | Star {h_formula_star_h1 = h1; h_formula_star_h2 = h2}
  | Phase {h_formula_phase_rd = h1; h_formula_phase_rw = h2}
    -> (get_ptrs h1)@(get_ptrs h2)
  | _ -> []

and get_ptrs_w_args_f_x ?(en_pure_field=false) (f: formula)=
  match f with
  | Base fb ->
    CP.remove_dups_svl (get_ptrs_w_args ~en_pure_field:en_pure_field fb.formula_base_heap)
  | Exists fe ->
    CP.remove_dups_svl (get_ptrs_w_args ~en_pure_field:en_pure_field fe.formula_exists_heap)
  | _ -> report_error no_pos "CF.get_ptrs_w_args_f: not handle yet"

and get_ptrs_w_args_f ?(en_pure_field=false) (f: formula) =
  let pr = !print_formula in
  Debug.no_2 "get_ptrs_w_args_f" string_of_bool pr !CP.print_svl
    (fun _ _ -> get_ptrs_w_args_f_x ~en_pure_field:en_pure_field f) en_pure_field f

and get_ptrs_w_args ?(en_pure_field=false) (f: h_formula): CP.spec_var list = match f with
  | DataNode {h_formula_data_node = c;
              h_formula_data_arguments = args} ->
        [c]@(if en_pure_field then args else List.filter CP.is_node_typ args)
  | ViewNode {h_formula_view_node = c;
              h_formula_view_ho_arguments = ho_args;
              h_formula_view_arguments = args} ->
    let hovars = List.concat (List.map (apply_rflow_formula get_ptrs_w_args_f) ho_args) in
    [c]@(if en_pure_field then args else List.filter CP.is_node_typ args)@hovars
  | Conj {h_formula_conj_h1 = h1; h_formula_conj_h2 = h2}
  | Star {h_formula_star_h1 = h1; h_formula_star_h2 = h2}
  | Phase {h_formula_phase_rd = h1; h_formula_phase_rw = h2}
    -> (get_ptrs_w_args ~en_pure_field:en_pure_field h1)@(get_ptrs_w_args ~en_pure_field:en_pure_field h2)
  | HRel (_,eargs,_) -> (List.fold_left List.append [] (List.map CP.afv eargs))
  | _ -> []

and get_all_sv_f (f: formula)=
  match f with
  | Base fb ->
    CP.remove_dups_svl (get_all_sv fb.formula_base_heap)
  | _ -> report_error no_pos "CF.get_all_sv_f: not handle yet"

and get_all_sv (f: h_formula): CP.spec_var list = match f with
  | DataNode {h_formula_data_node = c;
              h_formula_data_arguments = args;
              h_formula_data_imm = imm;
              h_formula_data_param_imm = param_imm;
             } ->
    let fv_ann_list = (* if (!Globals.allow_imm) then *) CP.fv_ann imm (* else [] *) in
    let fv_ann_list = if true (* (!Globals.allow_field_ann)y *) then fv_ann_list@(CP.fv_ann_lst param_imm) else fv_ann_list in
    [c]@(List.filter CP.is_node_typ args)@fv_ann_list
  | ViewNode {h_formula_view_node = c;
              h_formula_view_arguments = args;
              h_formula_view_imm = imm;
             } ->
    let fv_ann_list = (* if (!Globals.allow_imm) then *) CP.fv_ann imm (* else [] *) in
    [c]@(List.filter CP.is_node_typ args)@fv_ann_list
  | Conj {h_formula_conj_h1 = h1; h_formula_conj_h2 = h2}
  | Star {h_formula_star_h1 = h1; h_formula_star_h2 = h2}
  | Phase {h_formula_phase_rd = h1; h_formula_phase_rw = h2}
    -> (get_all_sv h1)@(get_all_sv h2)
  | HRel (hp,eargs,_) -> hp::(List.fold_left List.append [] (List.map CP.afv eargs))
  | _ -> []

and get_hnodes (f: h_formula) = match f with
  | DataNode _ -> [f]
  | Conj {h_formula_conj_h1 = h1; h_formula_conj_h2 = h2}
  | Star {h_formula_star_h1 = h1; h_formula_star_h2 = h2}
  | Phase {h_formula_phase_rd = h1; h_formula_phase_rw = h2}
    -> (get_hnodes h1)@(get_hnodes h2)
  | _ -> []


let elim_unused_pure_x (f0:formula) rhs =
  let rhs_ptrs = get_ptrs_w_args_f rhs in
  let rec helper f=
    match f with
    | Base b->
      let lhs_ptrs= get_ptrs_w_args b.formula_base_heap in
      let keep_svl = CP.remove_dups_svl (lhs_ptrs@rhs_ptrs) in
      let _,np1 = CP.prune_irr_neq (MCP.pure_of_mix b.formula_base_pure) keep_svl in
      let np2 = CP.filter_var np1 keep_svl in
      Base {b with formula_base_pure = MCP.mix_of_pure np2;}
    | Exists e -> let qvars, base_f = split_quantifiers f in
      let nf = helper base_f in
      (add_quantifiers qvars nf)
    | Or orf -> Or {orf with formula_or_f1 = helper orf.formula_or_f1;
                             formula_or_f2 = helper orf.formula_or_f2}
  in
  helper (elim_exists f0)

let elim_unused_pure (f0:formula) rhs =
  let pr= !print_formula in
  Debug.no_2 " elim_unused_pure" pr pr pr
    (fun _ _ -> elim_unused_pure_x f0 rhs) f0 rhs

let filter_var_pure r (f0:formula) =
  let rec helper f=
    match f with
    | Base b->
      let keep_svl = CP.diff_svl (fv f) [r] in
      Base {b with formula_base_pure = MCP.mix_of_pure
                       (CP.filter_var (MCP.pure_of_mix b.formula_base_pure)
                          keep_svl);
           }
    | Exists e -> let qvars, base_f = split_quantifiers f in
      let nf = helper base_f in
      (add_quantifiers qvars nf)
    | Or orf -> Or {orf with formula_or_f1 = helper orf.formula_or_f1;
                             formula_or_f2 = helper orf.formula_or_f2}
  in
  helper f0

let prune_irr_neq_formula_x ?(en_pure_field=false) must_kept_svl lhs_b rhs_b =
  let r_svl = fv (Base rhs_b) in
  let rec helper fb=
    let ptrs = get_ptrs_w_args ~en_pure_field:en_pure_field fb.formula_base_heap in
    let keep_svl = (ptrs@r_svl@must_kept_svl) in
    let _,np2 = CP.prune_irr_neq (MCP.pure_of_mix fb.formula_base_pure) (CP.remove_dups_svl keep_svl) in
    let np3 = CP.filter_var_new np2 keep_svl in
    let np4 = MCP.mix_of_pure np3 in
    {fb with formula_base_pure = np4;}
  in
  helper lhs_b

let prune_irr_neq_formula ?(en_pure_field=false) must_kept_svl lhs_b rhs_b=
  let pr1 = !print_formula_base in
  Debug.no_3 "prune_irr_neq_formula" !CP.print_svl pr1 pr1 pr1
    (fun _ _ _ -> prune_irr_neq_formula_x ~en_pure_field:en_pure_field must_kept_svl lhs_b rhs_b)
    must_kept_svl lhs_b rhs_b

let rec flatten_nodes_h (f0: h_formula) =
  let rec helper f=
    match f with
    | Conj {h_formula_conj_h1 = h1; h_formula_conj_h2 = h2}
    | Star {h_formula_star_h1 = h1; h_formula_star_h2 = h2}
    | Phase {h_formula_phase_rd = h1; h_formula_phase_rw = h2} ->
      let hds1,hvs1, hrels1=(helper h1) in
      let hds2,hvs2, hrels2 = (helper h2)in
      ((hds1@hds2),(hvs1@hvs2), hrels1@hrels2)
    | DataNode dn -> ([dn],[],[])
    | ViewNode vn -> ([],[vn],[])
    | HRel hr -> ([],[], [hr])
    | _ -> ([],[],[])
  in
  helper f0

let flatten_nodes (f0:formula) =
  let rec helper f=
    match f with
    | Base ({ formula_base_heap = h1;})
    | Exists ({ formula_exists_heap = h1;}) ->
      (
        flatten_nodes_h h1
      )
    | Or {formula_or_f1 = f1;
          formula_or_f2 = f2} ->
      let hds1,hvs1,hrels1=(helper f1) in
      let hds2,hvs2,hrels2 = (helper f2)in
      ((hds1@hds2),(hvs1@hvs2),hrels1@hrels2)
  in
  helper f0

let rec get_h_size_f (f: formula)=
  match f with
  | Base fb ->
    (get_h_size fb.formula_base_heap)
  | Exists fe ->
    (get_h_size fe.formula_exists_heap)
  | _ -> report_error no_pos "CF.get_h_size_f: not handle yet"

and get_h_size (f0: h_formula) =
  let rec helper f=
    match f with
    | Conj {h_formula_conj_h1 = h1; h_formula_conj_h2 = h2}
    | Star {h_formula_star_h1 = h1; h_formula_star_h2 = h2}
    | Phase {h_formula_phase_rd = h1; h_formula_phase_rw = h2}
      -> (helper h1)+(helper h2)
    | _ -> 1
  in
  helper f0

let get_hdnodes_hrel_hf (hf0: h_formula) =
  let rec helper hf=
    match hf with
    | DataNode _ -> [hf]
    | HRel _ -> [hf]
    | Conj {h_formula_conj_h1 = h1; h_formula_conj_h2 = h2}
    | Star {h_formula_star_h1 = h1; h_formula_star_h2 = h2}
    | Phase {h_formula_phase_rd = h1;h_formula_phase_rw = h2}
      -> (helper h1)@(helper h2)
    | _ -> []
  in
  helper hf0

let check_imm_mis rhs_mis rhs0=
  match rhs_mis with
  | DataNode hd1 ->
    if not(CP.isLend (hd1.h_formula_data_imm)) then rhs0
    else
      let mis_sv = hd1.h_formula_data_node in
      let rec helper rhs=
        match rhs with
        | Star { h_formula_star_h1 = hf1;
                 h_formula_star_h2 = hf2;
                 h_formula_star_pos = pos} ->
          Star {h_formula_star_h1 = helper hf1;
                h_formula_star_h2 = helper hf2;
                h_formula_star_pos = pos}
        |  Conj { h_formula_conj_h1 = hf1;
                  h_formula_conj_h2 = hf2;
                  h_formula_conj_pos = pos} ->
          Conj { h_formula_conj_h1 = helper hf1;
                 h_formula_conj_h2 = helper hf2;
                 h_formula_conj_pos = pos}
        | Phase { h_formula_phase_rd = hf1;
                  h_formula_phase_rw = hf2;
                  h_formula_phase_pos = pos} ->
          Phase { h_formula_phase_rd = helper hf1;
                  h_formula_phase_rw = helper hf2;
                  h_formula_phase_pos = pos}
        | DataNode hd -> if CP.eq_spec_var mis_sv hd.h_formula_data_node then
            if not(CP.isLend (hd.h_formula_data_imm)) then rhs else
              DataNode {hd with h_formula_data_imm = (CP.ConstAnn(Mutable));}
          else rhs
        | _ -> rhs
      in
      helper rhs0
  | _ -> rhs0

let check_imm_mis rhs_mis rhs0 =
  let pr = !print_h_formula in
  Debug.no_2 "check_imm_mis" pr pr pr check_imm_mis rhs_mis rhs0

(* asankhs : what is this method supported to do ? *)
let rec heap_trans_heap_node fct f0 =
  let recf = heap_trans_heap_node fct in
  let rec helper f=
    match f with
    | HRel b -> fct f
    | DataNode _ -> fct f
    | ViewNode _ -> fct f
    | ThreadNode _ -> fct f
    | HTrue | HFalse | HEmp | Hole _ | FrmHole _ | HVar _ -> f
    | Phase b -> Phase {b with h_formula_phase_rd = recf b.h_formula_phase_rd; h_formula_phase_rw = recf b.h_formula_phase_rw}
    | Conj b -> begin
        let hf2 = recf b.h_formula_conj_h2 in
        let hf1 = recf b.h_formula_conj_h1 in
        match hf1,hf2 with
        | HEmp,HEmp -> HEmp
        | HEmp,_ -> hf2
        | _ , HEmp -> hf1
        | _ -> Conj {b with h_formula_conj_h2 = hf2; h_formula_conj_h1 = hf1}
      end
    | Star b -> begin let hf2 = recf b.h_formula_star_h2 in
        let hf1 = recf b.h_formula_star_h1 in
        match hf1,hf2 with
        | HEmp,HEmp -> HEmp
        | HEmp,_ -> hf2
        | _ , HEmp -> hf1
        | _ ->
          Star {b with h_formula_star_h2 = hf2; h_formula_star_h1 = hf1}
      end
    | ConjStar _|ConjConj _|StarMinus _ -> f
    (*report_error no_pos "CF.heap_trans_heap_node: not handle yet"*)
  in
  helper f0


let rec formula_trans_heap_node fct f =
  let recf = formula_trans_heap_node fct in
  match f with
  | Base b-> Base{b with  formula_base_heap = heap_trans_heap_node fct b.formula_base_heap}
  | Exists b-> Exists{b with  formula_exists_heap = heap_trans_heap_node fct b.formula_exists_heap}
  | Or b-> Or {b with formula_or_f1 = recf b.formula_or_f1;formula_or_f2 = recf b.formula_or_f2}

let rec struc_formula_drop_infer unk_hps f =
  let recf = struc_formula_drop_infer unk_hps in
  let drop_unk hn =
    match hn with
    | HRel (hp,_, _)->
      if CP.mem_svl hp unk_hps then HEmp else hn
    | _ -> hn
  in
  match f with
  | ECase b-> ECase {b with formula_case_branches= Gen.map_l_snd recf b.formula_case_branches}
  | EBase b -> EBase {b with
                      formula_struc_base = formula_trans_heap_node drop_unk b.formula_struc_base;
                      formula_struc_continuation = Gen.map_opt recf b.formula_struc_continuation}
  | EAssume b -> EAssume {b with formula_assume_simpl = formula_trans_heap_node drop_unk b.formula_assume_simpl}
  | EInfer b->
        recf b.formula_inf_continuation
  | EList l-> EList (Gen.map_l_snd recf l)

let rec struc_formula_drop_unk unk_hps f =
  let recf = struc_formula_drop_unk unk_hps in
  let drop_unk hn =
    match hn with
    | HRel (hp,_, _)->
      if CP.mem_svl hp unk_hps then HEmp else hn
    | _ -> hn
  in
  match f with
  | ECase b-> ECase {b with formula_case_branches= Gen.map_l_snd recf b.formula_case_branches}
  | EBase b -> EBase {b with
                      formula_struc_base = formula_trans_heap_node drop_unk b.formula_struc_base;
                      formula_struc_continuation = Gen.map_opt recf b.formula_struc_continuation}
  | EAssume b -> EAssume {b with formula_assume_simpl = formula_trans_heap_node drop_unk b.formula_assume_simpl}
  | EInfer b->
        EInfer {b with formula_inf_continuation  = recf b.formula_inf_continuation}
  | EList l-> EList (Gen.map_l_snd recf l)



let formula_map hf_fct f0=
  let rec helper f=
    match f with
    | Base b -> Base {b with formula_base_heap = hf_fct b.formula_base_heap}
    | Exists _ ->
      let quans ,base = split_quantifiers f in
      let new_base = helper base in
      add_quantifiers quans new_base
    | Or orf ->
      Or {orf with formula_or_f1 = helper orf.formula_or_f1;
                   formula_or_f2 = helper orf.formula_or_f2;
         }
  in
  helper f0

let fresh_view f=
  let fresh_view_h hf=
    match hf with
    | ViewNode vn -> ViewNode {vn with h_formula_view_original = true;}
    | _ -> hf
  in
  formula_trans_heap_node fresh_view_h f

let rec mkAnd_pre_struc_formula sf f=
  let recf sf1 = mkAnd_pre_struc_formula sf1 f in
  match sf with
  | ECase b-> ECase {b with formula_case_branches= Gen.map_l_snd recf b.formula_case_branches}
  | EBase b -> EBase {b with
                      formula_struc_base = mkStar b.formula_struc_base f Flow_combine b.formula_struc_pos}
  | EAssume b -> sf
  | EInfer b-> EInfer {b with formula_inf_continuation = recf b.formula_inf_continuation;}
  | EList l-> EList (Gen.map_l_snd recf l)


let rec mkAnd_pure_pre_struc_formula_x p f =
  let recf =  mkAnd_pure_pre_struc_formula_x p in
  match f with
  | ECase b-> ECase {b with formula_case_branches= Gen.map_l_snd recf b.formula_case_branches}
  | EBase b -> EBase {b with
                      formula_struc_base= mkAnd_pure b.formula_struc_base (MCP.mix_of_pure p) b.formula_struc_pos;}
  | EAssume ea-> f
  | EInfer b -> EInfer {b with formula_inf_continuation = recf b.formula_inf_continuation}
  | EList l -> EList (Gen.map_l_snd recf l)


let rec mkAnd_pure_pre_struc_formula p f =
  let pr1 = !print_struc_formula in
  Debug.no_2 " mkAnd_pure_pre_struc_formula" !CP.print_formula pr1 pr1
    (fun _ _ -> mkAnd_pure_pre_struc_formula_x p f) p f


let rec elim_useless_term_struc_x sf=
  let recf = elim_useless_term_struc_x in
  match sf with
  | ECase b-> ECase {b with formula_case_branches= Gen.map_l_snd recf b.formula_case_branches}
  | EBase b -> begin if isTrivTerm b.formula_struc_base then
        match b.formula_struc_continuation with
        | None -> EBase {b with
                         formula_struc_continuation = Gen.map_opt recf b.formula_struc_continuation;}
        | Some sf1 -> recf sf1
      else EBase {b with
                  formula_struc_continuation = Gen.map_opt recf b.formula_struc_continuation;}
    end
  | EAssume ea-> EAssume {ea with formula_assume_struc = recf ea.formula_assume_struc}
  | EInfer b -> EInfer {b with formula_inf_continuation = recf b.formula_inf_continuation}
  | EList l -> EList (Gen.map_l_snd recf l)

let elim_useless_term_struc sf=
  let pr = !print_struc_formula in
  Debug.no_1 "elim_useless_term_struc" pr pr
    (fun _ -> elim_useless_term_struc_x sf) sf

(*node + args is one group*)
let rec get_ptrs_group_hf hf0=
  let rec helper hf=
    match hf with
    | Star {h_formula_star_h1 = hf1;
            h_formula_star_h2 = hf2;}
    | StarMinus { h_formula_starminus_h1 = hf1;
                  h_formula_starminus_h2 = hf2;}
    | Conj { h_formula_conj_h1 = hf1;
             h_formula_conj_h2 = hf2;}
    | ConjStar { h_formula_conjstar_h1 = hf1;
                 h_formula_conjstar_h2 = hf2;}
    | ConjConj { h_formula_conjconj_h1 = hf1;
                 h_formula_conjconj_h2 = hf2;}
    | Phase { h_formula_phase_rd = hf1;
              h_formula_phase_rw = hf2;} ->
      (helper hf1)@(helper hf2)
    | DataNode hd -> [hd.h_formula_data_node::hd.h_formula_data_arguments]
    | ViewNode hv ->
      let ho = List.concat (List.map (apply_rflow_formula get_ptrs_group) hv.h_formula_view_ho_arguments) in
      [hv.h_formula_view_node::hv.h_formula_view_arguments]@ho
    | ThreadNode ht -> [[ht.h_formula_thread_node]] (*TOCHECK*)
    | HRel _
    | Hole _ | FrmHole _
    | HTrue
    | HFalse
    | HEmp | HVar _ ->[]
  in helper hf0

and get_node_args hf0 =
  let rec helper hf=
    match hf with
    | Star {h_formula_star_h1 = hf1;
            h_formula_star_h2 = hf2;}
    | StarMinus { h_formula_starminus_h1 = hf1;
                  h_formula_starminus_h2 = hf2;}
    | Conj { h_formula_conj_h1 = hf1;
             h_formula_conj_h2 = hf2;}
    | ConjStar { h_formula_conjstar_h1 = hf1;
                 h_formula_conjstar_h2 = hf2;}
    | ConjConj { h_formula_conjconj_h1 = hf1;
                 h_formula_conjconj_h2 = hf2;}
    | Phase { h_formula_phase_rd = hf1;
              h_formula_phase_rw = hf2;} ->
      (helper hf1)@(helper hf2)
    | DataNode hd -> hd.h_formula_data_arguments
    | ViewNode hv -> hv.h_formula_view_arguments
    | ThreadNode ht -> []
    | HRel (hrel, el, _) ->
      (* (try *)
        List.map (fun e ->
          match e with
          | CP.Var (sv, _) -> sv
          | _ -> failwith ("Unexpected exp (not CP.Var) in HRel " ^
                (CP.name_of_spec_var hrel) ^ "'s arguments."))
          (* (List.tl el) *) el
      (* with _ -> failwith ("Empty arguments in HRel " ^ (CP.name_of_spec_var hrel))) *)
    | Hole _ | FrmHole _
    | HTrue
    | HFalse
    | HEmp | HVar _ -> []
  in helper hf0

and get_ptrs_group f0=
  let rec helper f=
    match f with
    | Base fb -> get_ptrs_group_hf fb.formula_base_heap
    | Exists _ -> let _, base_f = split_quantifiers f in helper base_f
    | Or orf -> (helper orf.formula_or_f1)@(helper orf.formula_or_f2)
  in helper f0

and get_data_node_ptrs_group_hf hf0=
  let rec helper hf=
    match hf with
    | Star {h_formula_star_h1 = hf1;
            h_formula_star_h2 = hf2;}
    | StarMinus { h_formula_starminus_h1 = hf1;
                  h_formula_starminus_h2 = hf2;}
    | Conj { h_formula_conj_h1 = hf1;
             h_formula_conj_h2 = hf2;}
    | ConjStar { h_formula_conjstar_h1 = hf1;
                 h_formula_conjstar_h2 = hf2;}
    | ConjConj { h_formula_conjconj_h1 = hf1;
                 h_formula_conjconj_h2 = hf2;}
    | Phase { h_formula_phase_rd = hf1;
              h_formula_phase_rw = hf2;} ->
      (helper hf1)@(helper hf2)
    | DataNode hd -> [hd.h_formula_data_node::hd.h_formula_data_arguments]
    | ViewNode _
    | ThreadNode _ (*TOCHECK*)
    | HRel _
    | Hole _ | FrmHole _
    | HTrue
    | HFalse
    | HEmp | HVar _->[]
  in helper hf0

let rec get_hp_rel_formula (f:formula) =
  match f with
  | Base  ({formula_base_heap = h1;
            formula_base_pure = p1})
  | Exists ({formula_exists_heap = h1;
             formula_exists_pure = p1}) -> (
      get_hp_rel_h_formula h1
    )
  | Or orf  ->
    let a1,b1,c1 = get_hp_rel_formula orf.formula_or_f1 in
    let a2,b2,c2 = get_hp_rel_formula orf.formula_or_f2 in
    (a1@a2,b1@b2,c1@c2)

and get_hp_rel_bformula bf=
  get_hp_rel_h_formula bf.formula_base_heap

(*data nodes, view nodes, rel*)
and get_hp_rel_h_formula hf=
  match hf with
  | Star { h_formula_star_h1 = hf1;
           h_formula_star_h2 = hf2}
  | StarMinus { h_formula_starminus_h1 = hf1;
                h_formula_starminus_h2 = hf2}
    ->
    let hd1, hv1,hr1 = get_hp_rel_h_formula hf1 in
    let hd2,hv2,hr2 = (get_hp_rel_h_formula hf2) in
    (hd1@hd2,hv1@hv2,hr1@hr2)
  | Conj { h_formula_conj_h1 = hf1;
           h_formula_conj_h2 = hf2;}
  | ConjStar { h_formula_conjstar_h1 = hf1;
               h_formula_conjstar_h2 = hf2;}
  | ConjConj { h_formula_conjconj_h1 = hf1;
               h_formula_conjconj_h2 = hf2;} ->
    let hd1,hv1,hr1 = (get_hp_rel_h_formula hf1)in
    let hd2,hv2,hr2 = (get_hp_rel_h_formula hf2) in
    (hd1@hd2,hv1@hv2,hr1@hr2)
  | Phase { h_formula_phase_rd = hf1;
            h_formula_phase_rw = hf2;} ->
    let hd1,hv1,hr1 = (get_hp_rel_h_formula hf1) in
    let hd2,hv2,hr2 = (get_hp_rel_h_formula hf2) in
    (hd1@hd2,hv1@hv2,hr1@hr2)
  | DataNode hd -> ([hd],[],[])
  | ViewNode hv -> ([],[hv],[])
  | HRel hr -> ([],[],[hr])
  | ThreadNode _ -> ([],[],[]) (*TOCHECK*)
  | Hole _ | FrmHole _
  | HTrue
  | HFalse
  | HEmp | HVar _-> ([],[],[])

(*******************)
(* Moved to Cfutil *)
(*******************)
(* (*first_ptr = true: stop at the first*)                                                        *)
(* let look_up_reachable_ptrs_f_x prog f roots ptr_only first_ptr =                               *)
(*   let search_fnc =                                                                             *)
(*     if first_ptr then look_up_first_reachable_unfold_ptr                                       *)
(*     else look_up_reachable_ptr_args                                                            *)
(*   in                                                                                           *)
(*   let obtain_reachable_ptr_conj f =                                                            *)
(*     let hds, hvs, hrs = get_hp_rel_formula f in                                                *)
(*     let hrs = List.map (fun hr -> CFU.) hrs in                                                 *)
(*     search_fnc prog hds hvs roots                                                              *)
(*   in                                                                                           *)
(*   let fs = list_of_disjs f in                                                                  *)
(*   let ptrs = List.fold_left (fun r f -> r@(obtain_reachable_ptr_conj f)) [] fs in              *)
(*   let ptrs1 = CP.remove_dups_svl ptrs in                                                       *)
(*   if ptr_only then List.filter CP.is_node_typ ptrs1 else ptrs1                                 *)

(* let look_up_reachable_ptrs_f prog f roots ptr_only first_ptr=                                  *)
(*   let pr1 = !print_formula in                                                                  *)
(*   let pr2 = !print_spec_var_list in                                                            *)
(*   let pr_out = !print_spec_var_list in                                                         *)
(*   Debug.no_2 "look_up_reachable_ptrs_f" pr1 pr2 pr_out                                         *)
(*     (fun _ _ -> look_up_reachable_ptrs_f_x prog f roots ptr_only first_ptr) f roots            *)

(* (*                                                                                             *)
(* output_ctr = 0 return all pointer                                                              *)
(* output_ctr = 1 return output_ctr + dnodes                                                      *)
(* output_ctr = 2 return output_ctr + vnodes                                                      *)
(* output_ctr = 3 return output_ctr + dnodes + vnodes                                             *)
(* *)                                                                                             *)
(* let look_up_reachable_ptrs_w_alias_x prog f roots output_ctr=                                  *)
(*   let search_fnc = look_up_reachable_ptrs_w_alias_helper in                                    *)
(*   let obtain_reachable_ptr_conj f=                                                             *)
(*     let (h ,mf,_,_,_,_) = split_components f in                                                *)
(*     let hds, hvs, _ = get_hp_rel_h_formula h in                                                *)
(*     let eqsets = (MCP.ptr_equations_without_null mf) in                                        *)
(*     let reach_ptrs = search_fnc prog hds hvs eqsets roots in                                   *)
(*     let dnodes = List.filter (fun hd -> CP.mem_svl hd.h_formula_data_node reach_ptrs) hds in   *)
(*     let vnodes = List.filter (fun vn -> CP.mem_svl vn.h_formula_view_node reach_ptrs) hvs in   *)
(*     (reach_ptrs, dnodes, vnodes)                                                               *)
(*   in                                                                                           *)
(*   let fs = list_of_disjs f in                                                                  *)
(*   let reach_ptrs,dnodes, vnodes = List.fold_left (fun (r1,r2,r3) f ->                          *)
(*       let reach_ptrs, reach_dns, reach_vns = obtain_reachable_ptr_conj f in                    *)
(*       (r1@reach_ptrs, r2@reach_dns, r3@reach_vns)                                              *)
(*     ) ([],[],[]) fs in                                                                         *)
(*   reach_ptrs,dnodes, vnodes                                                                    *)

(* let look_up_reachable_ptrs_w_alias prog f roots output_ctr=                                    *)
(*   let pr1 = !print_formula in                                                                  *)
(*   let pr2 = !print_spec_var_list in                                                            *)
(*   let pr_data_node dn= !print_h_formula (DataNode dn) in                                       *)
(*   let pr_view_node dn= !print_h_formula (ViewNode dn) in                                       *)
(*   Debug.no_3 "look_up_reachable_ptrs_w_alias" pr1 pr2 string_of_int                            *)
(*     (pr_triple !CP.print_svl (pr_list pr_data_node) (pr_list pr_view_node) )                   *)
(*     (fun _ _ _ -> look_up_reachable_ptrs_w_alias_x prog f roots output_ctr)                    *)
(*     f roots output_ctr                                                                         *)

(* let look_up_reachable_first_reachable_view prog f roots=                                       *)
(*   let ptrs = look_up_reachable_ptrs_f prog f roots true true in                                *)
(*   if ptrs = [] then [] else                                                                    *)
(*     let _, hvs, _ = get_hp_rel_formula f in                                                    *)
(*     List.filter (fun hv -> CP.mem_svl hv.h_formula_view_node ptrs) hvs                         *)

(* let look_up_reachable_first_reachable_view prog f roots=                                       *)
(*   let pr1 = !print_formula in                                                                  *)
(*   let pr_view_node dn= !print_h_formula (ViewNode dn) in                                       *)
(*   Debug.no_2 "look_up_reachable_first_reachable_view" pr1 !CP.print_svl (pr_list pr_view_node) *)
(*     (fun _ _ -> look_up_reachable_first_reachable_view prog f roots)                           *)
(*     f roots                                                                                    *)

(* let rec look_up_reachable_ptrs_sf_x prog sf roots ptr_only first_ptr=                          *)
(*   let look_up_reachable_ptrs_sf_list prog sfs roots = (                                        *)
(*     let ptrs = List.fold_left (fun r (_, sf) ->                                                *)
(*         r @ (look_up_reachable_ptrs_sf prog sf roots ptr_only first_ptr)                       *)
(*       ) [] sfs in                                                                              *)
(*     CP.remove_dups_svl ptrs                                                                    *)
(*   ) in                                                                                         *)
(*   match sf with                                                                                *)
(*   | EList sfs -> look_up_reachable_ptrs_sf_list prog sfs roots                                 *)
(*   | ECase { formula_case_branches = sfs } ->                                                   *)
(*     look_up_reachable_ptrs_sf_list prog sfs roots                                              *)
(*   | EBase { formula_struc_base = f; formula_struc_continuation = sf_opt } ->                   *)
(*     let ptrs1 = look_up_reachable_ptrs_f prog f roots ptr_only first_ptr in                    *)
(*     let ptrs2 = (match sf_opt with                                                             *)
(*         | None -> []                                                                           *)
(*         | Some sf -> look_up_reachable_ptrs_sf prog sf roots ptr_only first_ptr                *)
(*       ) in                                                                                     *)
(*     CP.remove_dups_svl (ptrs1 @ ptrs2)                                                         *)
(*   | EAssume { formula_assume_simpl = f; formula_assume_struc = sf} ->                          *)
(*     let ptrs1 = look_up_reachable_ptrs_f prog f roots ptr_only first_ptr in                    *)
(*     let ptrs2 = look_up_reachable_ptrs_sf prog sf roots  ptr_only first_ptr in                 *)
(*     CP.remove_dups_svl (ptrs1 @ ptrs2)                                                         *)
(*   | EInfer { formula_inf_continuation = sf } ->                                                *)
(*     look_up_reachable_ptrs_sf prog sf roots ptr_only first_ptr                                 *)

(* and look_up_reachable_ptrs_sf prog sf roots ptr_only first_ptr=                                *)
(*   let pr1 = !print_struc_formula in                                                            *)
(*   let pr2 = !print_spec_var_list in                                                            *)
(*   let pr_out = !print_spec_var_list in                                                         *)
(*   Debug.no_2 "look_up_reachable_ptrs_sf" pr1 pr2 pr_out                                        *)
(*     (fun _ _ -> look_up_reachable_ptrs_sf_x prog sf roots ptr_only first_ptr) sf roots         *)

let rec get_hprel (f:formula) =
  match f with
  | Base  ({formula_base_heap = h1;
            formula_base_pure = p1})
  | Exists ({formula_exists_heap = h1;
             formula_exists_pure = p1}) -> (
      get_hprel_h_formula h1
    )
  | Or orf  ->
    let a1 = get_hprel orf.formula_or_f1 in
    let a2 = get_hprel orf.formula_or_f2 in
    (a1@a2)

(*rel*)
and get_hprel_h_formula hf0=
  let rec helper hf=
    match hf with
    | Star { h_formula_star_h1 = hf1;
             h_formula_star_h2 = hf2}
    | StarMinus { h_formula_starminus_h1 = hf1;
                  h_formula_starminus_h2 = hf2} ->
      let hr1 = helper hf1 in
      let hr2 = helper hf2 in
      (hr1@hr2)
    | Conj { h_formula_conj_h1 = hf1;
             h_formula_conj_h2 = hf2;}
    | ConjStar { h_formula_conjstar_h1 = hf1;
                 h_formula_conjstar_h2 = hf2;}
    | ConjConj { h_formula_conjconj_h1 = hf1;
                 h_formula_conjconj_h2 = hf2;} ->
      let hr1 = (helper hf1)in
      let hr2 = (helper hf2) in
      (hr1@hr2)
    | Phase { h_formula_phase_rd = hf1;
              h_formula_phase_rw = hf2;} ->
      let hr1 = (helper hf1) in
      let hr2 = (helper hf2) in
      (hr1@hr2)
    | DataNode hd -> []
    | ViewNode hv -> []
    | ThreadNode ht -> []
    | HRel hr -> ([hr])
    | Hole _ | FrmHole _
    | HTrue
    | HFalse
    | HEmp | HVar _ -> ([])
  in
  helper hf0

let partition_heap_consj_hf hf0=
  let rec helper hf=
    match hf with
    | Star { h_formula_star_h1 = hf1;
             h_formula_star_h2 = hf2;
             h_formula_star_pos = pos} ->
      let ls1, rem1 = helper hf1 in
      let ls2, rem2 = helper hf2 in
      let n_rem =  (match rem1,rem2 with
          | (HEmp,HEmp) -> HEmp
          | (HEmp,_) -> rem2
          | (_,HEmp) -> rem1
          | _ -> Star {h_formula_star_h1 = rem1;
                       h_formula_star_h2 = rem2;
                       h_formula_star_pos = pos}
        ) in
      (ls1@ls2, n_rem)
    | StarMinus { h_formula_starminus_h1 = hf1;
                  h_formula_starminus_h2 = hf2;
                  h_formula_starminus_aliasing = al;
                  h_formula_starminus_pos = pos} ->
      let ls1, rem1 = helper hf1 in
      let ls2, rem2 = helper hf2 in
      let n_rem =  (match rem1,rem2 with
          | (HEmp,HEmp) -> HEmp
          | (HEmp,_) -> rem2
          | (_,HEmp) -> rem1
          | _ -> StarMinus { h_formula_starminus_h1 = rem1;
                             h_formula_starminus_h2 = rem2;
                             h_formula_starminus_aliasing = al;
                             h_formula_starminus_pos = pos}
        ) in
      (ls1@ls2, n_rem)
    | ConjStar  { h_formula_conjstar_h1 = hf1;
                  h_formula_conjstar_h2 = hf2;
                  h_formula_conjstar_pos = pos} ->
      let ls1, rem1 = helper hf1 in
      let ls2, rem2 = helper hf2 in
      let n_rem =  (match rem1,rem2 with
          | (HEmp,HEmp) -> HEmp
          | (HEmp,_) -> rem2
          | (_,HEmp) -> rem1
          | _ -> ConjStar { h_formula_conjstar_h1 = rem1;
                            h_formula_conjstar_h2 = rem2;
                            h_formula_conjstar_pos = pos}
        ) in
      (ls1@ls2, n_rem)
    | ConjConj { h_formula_conjconj_h1 = hf1;
                 h_formula_conjconj_h2 = hf2;
                 h_formula_conjconj_pos = pos} ->
      let ls1, rem1 = helper hf1 in
      let ls2, rem2 = helper hf2 in
      let n_rem =  (match rem1,rem2 with
          | (HEmp,HEmp) -> HEmp
          | (HEmp,_) -> rem2
          | (_,HEmp) -> rem1
          | _ -> ConjConj { h_formula_conjconj_h1 = rem1;
                            h_formula_conjconj_h2 = rem2;
                            h_formula_conjconj_pos = pos}
        ) in
      (ls1@ls2, n_rem)
    | Phase { h_formula_phase_rd = hf1;
              h_formula_phase_rw = hf2;
              h_formula_phase_pos = pos} ->
      let ls1, rem1 = helper hf1 in
      let ls2, rem2 = helper hf2 in
      let n_rem =  (match rem1,rem2 with
          | (HEmp,HEmp) -> HEmp
          | (HEmp,_) -> rem2
          | (_,HEmp) -> rem1
          | _ -> Phase { h_formula_phase_rd = rem1;
                         h_formula_phase_rw = rem2;
                         h_formula_phase_pos = pos}
        ) in
      (ls1@ls2, n_rem)
    | Conj { h_formula_conj_h1 = hf1;
             h_formula_conj_h2 = hf2;} -> ([hf1;hf2], HEmp)
    | DataNode _  | ViewNode _ | HRel _ | Hole _ | FrmHole _
    | ThreadNode _
    | HTrue  | HFalse | HEmp | HVar _ -> ([], hf)
  in
  helper hf0

let partition_heap_consj_x (f0:formula) =
  let rec helper f=
    match f with
    | Base fb ->
      let cons_hfs, rem_hf = partition_heap_consj_hf fb.formula_base_heap in
      (cons_hfs, Base {fb with formula_base_heap = rem_hf })
    | Exists _ ->
      let qvars, base_f = split_quantifiers f in
      let cons_hfs, rem_f = helper base_f in
      (cons_hfs, add_quantifiers qvars rem_f)
    | Or _  ->
      report_error no_pos "CF.partition_heap_consj: disj is not accepted"
  in
  helper f0

let partition_heap_consj (f0:formula) =
  let pr1 = !print_formula in
  let pr2 = pr_list_ln !print_h_formula in
  Debug.no_1 "partition_heap_consj" pr1 (pr_pair pr2 pr1)
    (fun _ -> partition_heap_consj_x f0) f0

let rec eq_svl ls1 ls2=
  match ls1,ls2 with
  | [],[] -> true
  | sv1::rest1,sv2::rest2 -> if CP.eq_spec_var sv1 sv2 then
      eq_svl rest1 rest2
    else false
  | _ -> false

let eq_hpargs (hp1,args1) (hp2,args2)=
  if (CP.eq_spec_var hp1 hp2) then
    (* let args1 = (List.fold_left List.append [] (List.map CP.afv eargs1)) in *)
    (* let args2 = (List.fold_left List.append [] (List.map CP.afv eargs2)) in *)
    eq_svl args1 args2
  else
    false

let eq_hprel (hp1,eargs1,_) (hp2,eargs2,_)=
  if (CP.eq_spec_var hp1 hp2) then
    let args1 = (List.fold_left List.append [] (List.map CP.afv eargs1)) in
    let args2 = (List.fold_left List.append [] (List.map CP.afv eargs2)) in
    eq_svl args1 args2
  else
    false

let rec get_one_kind_heap_h fn hf0=
  let rec helper hf=
    match hf with
    | Star { h_formula_star_h1 = hf1;
             h_formula_star_h2 = hf2}
    | StarMinus { h_formula_starminus_h1 = hf1;
                  h_formula_starminus_h2 = hf2} ->
      (helper hf1)@(helper hf2)
    | Conj { h_formula_conj_h1 = hf1;
             h_formula_conj_h2 = hf2;}
    | ConjStar { h_formula_conjstar_h1 = hf1;
                 h_formula_conjstar_h2 = hf2;}
    | ConjConj { h_formula_conjconj_h1 = hf1;
                 h_formula_conjconj_h2 = hf2;} ->
      (helper hf1)@(helper hf2)
    | Phase { h_formula_phase_rd = hf1;
              h_formula_phase_rw = hf2;} ->
      (helper hf1)@(helper hf2)
    | DataNode hd -> fn hf
    | ViewNode hv -> fn hf
    | ThreadNode hv -> fn hf
    | HRel (rl,_,_) ->fn hf
    | Hole _ | FrmHole _
    | HTrue
    | HFalse
    | HEmp | HVar _ -> fn hf
  in
  helper hf0

let get_one_kind_heap fnc (f0: formula) =
  let rec helper f=
    match f with
    | Base  ({formula_base_heap = h1;
              formula_base_pure = p1})
    | Exists ({ formula_exists_heap = h1;
                formula_exists_pure = p1}) -> get_one_kind_heap_h fnc h1
    | Or orf  ->
      ((helper orf.formula_or_f1)@
       (helper orf.formula_or_f2))
  in
  helper f0

let rec get_hp_rel_name_h_formula hf=
  match hf with
  | Star { h_formula_star_h1 = hf1;
           h_formula_star_h2 = hf2}
  | StarMinus { h_formula_starminus_h1 = hf1;
                h_formula_starminus_h2 = hf2} ->
    (get_hp_rel_name_h_formula hf1)@(get_hp_rel_name_h_formula hf2)
  | Conj { h_formula_conj_h1 = hf1;
           h_formula_conj_h2 = hf2;}
  | ConjStar { h_formula_conjstar_h1 = hf1;
               h_formula_conjstar_h2 = hf2;}
  | ConjConj { h_formula_conjconj_h1 = hf1;
               h_formula_conjconj_h2 = hf2;} ->
    (get_hp_rel_name_h_formula hf1)@(get_hp_rel_name_h_formula hf2)
  | Phase { h_formula_phase_rd = hf1;
            h_formula_phase_rw = hf2;} ->
    (get_hp_rel_name_h_formula hf1)@(get_hp_rel_name_h_formula hf2)
  | DataNode hd -> []
  | ViewNode hv -> []
  | ThreadNode hv -> []
  | HRel (rl,_,_) -> [rl]
  | Hole _ | FrmHole _
  | HTrue
  | HFalse
  | HEmp | HVar _ -> []

let rec get_hp_rel_name_formula_x (f0: formula) =
  (* let rec helper f= *)
  (* match f with *)
  (*   | Base  ({formula_base_heap = h1; *)
  (*     formula_base_pure = p1}) *)
  (*   | Exists ({ formula_exists_heap = h1; *)
  (*     formula_exists_pure = p1}) -> get_hp_rel_name_h_formula h1 *)
  (*   | Or orf  -> *)
  (*         CP.remove_dups_svl ((helper orf.formula_or_f1)@ *)
  (*             (helper orf.formula_or_f2)) *)
  (* in *)
  (* helper f0 *)
  let hrel_fnc hf = match hf with
    | HRel (rl,_,_) -> [hf]
    | _ -> []
  in
  let hrels = get_one_kind_heap hrel_fnc f0 in
  let hrel_svl = List.map (fun h -> match h with
      | HRel (rl,_,_) -> rl
      | _ -> report_error no_pos "CF.get_hp_rel_name_formula"
    ) hrels
  in
  CP.remove_dups_svl hrel_svl

let get_hp_rel_name_formula (f: formula) =
  let pr1 = !print_formula in
  let pr2 = !CP.print_svl in
  Debug.no_1 "get_hp_rel_name_formula" pr1 pr2
    (fun _ -> get_hp_rel_name_formula_x f) f

let get_hp_rel_name_bformula bf=
  get_hp_rel_name_formula (Base bf)

let get_hp_rel_name_struc sf0=
  let rec helper sf=
    let helper_list sfs =  List.fold_left (fun r (_,sf1) -> r@(helper sf1)) [] sfs in
    match sf with
    | EList sfs -> helper_list sfs
    | ECase { formula_case_branches = sfs } -> helper_list sfs
    | EBase { formula_struc_base = f; formula_struc_continuation = sf_opt } ->
      let vns1 = get_hp_rel_name_formula f in
      let vns2 = (match sf_opt with
          | None -> []
          | Some sf -> helper sf
        ) in
      (vns1 @ vns2)
    | EAssume { formula_assume_simpl = f; formula_assume_struc = sf} ->
      let vns1 = get_hp_rel_name_formula f in
      let vns2 = helper sf in
      (vns1 @ vns2)
    | EInfer { formula_inf_continuation = sf } -> helper sf
  in
  CP.remove_dups_svl (helper sf0)

let get_vnodes_x (f: formula) =
  let get_view_node hf=
    match hf with
    | ViewNode _ -> [hf]
    | _ -> []
  in
  get_one_kind_heap get_view_node f

let get_vnodes (f: formula) =
  let pr1 = !print_formula in
  let pr2 = pr_list_ln !print_h_formula in
  Debug.no_1 "get_vnodes" pr1 pr2
    (fun _ -> get_vnodes_x f) f

let get_vptrs_x (f: formula) =
  let get_view_ptr hf=
    match hf with
    | ViewNode vn -> [vn.h_formula_view_node]
    | _ -> []
  in
  get_one_kind_heap get_view_ptr f

let get_vptrs (f: formula) =
  let pr1 = !print_formula in
  let pr2 = pr_list_ln !print_sv in
  Debug.no_1 "get_vptrs" pr1 pr2
    (fun _ -> get_vptrs_x f) f


let get_views (f: formula) =
  let get_vn hf=
    match hf with
    | ViewNode vn -> [vn]
    | _ -> []
  in
  get_one_kind_heap get_vn f

let get_datas (f: formula) =
  let get_data hf=
    match hf with
    | DataNode dn -> [dn]
    | _ -> []
  in
  get_one_kind_heap get_data f

let get_dnodes (f: formula) =
  let get_dn hf=
    match hf with
    | DataNode dn -> [hf]
    | _ -> []
  in
  get_one_kind_heap get_dn f

let get_dptrs_x (f: formula) =
  let get_data_ptr hf=
    match hf with
    | DataNode dn -> [dn.h_formula_data_node]
    | _ -> []
  in
  get_one_kind_heap get_data_ptr f

let get_dptrs (f: formula) =
  let pr1 = !print_formula in
  let pr2 = pr_list_ln !print_sv in
  Debug.no_1 "get_dptrs" pr1 pr2
    (fun _ -> get_dptrs_x f) f

let is_rec_br vn f=
  let vns = get_views f in
  List.exists (fun v -> String.compare v.h_formula_view_name vn = 0) vns

let is_inductive f =
  let vns = get_views f in
  List.length vns > 0

let get_views_struc sf0=
  let rec helper sf=
    let helper_list sfs =  List.fold_left (fun r (_,sf1) -> r@(helper sf1)) [] sfs in
    match sf with
    | EList sfs -> helper_list sfs
    | ECase { formula_case_branches = sfs } -> helper_list sfs
    | EBase { formula_struc_base = f; formula_struc_continuation = sf_opt } ->
      let vns1 = get_views f in
      let vns2 = (match sf_opt with
          | None -> []
          | Some sf -> helper sf
        ) in
      (vns1 @ vns2)
    | EAssume { formula_assume_simpl = f; formula_assume_struc = sf} ->
      let vns1 = get_views f in
      let vns2 = helper sf in
      (vns1 @ vns2)
    | EInfer { formula_inf_continuation = sf } -> helper sf
  in
  helper sf0

let get_datas_struc sf0=
  let rec helper sf=
    let helper_list sfs =  List.fold_left (fun r (_,sf1) -> r@(helper sf1)) [] sfs in
    match sf with
    | EList sfs -> helper_list sfs
    | ECase { formula_case_branches = sfs } -> helper_list sfs
    | EBase { formula_struc_base = f; formula_struc_continuation = sf_opt } ->
      let vns1 = get_datas f in
      let vns2 = (match sf_opt with
          | None -> []
          | Some sf -> helper sf
        ) in
      (vns1 @ vns2)
    | EAssume { formula_assume_simpl = f; formula_assume_struc = sf} ->
      let vns1 = get_datas f in
      let vns2 = helper sf in
      (vns1 @ vns2)
    | EInfer { formula_inf_continuation = sf } -> helper sf
  in
  helper sf0

let get_hp_rel_name_assumption cs=
  CP.remove_dups_svl ((get_hp_rel_name_formula cs.hprel_lhs)@
                      (get_hp_rel_name_formula cs.hprel_rhs))

let get_hp_rel_name_assumption_set constrs=
  let all_hps = List.fold_left (fun ls cs -> ls@(get_hp_rel_name_assumption cs))
      [] constrs in
  (CP.remove_dups_svl all_hps)

let do_unfold_view_hf cprog pr_views hf0 =
  let fold_fnc ls1 ls2 aux_fnc = List.fold_left (fun r (hf2, p2) ->
      let in_r = List.map (fun (hf1, p1) ->
          let nh = aux_fnc hf1 hf2 in
          let np = x_add MCP.merge_mems p1 p2 true in
          (nh, np)
        ) ls1 in
      r@in_r
    ) [] ls2 in
  let rec look_up_vdef ls_pr_views vname=
    match ls_pr_views with
    | [] -> raise Not_found
    | (vname1, def, vars)::rest -> if String.compare vname vname1 = 0 then (vname, def, vars) else
        look_up_vdef rest vname
  in
  let fresh_var args f=
    let qvars, base1 = split_quantifiers f in
    let () = DD.ninfo_hprint (add_str "qvars" !CP.print_svl) qvars no_pos in
    let fr_qvars = CP.fresh_spec_vars qvars in
    let ss = List.combine qvars fr_qvars in
    let nf = x_add subst ss base1 in
    add_quantifiers fr_qvars ( nf)
  in
  let rec helper hf=
    match hf with
    | Star { h_formula_star_h1 = hf1;
             h_formula_star_h2 = hf2;
             h_formula_star_pos = pos} ->
      let ls_hf_p1 = helper hf1 in
      let ls_hf_p2 = helper hf2 in
      let star_fnc h1 h2 =
        Star {h_formula_star_h1 = h1;
              h_formula_star_h2 = h2;
              h_formula_star_pos = pos}
      in
      fold_fnc ls_hf_p1 ls_hf_p2 star_fnc
    | StarMinus { h_formula_starminus_h1 = hf1;
                  h_formula_starminus_h2 = hf2;
                  h_formula_starminus_aliasing = al;
                  h_formula_starminus_pos = pos} ->
      let ls_hf_p1 = helper hf1 in
      let ls_hf_p2 = helper hf2 in
      let starminus_fnc h1 h2 =
        StarMinus {h_formula_starminus_h1 = h1;
                   h_formula_starminus_h2 = h2;
                   h_formula_starminus_aliasing = al;
                   h_formula_starminus_pos = pos}
      in
      fold_fnc ls_hf_p1 ls_hf_p2 starminus_fnc
    | ConjStar  { h_formula_conjstar_h1 = hf1;
                  h_formula_conjstar_h2 = hf2;
                  h_formula_conjstar_pos = pos} ->
      let ls_hf_p1 = helper hf1 in
      let ls_hf_p2 = helper hf2 in
      let conjstar_fnc h1 h2 = ConjStar { h_formula_conjstar_h1 = h1;
                                          h_formula_conjstar_h2 = h2;
                                          h_formula_conjstar_pos = pos}
      in
      fold_fnc ls_hf_p1 ls_hf_p2 conjstar_fnc
    | ConjConj { h_formula_conjconj_h1 = hf1;
                 h_formula_conjconj_h2 = hf2;
                 h_formula_conjconj_pos = pos} ->
      let ls_hf_p1 = helper hf1 in
      let ls_hf_p2 = helper hf2 in
      let conjconj_fnc h1 h2 = ConjConj { h_formula_conjconj_h1 = h1;
                                          h_formula_conjconj_h2 = h2;
                                          h_formula_conjconj_pos = pos}
      in
      fold_fnc ls_hf_p1 ls_hf_p2 conjconj_fnc
    | Phase { h_formula_phase_rd = hf1;
              h_formula_phase_rw = hf2;
              h_formula_phase_pos = pos} ->
      let ls_hf_p1 = helper hf1 in
      let ls_hf_p2 = helper hf2 in
      let phase_fnc h1 h2 = Phase { h_formula_phase_rd = h1;
                                    h_formula_phase_rw = h2;
                                    h_formula_phase_pos = pos}
      in
      fold_fnc ls_hf_p1 ls_hf_p2 phase_fnc
    | Conj { h_formula_conj_h1 = hf1;
             h_formula_conj_h2 = hf2;
             h_formula_conj_pos = pos} ->
      let ls_hf_p1 = helper hf1 in
      let ls_hf_p2 = helper hf2 in
      let conj_fnc h1 h2 = Conj { h_formula_conj_h1 = h1;
                                  h_formula_conj_h2 = h2;
                                  h_formula_conj_pos = pos}
      in
      fold_fnc ls_hf_p1 ls_hf_p2 conj_fnc
    | ViewNode hv -> begin
        try
          let (v_name,v_un_struc_formula, v_vars) = look_up_vdef pr_views hv.h_formula_view_name in
          let f_args = (CP.SpecVar (Named v_name,self, Unprimed))::v_vars in
          let fs = List.map (fun (f,_) -> fresh_var f_args f) v_un_struc_formula in
          let a_args = hv.h_formula_view_node::hv.h_formula_view_arguments in
          let ss = List.combine f_args  a_args in
          let fs1 = List.map (x_add subst ss) fs in
          List.map (fun f -> (List.hd (heap_of f), MCP.mix_of_pure (get_pure f))) fs1
        with _ -> report_error no_pos ("LEM.do_unfold_view_hf: can not find view " ^ hv.h_formula_view_name)
      end
    | ThreadNode _
    | DataNode _  | HRel _ | Hole _ | FrmHole _
    | HTrue  | HFalse | HEmp | HVar _ -> [(hf, MCP.mix_of_pure (CP.mkTrue no_pos))]
  in
  helper hf0

(* let rec struc_formula_trans_heap_node2 formula_fct hf_fct f = *)
(*   let recf = struc_formula_trans_heap_node2 formula_fct  hf_fct in *)
(*   match f with *)
(*     | ECase b-> ECase {b with formula_case_branches= Gen.map_l_snd recf b.formula_case_branches} *)
(*     | EBase b -> EBase {b with *)
(* 	  formula_struc_continuation = Gen.map_opt recf b.formula_struc_continuation; *)
(* 	  formula_struc_base=(\* formula_trans_heap_node fct *\)formula_fct hf_fct b.formula_struc_base;} *)
(*     | EAssume ea-> EAssume {ea with  formula_assume_simpl = (\* formula_trans_heap_node fct *\) *)
(*               formula_fct hf_fct ea.formula_assume_simpl; *)
(*           formula_assume_struc = recf ea.formula_assume_struc} *)
(*           (\* (formula_trans_heap_node fct f, fl, et) *\) *)
(*     | EInfer b -> EInfer {b with formula_inf_continuation = recf b.formula_inf_continuation} *)
(*     | EList l -> EList (Gen.map_l_snd recf l) *)

let fresh_data_v is_pre f0=
  let rec helper f= match f with
    | Base _
    | Exists _ ->
      let quans, f0 = split_quantifiers f in
      let hds, hvs, hrs = get_hp_rel_formula f0 in
      let v_sps1 = List.fold_left (fun r hd -> r@(List.filter (fun sv -> not (CP.is_node_typ sv)) hd.h_formula_data_arguments)) [] hds in
      let v_sps2 = List.fold_left (fun r hd -> r@(List.filter (fun sv -> not (CP.is_node_typ sv)) hd.h_formula_view_arguments)) v_sps1 hvs in
      (* sleek7. strings/ex9ec *)
      if is_pre then
        let quans = CP.diff_svl quans v_sps2 in
        add_quantifiers quans f0, v_sps2
      else
      (*   f, CP.diff_svl v_sps2 quans *)
        f, CP.diff_svl (CP.remove_dups_svl v_sps2) quans
    | Or orf ->
          let n_f1, impl_svl1 = (helper orf.formula_or_f1) in
          let n_f2, impl_svl2 = (helper orf.formula_or_f2) in
          Or {orf with formula_or_f1 = n_f1; formula_or_f2 = n_f2}, CP.remove_dups_svl (impl_svl1@impl_svl2)
  in
  helper f0

let fresh_data_v_no_change is_pre f= f,[]

let rec struc_formula_trans_heap_node pre_quans formula_fct f=
  let recf pre_quans1 = struc_formula_trans_heap_node pre_quans1 formula_fct in
  let process_post_disj f0=
    let cur_quans, f1_bare = split_quantifiers f0 in
    let quans0 = CP.diff_svl (cur_quans@ (snd (fresh_data_v false f0))) pre_quans in
    let quans = List.filter (fun (CP.SpecVar (_,id,_)) -> not(string_eq id res_name)) quans0 in
    add_quantifiers quans f1_bare
  in
  match f with
  | ECase b-> ECase {b with formula_case_branches= Gen.map_l_snd (recf pre_quans) b.formula_case_branches}
  | EBase b ->
    let f1= formula_fct b.formula_struc_base in
    let () =  x_tinfo_hp (add_str " b.formula_struc_base pre" (!print_formula)) b.formula_struc_base no_pos in
    let () =  x_tinfo_hp (add_str "f1 pre" (!print_formula)) f1 no_pos in
    (* Loc: to split into case spec *)
    let _, new_pre_quans =  fresh_data_v true f1(* b.formula_struc_base *) in
    (* WN : Why must this new_pre_quans be added to implicit_inst?? *)
    (* I think this is probably not needed, as it is focussed on non-ptr fields *)
    let impl_vs = b.formula_struc_implicit_inst in
    let new_pre_quans =
      if !Globals.old_impl_gather then CP.diff_svl new_pre_quans impl_vs
      else []
    in
    let pre_cur_quans = CP.remove_dups_svl (impl_vs@(new_pre_quans)) in
    let pre_quans1 = CP.remove_dups_svl (pre_quans@pre_cur_quans) in
    let () =  x_tinfo_hp (add_str "new_pre_quans" (!CP.print_svl)) new_pre_quans no_pos in
    let () =  x_tinfo_hp (add_str "pre_quans" (!CP.print_svl)) pre_quans no_pos in
    let () =  x_tinfo_hp (add_str "pre_quans1" (!CP.print_svl)) pre_quans1 no_pos in
    let () =  x_tinfo_hp (add_str "new impl?" (!CP.print_svl)) pre_cur_quans no_pos in
    EBase {b with
           (* what is this map_opt recf for? *)
           formula_struc_continuation = Gen.map_opt (recf pre_quans1) b.formula_struc_continuation;
           formula_struc_implicit_inst =
             if !Globals.old_impl_gather then pre_cur_quans
             else impl_vs ;
           formula_struc_exists =
             if !Globals.old_impl_gather then b.formula_struc_exists
             else CP.remove_dups_svl (b.formula_struc_exists@(new_pre_quans));
           formula_struc_base=(* formula_trans_heap_node fct *)f1;
          }
  | EAssume ea-> begin
      let f1 = formula_fct ea.formula_assume_simpl in
      let () =  x_tinfo_hp (add_str "f1 post" (!print_formula)) f1 no_pos in
      let () =  x_tinfo_hp (add_str "pre_quans:post" (!CP.print_svl)) pre_quans no_pos in
      let fs = list_of_disjs f1 in
      let ass_sf =  (recf pre_quans) ea.formula_assume_struc in
      let sfs1 = List.map (fun f ->
          EAssume {ea with  formula_assume_simpl = process_post_disj f;
                            formula_assume_struc =ass_sf  }
        ) fs in
      match sfs1 with
      | [] -> report_error no_pos "Cformula. struc_formula_trans_heap_node"
      | [sf] -> sf
      | _ -> EList (List.map (fun sf -> (empty_spec_label_def, sf)) sfs1)
      (* let cur_quans, f1_bare = split_quantifiers f1 in *)
      (* let quans = CP.diff_svl (cur_quans@(fresh_data_v f1)) pre_quans in *)
      (* EAssume {ea with  formula_assume_simpl = (\* formula_trans_heap_node fct *\) (\* formula_fct ea.formula_assume_simpl *\) add_quantifiers quans f1_bare; *)
      (* formula_assume_struc = (recf pre_quans) ea.formula_assume_struc} *)
      (* (formula_trans_heap_node fct f, fl, et) *)
    end
  | EInfer b -> EInfer {b with formula_inf_continuation = (recf pre_quans) b.formula_inf_continuation}
  | EList l -> EList (Gen.map_l_snd (recf pre_quans) l)

let struc_formula_trans_heap_node pre_quans fct f =
  let pr = !print_struc_formula in
  Debug.no_1 "struc_formula_trans_heap_node" pr pr
    (struc_formula_trans_heap_node pre_quans fct) f

let do_unfold_view_x cprog pr_views (f0: formula) =
  let rec helper f=
    match f with
    | Base fb ->
      let ls_hf_pure = do_unfold_view_hf cprog  pr_views fb.formula_base_heap in
      let fs = List.map (fun (hf, p) -> Base {fb with formula_base_heap = hf;
                                                      formula_base_pure = x_add MCP.merge_mems p fb.formula_base_pure true;
                                             }) ls_hf_pure in
      disj_of_list fs fb.formula_base_pos
    | Exists _ ->
      let qvars, base1 = split_quantifiers f in
      let nf = helper base1 in
      add_quantifiers qvars ( nf)
    | Or orf  ->
      Or { orf with formula_or_f1 = helper orf.formula_or_f1;
                    formula_or_f2 = helper orf.formula_or_f2 }
  in
  if pr_views = [] then f0 else helper f0

let do_unfold_view cprog pr_views (f0: formula) =
  let pr1 = !print_formula in
  Debug.no_1 "CF.do_unfold_view" pr1 pr1
    (fun _ -> do_unfold_view_x cprog pr_views f0) f0

(*******UNFOLD HP DEF**************************)
let do_unfold_hp_def_hf cprog pr_hp_defs hf0 =
  let fold_fnc ls1 ls2 aux_fnc = List.fold_left (fun r (hf2, p2) ->
      let in_r = List.map (fun (hf1, p1) ->
          let nh = aux_fnc hf1 hf2 in
          let np = x_add MCP.merge_mems p1 p2 true in
          (nh, np)
        ) ls1 in
      r@in_r
    ) [] ls2 in
  let rec look_up_hp_def ls_pr_hp_defs hp=
    match ls_pr_hp_defs with
    | [] -> raise Not_found
    | (hp1, def, vars)::rest -> if CP.eq_spec_var hp hp1 then (hp, def, vars) else
        look_up_hp_def rest hp
  in
  (* let fresh_var args f= *)
  (*   let qvars, base1 = split_quantifiers f in *)
  (*   let () = DD.ninfo_hprint (add_str "qvars" !CP.print_svl) qvars no_pos in *)
  (*   let fr_qvars = CP.fresh_spec_vars qvars in *)
  (*   let ss = List.combine qvars fr_qvars in *)
  (*   let nf = subst ss base1 in *)
  (*   add_quantifiers fr_qvars ( nf) *)
  (* in *)
  let rec helper hf=
    match hf with
    | Star { h_formula_star_h1 = hf1;
             h_formula_star_h2 = hf2;
             h_formula_star_pos = pos} ->
      let ls_hf_p1 = helper hf1 in
      let ls_hf_p2 = helper hf2 in
      let star_fnc h1 h2 =
        Star {h_formula_star_h1 = h1;
              h_formula_star_h2 = h2;
              h_formula_star_pos = pos}
      in
      fold_fnc ls_hf_p1 ls_hf_p2 star_fnc
    | StarMinus { h_formula_starminus_h1 = hf1;
                  h_formula_starminus_h2 = hf2;
                  h_formula_starminus_aliasing = al;
                  h_formula_starminus_pos = pos} ->
      let ls_hf_p1 = helper hf1 in
      let ls_hf_p2 = helper hf2 in
      let starminus_fnc h1 h2 =
        StarMinus {h_formula_starminus_h1 = h1;
                   h_formula_starminus_h2 = h2;
                   h_formula_starminus_aliasing = al;
                   h_formula_starminus_pos = pos}
      in
      fold_fnc ls_hf_p1 ls_hf_p2 starminus_fnc
    | ConjStar  { h_formula_conjstar_h1 = hf1;
                  h_formula_conjstar_h2 = hf2;
                  h_formula_conjstar_pos = pos} ->
      let ls_hf_p1 = helper hf1 in
      let ls_hf_p2 = helper hf2 in
      let conjstar_fnc h1 h2 = ConjStar { h_formula_conjstar_h1 = h1;
                                          h_formula_conjstar_h2 = h2;
                                          h_formula_conjstar_pos = pos}
      in
      fold_fnc ls_hf_p1 ls_hf_p2 conjstar_fnc
    | ConjConj { h_formula_conjconj_h1 = hf1;
                 h_formula_conjconj_h2 = hf2;
                 h_formula_conjconj_pos = pos} ->
      let ls_hf_p1 = helper hf1 in
      let ls_hf_p2 = helper hf2 in
      let conjconj_fnc h1 h2 = ConjConj { h_formula_conjconj_h1 = h1;
                                          h_formula_conjconj_h2 = h2;
                                          h_formula_conjconj_pos = pos}
      in
      fold_fnc ls_hf_p1 ls_hf_p2 conjconj_fnc
    | Phase { h_formula_phase_rd = hf1;
              h_formula_phase_rw = hf2;
              h_formula_phase_pos = pos} ->
      let ls_hf_p1 = helper hf1 in
      let ls_hf_p2 = helper hf2 in
      let phase_fnc h1 h2 = Phase { h_formula_phase_rd = h1;
                                    h_formula_phase_rw = h2;
                                    h_formula_phase_pos = pos}
      in
      fold_fnc ls_hf_p1 ls_hf_p2 phase_fnc
    | Conj { h_formula_conj_h1 = hf1;
             h_formula_conj_h2 = hf2;
             h_formula_conj_pos = pos} ->
      let ls_hf_p1 = helper hf1 in
      let ls_hf_p2 = helper hf2 in
      let conj_fnc h1 h2 = Conj { h_formula_conj_h1 = h1;
                                  h_formula_conj_h2 = h2;
                                  h_formula_conj_pos = pos}
      in
      fold_fnc ls_hf_p1 ls_hf_p2 conj_fnc
    | HRel (hp, eargs, pos) ->begin
        try
          let (hp,hp_def, f_args) = look_up_hp_def pr_hp_defs hp in
          let fs = List.fold_left (fun r (f,_) -> r@(list_of_disjs f)) [] hp_def.def_rhs in
          let a_args = List.fold_left List.append [] (List.map CP.afv eargs) in
          let ss = List.combine f_args  a_args in
          let fs1 = List.map (x_add subst ss) fs in
          List.map (fun f -> (List.hd (heap_of f), MCP.mix_of_pure (get_pure f))) fs1
        with _ -> [(hf, MCP.mix_of_pure (CP.mkTrue no_pos))]
      end
    | DataNode _  | ViewNode _ | Hole _ | FrmHole _
    | ThreadNode _
    | HTrue  | HFalse | HEmp | HVar _ -> [(hf, MCP.mix_of_pure (CP.mkTrue no_pos))]
  in
  helper hf0

let do_unfold_hp_def_x cprog pr_hp_defs (f0: formula) =
  let rec helper f=
    match f with
    | Base fb ->
      let ls_hf_pure = do_unfold_hp_def_hf cprog pr_hp_defs fb.formula_base_heap in
      let fs = List.map (fun (hf, p) -> Base {fb with formula_base_heap = hf;
                                                      formula_base_pure = x_add MCP.merge_mems p fb.formula_base_pure true;
                                             }) ls_hf_pure in
      disj_of_list fs fb.formula_base_pos
    | Exists _ ->
      let qvars, base1 = split_quantifiers f in
      let nf = helper base1 in
      add_quantifiers qvars ( nf)
    | Or orf  ->
      Or { orf with formula_or_f1 = helper orf.formula_or_f1;
                    formula_or_f2 = helper orf.formula_or_f2 }
  in
  if pr_hp_defs = [] then f0 else helper f0

let do_unfold_hp_def cprog pr_hp_defs (f0: formula) =
  let pr1 = !print_formula in
  Debug.no_1 "CF.do_unfold_hp_def" pr1 pr1
    (fun _ -> do_unfold_hp_def_x cprog pr_hp_defs f0) f0



(*******************************)

let rec get_hp_rel_vars_formula (f: formula) =
  match f with
  | Base  ({formula_base_heap = h1;
            formula_base_pure = p1})
  | Exists ({ formula_exists_heap = h1;
              formula_exists_pure = p1}) -> get_hp_rel_vars_h_formula h1
  | Or orf  -> (get_hp_rel_vars_formula orf.formula_or_f1)@
               (get_hp_rel_vars_formula orf.formula_or_f2)

and get_hp_rel_vars_bformula bf=
  get_hp_rel_vars_h_formula bf.formula_base_heap

and get_hp_rel_vars_h_formula_x hf=
  match hf with
  | Star { h_formula_star_h1 = hf1;
           h_formula_star_h2 = hf2}
  | StarMinus { h_formula_starminus_h1 = hf1;
                h_formula_starminus_h2 = hf2} ->
    (get_hp_rel_vars_h_formula_x hf1)@(get_hp_rel_vars_h_formula_x hf2)
  | Conj { h_formula_conj_h1 = hf1;
           h_formula_conj_h2 = hf2;}
  | ConjStar { h_formula_conjstar_h1 = hf1;
               h_formula_conjstar_h2 = hf2;}
  | ConjConj { h_formula_conjconj_h1 = hf1;
               h_formula_conjconj_h2 = hf2;} ->
    (get_hp_rel_vars_h_formula_x hf1)@(get_hp_rel_vars_h_formula_x hf2)
  | Phase { h_formula_phase_rd = hf1;
            h_formula_phase_rw = hf2;} ->
    (get_hp_rel_vars_h_formula_x hf1)@(get_hp_rel_vars_h_formula_x hf2)
  | DataNode hd -> []
  | ViewNode hv -> []
  | ThreadNode ht -> []
  | HRel (rl,args,_) -> [rl]@(CP.remove_dups_svl (List.fold_left List.append [] (List.map CP.afv args)))
  | Hole _ | FrmHole _
  | HTrue
  | HFalse
  | HEmp | HVar _ -> []

and get_hp_rel_vars_h_formula hf=
  let pr1= !print_h_formula in
  let pr2 = !print_svl in
  Debug.no_1 "get_hp_rel_vars_h_formula" pr1 pr2
    ( fun _ -> get_hp_rel_vars_h_formula_x hf) hf

and filter_irr_hp_lhs_bf bf relevant_vars =
  {bf with formula_base_heap = filter_irr_hp_lhs_hf bf.formula_base_heap relevant_vars;}

and filter_irr_hp_lhs_hf hf relevant_vars=
  match hf with
  | Star {h_formula_star_h1 = hf1;
          h_formula_star_h2 = hf2;
          h_formula_star_pos = pos} ->
    let n_hf1 = filter_irr_hp_lhs_hf hf1 relevant_vars in
    let n_hf2 = filter_irr_hp_lhs_hf hf2 relevant_vars in
    (match n_hf1,n_hf2 with
     | (HEmp,HEmp) -> HEmp
     | (HEmp,_) -> n_hf2
     | (_,HEmp) -> n_hf1
     | _ -> Star {h_formula_star_h1 = n_hf1;
                  h_formula_star_h2 = n_hf2;
                  h_formula_star_pos = pos}
    )
  | StarMinus { h_formula_starminus_h1 = hf1;
                h_formula_starminus_h2 = hf2;
                h_formula_starminus_aliasing = al;
                h_formula_starminus_pos = pos} ->
    let n_hf1 = filter_irr_hp_lhs_hf hf1 relevant_vars in
    let n_hf2 = filter_irr_hp_lhs_hf hf2 relevant_vars in
    StarMinus { h_formula_starminus_h1 = n_hf1;
                h_formula_starminus_h2 = n_hf2;
                h_formula_starminus_aliasing = al;
                h_formula_starminus_pos = pos}
  | Conj { h_formula_conj_h1 = hf1;
           h_formula_conj_h2 = hf2;
           h_formula_conj_pos = pos} ->
    let n_hf1 = filter_irr_hp_lhs_hf hf1 relevant_vars in
    let n_hf2 = filter_irr_hp_lhs_hf hf2 relevant_vars in
    Conj { h_formula_conj_h1 = n_hf1;
           h_formula_conj_h2 = n_hf2;
           h_formula_conj_pos = pos}
  | ConjStar { h_formula_conjstar_h1 = hf1;
               h_formula_conjstar_h2 = hf2;
               h_formula_conjstar_pos = pos} ->
    let n_hf1 = filter_irr_hp_lhs_hf hf1 relevant_vars in
    let n_hf2 = filter_irr_hp_lhs_hf hf2 relevant_vars in
    ConjStar { h_formula_conjstar_h1 = n_hf1;
               h_formula_conjstar_h2 = n_hf2;
               h_formula_conjstar_pos = pos}
  | ConjConj { h_formula_conjconj_h1 = hf1;
               h_formula_conjconj_h2 = hf2;
               h_formula_conjconj_pos = pos} ->
    let n_hf1 = filter_irr_hp_lhs_hf hf1 relevant_vars in
    let n_hf2 = filter_irr_hp_lhs_hf hf2 relevant_vars in
    ConjConj { h_formula_conjconj_h1 = n_hf1;
               h_formula_conjconj_h2 = n_hf2;
               h_formula_conjconj_pos = pos}
  | Phase { h_formula_phase_rd = hf1;
            h_formula_phase_rw = hf2;
            h_formula_phase_pos = pos} ->
    let n_hf1 = filter_irr_hp_lhs_hf hf1 relevant_vars in
    let n_hf2 = filter_irr_hp_lhs_hf hf2 relevant_vars in
    Phase { h_formula_phase_rd = n_hf1;
            h_formula_phase_rw = n_hf2;
            h_formula_phase_pos = pos}
  | DataNode hd -> hf
  | ViewNode hv -> hf
  | ThreadNode ht -> hf
  | HRel (_, args, _) -> let args_vars = (CP.remove_dups_svl (List.fold_left List.append [] (List.map CP.afv args))) in
    if  CP.intersect args_vars relevant_vars = [] then HEmp
    else hf
  | Hole _ | FrmHole _
  | HTrue
  | HFalse
  | HEmp | HVar _ -> hf

and filter_vars_hf hf rvs=
  match hf with
  | Star {h_formula_star_h1 = hf1;
          h_formula_star_h2 = hf2;
          h_formula_star_pos = pos} ->
    let n_hf1 =  filter_vars_hf hf1 rvs in
    let n_hf2 = filter_vars_hf hf2 rvs in
    (match n_hf1,n_hf2 with
     | (HEmp,HEmp) -> HEmp
     | (HEmp,_) -> n_hf2
     | (_,HEmp) -> n_hf1
     | _ -> Star {h_formula_star_h1 = n_hf1;
                  h_formula_star_h2 = n_hf2;
                  h_formula_star_pos = pos}
    )
  | StarMinus { h_formula_starminus_h1 = hf1;
                h_formula_starminus_h2 = hf2;
                h_formula_starminus_aliasing = al;
                h_formula_starminus_pos = pos} ->
    let n_hf1 = filter_vars_hf hf1 rvs in
    let n_hf2 = filter_vars_hf hf2 rvs in
    StarMinus { h_formula_starminus_h1 = n_hf1;
                h_formula_starminus_h2 = n_hf2;
                h_formula_starminus_aliasing = al;
                h_formula_starminus_pos = pos}
  | Conj { h_formula_conj_h1 = hf1;
           h_formula_conj_h2 = hf2;
           h_formula_conj_pos = pos} ->
    let n_hf1 = filter_vars_hf hf1 rvs in
    let n_hf2 = filter_vars_hf hf2 rvs in
    Conj { h_formula_conj_h1 = n_hf1;
           h_formula_conj_h2 = n_hf2;
           h_formula_conj_pos = pos}
  | ConjStar { h_formula_conjstar_h1 = hf1;
               h_formula_conjstar_h2 = hf2;
               h_formula_conjstar_pos = pos} ->
    let n_hf1 = filter_vars_hf hf1 rvs in
    let n_hf2 = filter_vars_hf hf2 rvs in
    ConjStar { h_formula_conjstar_h1 = n_hf1;
               h_formula_conjstar_h2 = n_hf2;
               h_formula_conjstar_pos = pos}
  | ConjConj { h_formula_conjconj_h1 = hf1;
               h_formula_conjconj_h2 = hf2;
               h_formula_conjconj_pos = pos} ->
    let n_hf1 = filter_vars_hf hf1 rvs in
    let n_hf2 = filter_vars_hf hf2 rvs in
    ConjConj { h_formula_conjconj_h1 = n_hf1;
               h_formula_conjconj_h2 = n_hf2;
               h_formula_conjconj_pos = pos}
  | Phase { h_formula_phase_rd = hf1;
            h_formula_phase_rw = hf2;
            h_formula_phase_pos = pos} ->
    let n_hf1 = filter_vars_hf hf1 rvs in
    let n_hf2 = filter_vars_hf hf2 rvs in
    Phase { h_formula_phase_rd = n_hf1;
            h_formula_phase_rw = n_hf2;
            h_formula_phase_pos = pos}
  | DataNode hd -> if CP.mem_svl hd.h_formula_data_node rvs then hf
    else HEmp
  | ViewNode hv -> if CP.mem_svl hv.h_formula_view_node rvs then hf
    else HEmp
  | ThreadNode ht -> if CP.mem_svl ht.h_formula_thread_node rvs then hf
    else HEmp
  | HRel _ -> hf
  | Hole _ | FrmHole _
  | HTrue
  | HFalse
  | HEmp | HVar _ -> hf




let generate_xpure_view_x drop_hpargs total_unk_map=
  let rec lookup_xpure_view hp rem_map=
    match rem_map with
    | [] -> []
    | (hps,xpv)::tl ->
      if CP.mem_svl hp hps then
        [xpv]
      else lookup_xpure_view hp tl
  in
  let generate_xpure_view_one_hp pos (hp,args)=
    let hp_name = CP.name_of_spec_var hp in
    let p,unk_svl,unk_map =
      let xpvs = lookup_xpure_view hp total_unk_map in
      match xpvs with
      | [xp] -> let xp_r, xp_args = match xp.CP.xpure_view_node with
          | None -> None, xp.CP.xpure_view_arguments
          |Some _ -> Some (List.hd args), (List.tl args)
        in
        let new_xpv = {xp with CP.xpure_view_node =  xp_r;
                               xpure_view_arguments =  xp_args
                      }
        in
        let p = CP.mkFormulaFromXP new_xpv in
        (p,args,[])
      | [] ->
        let xpv = { CP.xpure_view_node = None;
                    CP.xpure_view_name = hp_name;
                    CP.xpure_view_arguments = args;
                    CP.xpure_view_remaining_branches= None;
                    CP.xpure_view_pos = no_pos;
                  }
        in
        let p = CP.mkFormulaFromXP xpv in
        (p,args,[([hp],xpv)])
      | _ -> report_error no_pos "cformula.generate_xpure_view: impossible"
    in
    (p,unk_svl,unk_map)
  in
  let ps,ls_fr_svl,ls_unk_map = split3 (List.map (generate_xpure_view_one_hp no_pos) drop_hpargs) in
  (List.concat ls_fr_svl,CP.conj_of_list ps no_pos,List.concat ls_unk_map)

let generate_xpure_view drop_hpargs total_unk_map=
  let pr1 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in
  let pr2 = pr_triple !CP.print_svl !CP.print_formula
      (pr_list (pr_pair !CP.print_svl CP.string_of_xpure_view)) in
  Debug.no_1 "generate_xpure_view" pr1 pr2
    (fun _ -> generate_xpure_view_x drop_hpargs total_unk_map) drop_hpargs

let annotate_dl_hf hf0 unk_hps=
  let rec helper hf=
    match hf with
    | Star {h_formula_star_h1 = hf1;
            h_formula_star_h2 = hf2;
            h_formula_star_pos = pos} ->
      let n_hf1,ps1 = helper hf1 in
      let n_hf2,ps2 = helper hf2 in
      let new_hf=
        match n_hf1,n_hf2 with
        | (HEmp,HEmp) -> HEmp
        | (HEmp,_) -> n_hf2
        | (_,HEmp) -> n_hf1
        | _ -> (Star {h_formula_star_h1 = n_hf1;
                      h_formula_star_h2 = n_hf2;
                      h_formula_star_pos = pos})
      in
      (new_hf, ps1@ps2)
    | Conj { h_formula_conj_h1 = hf1;
             h_formula_conj_h2 = hf2;
             h_formula_conj_pos = pos} ->
      let n_hf1,ps1 = helper hf1 in
      let n_hf2,ps2 = helper hf2 in
      (Conj { h_formula_conj_h1 = n_hf1;
              h_formula_conj_h2 = n_hf2;
              h_formula_conj_pos = pos}, ps1@ps2)
    | Phase { h_formula_phase_rd = hf1;
              h_formula_phase_rw = hf2;
              h_formula_phase_pos = pos} ->
      let n_hf1,ps1 = helper hf1 in
      let n_hf2,ps2 = helper hf2 in
      (Phase { h_formula_phase_rd = n_hf1;
               h_formula_phase_rw = n_hf2;
               h_formula_phase_pos = pos}, ps1@ps2)
    | DataNode hd -> (hf,[])
    | ViewNode hv -> (hf,[])
    | ThreadNode ht -> (hf,[])
    | HRel (hp, eargs, _) -> if CP.mem_svl hp unk_hps then
        let args = (List.fold_left List.append [] (List.map CP.afv eargs)) in
        let _,p,_ = generate_xpure_view [(hp,args)] [] in
        (* (HEmp,[p]) *) (hf,[p])
      else (hf,[])
    | Hole _ | FrmHole _
    | HTrue
    | HFalse
    | HEmp | HVar _ -> (hf,[])
    | StarMinus _ | ConjStar _ | ConjConj _ -> report_error no_pos "annotate_dl_hf: not handle yet"

  in
  helper hf0

let annotate_dl_x (f0: formula) unk_hps =
  let rec helper f=
    match f with
    | Base  b ->
      let new_h,ps = annotate_dl_hf b.formula_base_heap unk_hps in
      let new_p = MCP.mix_of_pure (CP.mkAnd (MCP.pure_of_mix b.formula_base_pure) (CP.conj_of_list ps no_pos) no_pos)
      in
      Base {b with (* formula_base_heap = new_h; *)
            formula_base_pure = new_p;
           }
    | Exists e ->
      let new_h,ps = annotate_dl_hf e.formula_exists_heap unk_hps in
      let new_p = MCP.mix_of_pure (CP.mkAnd (MCP.pure_of_mix e.formula_exists_pure) (CP.conj_of_list ps no_pos) no_pos) in
      Exists {e with (* formula_exists_heap = new_h; *)
              formula_exists_pure = new_p;}
    | Or orf  -> Or {orf with formula_or_f1 = helper orf.formula_or_f1;
                              formula_or_f2 = helper orf.formula_or_f2}
  in
  if unk_hps=[] then f0 else helper f0

let annotate_dl (f0: formula) unk_hps =
  let pr1 = !print_formula in
  let pr2 = !CP.print_svl in
  Debug.no_2 "annotate_dl" pr1 pr2 pr1
    (fun _ _ ->  annotate_dl_x f0 unk_hps) f0 unk_hps

let rec extract_pure (f0: formula)=
  let rec helper f=
    match f with
    | Base fb -> (MCP.pure_of_mix fb.formula_base_pure)
    | Or orf ->CP.disj_of_list [(helper orf.formula_or_f1); (helper orf.formula_or_f2)] no_pos
    | Exists fe -> (MCP.pure_of_mix fe.formula_exists_pure)
  in
  helper f0


let rec subst_hprel (f0: formula) from_hps to_hp=
  let rec helper f=
    match f with
    | Base fb -> let nh = subst_hprel_hf fb.formula_base_heap from_hps to_hp in
      (Base {fb with formula_base_heap = nh})
    | Or orf -> let nf1 = helper orf.formula_or_f1 in
      let nf2 = helper orf.formula_or_f2 in
      ( Or {orf with formula_or_f1 = nf1;
                     formula_or_f2 = nf2;})
    | Exists fe -> let nh = subst_hprel_hf fe.formula_exists_heap from_hps to_hp in
      (Exists {fe with formula_exists_heap = nh;})
  in
  if from_hps = [] then f0 else helper f0

and subst_hprel_hf hf0 from_hps to_hp=
  let rec helper hf=
    match hf with
    | Star {h_formula_star_h1 = hf1;
            h_formula_star_h2 = hf2;
            h_formula_star_pos = pos} ->
      let n_hf1 = helper hf1 in
      let n_hf2 = helper hf2 in
      Star {h_formula_star_h1 = n_hf1;
            h_formula_star_h2 = n_hf2;
            h_formula_star_pos = pos}
    | StarMinus {h_formula_starminus_h1 = hf1;
                 h_formula_starminus_h2 = hf2;
                 h_formula_starminus_aliasing = al;
                 h_formula_starminus_pos = pos} ->
      let n_hf1 = helper hf1 in
      let n_hf2 = helper hf2 in
      StarMinus {h_formula_starminus_h1 = n_hf1;
                 h_formula_starminus_h2 = n_hf2;
                 h_formula_starminus_aliasing = al;
                 h_formula_starminus_pos = pos}
    | Conj { h_formula_conj_h1 = hf1;
             h_formula_conj_h2 = hf2;
             h_formula_conj_pos = pos} ->
      let n_hf1 = helper hf1 in
      let n_hf2 = helper hf2 in
      Conj { h_formula_conj_h1 = n_hf1;
             h_formula_conj_h2 = n_hf2;
             h_formula_conj_pos = pos}
    | ConjStar { h_formula_conjstar_h1 = hf1;
                 h_formula_conjstar_h2 = hf2;
                 h_formula_conjstar_pos = pos} ->
      let n_hf1 = helper hf1 in
      let n_hf2 = helper hf2 in
      ConjStar { h_formula_conjstar_h1 = n_hf1;
                 h_formula_conjstar_h2 = n_hf2;
                 h_formula_conjstar_pos = pos}
    | ConjConj { h_formula_conjconj_h1 = hf1;
                 h_formula_conjconj_h2 = hf2;
                 h_formula_conjconj_pos = pos} ->
      let n_hf1 = helper hf1 in
      let n_hf2 = helper hf2 in
      ConjConj { h_formula_conjconj_h1 = n_hf1;
                 h_formula_conjconj_h2 = n_hf2;
                 h_formula_conjconj_pos = pos}
    | Phase { h_formula_phase_rd = hf1;
              h_formula_phase_rw = hf2;
              h_formula_phase_pos = pos} ->
      let n_hf1 = helper hf1 in
      let n_hf2 = helper hf2 in
      Phase { h_formula_phase_rd = n_hf1;
              h_formula_phase_rw = n_hf2;
              h_formula_phase_pos = pos}
    | HRel (hp, eargs, p) -> if CP.mem_svl hp from_hps then  HRel (to_hp, eargs, p)
      else hf
    | DataNode _
    | ViewNode _
    | ThreadNode _
    | Hole _ | FrmHole _
    | HTrue
    | HFalse
    | HEmp | HVar _-> hf
  in
  if from_hps = [] then hf0 else helper hf0

(* and add_pure_formula_to_formula (f1_pure: CP.formula) (f2_f:formula)  : formula =  *)
(*   add_mix_formula_to_formula (MCP.mix_of_pure f1_pure) f2_f *)

let drop_views_h_formula hf0 views=
  let rec helper hf=
    match hf with
    | Star {h_formula_star_h1 = hf1;
            h_formula_star_h2 = hf2;
            h_formula_star_pos = pos} ->
      let n_hf1 = helper hf1 in
      let n_hf2 = helper hf2 in
      let new_hf=
        match n_hf1,n_hf2 with
        | (HEmp,HEmp) -> HEmp
        | (HEmp,_) -> n_hf2
        | (_,HEmp) -> n_hf1
        | _ -> (Star {h_formula_star_h1 = n_hf1;
                      h_formula_star_h2 = n_hf2;
                      h_formula_star_pos = pos})
      in
      (new_hf)
    | Conj { h_formula_conj_h1 = hf1;
             h_formula_conj_h2 = hf2;
             h_formula_conj_pos = pos} ->
      let n_hf1 = helper hf1 in
      let n_hf2 = helper hf2 in
      (Conj { h_formula_conj_h1 = n_hf1;
              h_formula_conj_h2 = n_hf2;
              h_formula_conj_pos = pos})
    | Phase { h_formula_phase_rd = hf1;
              h_formula_phase_rw = hf2;
              h_formula_phase_pos = pos} ->
      let n_hf1 = helper hf1 in
      let n_hf2 = helper hf2 in
      (Phase { h_formula_phase_rd = n_hf1;
               h_formula_phase_rw = n_hf2;
               h_formula_phase_pos = pos})
    | DataNode hd -> (hf)
    | ViewNode hv ->
      if List.exists (fun view -> String.compare view hv.h_formula_view_name = 0) views then
        HEmp
      else hf
    | ThreadNode _ -> (hf)
    | HRel _
    | Hole _ | FrmHole _
    | HTrue
    | HFalse
    | HEmp | HVar _ -> hf
    | StarMinus _ | ConjStar _ | ConjConj _ -> report_error no_pos "drop_views_h_formula: not handle yet"
  in
  helper hf0

let drop_views_formula_x (f0:formula) views : formula=
  let rec helper f2_f=
    match f2_f with
    | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) ->
      Or ({formula_or_f1 = helper f1 ; formula_or_f2 =  helper f2 ; formula_or_pos = pos})
    | Base b -> Base { b with formula_base_heap = drop_views_h_formula b.formula_base_heap views;}
    | Exists b -> Exists {b with formula_exists_heap = drop_views_h_formula b.formula_exists_heap views;}
  in
  helper f0

let drop_views_formula (f2_f:formula) views: formula =
  let pr2 x= String.concat ";" x in
  Debug.no_2 "drop_views_formula" !print_formula pr2
    !print_formula
    drop_views_formula_x f2_f views

let drop_view_struc_formula_x (f0 : struc_formula) views: struc_formula =
  let rec helper f=
    match f with
    | ECase b -> report_error no_pos "drop_view_struc_formula: not handle yet"
    | EBase b -> EBase {b with  formula_struc_base = drop_views_formula b.formula_struc_base views;
                                formula_struc_continuation = map_opt (helper) b.formula_struc_continuation;}
    | EAssume _ -> f
    | EInfer b -> EInfer { b with formula_inf_continuation = helper b.formula_inf_continuation;}
    (* | EOr b -> EOr {b with  *)
    (*     formula_struc_or_f1 = helper b.formula_struc_or_f1;  *)
    (*     formula_struc_or_f2 = helper b.formula_struc_or_f2; } *)
    | EList b -> EList (map_l_snd (helper) b)
  in
  helper f0

let drop_view_struc_formula (f : struc_formula) views: struc_formula =
  let pr1 = !print_struc_formula in
  let pr2 x= String.concat ";" x in
  Debug.no_2 " drop_view_struc_formula" pr1 pr2 pr1
    (fun _ _ -> drop_view_struc_formula_x f views) f views

(*******************************************)

let drop_view_paras_h_formula hf0 ls_view_pos=
  let retrieve_args_from_locs args locs=
    let rec retrieve_args_from_locs_helper args locs index res=
      match args with
      | [] -> res
      | a::ss -> if List.mem index locs then
          retrieve_args_from_locs_helper ss locs (index+1) (res@[a])
        else retrieve_args_from_locs_helper ss locs (index+1) res
    in
    retrieve_args_from_locs_helper args locs 0 []
  in
  let rec lookup_view vn args ls=
    match ls with
    | [] -> None
    | (vn1,n_vn1, ls_pos)::rest ->
      if String.compare vn vn1 = 0 then
        Some (retrieve_args_from_locs args ls_pos,n_vn1)
      else
        lookup_view vn args rest
  in
  let rec helper hf=
    match hf with
    | Star {h_formula_star_h1 = hf1;
            h_formula_star_h2 = hf2;
            h_formula_star_pos = pos} ->
      let n_hf1 = helper hf1 in
      let n_hf2 = helper hf2 in
      let new_hf=
        match n_hf1,n_hf2 with
        | (HEmp,HEmp) -> HEmp
        | (HEmp,_) -> n_hf2
        | (_,HEmp) -> n_hf1
        | _ -> (Star {h_formula_star_h1 = n_hf1;
                      h_formula_star_h2 = n_hf2;
                      h_formula_star_pos = pos})
      in
      (new_hf)
    | Conj { h_formula_conj_h1 = hf1;
             h_formula_conj_h2 = hf2;
             h_formula_conj_pos = pos} ->
      let n_hf1 = helper hf1 in
      let n_hf2 = helper hf2 in
      (Conj { h_formula_conj_h1 = n_hf1;
              h_formula_conj_h2 = n_hf2;
              h_formula_conj_pos = pos})
    | Phase { h_formula_phase_rd = hf1;
              h_formula_phase_rw = hf2;
              h_formula_phase_pos = pos} ->
      let n_hf1 = helper hf1 in
      let n_hf2 = helper hf2 in
      (Phase { h_formula_phase_rd = n_hf1;
               h_formula_phase_rw = n_hf2;
               h_formula_phase_pos = pos})
    | ThreadNode _ -> (hf)
    | DataNode hd -> (hf)
    | ViewNode hv -> begin
        let on_args = lookup_view hv.h_formula_view_name hv.h_formula_view_arguments ls_view_pos in
        match on_args with
        | None -> hf
        | Some (n_args, n_vn) -> ViewNode {hv with
                                           h_formula_view_name = n_vn;
                                           h_formula_view_arguments = n_args}
      end
    | HRel _
    | Hole _ | FrmHole _
    | HTrue
    | HFalse
    | HEmp | HVar _ -> hf
    | StarMinus _ | ConjStar _ | ConjConj _ -> report_error no_pos "drop_view_paras_h_formula: not handle yet"
  in
  helper hf0

let drop_view_paras_formula_x (f0:formula) ls_view_pos : formula=
  let rec helper f2_f=
    match f2_f with
    | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) ->
      Or ({formula_or_f1 = helper f1 ; formula_or_f2 =  helper f2 ; formula_or_pos = pos})
    | Base b -> Base { b with formula_base_heap = drop_view_paras_h_formula b.formula_base_heap ls_view_pos;}
    | Exists b -> Exists {b with formula_exists_heap = drop_view_paras_h_formula b.formula_exists_heap ls_view_pos;}
  in
  let f1 = elim_exists f0 in
  helper f1

let drop_view_paras_formula (f2_f:formula) ls_view_pos: formula =
  let pr2 = pr_list(pr_triple pr_id pr_id (pr_list string_of_int)) in
  Debug.no_2 "drop_view_paras_formula" !print_formula pr2
    !print_formula
    drop_view_paras_formula_x f2_f ls_view_pos

let drop_view_paras_struc_formula_x (f0 : struc_formula) ls_view_pos: struc_formula =
  let rec helper f=
    match f with
    | ECase b -> report_error no_pos "CF.drop_view_struc_formula: not handle yet"
    | EBase b -> EBase {b with  formula_struc_base = drop_view_paras_formula b.formula_struc_base ls_view_pos;
                                formula_struc_continuation = map_opt (helper) b.formula_struc_continuation;}
    | EAssume _-> f
    | EInfer b -> EInfer { b with formula_inf_continuation = helper b.formula_inf_continuation;}
    (* | EOr b -> EOr {b with *)
    (*     formula_struc_or_f1 = helper b.formula_struc_or_f1; *)
    (*     formula_struc_or_f2 = helper b.formula_struc_or_f2; } *)
    | EList b -> EList (map_l_snd (helper) b)
  in
  helper f0

let drop_view_paras_struc_formula (f : struc_formula) ls_view_pos: struc_formula =
  let pr1 = !print_struc_formula in
  let pr2 = pr_list (pr_triple pr_id pr_id (pr_list string_of_int)) in
  Debug.no_2 " drop_view_paras_struc_formula" pr1 pr2 pr1
    (fun _ _ -> drop_view_paras_struc_formula_x f ls_view_pos) f ls_view_pos
(*******************************************)

let xpure_for_hnodes hf=
  let hds, _, _ (*hvs, hrs*) =  get_hp_rel_h_formula hf in
  (*currently we just work with data nodes*)
  let neqNulls = List.map (fun dn -> CP.mkNeqNull dn.h_formula_data_node dn.h_formula_data_pos) hds in
  let new_mf = MCP.mix_of_pure (CP.join_conjunctions neqNulls) in
  new_mf

let xpure_for_hnodes_f_x f0=
  let rec helper f=
    match f with
    | Base fb ->
      let h_pure = xpure_for_hnodes fb.formula_base_heap in
      CP.conj_of_list [(MCP.pure_of_mix h_pure);(MCP.pure_of_mix fb.formula_base_pure)] fb.formula_base_pos
    | Exists _ ->
      let qvars, base1 = split_quantifiers f in
      (* let nbase1 = helper base1 in *)
      helper base1
    (* add_quantifiers qvars nbase1 *)
    | Or orf -> CP.disj_of_list [(helper orf.formula_or_f1);(helper orf.formula_or_f2)] orf.formula_or_pos
  in
  helper f0

let xpure_for_hnodes_f f0=
  let pr1 = !print_formula in
  let pr2 = !CP.print_formula in
  Debug.no_1 "xpure_for_hnodes_f" pr1 pr2
    (fun _ -> xpure_for_hnodes_f_x f0) f0

(*check the form: hp(x,y) = x!=null & y !=null*)
let is_only_neqNull_pure p args=
  let neqNulls = List.map (fun sv -> CP.mkNeqNull sv no_pos) args in
  let ps = (CP.split_conjunctions p) in
  let ps1 = CP.remove_redundant_helper ps [] in
  (Gen.BList.difference_eq CP.equalFormula ps1 neqNulls) = []

let is_only_neqNull_x args unk_hps f0=
  let rec helper f=
    match f with
    | Base fb ->
      if is_empty_heap fb.formula_base_heap then
        is_only_neqNull_pure (MCP.pure_of_mix fb.formula_base_pure) args
      else
        let hds,hvs,hrels = get_hp_rel_h_formula fb.formula_base_heap in
        if hds=[] && hvs=[] then
          let hps = List.map (fun (hp,_,_) -> hp) hrels in
          if (CP.diff_svl hps unk_hps = []) then
            is_only_neqNull_pure (MCP.pure_of_mix fb.formula_base_pure) args
          else false
        else false
    | Exists fe ->
      if is_empty_heap fe.formula_exists_heap then
        is_only_neqNull_pure (MCP.pure_of_mix fe.formula_exists_pure) args
      else
        let hds,hvs,hrels = get_hp_rel_h_formula fe.formula_exists_heap in
        if hds=[] && hvs=[] then
          let hps = List.map (fun (hp,_,_) -> hp) hrels in
          if (CP.diff_svl hps unk_hps = []) then
            is_only_neqNull_pure (MCP.pure_of_mix fe.formula_exists_pure) args
          else false
        else false
    | Or orf -> (helper orf.formula_or_f1) && (helper orf.formula_or_f2)
  in
  helper f0

let is_only_neqNull args unk_hps f0=
  let pr1 = !print_formula in
  Debug.no_2 "is_only_neqNull" !CP.print_svl pr1 string_of_bool
    (fun _ _ -> is_only_neqNull_x args unk_hps f0) args f0

let get_null_svl f0=
  let rec helper f=
    match f with
    | Base fb ->
      let null_ptrs = MCP.get_null_ptrs fb.formula_base_pure in
      let eqs = (MCP.ptr_equations_without_null fb.formula_base_pure) in
      find_close null_ptrs eqs
    | Exists _ ->
      let _, base1 = split_quantifiers f in
      helper base1
    | Or orf -> ((helper orf.formula_or_f1) @ (helper orf.formula_or_f2))
  in
  helper f0

let get_args_neqNull_x args expl_ptrs f0=
  (* let non_root_svl = List.concat *)
  (*   (List.map (fun hd -> List.filter CP.is_node_typ hd.h_formula_data_arguments) hds) in *)
  (* let non_root_args = CP.diff_svl args non_root_svl in *)
  let helper1 p=
    let neqNull_svl = CP.get_neq_null_svl p in
    let neqNull_svl1 = CP.diff_svl neqNull_svl expl_ptrs in
    CP.intersect_svl neqNull_svl1 args
  in
  let rec helper f=
    match f with
    | Base fb ->
      helper1 (MCP.pure_of_mix fb.formula_base_pure)
    | Exists fe ->
      helper1 (MCP.pure_of_mix fe.formula_exists_pure)
    | Or orf -> CP.remove_dups_svl ((helper orf.formula_or_f1) @ (helper orf.formula_or_f2))
  in
  helper f0

let get_args_neqNull args expl_svl f0=
  let pr1 = !print_formula in
  Debug.no_1 "get_args_neqNull" pr1 !CP.print_svl
    (fun _ -> get_args_neqNull_x args expl_svl f0) f0

let get_neqNull_x f0=
  let helper1 p=
    CP.get_neq_null_svl p
  in
  let rec helper f=
    match f with
    | Base fb ->
      helper1 (MCP.pure_of_mix fb.formula_base_pure)
    | Exists fe ->
      helper1 (MCP.pure_of_mix fe.formula_exists_pure)
    | Or orf -> CP.remove_dups_svl ((helper orf.formula_or_f1) @ (helper orf.formula_or_f2))
  in
  helper f0

let get_neqNull f0=
  let pr1 = !print_formula in
  Debug.no_1 "get_neqNull" pr1 !CP.print_svl
    (fun _ -> get_neqNull_x f0) f0

let remove_neqNulls p=
  let ps = (CP.split_conjunctions p) in
  let ps1 = CP.remove_redundant_helper ps [] in
  let ps2 = List.filter (fun p -> not (CP.is_neq_null_exp p)) ps1 in
  (CP.join_conjunctions ps2)

let remove_neqNulls_f_x f0=
  let rec helper f=
    match f with
    | Base fb -> let np = remove_neqNulls (MCP.pure_of_mix fb.formula_base_pure) in
      (Base {fb with formula_base_pure = MCP.mix_of_pure np})
    | Or orf -> let nf1 = helper orf.formula_or_f1 in
      let nf2 = helper orf.formula_or_f2 in
      ( Or {orf with formula_or_f1 = nf1;
                     formula_or_f2 = nf2;})
    | Exists fe -> let np = remove_neqNulls(MCP.pure_of_mix fe.formula_exists_pure) in
      (Exists {fe with formula_exists_pure = MCP.mix_of_pure np;})
  in
  helper f0

let remove_neqNulls_f f0=
  let pr1 = !print_formula in
  Debug.no_1 "remove_neqNulls_f" pr1 pr1
    (fun _ -> remove_neqNulls_f_x f0) f0


(*elim redundant x!=null in p*)
let remove_neqNull_redundant_hnodes svl p=
  (*currently we just work with data nodes*)
  let neqNulls = List.map (fun sv -> CP.mkNeqNull sv no_pos) svl in
  let ps = (CP.split_conjunctions p) in
  let ps1 = CP.remove_redundant_helper ps [] in
  let new_ps = Gen.BList.difference_eq CP.equalFormula ps1 neqNulls in
  let p1 =  (CP.join_conjunctions new_ps) in
  let quans, bare_p, lbl,pos = CP.split_forall_quantifiers p1 in
  (* let () = Debug.info_zprint (lazy  ("  quans: " ^ (!CP.print_svl quans) )) no_pos in *)
  if quans<> [] then
    let null_svl = CP.get_null_ptrs bare_p in
    if svl <> [] && null_svl <> [] then
      let new_quans = CP.diff_svl quans null_svl in
      let disjs = CP.list_of_disjs bare_p in
      let rem = List.filter (fun p -> not (CP.is_eq_null_exp p)) disjs in
      let bare1 = CP.disj_of_list rem pos in
      let p2 = if new_quans = [] then bare1 else CP.mkForall new_quans bare1 lbl pos in
      p2
    else p1
  else p1

(*elim redundant x::node<_> & x!=null: remove x!=null*)
let remove_neqNull_redundant_hnodes_hf_x hf p=
  let hds, _, _ (*hvs, hrs*) =  get_hp_rel_h_formula hf in
  let svl = List.map (fun dn -> dn.h_formula_data_node) hds in
  let p1 = remove_neqNull_redundant_hnodes svl p in
  p1

let remove_neqNull_redundant_hnodes_hf hf0 p=
  let pr1 = !print_h_formula in
  let pr2 = !CP.print_formula in
  Debug.no_2 "remove_neqNull_redundant_hnodes_hf" pr1 pr2 pr2
    (fun _ _ -> remove_neqNull_redundant_hnodes_hf_x hf0 p) hf0 p

let remove_neqNull_redundant_hnodes_f_x f0=
  let rec helper f=
    match f with
    | Base fb -> let np = remove_neqNull_redundant_hnodes_hf fb.formula_base_heap
                     (MCP.pure_of_mix fb.formula_base_pure) in
      (Base {fb with formula_base_pure = MCP.mix_of_pure np})
    | Or orf -> let nf1 = helper orf.formula_or_f1 in
      let nf2 = helper orf.formula_or_f2 in
      ( Or {orf with formula_or_f1 = nf1;
                     formula_or_f2 = nf2;})
    | Exists fe -> let np = remove_neqNull_redundant_hnodes_hf fe.formula_exists_heap
                       (MCP.pure_of_mix fe.formula_exists_pure) in
      (Exists {fe with formula_exists_pure = MCP.mix_of_pure np;})
  in
  helper f0

let remove_neqNull_redundant_hnodes_f f0=
  let pr1 = !print_formula in
  Debug.no_1 "CF.remove_neqNull_redundant_hnodes_f" pr1 pr1
    (fun _ -> remove_neqNull_redundant_hnodes_f_x f0) f0

let remove_neqNull_redundant_hnodes_f_wg (f0,og)=
  let rec helper f=
    match f with
    | Base fb -> let np = remove_neqNull_redundant_hnodes_hf fb.formula_base_heap
                     (MCP.pure_of_mix fb.formula_base_pure) in
      (Base {fb with formula_base_pure = MCP.mix_of_pure np})
    | Or orf -> let nf1 = helper orf.formula_or_f1 in
      let nf2 = helper orf.formula_or_f2 in
      ( Or {orf with formula_or_f1 = nf1;
                     formula_or_f2 = nf2;})
    | Exists fe -> let np = remove_neqNull_redundant_hnodes_hf fe.formula_exists_heap
                       (MCP.pure_of_mix fe.formula_exists_pure) in
      (Exists {fe with formula_exists_pure = MCP.mix_of_pure np;})
  in
  let nf = helper f0 in
  (nf, og)

(*
  p will be Neg then And with f0
*)
let remove_neqNull_redundant_andNOT_x f0 p=
  let mf = (MCP.mix_of_pure p) in
  let rec helper f=
    match f with
    | Base fb ->
      let null_ptrs = MCP.get_null_ptrs mf in
      let eqs = (MCP.ptr_equations_without_null mf) in
      let hds, _, _ (*hvs, hrs*) =  get_hp_rel_h_formula fb.formula_base_heap in
      let node_ptrs = List.map (fun dn -> dn.h_formula_data_node) hds in
      let null_ptrs1 = find_close null_ptrs eqs in
      let null_diff = CP.diff_svl null_ptrs1 node_ptrs in
      let np = CP.remove_redundant (CP.filter_var p null_diff) in
      let pos = (CP.pos_of_formula np) in
      if CP.isConstTrue np then (CP.mkFalse pos) else
        (*!(a!=b /\ p) /\ a=b ===> a=b *)
        let ps1 = CP.list_of_conjs np in
        let neqs1_added, _ = List.partition CP.is_neq_exp ps1 in
        let cur_eqs = MCP.ptr_equations_without_null fb.formula_base_pure in
        if List.exists (fun (sv1,sv2) -> (List.exists (fun neq ->
            let svl = CP.fv neq in
            if List.length svl != 2 then false else
              CP.diff_svl [sv1;sv2] svl = [])) neqs1_added
          ) cur_eqs then CP.mkFalse pos
        else
          np
    | Exists _ -> let _, base1 = split_quantifiers f in
      helper base1
    | Or orf -> report_error no_pos "CF.remove_neqNull_redundant_andNOT: should not OR"
  in
  helper f0

let remove_neqNull_redundant_andNOT f0 p=
  let pr1 = !print_formula in
  let pr2 = !CP.print_formula in
  Debug.no_2 "remove_neqNull_redundant_hnodes_f" pr1 pr2 pr2
    (fun _ _ -> remove_neqNull_redundant_andNOT_x f0 p) f0 p

let remove_neqNull_redundant_andNOT_opt f0 p=
  match f0 with
  | None -> p
  | Some f -> remove_neqNull_redundant_andNOT f p

let remove_neqNull_svl svl f0=
  let rec helper f=
    match f with
    | Base fb ->
      let np = remove_neqNull_redundant_hnodes svl
          (MCP.pure_of_mix fb.formula_base_pure) in
      (Base {fb with formula_base_pure = MCP.mix_of_pure np})
    | Or orf -> let nf1 = helper orf.formula_or_f1 in
      let nf2 = helper orf.formula_or_f2 in
      ( Or {orf with formula_or_f1 = nf1;
                     formula_or_f2 = nf2;})
    | Exists fe ->
      let np = remove_neqNull_redundant_hnodes svl
          (MCP.pure_of_mix fe.formula_exists_pure) in
      (Exists {fe with formula_exists_pure = MCP.mix_of_pure np;})
  in
  helper f0


let remove_com_pures_x f0 nullPtrs com_eqPures=
  let remove p elim_svl=
    if elim_svl = [] then p else
      begin
        let all = CP.remove_dups_svl (CP.fv p) in
        let keep_svl = Gen.BList.difference_eq CP.eq_spec_var all elim_svl in
        CP.filter_var_new p keep_svl
      end
  in
  let remove_com_pures p com_ps=
    let ps0 = CP.split_conjunctions p in
    let rem_ps = Gen.BList.difference_eq CP.equalFormula ps0 com_ps in
    (CP.conj_of_list rem_ps no_pos)
  in
  let rec helper f=
    match f with
    | Base fb ->
      (*assume keep vars = dnodes*)
      let new_p = remove (MCP.pure_of_mix fb.formula_base_pure) nullPtrs in
      let new_p1 = remove_com_pures new_p com_eqPures in
      Base {fb with formula_base_pure = MCP.mix_of_pure new_p1;
           }
    | Or orf -> let nf1 = helper orf.formula_or_f1 in
      let nf2 = helper orf.formula_or_f2 in
      ( Or {orf with formula_or_f1 = nf1;
                     formula_or_f2 = nf2;})
    | Exists fe ->
      let qvars, base1 = split_quantifiers f in
      let nf = helper base1 in
      add_quantifiers qvars nf
      (* let new_p = remove (MCP.pure_of_mix fe.formula_exists_pure) nullPtrs in *)
      (*            let new_p1 = remove_com_pures new_p com_eqPures in *)
      (*            (Exists {fe with formula_exists_pure = MCP.mix_of_pure new_p1;}) *)
  in
  helper f0

let remove_com_pures f0 nullPtrs com_eqPures=
  let pr1 = !print_formula in
  let pr2 = !CP.print_svl in
  let pr3 = pr_list !CP.print_formula in
  Debug.no_3 "remove_com_pures" pr1 pr2 pr3 pr1
    (fun _ _ _ -> remove_com_pures_x f0 nullPtrs com_eqPures)
    f0 nullPtrs com_eqPures

(*drop HRel in the set hp_names and return corresponding subst of their args*)
let rec drop_hrel_f_x f0 hp_names=
  let rec helper f=
    match f with
    | Base fb -> let nfb,argsl = drop_hrel_hf fb.formula_base_heap hp_names in
      (Base {fb with formula_base_heap =  nfb;}, argsl)
    | Or orf -> let nf1,argsl1 =  helper orf.formula_or_f1 in
      let nf2,argsl2 = helper orf.formula_or_f2 in
      ( Or {orf with formula_or_f1 = nf1;
                     formula_or_f2 = nf2;}, argsl1@argsl2)
    | Exists fe ->let qvars, base1 = split_quantifiers f in
      let nf,argsl = helper base1 in
      (add_quantifiers qvars nf,argsl)
  in
  if hp_names = [] then (f0, []) else
    helper f0

and drop_hrel_f f0 hp_names=
  let pr1 = !print_formula in
  let pr2 = !CP.print_svl in
  let pr3 (f,_) = pr1 f in
  Debug.no_2 "drop_hrel_f" pr1 pr2 pr3
    (fun _ _ -> drop_hrel_f_x f0 hp_names)
    f0 hp_names

and drop_hrel_hf hf hp_names=
  match hf with
  | Star {h_formula_star_h1 = hf1;
          h_formula_star_h2 = hf2;
          h_formula_star_pos = pos} ->
    let n_hf1, argsl1 = drop_hrel_hf hf1 hp_names in
    let n_hf2, argsl2 = drop_hrel_hf hf2 hp_names in
    let newf =
      (match n_hf1,n_hf2 with
       | (HEmp,HEmp) -> HEmp
       | (HEmp,_) -> n_hf2
       | (_,HEmp) -> n_hf1
       | _ -> (Star {h_formula_star_h1 = n_hf1;
                     h_formula_star_h2 = n_hf2;
                     h_formula_star_pos = pos})
      ) in
    (newf, argsl1@argsl2)
  | StarMinus { h_formula_starminus_h1 = hf1;
                h_formula_starminus_h2 = hf2;
                h_formula_starminus_aliasing = al;
                h_formula_starminus_pos = pos} ->
    let n_hf1,argsl1 = drop_hrel_hf hf1 hp_names in
    let n_hf2,argsl2 = drop_hrel_hf hf2 hp_names in
    let newf =
      (match n_hf1,n_hf2 with
       | (HEmp,HEmp) -> HEmp
       | (HEmp,_) -> n_hf2
       | (_,HEmp) -> n_hf1
       | _ -> (StarMinus { h_formula_starminus_h1 = n_hf1;
                           h_formula_starminus_h2 = n_hf2;
                           h_formula_starminus_aliasing = al;
                           h_formula_starminus_pos = pos})
      ) in
    (newf, argsl1@argsl2)
  | Conj { h_formula_conj_h1 = hf1;
           h_formula_conj_h2 = hf2;
           h_formula_conj_pos = pos} ->
    let n_hf1,argsl1 = drop_hrel_hf hf1 hp_names in
    let n_hf2,argsl2 = drop_hrel_hf hf2 hp_names in
    let newf =
      (match n_hf1,n_hf2 with
       | (HEmp,HEmp) -> HEmp
       | (HEmp,_) -> n_hf2
       | (_,HEmp) -> n_hf1
       | _ -> (Conj { h_formula_conj_h1 = n_hf1;
                      h_formula_conj_h2 = n_hf2;
                      h_formula_conj_pos = pos})
      ) in
    (newf, argsl1@argsl2)
  | ConjStar { h_formula_conjstar_h1 = hf1;
               h_formula_conjstar_h2 = hf2;
               h_formula_conjstar_pos = pos} ->
    let n_hf1,argsl1 = drop_hrel_hf hf1 hp_names in
    let n_hf2,argsl2 = drop_hrel_hf hf2 hp_names in
    let newf =
      (match n_hf1,n_hf2 with
       | (HEmp,HEmp) -> HEmp
       | (HEmp,_) -> n_hf2
       | (_,HEmp) -> n_hf1
       | _ -> (ConjStar { h_formula_conjstar_h1 = n_hf1;
                          h_formula_conjstar_h2 = n_hf2;
                          h_formula_conjstar_pos = pos})
      ) in
    (newf, argsl1@argsl2)
  | ConjConj { h_formula_conjconj_h1 = hf1;
               h_formula_conjconj_h2 = hf2;
               h_formula_conjconj_pos = pos} ->
    let n_hf1,argsl1 = drop_hrel_hf hf1 hp_names in
    let n_hf2,argsl2 = drop_hrel_hf hf2 hp_names in
    (ConjConj { h_formula_conjconj_h1 = n_hf1;
                h_formula_conjconj_h2 = n_hf2;
                h_formula_conjconj_pos = pos}, argsl1@argsl2)
  | Phase { h_formula_phase_rd = hf1;
            h_formula_phase_rw = hf2;
            h_formula_phase_pos = pos} ->
    let n_hf1,argsl1 = drop_hrel_hf hf1 hp_names in
    let n_hf2,argsl2 = drop_hrel_hf hf2 hp_names in
    (Phase { h_formula_phase_rd = n_hf1;
             h_formula_phase_rw = n_hf2;
             h_formula_phase_pos = pos},argsl1@argsl2)
  | DataNode hd -> (hf,[])
  | ViewNode hv -> (hf,[])
  | ThreadNode _ -> (hf,[])
  | HRel (id,args,_) -> if CP.mem_svl id hp_names then (HEmp, [args])
    else (hf,[])
  | Hole _ | FrmHole _
  | HTrue
  | HFalse
  | HEmp | HVar _ -> (hf,[])

(* formula -> CP.spec_var list -> formula * CP.exp list list *)
let drop_hrel_f f0 hp_names =
  let pr1 = !print_formula in
  let pr2 = !print_svl in
  let pr3 = pr_pair !print_formula (pr_list (pr_list !CP.print_exp)) in
  Debug.no_2 "drop_hrel_f" pr1 pr2 pr3 drop_hrel_f f0 hp_names

let drop_hprel_constr cs drop_hps=
  if drop_hps = [] then cs else
    let nlhs,_ = drop_hrel_f cs.hprel_lhs drop_hps in
    let nrhs,_ = drop_hrel_f cs.hprel_rhs drop_hps in
    {cs with hprel_lhs = nlhs;
             hprel_rhs = nrhs;
    }

let drop_unk_hrel f0 hp_names=
  let rec helper f=
    match f with
    | Base fb -> let nfb,args = drop_hrel_hf fb.formula_base_heap hp_names in
      let p = (MCP.pure_of_mix fb.formula_base_pure) in
      let unk_hp_args = CP.get_xpure p in
      let n_p,n_b = if unk_hp_args = [] then (p, List.length args > 0) else
          (CP.drop_xpure p, true)
      in
      (Base {fb with formula_base_heap =  nfb;
                     formula_base_pure = MCP.mix_of_pure n_p;
            }, n_b)
    | Or orf -> let nf1,b1 = helper orf.formula_or_f1 in
      let nf2,b2 = helper orf.formula_or_f2 in
      ( Or {orf with formula_or_f1 = nf1;
                     formula_or_f2 = nf2;}, b1||b2)
    | Exists fe ->
      let qvars, base1 = split_quantifiers f in
      let nf,b = helper base1 in
      (add_quantifiers qvars nf, b)
  in
  helper f0

(*drop HRel in the set hp_namesxeargs*)
let rec drop_exact_hrel_f f0 hprels com_eqPures=
  let hpargs = List.map (fun (hp,eargs,_) -> (hp, (List.fold_left List.append [] (List.map CP.afv eargs)))) hprels in
  let xpures = List.fold_left (fun ls p -> ls@(CP.get_xpure p)) [] com_eqPures in
  let total_unk_hpargs = hpargs@xpures in
  let rec helper f=
    match f with
    | Base fb -> let nfb = drop_exact_hrel_hf fb.formula_base_heap total_unk_hpargs in
      (Base {fb with formula_base_heap =  nfb;})
    | Or orf -> let nf1 = helper orf.formula_or_f1 in
      let nf2 = helper orf.formula_or_f2 in
      ( Or {orf with formula_or_f1 = nf1;
                     formula_or_f2 = nf2;})
    | Exists fe -> let nfe = drop_exact_hrel_hf fe.formula_exists_heap total_unk_hpargs in
      (Exists {fe with formula_exists_heap = nfe ;})
  in
  helper f0

and drop_exact_hrel_hf hf0 unk_hpargs=
  let rec helper hf=
    match hf with
    | Star {h_formula_star_h1 = hf1;
            h_formula_star_h2 = hf2;
            h_formula_star_pos = pos} ->
      let n_hf1 = helper hf1 in
      let n_hf2 = helper hf2 in
      let newf =
        (match n_hf1,n_hf2 with
         | (HEmp,HEmp) -> HEmp
         | (HEmp,_) -> n_hf2
         | (_,HEmp) -> n_hf1
         | _ -> (Star {h_formula_star_h1 = n_hf1;
                       h_formula_star_h2 = n_hf2;
                       h_formula_star_pos = pos})
        ) in
      (newf)
    | Conj { h_formula_conj_h1 = hf1;
             h_formula_conj_h2 = hf2;
             h_formula_conj_pos = pos} ->
      let n_hf1= helper hf1 in
      let n_hf2 = helper hf2 in
      (Conj { h_formula_conj_h1 = n_hf1;
              h_formula_conj_h2 = n_hf2;
              h_formula_conj_pos = pos})
    | Phase { h_formula_phase_rd = hf1;
              h_formula_phase_rw = hf2;
              h_formula_phase_pos = pos} ->
      let n_hf1 = helper hf1 in
      let n_hf2 = helper hf2 in
      (Phase { h_formula_phase_rd = n_hf1;
               h_formula_phase_rw = n_hf2;
               h_formula_phase_pos = pos})
    | DataNode hd -> (hf)
    | ViewNode hv -> (hf)
    | ThreadNode _ -> (hf)
    | HRel (hp,eargs,_) ->
      let args = (List.fold_left List.append [] (List.map CP.afv eargs)) in
      if Gen.BList.mem_eq eq_hpargs (hp,args) unk_hpargs then (HEmp)
      else (hf)
    | Hole _ | FrmHole _
    | HTrue
    | HFalse
    | HEmp | HVar _ -> (hf)
    | StarMinus _ | ConjStar _ | ConjConj _ -> report_error no_pos "CF.drop_exact_hrel_hf: not handle yet"
  in
  helper hf0

and drop_hnodes_f f hn_names=
  match f with
  | Base fb -> let nfb = drop_hnodes_hf fb.formula_base_heap hn_names in
    (* let np = remove_neqNull_redundant_hnodes_hf nfb (MCP.pure_of_mix fb.formula_base_pure) in *)
    (Base {fb with formula_base_heap =  nfb;
                   (* formula_base_pure = MCP.mix_of_pure np *) })
  | Or orf -> let nf1 =  drop_hnodes_f orf.formula_or_f1 hn_names in
    let nf2 =  drop_hnodes_f orf.formula_or_f2 hn_names in
    ( Or {orf with formula_or_f1 = nf1;
                   formula_or_f2 = nf2;})
  | Exists fe -> let nfe = drop_hnodes_hf fe.formula_exists_heap hn_names in
    (Exists {fe with formula_exists_heap = nfe ;})

and drop_hnodes_hf hf0 hn_names=
  let rec helper hf=
    match hf with
    | Star {h_formula_star_h1 = hf1;
            h_formula_star_h2 = hf2;
            h_formula_star_pos = pos} ->
      let n_hf1 = helper hf1 in
      let n_hf2 = helper hf2 in
      let newf =
        (match n_hf1,n_hf2 with
         | (HEmp,HEmp) -> HEmp
         | (HEmp,_) -> n_hf2
         | (_,HEmp) -> n_hf1
         | _ -> (Star {h_formula_star_h1 = n_hf1;
                       h_formula_star_h2 = n_hf2;
                       h_formula_star_pos = pos})
        ) in
      (newf)
    | StarMinus { h_formula_starminus_h1 = hf1;
                  h_formula_starminus_h2 = hf2;
                  h_formula_starminus_aliasing = al;
                  h_formula_starminus_pos = pos} ->
      let n_hf1 = helper hf1 in
      let n_hf2 = helper hf2 in
      let newf =
        (match n_hf1,n_hf2 with
         | (HEmp,HEmp) -> HEmp
         | (HEmp,_) -> n_hf2
         | (_,HEmp) -> n_hf1
         | _ -> StarMinus { h_formula_starminus_h1 = n_hf1;
                            h_formula_starminus_h2 = n_hf2;
                            h_formula_starminus_aliasing = al;
                            h_formula_starminus_pos = pos}
        ) in
      (newf)
    | Conj { h_formula_conj_h1 = hf1;
             h_formula_conj_h2 = hf2;
             h_formula_conj_pos = pos} ->
      let n_hf1 = helper hf1 in
      let n_hf2 = helper hf2 in
      let newf =
        (match n_hf1,n_hf2 with
         | (HEmp,HEmp) -> HEmp
         | (HEmp,_) -> n_hf2
         | (_,HEmp) -> n_hf1
         | _ -> (Conj { h_formula_conj_h1 = n_hf1;
                        h_formula_conj_h2 = n_hf2;
                        h_formula_conj_pos = pos})
        ) in
      (newf)
    | ConjStar { h_formula_conjstar_h1 = hf1;
                 h_formula_conjstar_h2 = hf2;
                 h_formula_conjstar_pos = pos} ->
      let n_hf1 = helper hf1 in
      let n_hf2 = helper hf2 in
      let newf =
        (match n_hf1,n_hf2 with
         | (HEmp,HEmp) -> HEmp
         | (HEmp,_) -> n_hf2
         | (_,HEmp) -> n_hf1
         | _ -> (ConjStar { h_formula_conjstar_h1 = n_hf1;
                            h_formula_conjstar_h2 = n_hf2;
                            h_formula_conjstar_pos = pos})
        ) in
      (newf)
    | ConjConj { h_formula_conjconj_h1 = hf1;
                 h_formula_conjconj_h2 = hf2;
                 h_formula_conjconj_pos = pos} ->
      let n_hf1 = helper hf1 in
      let n_hf2 = helper hf2 in
      let newf =
        (match n_hf1,n_hf2 with
         | (HEmp,HEmp) -> HEmp
         | (HEmp,_) -> n_hf2
         | (_,HEmp) -> n_hf1
         | _ -> (ConjConj { h_formula_conjconj_h1 = n_hf1;
                            h_formula_conjconj_h2 = n_hf2;
                            h_formula_conjconj_pos = pos})
        ) in
      (newf)
    | Phase { h_formula_phase_rd = hf1;
              h_formula_phase_rw = hf2;
              h_formula_phase_pos = pos} ->
      let n_hf1 = helper hf1 in
      let n_hf2 = helper hf2 in
      let newf =
        (match n_hf1,n_hf2 with
         | (HEmp,HEmp) -> HEmp
         | (HEmp,_) -> n_hf2
         | (_,HEmp) -> n_hf1
         | _ -> (Phase { h_formula_phase_rd = n_hf1;
                         h_formula_phase_rw = n_hf2;
                         h_formula_phase_pos = pos})
        ) in
      (newf)
    | DataNode hd ->  if CP.mem_svl hd.h_formula_data_node hn_names then HEmp
      else hf
    | ViewNode hv -> if CP.mem_svl hv.h_formula_view_node hn_names then HEmp
      else hf
    | ThreadNode ht -> if CP.mem_svl ht.h_formula_thread_node hn_names then HEmp
      else hf
    | HRel _
    | Hole _ | FrmHole _
    | HTrue
    | HFalse
    | HEmp | HVar _ -> hf
  in
  if hn_names = [] then hf0 else
    helper hf0

and filter_not_rele_eq p keep_svl=
  let rec filter_fn leqs res=
    match leqs with
    | [] -> res
    | (sv1,sv2)::ss ->
      let b1 = CP.mem_svl sv1 keep_svl in
      let b2 = CP.mem_svl sv1 keep_svl in
      match b1,b2 with
      | true,true -> filter_fn ss res
      | true,false -> filter_fn ss (res@[(sv2,sv1)])
      | false,true -> filter_fn ss (res@[(sv1,sv2)])
      | _ -> report_error no_pos "sau.filter_not_rele_eq: at least one sv belongs to keep_svl"
  in
  let eqs = (MCP.ptr_equations_without_null (MCP.mix_of_pure p)) in
  let eqs1 = filter_fn eqs [] in
  if eqs1 = [] then p else
    let p1 = CP.subst eqs1 p in
    CP.remove_redundant p1

(*todo: merge three following functions in a higher-order function*)
and drop_data_view_hrel_nodes f0 fn_data_select fn_view_select fn_hrel_select dnodes vnodes relnodes=
  let rec helper f=
    match f with
    | Base fb ->
      let new_hf = drop_data_view_hrel_nodes_hf
          fb.formula_base_heap fn_data_select fn_view_select fn_hrel_select
          dnodes vnodes relnodes in
      (*assume keep vars = dnodes*)
      let new_p = CP.filter_var_new (MCP.pure_of_mix fb.formula_base_pure) dnodes in
      (*currently we drop all neqnull*)
      let new_p1 = remove_neqNull_redundant_hnodes_hf new_hf new_p in
      (* let new_p1 = remove_neqNulls new_p in *)
      Base {fb with formula_base_heap = new_hf;
                    formula_base_pure = MCP.mix_of_pure new_p1;
           }
    | Exists fe ->
      let new_hf = drop_data_view_hrel_nodes_hf
          fe.formula_exists_heap fn_data_select fn_view_select fn_hrel_select
          dnodes vnodes relnodes in
      (*assume keep vars = dnodes*)
      let new_p = CP.filter_var_new (MCP.pure_of_mix fe.formula_exists_pure) dnodes in
      (*currently we drop all neqnull*)
      let new_p1 = remove_neqNull_redundant_hnodes_hf new_hf new_p in
      (* let new_p1 = remove_neqNulls new_p in *)
      Exists {fe with formula_exists_heap = new_hf;
                      formula_exists_pure = MCP.mix_of_pure new_p1;
             }
    | Or orf ->Or {orf with formula_or_f1 = helper orf.formula_or_f1;
                            formula_or_f2 = helper orf.formula_or_f2;
                  }
  in
  helper f0

and drop_data_view_hpargs_nodes f0 fn_data_select fn_view_select fn_hrel_select dnodes vnodes hpargs=
  let rec helper f=match f with
    | Base fb ->
      let new_hf = drop_data_view_hpargs_nodes_hf
          fb.formula_base_heap fn_data_select fn_view_select fn_hrel_select
          dnodes vnodes hpargs in
      (*assume keep vars = dnodes*)
      let new_p = CP.filter_var_new (MCP.pure_of_mix fb.formula_base_pure) dnodes in
      (*currently we drop all neqnull*)
      let new_p1 = remove_neqNull_redundant_hnodes_hf new_hf new_p in
      (* let new_p1 = remove_neqNulls new_p in *)
      Base {fb with formula_base_heap = new_hf;
                    formula_base_pure = MCP.mix_of_pure new_p1;
           }
    | Exists fe ->
      let new_hf = drop_data_view_hpargs_nodes_hf
          fe.formula_exists_heap fn_data_select fn_view_select fn_hrel_select
          dnodes vnodes hpargs in
      (*assume keep vars = dnodes*)
      let new_p = CP.filter_var_new (MCP.pure_of_mix fe.formula_exists_pure) dnodes in
      (*currently we drop all neqnull*)
      let new_p1 = remove_neqNull_redundant_hnodes_hf new_hf new_p in
      (* let new_p1 = remove_neqNulls new_p in *)
      Exists {fe with formula_exists_heap = new_hf;
                      formula_exists_pure = MCP.mix_of_pure new_p1;
             }
    | Or orf ->
      Or {orf with formula_or_f1 = helper orf.formula_or_f1;
                   formula_or_f2 = helper orf.formula_or_f2;
         }
  in
  helper f0

and drop_data_view_hpargs_nodes_fb fb fn_data_select fn_view_select fn_hrel_select matched_data_nodes
    matched_view_nodes matched_hpargs_nodes keep_pure_vars=
  let new_hf = drop_data_view_hpargs_nodes_hf
      fb.formula_base_heap fn_data_select fn_view_select fn_hrel_select
      matched_data_nodes matched_view_nodes matched_hpargs_nodes in
  (*assume keep vars = dnodes*)
  let () = DD.ninfo_zprint (lazy  ("  keep" ^ (!CP.print_svl keep_pure_vars))) no_pos in
  let new_p = CP.filter_var_new (MCP.pure_of_mix fb.formula_base_pure) keep_pure_vars in
  let () = DD.ninfo_hprint (add_str  " new_p" !CP.print_formula) new_p no_pos in
  let new_p1 = remove_neqNull_redundant_hnodes_hf new_hf new_p in
  (* DD.info_zprint (lazy  ("  keep" ^ (!CP.print_svl keep_pure_vars))) no_pos; *)
  let () = DD.ninfo_zprint (lazy  ("  new_p1 (after neqNull)" ^ (!CP.print_formula new_p1))) no_pos in
  {fb with formula_base_heap = new_hf;
           formula_base_pure = MCP.mix_of_pure new_p1;}

and drop_data_view_hrel_nodes_fb fb fn_data_select fn_view_select fn_hrel_select matched_data_nodes
    matched_view_nodes matched_hrel_nodes keep_pure_vars=
  let () = DD.ninfo_zprint (lazy  ("  matched_hrel_nodes:" ^ (!CP.print_svl matched_hrel_nodes))) no_pos in
  let new_hf = drop_data_view_hrel_nodes_hf
      fb.formula_base_heap fn_data_select fn_view_select fn_hrel_select
      matched_data_nodes matched_view_nodes matched_hrel_nodes in
  (*assume keep vars = dnodes*)
  let new_p = CP.filter_var_new (MCP.pure_of_mix fb.formula_base_pure) keep_pure_vars in
  let new_p1 = remove_neqNull_redundant_hnodes_hf new_hf new_p in
  (* DD.info_zprint (lazy  ("  keep" ^ (!CP.print_svl keep_pure_vars))) no_pos; *)
  (* DD.info_zprint (lazy  ("  new_p" ^ (!CP.print_formula new_p))) no_pos; *)
  {fb with formula_base_heap = new_hf;
           formula_base_pure = MCP.mix_of_pure new_p1;}

and drop_data_view_hrel_nodes_hf hf0 fn_data_select fn_view_select fn_hrel_select
    data_nodes view_nodes hpargs_nodes=
  let rec helper hf= match hf with
    | Star {h_formula_star_h1 = hf1;
            h_formula_star_h2 = hf2;
            h_formula_star_pos = pos} ->
      let n_hf1 = helper hf1 in
      let n_hf2 = helper hf2 in
      Debug.ninfo_hprint (add_str "nhf1: " !print_h_formula) n_hf1 no_pos;
      Debug.ninfo_hprint (add_str "nhf2: " !print_h_formula) n_hf2 no_pos;
      let res=
        if (n_hf1 = HEmp) then n_hf2
        else if (n_hf2 = HEmp) then n_hf1
        else
          Star {h_formula_star_h1 = n_hf1;
                h_formula_star_h2 = n_hf2;
                h_formula_star_pos = pos}
      in
      Debug.ninfo_hprint (add_str "nhf1*nhf2: " !print_h_formula) res no_pos;
      res
    | StarMinus { h_formula_starminus_h1 = hf1;
                  h_formula_starminus_h2 = hf2;
                  h_formula_starminus_aliasing = al;
                  h_formula_starminus_pos = pos} ->
      let n_hf1 = helper hf1 in
      let n_hf2 = helper hf2 in
      StarMinus { h_formula_starminus_h1 = n_hf1;
                  h_formula_starminus_h2 = n_hf2;
                  h_formula_starminus_aliasing = al;
                  h_formula_starminus_pos = pos}
    | Conj { h_formula_conj_h1 = hf1;
             h_formula_conj_h2 = hf2;
             h_formula_conj_pos = pos} ->
      let n_hf1 = helper hf1 in
      let n_hf2 = helper hf2 in
      Conj { h_formula_conj_h1 = n_hf1;
             h_formula_conj_h2 = n_hf2;
             h_formula_conj_pos = pos}
    | ConjStar { h_formula_conjstar_h1 = hf1;
                 h_formula_conjstar_h2 = hf2;
                 h_formula_conjstar_pos = pos} ->
      let n_hf1 = helper hf1 in
      let n_hf2 = helper hf2 in
      ConjStar { h_formula_conjstar_h1 = n_hf1;
                 h_formula_conjstar_h2 = n_hf2;
                 h_formula_conjstar_pos = pos}
    | ConjConj { h_formula_conjconj_h1 = hf1;
                 h_formula_conjconj_h2 = hf2;
                 h_formula_conjconj_pos = pos} ->
      let n_hf1 = helper hf1 in
      let n_hf2 = helper hf2 in
      ConjConj { h_formula_conjconj_h1 = n_hf1;
                 h_formula_conjconj_h2 = n_hf2;
                 h_formula_conjconj_pos = pos}
    | Phase { h_formula_phase_rd = hf1;
              h_formula_phase_rw = hf2;
              h_formula_phase_pos = pos} ->
      let n_hf1 = helper hf1 in let n_hf2 = helper hf2 in
      Phase { h_formula_phase_rd = n_hf1; h_formula_phase_rw = n_hf2;
              h_formula_phase_pos = pos}
    | DataNode hd -> if fn_data_select hd data_nodes then HEmp
      else hf
    | ViewNode hv -> if fn_view_select hv view_nodes then HEmp
      else hf
    | ThreadNode ht -> hf (*TOCHECK*)
    | HRel (id,_,_) ->
      Debug.ninfo_hprint (add_str "HRel: " !CP.print_sv) id no_pos;
      if fn_hrel_select id hpargs_nodes then HEmp
      else hf
    | Hole _ | FrmHole _
    | HTrue
    | HFalse
    | HEmp | HVar _ -> hf
  in
  helper hf0

and drop_data_view_hpargs_nodes_hf hf0 fn_data_select fn_view_select fn_hrel_select
    data_nodes view_nodes hpargs_nodes=
  let rec helper hf= match hf with
    | Star {h_formula_star_h1 = hf1;
            h_formula_star_h2 = hf2;
            h_formula_star_pos = pos} ->
      let n_hf1 = helper hf1 in
      let n_hf2 = helper hf2 in
      Debug.ninfo_hprint (add_str "nhf1: " !print_h_formula) n_hf1 no_pos;
      Debug.ninfo_hprint (add_str "nhf2: " !print_h_formula) n_hf2 no_pos;
      let res=
        if (n_hf1 = HEmp) then n_hf2
        else if (n_hf2 = HEmp) then n_hf1
        else
          Star {h_formula_star_h1 = n_hf1;
                h_formula_star_h2 = n_hf2;
                h_formula_star_pos = pos}
      in
      Debug.ninfo_hprint (add_str "nhf1*nhf2: " !print_h_formula) res no_pos;
      res
    | StarMinus { h_formula_starminus_h1 = hf1;
                  h_formula_starminus_h2 = hf2;
                  h_formula_starminus_aliasing = al;
                  h_formula_starminus_pos = pos} ->
      let n_hf1 = helper hf1 in
      let n_hf2 = helper hf2 in
      StarMinus { h_formula_starminus_h1 = n_hf1;
                  h_formula_starminus_h2 = n_hf2;
                  h_formula_starminus_aliasing = al;
                  h_formula_starminus_pos = pos}
    | Conj { h_formula_conj_h1 = hf1;
             h_formula_conj_h2 = hf2;
             h_formula_conj_pos = pos} ->
      let n_hf1 = helper hf1 in
      let n_hf2 = helper hf2 in
      Conj { h_formula_conj_h1 = n_hf1;
             h_formula_conj_h2 = n_hf2;
             h_formula_conj_pos = pos}
    | ConjStar { h_formula_conjstar_h1 = hf1;
                 h_formula_conjstar_h2 = hf2;
                 h_formula_conjstar_pos = pos} ->
      let n_hf1 = helper hf1 in
      let n_hf2 = helper hf2 in
      ConjStar { h_formula_conjstar_h1 = n_hf1;
                 h_formula_conjstar_h2 = n_hf2;
                 h_formula_conjstar_pos = pos}
    | ConjConj { h_formula_conjconj_h1 = hf1;
                 h_formula_conjconj_h2 = hf2;
                 h_formula_conjconj_pos = pos} ->
      let n_hf1 = helper hf1 in
      let n_hf2 = helper hf2 in
      ConjConj { h_formula_conjconj_h1 = n_hf1;
                 h_formula_conjconj_h2 = n_hf2;
                 h_formula_conjconj_pos = pos}
    | Phase { h_formula_phase_rd = hf1;
              h_formula_phase_rw = hf2;
              h_formula_phase_pos = pos} ->
      let n_hf1 = helper hf1 in let n_hf2 = helper hf2 in
      Phase { h_formula_phase_rd = n_hf1; h_formula_phase_rw = n_hf2;
              h_formula_phase_pos = pos}
    | DataNode hd -> if fn_data_select hd data_nodes then HEmp
      else hf
    | ViewNode hv -> if fn_view_select hv view_nodes then HEmp
      else hf
    | ThreadNode ht -> hf (*TOCHECK*)
    | HRel (id,eargs,_) ->
      Debug.ninfo_hprint (add_str "HRel: " !CP.print_sv) id no_pos;
      if fn_hrel_select (id, List.concat (List.map CP.afv eargs)) hpargs_nodes then HEmp
      else hf
    | Hole _ | FrmHole _
    | HTrue
    | HFalse
    | HEmp | HVar _ -> hf
  in
  helper hf0

and mkAnd_f_hf f hf pos=
  match f with
  | Base fb -> Base (mkAnd_fb_hf fb hf pos)
  | Or orf -> Or {orf with formula_or_f1 = mkAnd_f_hf orf.formula_or_f1 hf pos;
                           formula_or_f2 = mkAnd_f_hf orf.formula_or_f2 hf pos;}
  | Exists fe ->
    let new_hf = Star { h_formula_star_h1 = fe.formula_exists_heap;
                        h_formula_star_h2 = hf;
                        h_formula_star_pos = pos
                      }
    in
    Exists {fe with formula_exists_heap =  new_hf;}

and mkAnd_fb_hf fb hf pos=
  let new_hf = if fb.formula_base_heap = HEmp then hf
    else Star { h_formula_star_h1 = fb.formula_base_heap ;
                h_formula_star_h2 = hf;
                h_formula_star_pos = pos
              } in
  {fb with formula_base_heap = new_hf}

let rec combine_length_leq ls1 ls2 res=
  match ls1,ls2 with
  | [],_ -> res
  | sv1::tl1,sv2::tl2 -> combine_length_leq tl1 tl2 (res@[sv1,sv2])
  | _ -> report_error no_pos "sau.combine_length_leq"

(*List.combine but ls1 >= ls2*)
let rec combine_length_geq_x ls1 ls2 res=
  match ls1,ls2 with
  | [],[] -> res
  | sv1::_,[] -> res
  | sv1::tl1,sv2::tl2 -> combine_length_geq_x tl1 tl2 (res@[sv1,sv2])
  | _ -> report_error no_pos "sau.combine_length_geq"

let combine_length_geq ls1 ls2 res=
  let pr1= !CP.print_svl in
  let pr2 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
  Debug.no_2 "combine_length_geq" pr1 pr1 pr2
    (fun _ _ -> combine_length_geq_x ls1 ls2 res) ls1 ls2

let rec subst_hrel_hf hf hprel_subst=
  (* let helper (HRel (id,el,p)) (HRel (id1,el1,_), hf)= *)
  let helper hrel1 (hrel2, hf)=
    let id1,el1,_ = extract_HRel_orig hrel1 in
    let id2,el2,_ = extract_HRel_orig hrel2 in
    if CP.eq_spec_var id1 id2 then
      (*fresh svl of the subst to avoid clash in tree which has more than one subst*)
      (*should specvar subst*)
      let svl1 = (List.fold_left List.append [] (List.map CP.afv el1)) in
      let svl2 = (List.fold_left List.append [] (List.map CP.afv el2)) in
      let svl = CP.remove_dups_svl ((h_fv hf)@svl2) in
      (*elim hp*)
      let ls1 = List.filter (fun sv -> not (CP.is_hprel_typ sv)) svl in
      let fr_svl = CP.fresh_spec_vars ls1 in
      let ss = List.combine ls1 fr_svl in
      let fr_svl2 = subst_var_list ss svl2 in
      let hf2 = h_subst ((*List.combine*) combine_length_geq fr_svl2 svl1 [])
          (h_subst ss hf) in
      (true, hf2)
    else (false, hrel1)
  in
  let rec find_and_subst hrel subst =
    match subst with
    | [] -> hrel
    | (hrel1, hf)::ss ->
      let stop,f = helper hrel (hrel1, hf) in
      if stop then f
      else find_and_subst hrel ss
  in
  match hf with
  | Star {h_formula_star_h1 = hf1;
          h_formula_star_h2 = hf2;
          h_formula_star_pos = pos} ->
    let n_hf1 = subst_hrel_hf hf1 hprel_subst in
    let n_hf2 = subst_hrel_hf hf2 hprel_subst in
    Star {h_formula_star_h1 = n_hf1;
          h_formula_star_h2 = n_hf2;
          h_formula_star_pos = pos}
  | StarMinus {h_formula_starminus_h1 = hf1;
               h_formula_starminus_h2 = hf2;
               h_formula_starminus_aliasing = al;
               h_formula_starminus_pos = pos} ->
    let n_hf1 = subst_hrel_hf hf1 hprel_subst in
    let n_hf2 = subst_hrel_hf hf2 hprel_subst in
    StarMinus {h_formula_starminus_h1 = n_hf1;
               h_formula_starminus_h2 = n_hf2;
               h_formula_starminus_aliasing = al;
               h_formula_starminus_pos = pos}
  | Conj { h_formula_conj_h1 = hf1;
           h_formula_conj_h2 = hf2;
           h_formula_conj_pos = pos} ->
    let n_hf1 = subst_hrel_hf hf1 hprel_subst in
    let n_hf2 = subst_hrel_hf hf2 hprel_subst in
    Conj { h_formula_conj_h1 = n_hf1;
           h_formula_conj_h2 = n_hf2;
           h_formula_conj_pos = pos}
  | ConjStar { h_formula_conjstar_h1 = hf1;
               h_formula_conjstar_h2 = hf2;
               h_formula_conjstar_pos = pos} ->
    let n_hf1 = subst_hrel_hf hf1 hprel_subst in
    let n_hf2 = subst_hrel_hf hf2 hprel_subst in
    ConjStar { h_formula_conjstar_h1 = n_hf1;
               h_formula_conjstar_h2 = n_hf2;
               h_formula_conjstar_pos = pos}
  | ConjConj { h_formula_conjconj_h1 = hf1;
               h_formula_conjconj_h2 = hf2;
               h_formula_conjconj_pos = pos} ->
    let n_hf1 = subst_hrel_hf hf1 hprel_subst in
    let n_hf2 = subst_hrel_hf hf2 hprel_subst in
    ConjConj { h_formula_conjconj_h1 = n_hf1;
               h_formula_conjconj_h2 = n_hf2;
               h_formula_conjconj_pos = pos}
  | Phase { h_formula_phase_rd = hf1;
            h_formula_phase_rw = hf2;
            h_formula_phase_pos = pos} ->
    let n_hf1 = subst_hrel_hf hf1 hprel_subst in
    let n_hf2 = subst_hrel_hf hf2 hprel_subst in
    Phase { h_formula_phase_rd = n_hf1;
            h_formula_phase_rw = n_hf2;
            h_formula_phase_pos = pos}
  | DataNode hd -> hf
  | ViewNode hv -> hf
  | ThreadNode ht -> hf
  | HRel _ -> find_and_subst hf hprel_subst
  | Hole _ | FrmHole _
  | HTrue
  | HFalse
  | HEmp | HVar _ -> hf

let rec subst_hrel_f_x f0 hprel_subst=
  let rec helper f=
    match f with
    | Base fb -> Base {fb with formula_base_heap =  subst_hrel_hf fb.formula_base_heap hprel_subst;}
    | Or orf -> Or {orf with formula_or_f1 = helper orf.formula_or_f1;
                             formula_or_f2 = helper orf.formula_or_f2;}
    | Exists fe -> Exists {fe with formula_exists_heap = subst_hrel_hf fe.formula_exists_heap hprel_subst;}
  in
  if hprel_subst = [] then f0 else helper f0

let subst_hrel_f f0 hprel_subst=
  let pr1 = !print_h_formula in
  let pr2 = !print_formula in
  Debug.no_2 "subst_hrel_f" pr2 (pr_list (pr_pair pr1 pr1)) pr2
    (fun _ _ -> subst_hrel_f_x f0 hprel_subst) f0 hprel_subst

let subst_hrel_hview_hf hf0 subst=
  let helper (* (HRel (id,el,p)) *) hrel (id1, hf)=
    let id,el,_ = extract_HRel_orig hrel in
    if CP.eq_spec_var id id1 then
      (*should specvar subst*)
      let svl1 = (List.fold_left List.append [] (List.map CP.afv el)) in
      let hv = match hf with
        | ViewNode hv -> hv
        | _ -> report_error no_pos "CF.subst_hrel_hview_hf.helper"
      in
      let svl2 = hv.h_formula_view_node::hv.h_formula_view_arguments in
      let f = h_subst (List.combine svl2 svl1) hf in
      (true, f)
    else (false, hrel)
  in
  let rec find_and_subst (* (HRel (id,el,p)) *)hrel subst =
    let id,el,p = extract_HRel_orig hrel in
    (* List.fold_left helper (HRel (id,el,p)) subst *)
    match subst with
    | [] -> (HRel (id,el,p))
    | (id1, hf)::ss ->
      let stop,f = helper (HRel (id,el,p)) (id1, hf) in
      if stop then f
      else find_and_subst (HRel (id,el,p)) ss
  in
  let rec helper2 hf=
    match hf with
    | Star {h_formula_star_h1 = hf1;
            h_formula_star_h2 = hf2;
            h_formula_star_pos = pos} ->
      let n_hf1 = helper2 hf1 in
      let n_hf2 = helper2 hf2 in
      Star {h_formula_star_h1 = n_hf1;
            h_formula_star_h2 = n_hf2;
            h_formula_star_pos = pos}
    | StarMinus {h_formula_starminus_h1 = hf1;
                 h_formula_starminus_h2 = hf2;
                 h_formula_starminus_aliasing = al;
                 h_formula_starminus_pos = pos} ->
      let n_hf1 = helper2 hf1 in
      let n_hf2 = helper2 hf2 in
      StarMinus {h_formula_starminus_h1 = n_hf1;
                 h_formula_starminus_h2 = n_hf2;
                 h_formula_starminus_aliasing = al;
                 h_formula_starminus_pos = pos}
    | Conj { h_formula_conj_h1 = hf1;
             h_formula_conj_h2 = hf2;
             h_formula_conj_pos = pos} ->
      let n_hf1 = helper2 hf1 in
      let n_hf2 = helper2 hf2 in
      Conj { h_formula_conj_h1 = n_hf1;
             h_formula_conj_h2 = n_hf2;
             h_formula_conj_pos = pos}
    | ConjStar { h_formula_conjstar_h1 = hf1;
                 h_formula_conjstar_h2 = hf2;
                 h_formula_conjstar_pos = pos} ->
      let n_hf1 = helper2 hf1 in
      let n_hf2 = helper2 hf2 in
      ConjStar { h_formula_conjstar_h1 = n_hf1;
                 h_formula_conjstar_h2 = n_hf2;
                 h_formula_conjstar_pos = pos}
    | ConjConj { h_formula_conjconj_h1 = hf1;
                 h_formula_conjconj_h2 = hf2;
                 h_formula_conjconj_pos = pos} ->
      let n_hf1 = helper2 hf1 in
      let n_hf2 = helper2 hf2 in
      ConjConj { h_formula_conjconj_h1 = n_hf1;
                 h_formula_conjconj_h2 = n_hf2;
                 h_formula_conjconj_pos = pos}
    | Phase { h_formula_phase_rd = hf1;
              h_formula_phase_rw = hf2;
              h_formula_phase_pos = pos} ->
      let n_hf1 = helper2 hf1 in
      let n_hf2 = helper2 hf2 in
      Phase { h_formula_phase_rd = n_hf1;
              h_formula_phase_rw = n_hf2;
              h_formula_phase_pos = pos}
    | DataNode hd -> hf
    | ViewNode hv -> hf
    | ThreadNode ht -> hf
    | HRel _ -> find_and_subst hf subst
    | Hole _ | FrmHole _
    | HTrue
    | HFalse
    | HEmp | HVar _ -> hf
  in
  helper2 hf0


let rec subst_hrel_hview_f_x f0 subst=
  let rec helper f=
    match f with
    | Base fb -> Base {fb with formula_base_heap =  subst_hrel_hview_hf fb.formula_base_heap subst;}
    | Or orf -> Or {orf with formula_or_f1 = helper orf.formula_or_f1 ;
                             formula_or_f2 = helper orf.formula_or_f2;}
    | Exists fe -> Exists {fe with formula_exists_heap =  subst_hrel_hview_hf fe.formula_exists_heap subst;}
  in
  helper f0

let subst_hrel_hview_f f subst=
  let pr1 = !print_formula in
  Debug.no_1 "subst_hrel_hview_f" pr1 pr1
    (fun _ -> subst_hrel_hview_f_x f subst) f

let ins_x ss f0=
  let rec helper f=
    match f with
    | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) ->
      Or ({formula_or_f1 = helper f1; formula_or_f2 =  helper f2; formula_or_pos = pos})
    | Base _-> x_add subst ss f
    | Exists fe ->
      let qvars, base1 = split_quantifiers f in
      let nf = x_add subst ss base1 in
      let ins_svl = fst (List.split ss) in
      let n_qvars = List.filter (fun sv -> not (CP.mem_svl sv ins_svl)) qvars in
      add_quantifiers n_qvars nf
  in
  helper f0

let ins ss f0=
  let pr1 = !print_formula in
  let pr2 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
  Debug.no_2 "ins" pr2 pr1 pr1
    (fun _ _ -> ins_x ss f0) ss f0

let drop_dups_x base f0=
  let rec helper f=
    match f with
    | Base fb->
      (*heap*)
      let g_nodes = get_ptrs_group_hf fb.formula_base_heap in
      let base_nodes =  get_ptrs_group base in
      let inter, ss = List.fold_left (fun (r1,r2) args ->
          let ls_args2 = List.fold_left (fun r args2 ->
              if List.length args = List.length args2 &&
                 CP.intersect args args2 <> [] then
                r@[args2]
              else r
            ) [] base_nodes
          in
          let nr1 = r1@[(List.hd args)] in
          let tl = List.tl args in
          let ss = List.fold_left (fun r args2 ->
              r@(List.combine tl (List.tl args2))
            ) [] ls_args2 in
          (nr1, r2@ss)
        ) ([],[]) g_nodes in
      let n_hf = drop_hnodes_hf fb.formula_base_heap inter in
      (*pure*)
      (* let g_svl = h_fv n_hf in *)
      let () = Debug.ninfo_zprint (lazy (("    ss: " ^ ((pr_list (pr_pair (!CP.print_sv) (!CP.print_sv))) ss)))) no_pos in
      let p = (MCP.pure_of_mix fb.formula_base_pure) in
      let g_pure = (* CP.filter_var *) (* CP.subst ss *) p in
      let p_base = get_pure base in
      let g_pure_base = (* CP.filter_var *) p_base (* g_svl *) in
      let g_pure_rem = Gen.BList.difference_eq (CP.equalFormula) (CP.split_conjunctions g_pure)
          (CP.split_conjunctions g_pure_base) in
      Base {fb with formula_base_heap= n_hf;
                    formula_base_pure = (MCP.mix_of_pure (CP.join_conjunctions g_pure_rem));}
    | Exists fe ->
      let qvars, base1 = split_quantifiers f in
      add_quantifiers qvars (helper base1)
    | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) ->
      Or ({formula_or_f1 = helper f1; formula_or_f2 =  helper f2; formula_or_pos = pos})
  in
  helper f0

let drop_dups base f0=
  let pr1 = !print_formula in
  Debug.no_2 "drop_dups" pr1 pr1 pr1
    (fun _ _ -> drop_dups_x base f0) base f0

(*end for sa*)
(*****************************************)
(*************INFER*******************)
(*****************************************)
let extract_rec_extn_h hf0 v_name v_args inv=
  let rec helper hf=
    match hf with
    | Star {h_formula_star_h1 = hf1;
            h_formula_star_h2 = hf2;} ->
      (helper hf1)@(helper hf2)
    | Conj { h_formula_conj_h1 = hf1;
             h_formula_conj_h2 = hf2;} ->
      (helper hf1)@(helper hf2)
    | Phase { h_formula_phase_rd = hf1;
              h_formula_phase_rw = hf2;} ->
      (helper hf1)@(helper hf2)
    | DataNode hd -> []
    | ViewNode hv -> if String.compare hv.h_formula_view_name v_name = 0 then
        let ss = List.combine v_args hv.h_formula_view_arguments in
        let inv1 = CP.subst ss inv in
        let refined_inv = CP.filter_var inv1 hv.h_formula_view_arguments in
        [((hv.h_formula_view_node, hv.h_formula_view_arguments),refined_inv)] else []
    | ThreadNode hd -> []
    | HRel _
    | Hole _ | FrmHole _
    | HTrue
    | HFalse
    | HEmp | HVar _-> []
    | StarMinus _ | ConjStar _| ConjConj _ -> []
  in
  helper hf0

let extract_rec_extn_x f v_name v_args inv=
  let rec helper f0=
    match f0 with
    | Base fb -> extract_rec_extn_h fb.formula_base_heap v_name v_args inv
    | Exists fe -> extract_rec_extn_h fe.formula_exists_heap v_name v_args inv
    | Or orf -> report_error no_pos "cformula.extract_rec_extn: f should not an or formula"
  in
  helper f

let extract_rec_extn f v_name v_args inv=
  let pr1 = !print_formula in
  let pr2 = pr_list (pr_pair (pr_pair !CP.print_sv !CP.print_svl) !CP.print_formula) in
  Debug.no_4 "extract_rec_extn" pr1 pr_id !CP.print_svl !CP.print_formula pr2
    (fun _ _ _  _ -> extract_rec_extn_x f v_name v_args inv) f v_name v_args inv

let classify_formula_branch_x fs inv v_name v_args v_extns=
  let rec assoc_all sv ls res=
    match ls with
    | [] -> if res = [] then raise Not_found
      else res
    | (sv1,b)::rest -> if CP.eq_spec_var sv sv1 then
        assoc_all sv rest (res@[(sv1,b)])
      else assoc_all sv rest res
  in
  let rec list_assoc extns r_svl res=
    match extns with
    | [] -> res
    | sv::rest ->
      try
        let l_args = assoc_all sv r_svl [] in
        list_assoc rest r_svl (res@ l_args)
      with Not_found -> list_assoc rest r_svl res
  in
  let process_one f=
    let p = extract_pure f in
    (*prune out p*)
    let rec_svl, ls_inv = List.split (extract_rec_extn f v_name v_args inv) in
    let rec_extns = list_assoc v_extns rec_svl [] in
    let keep_svl = if rec_extns=[] then v_args else (v_args@v_extns@(List.concat (snd (List.split rec_svl)))) in
    let p1 = CP.filter_var p keep_svl in
    (*involve inv*)
    (* let filtered_inv = CP.filter_var inv keep_svl in *)
    let filtered_inv = List.fold_left (fun p1 p2 -> CP.mkAnd p1 p2 no_pos) (CP.mkTrue no_pos) ls_inv in
    (CP.mkAnd p1 filtered_inv (CP.pos_of_formula p1),rec_extns)
  in
  let ls_p_r = List.map process_one fs in
  let rec_extns_all= CP.remove_dups_svl (fst (List.split
                                                (List.concat (snd (List.split ls_p_r))))) in
  let val_extns = CP.diff_svl v_extns rec_extns_all in
  (ls_p_r, val_extns)

let classify_formula_branch fs inv v_name v_args v_extns=
  let pr0 = pr_list !print_formula in
  let pr1 = !CP.print_svl in
  let pr2 = pr_pair (pr_list (pr_pair !CP.print_formula
                                (pr_list (pr_pair !CP.print_sv pr1)) )) pr1 in
  Debug.no_5 "classify_formula_branch" pr0 !CP.print_formula pr_id pr1 pr1 pr2
    (fun _ _ _ _ _ -> classify_formula_branch_x fs inv v_name v_args v_extns)
    fs inv v_name v_args v_extns

let extend_view_nodes_h hf0 old_v_name new_v_name extra_args =
  let rec helper hf=
    match hf with
    | Star { h_formula_star_h1 = hf1; h_formula_star_h2 = hf2; h_formula_star_pos = pos} ->
      Star {h_formula_star_h1 = helper hf1; h_formula_star_h2 = helper hf2; h_formula_star_pos = pos}
    |  Conj { h_formula_conj_h1 = hf1; h_formula_conj_h2 = hf2; h_formula_conj_pos = pos} ->
      Conj { h_formula_conj_h1 = helper hf1; h_formula_conj_h2 = helper hf2; h_formula_conj_pos = pos}
    | Phase { h_formula_phase_rd = hf1; h_formula_phase_rw = hf2; h_formula_phase_pos = pos} ->
      Phase { h_formula_phase_rd = helper hf1; h_formula_phase_rw = helper hf2; h_formula_phase_pos = pos}
    | ViewNode vn -> if String.compare vn.h_formula_view_name old_v_name = 0 then
        let fr_extra_args = CP.fresh_spec_vars extra_args in
        let ext_anns = List.map (fun _ -> (CP.ImmAnn (CP.ConstAnn Mutable),0)) fr_extra_args in
        let ext_map,_ = List.fold_left (fun (r, i) sv ->
            let i = i +1 in
            (r@[(CP.SVArg sv, i)], i)
          )  ([],(List.length vn.h_formula_view_arguments)) fr_extra_args in
        (* let () =  Debug.info_pprint ("  fr_extra_args: "^ (!CP.print_svl fr_extra_args)) no_pos in *)
        (* let () =  Debug.info_pprint ("  vn.h_formula_view_annot_arg: "^ ( *)
        (*     (pr_list (pr_pair !CP.print_annot_arg string_of_int)) vn.h_formula_view_annot_arg)) no_pos in *)
        (* let () =  Debug.info_pprint ("  vn.h_formula_view_args_orig: "^ ( *)
        (*     (pr_list (pr_pair CP.print_view_arg string_of_int)) (vn.h_formula_view_args_orig@ext_map))) no_pos in *)
        ViewNode {vn with h_formula_view_name = new_v_name;
                          h_formula_view_arguments = (vn.h_formula_view_arguments@ fr_extra_args);
                          h_formula_view_annot_arg = vn.h_formula_view_annot_arg@ext_anns;
                          h_formula_view_args_orig = vn.h_formula_view_args_orig@ext_map;
                 }
      else hf
    | HRel (CP.SpecVar (t, id, p), eargs, pos) ->
      if String.compare id old_v_name = 0 then
        let fr_extra_args = CP.fresh_spec_vars extra_args in
        let fr_eargs = List.map (fun x -> CP.mkVar x pos) fr_extra_args in
        HRel (CP.SpecVar (t, new_v_name, p), eargs@fr_eargs, pos)
      else hf
    | _ -> hf
  in
  helper hf0

let extend_view_nodes_x (f0:formula) old_v_name new_v_name extra_args =
  let rec helper f=
    match f with
    | Base fb -> Base {fb with formula_base_heap = extend_view_nodes_h fb.formula_base_heap
                                   old_v_name new_v_name extra_args}
    | Exists fe -> Exists {fe with formula_exists_heap = extend_view_nodes_h fe.formula_exists_heap
                                       old_v_name new_v_name extra_args}
    | Or orf -> Or {orf with formula_or_f1 = helper orf.formula_or_f1;
                             formula_or_f2 = helper orf.formula_or_f2;}
  in
  helper f0

let extend_view_nodes (f0:formula) old_v_name new_v_name extra_args =
  let pr1 = !print_formula in
  let pr2 = !CP.print_svl in
  Debug.no_4 "extend_view_nodes" pr1 pr_id pr_id pr2 pr1
    (fun _ _ _ _ -> extend_view_nodes_x f0 old_v_name new_v_name extra_args)
    f0 old_v_name new_v_name extra_args

let rec retrieve_args_from_locs_helper args locs index res=
  match args with
  | [] -> res
  | a::ss -> if List.mem index locs then
      retrieve_args_from_locs_helper ss locs (index+1) (res@[a])
    else retrieve_args_from_locs_helper ss locs (index+1) res

let retrieve_args_from_locs args locs=
  retrieve_args_from_locs_helper args locs 0 []

let extract_abs_formula_branch_x fs v_base_name v_new_name extn_args ls_ann_infos pure_extn_svl is_spec is_view=
  (* let gen_null_svl extn_args= *)
  (*   List.map (fun (CP.SpecVar (t,_,p)) -> (CP.SpecVar (t,null_sv,p))) extn_args *)
  (* in *)
  let rec get_args_from_pos args all_sel_pos=
    let rec gen_n cur n res=
      if cur>=n then res
      else gen_n (cur+1) n (res@[cur])
    in
    let l = List.length args in
    let ns = gen_n 0 l [] in
    (* let pr = pr_list string_of_int in *)
    (* let () =  Debug.info_pprint ("  sel_pos: "^ (pr ns)) no_pos in *)
    let cmb = List.combine ns args in
    List.map (fun p -> List.assoc p cmb) all_sel_pos
  in
  let get_sel_args_from_dnode dn=
    let all_sel_pos = List.fold_left (fun ls1 ls2 -> ls1@ls2) []
        (List.map (fun (dname, pos) -> if String.compare dname dn.h_formula_data_name =0 &&
                                          (* pointers are to be pure-extended*)
                                          (is_view || Gen.BList.mem_eq CP.eq_spec_var dn.h_formula_data_node pure_extn_svl)
                    then [pos] else []) ls_ann_infos) in
    (* let all_sel_pos1 = List.sort (fun a b -> a - b) all_sel_pos in *)
    (* let pr = pr_list string_of_int in *)
    (* let () =  Debug.info_pprint ("  all_sel_pos1: "^ (pr  all_sel_pos)) no_pos in *)
    let sel_args = get_args_from_pos dn.h_formula_data_arguments all_sel_pos in
    sel_args
  in
  let get_last_n n args =
    (* BUG : OCaml compiler bug when n>length args *)
    (* let args = hv.h_formula_view_arguments in *)
    let len = List.length args in
    let () = y_ninfo_hp (add_str "len" string_of_int) len in
    let () = y_ninfo_hp (add_str "n" string_of_int) n in
    let () = y_ninfo_hp (add_str "args" !CP.print_svl) args in
    let arr = Array.of_list args in
    let arr_ex = Array.sub arr (len - n) n in
    let r = Array.to_list arr_ex in
    let () = y_ninfo_hp (add_str "r" !CP.print_svl) r in
    r
  in
  let get_last_n n args =
    let n_a = List.length args in
    let rec drop args n =
      if n<=0 then args
      else
        match args with
        | [] -> []
        | x::xs -> drop xs (n-1) in
    drop args (n_a - n) in
  let get_last_n n args =
    let pr = !CP.print_svl in
    Debug.no_2 "get_last_n" string_of_int pr pr get_last_n n args in
  let classify_rec_svl hvs n sv=
    let rec look_up l_hvs=
      match l_hvs with
      | [] -> []
      | hv::rest -> if CP.eq_spec_var hv.h_formula_view_node sv then
          begin
            let args = hv.h_formula_view_arguments in
            get_last_n n args
            (* let len = List.length args in *)
            (* let () = y_ninfo_hp (add_str "len" string_of_int) len in *)
            (* let () = y_ninfo_hp (add_str "n" string_of_int) n in *)
            (* let () = y_ninfo_hp (add_str "args" !CP.print_svl) args in *)
            (* let arr = Array.of_list args in *)
            (* let arr_ex = Array.sub arr (len - n) n in *)
            (* let r = Array.to_list arr_ex in *)
            (* let () = y_ninfo_hp (add_str "r" !CP.print_svl) r in *)
            (* r *)
          end
        else
          look_up rest
    in
    let extra_args= look_up hvs in
    let () =  x_ninfo_pp ("  extra_args: "^ (!CP.print_svl extra_args)) no_pos in
    if extra_args = [] then ([sv],[]) else ([],[(sv,extra_args)])
  in
  let pred_classify_rec_svl hrels n sv=
    let rec look_up l_hrels=
      match l_hrels with
      | [] -> []
      | (hp, eargs,_)::rest ->
        let args = (List.fold_left List.append [] (List.map CP.afv eargs)) in
        if CP.mem_svl sv args then
          begin
            get_last_n n args
            (*  let arr = Array.of_list args in *)
            (* let arr_ex = Array.sub arr (List.length args - n) n in *)
            (* Array.to_list arr_ex *)
          end
        else
          look_up rest
    in
    let extra_args= look_up hrels in
    (* let () =  Debug.info_pprint ("  extra_args: "^ (!CP.print_svl extra_args)) no_pos in *)
    if extra_args = [] then ([sv],[]) else ([],[(sv,extra_args)])
  in
  let classify_sel_null_svl f sel_svl=
    let null_svl =  get_null_svl f in
    let sel_null_svl = CP.intersect_svl null_svl sel_svl in
    let sel_null_pair = List.map (fun sv -> (sv, [](* gen_null_svl extn_args *)))
        sel_null_svl in
    (sel_null_svl, sel_null_pair)
  in
  let process_one f=
    (*extend new view name, new args*)
    let extn_args1 = if is_spec then [] else  extn_args in
    let f1 = extend_view_nodes f v_base_name v_new_name extn_args1 in
    (*get dataNode, ViewNode*)
    let hds,hvs, hrels= flatten_nodes f1 in
    let sel_svl = CP.remove_dups_svl ( List.concat (List.map get_sel_args_from_dnode hds)) in
    (*process null pointer*)
    let () =  x_ninfo_pp ("  f1: "^ (!print_formula f1)) no_pos in
    let () =  x_ninfo_pp ("  sel_svl: "^ (!CP.print_svl sel_svl)) no_pos in
    let null_svl,null_paired_svl = classify_sel_null_svl f1 sel_svl in
    let () =  x_ninfo_pp ("  null_svl: "^ (!CP.print_svl null_svl)) no_pos in
    let sel_svl_rest = x_add CP.diff_svl sel_svl null_svl in
    (* let () =  Debug.info_pprint ("  sel_svl_rest: "^ (!CP.print_svl sel_svl_rest)) no_pos in *)
    let () = y_tinfo_pp "1" in
    let val_svl,rec_svl= if is_view then
        let () = y_tinfo_pp "2a" in
        List.split (List.map (classify_rec_svl hvs (List.length extn_args)) sel_svl_rest)
      else
        let () = y_tinfo_pp "2b" in
        List.split (List.map (pred_classify_rec_svl hrels (List.length extn_args)) sel_svl_rest)
    in
    let () = y_tinfo_hp (add_str "rec_svl" (pr_list (pr_list (pr_pair !CP.print_sv pr_none)))) rec_svl in
    let () = y_tinfo_pp "3" in
    let val_svl1 = List.concat val_svl in
    let () = y_tinfo_pp "4" in
    let rec_svl1 = List.concat rec_svl in
    if (* val_svl1=[] && *) rec_svl1=[] && null_paired_svl = []
    then ([(f1,val_svl1)],[]) else ([],
                                    [(f1, (* List.filter (fun sv -> not (CP.is_node_typ sv)) *) val_svl1 (*todo: should improve with double check*),
                                      rec_svl1@null_paired_svl)])
  in
  let () = y_tinfo_pp "5" in
  let ls_bases,ls_inds = List.split (List.map process_one fs) in
  let () = y_tinfo_pp "6" in
  let r1 = List.concat ls_bases in
  let n1 = List.length r1 in
  let () = y_tinfo_hp (add_str "ls_bases" string_of_int) n1 in
  let r2 = List.concat ls_inds in
  let n2 = List.length r2 in
  let () = y_tinfo_hp (add_str "ls_inds" string_of_int) n2 in
  let pr1a x = string_of_int (List.length x) in
  let pr1 = !CP.print_svl in
  let pr_1 = (pr_list (pr_pair !print_formula pr1)) in
  let pr_2 = (pr_list (pr_triple pr_none pr1 (pr_list (pr_pair !CP.print_sv pr1a)))) in
  let pr_3 = (pr_list (pr_triple !print_formula pr_none pr_none)) in
  let () = y_tinfo_hp (add_str "ls_bases" pr_1) r1 in
  let () = y_tinfo_hp (add_str "ls_inds" pr_3) r2 in
  let () = y_tinfo_hp (add_str "ls_inds" pr_2) r2 in
  (* let v = match r2 with *)
  (*   | [(_,_,lst)] -> lst  *)
  (*   | _ -> [] in *)
  (* let () = y_tinfo_pp "7a" in *)
  (* let v = List.hd v in *)
  (* let v = List.hd (snd v) in *)
  (* let () = y_tinfo_pp "7b" in *)
  (* let t = CP.type_of_spec_var v in *)
  (* let () = y_tinfo_pp "7b1" in *)
  (* let n = CP.name_of_spec_var v in *)
  (* let () = y_tinfo_pp "8" in *)
  (* let () = y_tinfo_hp (add_str "len(problem sv)" (fun s -> string_of_int (String.length s))) n in   *)
  (r1,r2)

(* (==derive.ml#209==) *)
(* extract_abs_formula_branch@2 *)
(* extract_abs_formula_branch inp1 :[ emp&self=null&{FLOW,(1,26)=__flow#E}[], (exists p_82,Anon_81: self::node<Anon_81,p_82>@M * p_82::ll<>@M& *)
(* {FLOW,(1,26)=__flow#E}[])] *)
(* extract_abs_formula_branch inp2 :ll *)
(* extract_abs_formula_branch inp3 :extn_ll *)
(* extract_abs_formula_branch inp4 :[size_prop] *)
(* extract_abs_formula_branch inp5 :[(node,1)] *)
(* extract_abs_formula_branch inp6 :[self] *)
(* extract_abs_formula_branch@2 EXIT:(emp&self=null&{FLOW,(1,26)=__flow#E}[],[])],[( (exists p_82,Anon_81: self::node<Anon_81,p_82>@M * p_82::extn_ll<size_83>@M& *)
(* {FLOW,(1,26)=__flow#E}[]),[],[(p_82,[size_83])])]) *)
let extract_abs_formula_branch fs v_base_name v_new_name extn_args ls_ann_infos
    pure_extn_svl is_spec is_view=
  let pr0 = pr_list !print_formula in
  let pr1 = !CP.print_svl in
  let pr2 = pr_list (pr_pair pr_id string_of_int) in
  let pr3 = pr_pair (pr_list (pr_pair !print_formula pr1)) (pr_list (pr_triple !print_formula pr1 (pr_list (pr_pair !CP.print_sv pr1)))) in
  Debug.no_6 "extract_abs_formula_branch" pr0 pr_id pr_id pr1 pr2 (pr1) pr3
    (fun _ _ _ _ _ _ -> extract_abs_formula_branch_x fs v_base_name v_new_name extn_args ls_ann_infos
        pure_extn_svl is_spec is_view)
    fs v_base_name v_new_name extn_args ls_ann_infos pure_extn_svl

(*****************************************)
(*************END INFER*************)
(*****************************************)
(* context functions *)

(*type formula_cache_no = int

  type formula_cache_no_list = formula_cache_no list*)
type formula_trace = string list

type list_formula_trace = formula_trace list

class infer_acc =
  object (self)
    val mutable pure = None
    (* return false if unsat in inferred pure *)
    method logging s pr e =
      let () = y_info_hp (add_str ("*** infer_acc "^s) pr) e in
      ()
    method add_pure_list plst  =
      if plst==[] then true
      else self # add_pure (CP.join_conjunctions plst)
    method add_pure p  =
      let () = self # logging "add_pure" !CP.print_formula p in
      match pure with
      | None ->
        let () = pure <- Some p in
        true
      | Some p1 ->
        let np = CP.mkAnd p1 p no_pos in
        let sat_flag = x_add_1 !CP.tp_is_sat np in
        if sat_flag then
        let () = pure <- Some np in
        true
        else
          let () = y_dinfo_hp (add_str "previously inferred" !CP.print_formula) p1 in
          let () = y_dinfo_hp (add_str "false contra with" !CP.print_formula) p in
          false
  end;;

type entail_state = {
  es_formula : formula; (* can be any formula ;
                           !!!!!  make sure that for each change to this formula the es_cache_no_list is update apropriatedly*)
  es_heap : h_formula; (* consumed nodes *)
  es_ho_vars_map :  ( CP.spec_var * formula) list; (* map: HVar -> its formula *)
  es_heap_lemma : h_formula list;
  es_conseq_pure_lemma : CP.formula; (*conseq of entailment before rhs_plit. for lemmasyn*)
  (* heaps that have been replaced by lemma rewriting *)
  (* to be used for xpure conversion *)
  (* es_history : h_formula list;  *)(* for sa: no longer used *)
  es_evars : CP.spec_var list; (* existential variables on RHS *)

  (* WN : What is es_pure for? *)
  (*  It is added into the residue in
      the method "heap_entail_empty_rhs_heap" but only when we do folding. It
      is the pure constraints of the RHS when there is no heap. This es_pure
      will be split into to_ante and to_conseq when ~Sprocess_fold_result~T. I
      think it is used to instantiate when folding.
  *)
  es_pure : MCP.mix_formula;
  es_folding_conseq_pure : MCP.mix_formula option; (* while folding, pure of current conseq has not been fwded. pass this pure to guide strategy *)
  (*used by universal LEMMAS for instantiation? *)
  es_ivars : CP.spec_var list;
  (* ivars are the variables to be instantiated (for the universal lemma application)  *)
  (* es_expl_vars : CP.spec_var list; (\* vars to be explicit instantiated *\) *)
  es_ante_evars : CP.spec_var list;
  (* es_must_match : bool; *)
  (*used by late instantiation*)
  es_gen_expl_vars: CP.spec_var list; (* explicit instantiation var *)
  es_gen_impl_vars: CP.spec_var list; (* implicit instantiation var *)

  (* to indicate if unsat check has been done for current state *)
  es_unsat_flag : bool; (* true - unsat already performed; false - requires unsat test *)
  es_pp_subst : (CP.spec_var * CP.spec_var) list;
  es_arith_subst : (CP.spec_var * CP.exp) list;
  es_success_pts : (formula_label * formula_label)  list  ;(* successful pt from conseq *)
  es_residue_pts : formula_label  list  ;(* residue pts from antecedent *)
  es_id      : int              ; (* unique +ve id *)
  (* below is to store an antecedent prior to it becoming false *)
  es_orig_ante   : formula option       ;  (* original antecedent formula *)
  es_orig_conseq : struc_formula ;
  es_path_label : path_trace;
  es_cond_path : cond_path_type;
  es_prior_steps : steps; (* prior steps in reverse order *)
  (*es_cache_no_list : formula_cache_no_list;*)
  (* For Termination checking *)
  (* Term ann with Lexical ordering *)
  es_var_measures : (CP.term_ann * CP.exp list * CP.exp list) option;
  (* For TNT inference: List of unknown returned context *)
  (* es_infer_tnt: bool; *)
  es_infer_obj: Globals.inf_obj_sub; (* includes Global.infer_const_obj *)
  (* es_infer_consts: array of 1..n of bool; *)
  es_term_res_lhs: CP.term_ann list;
  es_term_res_rhs: CP.term_ann option;
  es_term_call_rhs: CP.term_ann option;
  es_infer_term_rel: Tid.tntrel list;
  es_var_stack :  string list;
  (* this should store first termination error detected *)
  (* in case an error has already been detected *)
  (* we will not do any further termination checking *)
  (* from this context *)
  es_term_err: string option;

  (* for IMMUTABILITY *)
  (* INPUT : this is an alias set for the RHS conseq *)
  (* to be used by matching strategy for imm *)
  es_rhs_eqset : (CP.spec_var * CP.spec_var) list;
  (*  es_frame : (h_formula * int) list; *)
  es_cont : h_formula list;
  es_crt_holes : (h_formula * int) list;
  es_hole_stk : ((h_formula * int) list) list;
  es_aux_xpure_1 : MCP.mix_formula;
  es_imm_last_phase : bool;
  (* below are being used as OUTPUTS *)
  es_subst :  (CP.spec_var list *  CP.spec_var list) (* from * to *);
  (* for immutability ann: as opposed to other vars, related imm vars are not substituted during a match, but added to the pure as a formula *)
  es_exists_pure : CP.formula option;
  es_rhs_pure : CP.formula option;      (* updated before doing a rhs split; used to guide ann instantiation *)
  es_aux_conseq : CP.formula;
  (* es_imm_pure_stk : MCP.mix_formula list; *)
  es_must_error : (string * fail_type * failure_cex) option;
  es_may_error : (string * fail_type * failure_cex) option;
  (* accumulated erors *)
  es_final_error: (string * fail_type * failure_kind) list;
  (* es_must_error : string option *)
  es_trace : formula_trace; (*LDK: to keep track of past operations: match,fold...*)
  (*for cyclic proof*)
  es_proof_traces: (formula*formula) list;
  (* WN : isn't above the same as prior steps? *)
  es_is_normalizing : bool; (*normalizing process*)

  (* VPERM: to support permission of variables *)
  (* denotes stack variables with possibly zero permission *)
  (* TODO: To be removed *)
  es_var_zero_perm : CP.spec_var list;
  es_conc_err: (string * loc) list; (* To contain concurrencyc error msg *)

  (* FOR INFERENCE *)
  (* input flag to indicate if post-condition is to be inferred *)
  es_infer_post : bool;
  (*input vars where inference expected*)
  (* es_subst_ref: (CP.spec_var * CP.spec_var) list; *)
  (* WN : why so many diff type of infer vars, can we streamline?? *)
  es_infer_vars : CP.spec_var list;  (* for first-order object *)
  (* es_infer_vars_done_heap: CP.spec_var list; *)  (* by first-order infer_heap *)
  es_infer_vars_rel : CP.spec_var list; (* for relations *)
  es_infer_vars_sel_hp_rel: CP.spec_var list;
  es_infer_vars_sel_post_hp_rel: CP.spec_var list;
  es_infer_hp_unk_map: ((CP.spec_var * int list)  * CP.xpure_view) list ;
  es_infer_vars_hp_rel : CP.spec_var list;
  (* input vars to denote vars already instantiated - WN: above or below?*)
  es_infer_vars_dead : CP.spec_var list;
  (*  es_infer_init : bool; (* input : true : init, false : non-init *)                *)
  (*  es_infer_pre : (formula_label option * formula) list;  (* output heap inferred *)*)
  (* output : pre heap inferred *)
  es_infer_heap : h_formula list;
  (* Template: For template inference *)
  es_infer_vars_templ: CP.spec_var list;
  es_infer_templ_assume: (CP.formula * CP.formula) list;
  es_infer_templ: CP.exp list;
  (* output : pre pure inferred *)
  es_infer_pure : CP.formula list;
  (* output : post inferred relation lhs --> rhs *)

  (*  (i) defn for relation:
          lhs -> p(...);
      (ii) proof obligation for unknown relation
          p(...) -> ctr
      (ii) term measures:
          lhs -> r(..)>=0
          lhs -> r(..)-r(..)>0
      RelCat = RelDef (rid) | RelAssume(rid)
      | RankDec [rid] | RankBounded id
  *)
  (* es_infer_rel : (CP.formula * CP.formula) list; *)
  es_infer_rel : CP.infer_rel_type Gen.stack_pr; (* CP.infer_rel_type list; *)
  es_infer_hp_rel : hprel Gen.stack_pr; (* hprel list; *) (*(CP.rel_cat * formula * formula) list;*)
  (* output : pre pure assumed to infer relation *)
  (* es_infer_pures : CP.formula list; *)
  (* es_infer_invs : CP.formula list (\* WN : what is this? *\) *)
  (* input precondition inferred so far, for heap
     you may accumulate the xpure0 information;
     to be used by infer_lhs_contra to determine if
     a FALSE is being inferred
  *)
  es_infer_pure_thus : CP.formula; (* WN:whay is this needed? docu*)
  (* es_infer_acc  : infer_acc; (\* outcome of accumulated inference *\) *)
  es_group_lbl: spec_label_def;
}

and context =
  | Ctx of entail_state
  | OCtx of (context * context) (* disjunctive context *)
(*| FailCtx of (fail_context list)*)

and steps = string list

(*      MAY

        VALID       MUST

        BOT
*)
and failure_kind =
  | Failure_May of string
  | Failure_Must of string
  | Failure_Bot of string
  | Failure_Valid

and failure_cex = {
  cex_sat: bool;
  cex_processed_mark: bool;
}

and fail_explaining = {
  fe_kind: failure_kind; (*may/must*)
  fe_name: string;
  fe_locs: (*VarGen.loc*) int list; (*line number*)
  (* fe_explain: string;  *)
  (* string explaining must failure *)
  (*  fe_sugg = struc_formula *)
}

and fail_context = {
  fc_prior_steps : steps; (* prior steps in reverse order *)
  fc_message : string;          (* error message *)
  fc_current_lhs : entail_state;     (* LHS context with success points *)
  fc_orig_conseq : struc_formula;     (* RHS conseq at the point of failure *)
  fc_failure_pts : Globals.formula_label list;     (* failure points in conseq *)
  fc_current_conseq : formula;
}

and fail_type =
  | Basic_Reason of (fail_context * fail_explaining * formula_trace)
  | Trivial_Reason of (fail_explaining * formula_trace)
  | Or_Reason of (fail_type * fail_type)
  | And_Reason of (fail_type * fail_type)
  | Union_Reason of (fail_type * fail_type)
  | ContinuationErr of (fail_context * formula_trace)
  | Or_Continuation of (fail_type * fail_type)

(* Fail | List of Successes *)
and list_context =
  | FailCtx of (fail_type * context * failure_cex)
  | SuccCtx of context list

and branch_fail = path_trace * fail_type

and branch_ctx =  path_trace * context  * fail_type option

(* disjunction of state with failures and partial success *)
(* a state is successful if it has empty branch_fail *)
and partial_context = (branch_fail list) * (branch_ctx list)
(* disjunct of failures and success *)

(* successful partial states that have escaped through exceptions *)
and esc_stack = ((control_path_id_strict * branch_ctx list) list)

and failesc_context = (branch_fail list) * esc_stack * (branch_ctx list)

(* conjunct of context in the form of /\(f1|f2 ..s1|s2|s3) *)
and list_partial_context = partial_context list

and list_failesc_context = failesc_context list
(* conjunct of contexts *)

and list_failesc_context_tag = failesc_context Gen.Stackable.tag_list

let print_list_context_short = ref(fun (c:list_context) -> "printer not initialized")
let print_cex = ref( fun (c: failure_cex) -> "printer not initialized")
let print_list_context = ref(fun (c:list_context) -> "printer not initialized")
let print_context_list_short = ref(fun (c:context list) -> "printer not initialized")
let print_context_short = ref(fun (c:context) -> "printer not initialized")
let print_context = ref(fun (c:context) -> "printer not initialized")
let print_entail_state = ref(fun (c:entail_state) -> "printer not initialized")
let print_entail_state_short = ref(fun (c:entail_state) -> "printer not initialized")
let print_list_partial_context = ref(fun (c:list_partial_context) -> "printer not initialized")
let print_partial_context = ref(fun (c:partial_context) -> "printer not initialized")
let print_list_failesc_context = ref(fun (c:list_failesc_context) -> "printer not initialized")
(* let print_flow = ref(fun (c:nflow) -> "printer not initialized") *)
let print_esc_stack = ref(fun (c:esc_stack) -> "printer not initialized")
let print_failesc_context = ref(fun (c:failesc_context) -> "printer not initialized")
let print_failure_kind_full = ref(fun (c:failure_kind) -> "printer not initialized")
let print_fail_type = ref(fun (c:fail_type) -> "printer not initialized")



let rec is_infer_pre_must sf = match sf with
  | EList el -> List.exists (fun (lbl,sf) ->
      is_infer_pre_must sf) el
  | EInfer ei ->
    let inf_obj = ei.formula_inf_obj in
    (inf_obj # is_pre_must)
  | _ -> false

let is_dis_err_exc es =
  es.es_infer_obj # is_dis_err_all

let is_err_must_exc es =
  es.es_infer_obj # is_err_must_all

let is_err_must_only_exc es =
  es.es_infer_obj # is_err_must_only

let is_en_error_exc es =
  not(is_dis_err_exc es)
(* es.es_infer_obj # is_err_must || es.es_infer_obj # is_err_may *)


let rec is_en_error_exc_ctx c =
  match c with
  | Ctx es -> is_en_error_exc es
  | OCtx (c1,c2) -> is_en_error_exc_ctx c1 || is_en_error_exc_ctx c2

let rec is_err_must_exc_ctx c =
  match c with
  | Ctx es -> is_err_must_only_exc es
  | OCtx (c1,c2) -> is_err_must_exc_ctx c1 || is_err_must_exc_ctx c2

let is_en_error_exc_ctx_list lc =
  match lc with
  | FailCtx (_,c,_) -> is_en_error_exc_ctx c
  | SuccCtx cs -> List.exists is_en_error_exc_ctx cs

let is_dis_error_exc es=
  es.es_infer_obj # is_dis_err

let rec is_dis_error_exc_ctx c=
  match c with
  | Ctx es -> is_dis_error_exc es
  | OCtx (c1,c2) -> is_dis_error_exc_ctx c1 && is_dis_error_exc_ctx c2

let is_dis_error_exc_ctx_list lc=
  match lc with
  | FailCtx (_,c,_) -> is_dis_error_exc_ctx c
  | SuccCtx cs -> List.for_all is_dis_error_exc_ctx cs

let is_dfa es=
  es.es_infer_obj # is_dfa

let rec is_dfa_ctx c=
  match c with
  | Ctx es -> is_dfa es
  | OCtx (c1,c2) -> is_dfa_ctx c1 || is_dfa_ctx c2

let is_dfa_ctx_list lc=
  match lc with
  | FailCtx (_,c,_) -> is_dfa_ctx c
  | SuccCtx cs -> List.exists is_dfa_ctx cs

let is_infer_none_es es =
  (es.es_infer_heap==[] && es.es_infer_templ_assume==[] && es.es_infer_pure==[] && es.es_infer_rel # is_empty_recent && es.es_infer_hp_rel # is_empty_recent)

let is_infer_none_ctx c =
  let rec aux c =
    match c with
      | Ctx es -> is_infer_none_es es
      | OCtx (c1,c2) -> aux c1 && aux c2
  in aux c
let is_infer_type_es it es =
  es.es_infer_obj # is_infer_type it

let is_infer_type_ctx it c =
  let rec aux c =
    match c with
    | Ctx es -> is_infer_type_es it es
    | OCtx (c1,c2) -> aux c1 || aux c2
  in aux c

(* let is_arr_as_var_ctx c = *)
(*   is_infer_type_ctx Globals.INF_ARR_AS_VAR c *)

let acc_error_msg final_error_opt add_msg =
  let rec aux ferr =
    match ferr with
    | [] -> []
    | (s,c,ft)::rest -> ((add_msg ^";\n"^s),c,ft)::(aux rest)
  in aux final_error_opt

let acc_error_msg final_error_opt add_msg =
  let pr1 = pr_list (fun (s,_,_) -> s) in
  Debug.no_2 "acc_error_msg" pr1 pr_id pr1 acc_error_msg final_error_opt add_msg
(****************************************************)
(********************CEX**********************)
(****************************************************)

let get_short_str_fail_type ft =
  match ft with
  | Basic_Reason (fc,fe,_) -> fc.fc_message
  | Trivial_Reason (fe,_) -> ("Trivial :"^fe.fe_name)
  | _ -> "Complex : ??"

let rec get_false_entail_state ctx =
  match ctx with
  | Ctx es -> es
  | OCtx (left,_) -> get_false_entail_state left

let mk_cex is_sat=
  {cex_sat = is_sat;
   cex_processed_mark=false;
  }

let is_sat_fail cex=
  cex.cex_sat

let cmb_fail_msg s cex=
  let is_sat, s =
    if cex.cex_sat then
      (true,("(cex)"^s))
    else
      (false,"(no cex)" ^s)
  in is_sat,s

let cex_union cex1 cex2=
  match cex1.cex_sat, cex2.cex_sat with
  | false,false -> (* to combine cex*) cex1
  | true,false -> cex1
  | false, true -> cex2
  | true,true -> cex1

(* to implement *)
let cex_lor cex1 cex2= cex1

let cex_land cex1 cex2= cex1

(****************************************************)
(********************END CEX**********************)
(****************************************************)

let get_estate_from_context ctx =
  match ctx with
  | Ctx es -> Some es
  | _ -> None

let get_infer_vars_sel_hp_ctx ctx0=
  let rec helper ctx=
    match ctx with
    | Ctx es -> es.es_infer_vars_sel_hp_rel
    | OCtx (ctx1,ctx2) -> (* CP.remove_dups_svl *) ((helper ctx1)(* @(helper ctx2) *))
  in
  helper ctx0

let get_infer_vars_sel_hp_list_ctx lc=
  match lc with
  | FailCtx _ -> []
  | SuccCtx cl -> List.fold_left (fun rs ctx->
      let r = get_infer_vars_sel_hp_ctx ctx in
      (rs@r)
    ) [] cl

let get_infer_vars_sel_post_hp_ctx ctx0=
  let rec helper ctx=
    match ctx with
    | Ctx es -> es.es_infer_vars_sel_post_hp_rel
    | OCtx (ctx1,ctx2) -> (helper ctx1)@(helper ctx2)
  in
  helper ctx0

let get_infer_vars_sel_hp_branch_ctx (_,ctx,_)=
  get_infer_vars_sel_hp_ctx ctx

let get_infer_vars_sel_post_hp_branch_ctx (_,ctx,_)=
  get_infer_vars_sel_post_hp_ctx ctx

let get_infer_vars_sel_hp_partial_ctx (_, br_list)=
  if List.length br_list == 0 then [] else
    get_infer_vars_sel_hp_branch_ctx (List.hd br_list)

let get_infer_vars_sel_post_hp_partial_ctx (_, br_list)=
  if List.length br_list == 0 then [] else
    get_infer_vars_sel_post_hp_branch_ctx (List.hd  br_list)

let get_infer_vars_sel_hp_partial_ctx_list ls =
  if List.length ls == 0 then [] else
    get_infer_vars_sel_hp_partial_ctx (List.hd ls)

let get_infer_vars_sel_post_hp_partial_ctx_list ls=
  if List.length ls == 0  then [] else
    get_infer_vars_sel_post_hp_partial_ctx (List.hd ls)

let infer_type_of_entail_state es =
  if (* es.es_infer_tnt *) es.es_infer_obj # is_term
  then Some INF_TERM
  else None

let rec is_inf_term_ctx ctx =
  match ctx with
  | Ctx es -> es.es_infer_obj # is_term
  | OCtx (ctx1, ctx2) -> (is_inf_term_ctx ctx1) || (is_inf_term_ctx ctx2)

let rec is_inf_term_struc f =
  match f with
  | EInfer ei -> (ei.formula_inf_obj # is_term) || (ei.formula_inf_obj # is_term_wo_post)
  | EBase eb -> begin
      match eb.formula_struc_continuation with
      | None -> false
      | Some c -> is_inf_term_struc c
    end
  | EAssume _ -> false
  | ECase ec -> List.exists (fun (_, c) -> is_inf_term_struc c) ec.formula_case_branches
  | EList el -> List.exists (fun (_, c) -> is_inf_term_struc c) el

let rec is_inf_term_only_struc f =
  match f with
  | EInfer ei -> (ei.formula_inf_obj # is_term) && not (ei.formula_inf_obj # is_term_wo_post)
  | EBase eb -> begin
      match eb.formula_struc_continuation with
      | None -> false
      | Some c -> is_inf_term_struc c
    end
  | EAssume _ -> false
  | ECase ec -> List.exists (fun (_, c) -> is_inf_term_only_struc c) ec.formula_case_branches
  | EList el -> List.exists (fun (_, c) -> is_inf_term_only_struc c) el

let rec is_inf_term_wo_post_struc f =
  match f with
  | EInfer ei -> ei.formula_inf_obj # is_term_wo_post
  | EBase eb -> begin
      match eb.formula_struc_continuation with
      | None -> false
      | Some c -> is_inf_term_wo_post_struc c
    end
  | EAssume _ -> false
  | ECase ec -> List.exists (fun (_, c) -> is_inf_term_wo_post_struc c) ec.formula_case_branches
  | EList el -> List.exists (fun (_, c) -> is_inf_term_wo_post_struc c) el

let rec is_inf_post_struc f =
  match f with
  | EInfer ei -> ei.formula_inf_obj # is_post
  | EBase eb -> begin
      match eb.formula_struc_continuation with
      | None -> false
      | Some c -> is_inf_post_struc c
    end
  | EAssume _ -> false
  | ECase ec -> List.exists (fun (_, c) -> is_inf_post_struc c) ec.formula_case_branches
  | EList el -> List.exists (fun (_, c) -> is_inf_post_struc c) el

let rec add_infer_vars_templ_ctx ctx inf_vars_templ =
  match ctx with
  | Ctx es -> Ctx { es with es_infer_vars_templ = es.es_infer_vars_templ @ inf_vars_templ; }
  | OCtx (ctx1, ctx2) ->
    OCtx (add_infer_vars_templ_ctx ctx1 inf_vars_templ,
          add_infer_vars_templ_ctx ctx2 inf_vars_templ)

let es_fv (es:entail_state) : CP.spec_var list =
  (fv es.es_formula)@(h_fv es.es_heap)

let rec context_fv (c:context) : CP.spec_var list =
  match c with
  | Ctx es ->  es_fv es
  | OCtx (c1,c2) -> (context_fv c1)@(context_fv c2)

let empty_infer_rel () = new Gen.stack

let repl_pure_formula pf f =
  let mpf = MCP.mix_of_pure pf in
  let rec aux f = match f with
    | Base e -> Base {e with formula_base_pure = mpf}
    | Exists e -> Exists {e with formula_exists_pure = mpf}
    | Or ({formula_or_f1=f1; formula_or_f2=f2} as b) ->
      Or {b with formula_or_f1=aux f1; formula_or_f2=aux f2}
  in aux f

let repl_heap_formula h f =
  let rec aux f = match f with
    | Base e -> Base {e with formula_base_heap = h}
    | Exists e -> Exists {e with formula_exists_heap = h}
    | Or ({formula_or_f1=f1; formula_or_f2=f2} as b) ->
      Or {b with formula_or_f1=aux f1; formula_or_f2=aux f2}
  in aux f

let mkEmp_formula f = repl_heap_formula HEmp f
  (* let rec aux f = match f with *)
  (*   | Base e -> Base {e with formula_base_heap = HEmp} *)
  (*   | Exists e -> Exists {e with formula_exists_heap = HEmp} *)
  (*   | Or ({formula_or_f1=f1; formula_or_f2=f2} as b) -> *)
  (*     Or {b with formula_or_f1=aux f1; formula_or_f2=aux f2} *)
  (* in aux f *)

let mkEmp_es es =
  let emp_f = mkEmp_formula es.es_formula in
  {es with es_formula = emp_f}

let empty_es flowt grp_lbl pos =
  let x = mkTrue flowt pos in
  {
    es_formula = x;
    es_heap = HEmp;
    es_ho_vars_map = [];
    es_heap_lemma = [];
    es_conseq_pure_lemma = CP.mkTrue pos;
    (* es_history = []; *)
    es_pure = MCP.mkMTrue pos;
    es_evars = [];
    (* es_must_match = false; *)
    es_ivars = [];
    (* es_expl_vars = []; *)
    es_ante_evars = [];
    es_gen_expl_vars = [];
    es_gen_impl_vars = [];
    es_pp_subst = [];
    es_unsat_flag = true;
    es_arith_subst = [];
    es_success_pts = [];
    es_residue_pts  = [];
    es_id = 0 ;
    es_orig_ante = None;
    es_orig_conseq = mkETrue flowt pos;
    es_folding_conseq_pure = None;
    es_rhs_eqset = [];
    es_path_label  =[];
    es_cond_path  = [] ;
    es_prior_steps  = [];
    es_var_measures = None;
    (* es_infer_tnt = false; *)
    es_infer_obj = new Globals.inf_obj_sub; (* Globals.infer_const_obj # clone; *)
    es_term_res_lhs = [];
    es_term_res_rhs = None;
    es_term_call_rhs = None;
    es_infer_term_rel = [];
    es_var_stack = [];
    (*es_cache_no_list = [];*)
    es_cont = [];
    es_crt_holes = [];
    es_hole_stk = [];
    es_aux_xpure_1 = MCP.mkMTrue pos;
    es_imm_last_phase = true;
    es_subst = ([], []);
    es_exists_pure = None;
    es_aux_conseq = CP.mkTrue pos;
    (* es_imm_pure_stk = []; *)
    es_must_error = None;
    es_may_error = None;
    es_final_error = [];
    es_trace = [];
    es_proof_traces = [];
    es_is_normalizing = false;
    es_infer_post = false;
    es_infer_vars = [];
    (* es_infer_vars_done_heap = []; *)
    es_infer_vars_dead = [];
    es_infer_vars_rel = [];
    es_infer_vars_sel_hp_rel = [];
    es_infer_vars_sel_post_hp_rel = [];
    (* es_subst_ref = []; *)
    es_infer_hp_unk_map = [];
    es_infer_vars_hp_rel = [];
    es_infer_vars_templ = [];
    es_infer_heap = []; (* HTrue; *)
    es_infer_templ = [];
    es_infer_templ_assume = [];
    es_infer_pure = []; (* (CP.mkTrue no_pos); *)
    es_infer_rel = new Gen.stack_pr "es_infer_rel"  CP.print_lhs_rhs (==);
    es_infer_hp_rel = new Gen.stack_pr "es_infer_hp_rel" !print_hprel_short (==);
    es_infer_pure_thus = CP.mkTrue no_pos ;
    (* es_infer_acc = new infer_acc; *)
    es_var_zero_perm = [];
    es_group_lbl = grp_lbl;
    es_term_err = None;
    es_conc_err = [];
    es_rhs_pure = None;
    (*es_infer_invs = [];*)
  }

let flatten_context ctx0=
  let rec helper ctx =
    match ctx with
    | Ctx es -> [es]
    | OCtx (ctx1, ctx2) -> (helper ctx1)@(helper ctx2)
  in
  helper ctx0

let es_fv es=
  CP.remove_dups_svl ((fv es.es_formula)@(es.es_infer_vars_rel)@es.es_infer_vars_hp_rel@es.es_infer_vars_templ@
                      (List.fold_left (fun ls (_,p1,p2) -> ls@(CP.fv p1)@(CP.fv p2)) [] es.es_infer_rel # get_stk)@
                      (List.fold_left (fun ls hprel -> ls@(fv hprel.hprel_lhs)@(fv hprel.hprel_rhs)) [] es.es_infer_hp_rel # get_stk))

let is_one_context (c:context) =
  match c with
  | Ctx _ -> true
  | OCtx _ -> false

let is_cont t =
  match t with
  | ContinuationErr _ -> true
  | Or_Continuation _ -> true
  | _ -> false

let isFailCtx cl = match cl with
  | FailCtx _ -> true
  | SuccCtx _ -> false

let isFailCtx cl =
  Debug.no_1 "isFailCtx"
    !print_list_context_short string_of_bool isFailCtx cl

(* let combine_ctx_list_err ctxs= *)
(*   let extract_failure_kind es= *)
(*     if is_error_flow es.es_formula then *)
(*       Failure_Must, !print_formula es.es_formula *)
(*     else if is_mayerror_flow es.es_formula  then *)
(*       Failure_May, !print_formula es.es_formula *)
(*     else Valid,"Valid" *)
(*   in *)
(*   let fold_helper (m1,n1,e1) (Ctx es)= *)
(*     let m2, n2 = extract_failure_kind es in *)

(*   in *)

(* let get_must_error_from_ctx cs =  *)
(*   match cs with  *)
(*     | [Ctx es] -> (match es.es_must_error with *)
(*         | None -> None *)
(*         | Some (msg,_,cex) -> Some (msg,cex)) *)
(*     | cl -> None *)

let get_bot_status_from_ctx cs=
  match cs with
  | [Ctx es] ->
    ( match formula_is_eq_flow es.es_formula false_flow_int with
      | true -> Some ""
      | false -> None
    )
  | _ -> None

let rec set_must_error_from_one_ctx ctx msg ft cex=
  match ctx with
  | Ctx es ->
    begin
      let instance_ft=
        (
          match ft with
          | Basic_Reason (fc, fe, ft) ->
            let instance_fc = {fc with fc_current_lhs = es;
                                       fc_message = msg;
                                       fc_prior_steps = es.es_prior_steps
                              }
            in Basic_Reason (instance_fc, fe, ft)
          | _ -> report_error no_pos "Cformula.set_must_error_from_one_ctx: should be basic reason here"
        )
      in
      Ctx {es with  es_formula = substitute_flow_into_f  !error_flow_int es.es_formula;
                    es_must_error = Some (msg,instance_ft, cex)}
    end
  | OCtx (ctx1, ctx2) -> OCtx (set_must_error_from_one_ctx ctx1 msg ft cex, set_must_error_from_one_ctx ctx2 msg ft cex)

let rec set_must_error_from_ctx cs msg ft cex=
  match cs with
  | [] -> []
  | es::ls -> (set_must_error_from_one_ctx es msg ft cex):: (set_must_error_from_ctx ls msg ft cex)

(* let isFailCtx_gen cl = match cl with *)
(* 	| FailCtx _ -> true *)
(* 	| SuccCtx cs -> (get_must_error_from_ctx cs) !=None *)
(* | _ -> false *)

let convert_to_must_es es = ({es with es_formula = substitute_flow_into_f !error_flow_int es.es_formula})
let convert_to_may_es es = ({es with es_formula = substitute_flow_into_f !mayerror_flow_int es.es_formula})

let mk_failure_bot_raw msg = Failure_Bot msg

let mk_failure_must_raw msg = Failure_Must msg

let mk_failure_may_raw msg = Failure_May msg

let mk_failure_may msg name = {fe_kind = Failure_May msg;fe_name = name ;fe_locs=[]}

let mk_failure_must msg name = {fe_kind = mk_failure_must_raw msg;fe_name = name ;fe_locs=[]}

let mk_failure_bot msg name= {fe_kind = mk_failure_bot_raw msg;fe_name = name ;fe_locs=[]}

let mk_failure_valid = {fe_kind = Failure_Valid;fe_name = "Valid" ;fe_locs=[]}

let mkAnd_Reason (ft1:fail_type option) (ft2:fail_type option): fail_type option=
  match ft1, ft2 with
  | None, ft2 -> ft2
  | _ , None -> ft1
  | Some ft1, Some ft2 -> Some (And_Reason (ft1, ft2))

let mkOr_Reason ft1 ft2=
  Or_Reason (ft1, ft2)

let comb_must m1 m2 = "["^m1^","^m2^"]"

let add_error_message_fail_type (msg:string) (f:fail_type) =
  let rec helper f =
    match f with
    | Basic_Reason (fc,fe,ft) ->
      let new_fc_message = msg ^ "\n" ^ fc.fc_message in
      let nfc = {fc with fc_message = new_fc_message} in
      Basic_Reason (nfc,fe,ft)
    | _ -> f
  in helper f

let add_error_message_list_context (msg:string) (l:list_context) =
  match l with
  | FailCtx (ft,ctx, cex) ->
    let nft = add_error_message_fail_type msg ft in
    FailCtx (nft, ctx, cex)
  | _ -> l

let is_must_failure_fe (f:fail_explaining) =
  match f.fe_kind with
  | Failure_Must _ -> true
  | _ -> false

let is_may_failure_fe (f:fail_explaining) =
  match f.fe_kind with
  | Failure_May _ -> true
  | _ -> false

let is_bot_failure_fe (f:fail_explaining) =
  match f.fe_kind with
  | Failure_Bot _ -> true
  | _ -> false

let rec is_must_failure_ft (f:fail_type) =
  match f with
  | Basic_Reason (_,fe,_) -> is_must_failure_fe fe
  | Or_Reason (f1,f2) -> (((is_must_failure_ft f1) && (is_must_failure_ft f2)) ||
                          ((is_bot_failure_ft f1) && (is_must_failure_ft f2)) ||
                          ((is_must_failure_ft f1) && (is_bot_failure_ft f2)) )
  | And_Reason (f1,f2) -> (is_must_failure_ft f1) || (is_must_failure_ft f2)
  | Union_Reason (f1,f2) -> (is_must_failure_ft f1) && (is_must_failure_ft f2)
  | _ -> false

and is_may_failure_ft (f:fail_type) =
  match f with
  | Basic_Reason (_,fe,_) -> is_may_failure_fe fe
  | Or_Reason (f1,f2) -> (((is_may_failure_ft f1) || (is_may_failure_ft f2)) ||
                          ((is_bot_failure_ft f1) && (is_may_failure_ft f2)) ||
                          ((is_may_failure_ft f1) && (is_bot_failure_ft f2)) ||
                          ((is_must_failure_ft f1) && not (is_must_failure_ft f2)) ||
                          (not (is_must_failure_ft f1) && (is_must_failure_ft f2))
                         )
  | And_Reason (f1,f2) -> (is_may_failure_ft f1) || (is_may_failure_ft f2)
  | Union_Reason (f1,f2) -> (is_may_failure_ft f1) && (is_may_failure_ft f2)
  | _ -> false

and is_bot_failure_ft (f:fail_type) =
  match f with
  | Basic_Reason (_,fe,_) -> is_bot_failure_fe fe
  | Or_Reason (f1,f2) -> (is_bot_failure_ft f1) && (is_bot_failure_ft f2)
  | And_Reason (f1,f2) -> (is_bot_failure_ft f1) || (is_bot_failure_ft f2)
  | Union_Reason (f1,f2) -> (is_bot_failure_ft f1) || (is_bot_failure_ft f2)
  | _ -> false

let is_must_failure (f:list_context) =
  match f with
  | FailCtx (f,_,_) -> (is_must_failure_ft f)
  | _ -> false

let is_may_failure (f:list_context) =
  match f with
  | FailCtx (f,_,_) -> (is_may_failure_ft f)
  | _ -> false

let is_sat_failure f=
  match f with
  | FailCtx (_,_,cex) -> (is_sat_fail cex)
  | _ -> false

let is_bot_failure (f:list_context) =
  match f with
  | FailCtx (f,_,_) -> is_bot_failure_ft f
  | _ -> false

let get_must_failure_fe (f:fail_explaining) =
  match f.fe_kind with
  | Failure_Must m -> Some m
  | _ -> None

let comb_or m1 m2 = match m1,m2 with
  | Some m1, Some m2 -> Some ("or["^m1^","^m2^"]")
  | _, _ -> None

let comb_and m1 m2 = match m1,m2 with
  | Some m1, Some m2 -> Some ("and["^m1^","^m2^"]")
  | Some m1, None -> Some (m1)
  | None, Some m2 -> Some (m2)
  | _, _ -> None

let rec context_is_eq_flow (f:context) (ff)  : bool=
  match f with
  | Ctx es -> formula_is_eq_flow es.es_formula ff
  | OCtx (c1,c2) -> (context_is_eq_flow c1 ff) && (context_is_eq_flow c2 ff)

let list_context_is_eq_flow (f:list_context) (ff)  : bool=
  match f with
  | FailCtx _ -> false
  | SuccCtx ls -> if ls = [] then false else List.for_all (fun f -> context_is_eq_flow f ff) ls


(* let rec get_must_failure_ft (ft:fail_type) = *)
(*   match ft with *)
(*     | Basic_Reason (_,fe) -> get_must_failure_fe fe *)
(*     | Or_Reason (f1,f2) -> comb_or (get_must_failure_ft f1) (get_must_failure_ft f2) *)
(*     | And_Reason (f1,f2) -> comb_and (get_must_failure_ft f1) (get_must_failure_ft f2) *)
(*     | Union_Reason (f1,f2) -> comb_and (get_must_failure_ft f1) (get_must_failure_ft f2) *)
(*     | ContinuationErr _ -> None *)
(*     | Or_Continuation (f1,f2) -> comb_or (get_must_failure_ft f1) (get_must_failure_ft f2) *)
(*           (\* report_error no_pos "get_must_failure : or continuation encountered" *\) *)
(*     | _ -> None *)

let get_failure_fe (f:fail_explaining) = f.fe_kind

(*gen_land*)
let gen_land (m1,n1,e1) (m2,n2,e2) = match m1,m2 with
  | Failure_Bot _, _ -> m1, n1, e1
  (*report_error no_pos "Failure_None not expected in gen_and"*)
  | _, Failure_Bot _ -> m2, n2, e2
  (*report_error no_pos "Failure_None not expected in gen_and"*)
  | Failure_May m1, Failure_May m2 -> (Failure_May ("LAndR[\n"^m1^",\n"^m2^"\n]"),n1,None)
  | Failure_May m1, _ -> m2, n2, e2
  | _ , Failure_May m2 -> m1,n1, e1
  | Failure_Must m1, Failure_Must m2 ->
    if (n1==sl_error) then (Failure_Must m2, n2, e2)
    else if (n2==sl_error) then (Failure_Must m1, n1, e1)
    else Failure_Must ("LAndR[\n"^m1^",\n"^m2^"\n]"), n1, e1 (*combine state here?*)
  | Failure_Must m1, Failure_Valid -> Failure_May ("LAndR[\n"^m1^",\nValid\n]"), n1, None (*combine state here?*)
  | Failure_Valid, x  -> (m2, n2, e2)

(*gen_rand*)
let gen_rand_x (m1,n1,e1) (m2,n2,e2) = match m1,m2 with
  | Failure_Bot m, _ -> Failure_Bot m, n1,e1
  (*report_error no_pos "Failure_None not expected in gen_and"*)
  | _, Failure_Bot m -> Failure_Bot m, n2, e2
  (*report_error no_pos "Failure_None not expected in gen_and"*)
  | Failure_Must m1, Failure_Must m2 ->
    if (n1=sl_error) then (Failure_Must m2, n2, e2)
    else if (n2= sl_error) then (Failure_Must m1, n1, e1)
    else Failure_Must ("AndR[\n"^m1^",\n"^m2^"\n]"), n1, e1 (*combine state here?*)
  | Failure_Must m, _ -> Failure_Must m, n1, e1
  | _, Failure_Must m -> Failure_Must m, n2, e2
  | Failure_May m1, Failure_May m2 -> (Failure_May ("AndR[\n"^m1^",\n"^m2^"\n]"),n1,None)
  | Failure_May m, _ -> Failure_May m,n1,None
  | _, Failure_May m -> Failure_May m,n2,None
  | Failure_Valid, x  -> (m2,n2,e2)
(* | x, Failure_Valid -> x *)

let gen_rand (m1,n1,e1) (m2,n2,e2)=
  let pr (m, n , e) = (!print_failure_kind_full m) ^ ", name: " ^ n in
  let pr1 (m, n, e) = let tmp = (!print_failure_kind_full m) ^ ", name: " ^ n in
    match e with
    | None -> tmp
    | Some f -> tmp ^ "\n" ^ (!print_entail_state f)
  in
  Debug.no_2 "gen_rand" pr pr pr1 (fun x y -> gen_rand_x x y) (m1,n1,e1) (m2,n2,e2)

let gen_rand_ctx (m1,n1,e1) (m2,n2,e2) = match m1,m2 with
  | Failure_Bot m, _ -> Failure_Bot m, n1,e1
  (*report_error no_pos "Failure_None not expected in gen_and"*)
  | _, Failure_Bot m -> Failure_Bot m, n2, e2
  (*report_error no_pos "Failure_None not expected in gen_and"*)
  | Failure_Must m1, Failure_Must m2 ->
    if (n1=sl_error) then (Failure_Must m2, n2, e2)
    else if (n2= sl_error) then (Failure_Must m1, n1, e1)
    else Failure_Must ("AndR[\n"^m1^",\n"^m2^"]"), n1, e1 (*combine state here?*)
  | Failure_Must m, _ -> Failure_Must m, n1, e1
  | _, Failure_Must m -> Failure_Must m, n2, e2
  | Failure_May m1, Failure_May m2 -> (Failure_May ("AndR[\n"^m1^",\n"^m2^"\n]"),n1,None)
  | Failure_May m, _ -> Failure_May m,n1,None
  | _, Failure_May m -> Failure_May m,n2,None
  | Failure_Valid, x  -> (m2,n2,e2)
(* | x, Failure_Valid -> x *)

(* state to be refined to accurate one for must-bug *)
(*gen_lor*)
let gen_lor_x (m1,n1,e1) (m2,n2,e2) : (failure_kind * string * (entail_state option)) = match m1,m2 with
  | Failure_Bot m1,  Failure_Bot m2 ->  Failure_Bot ("OrL[\n"^m1^",\n"^m2^"\n]"), n1, e1 (*combine state here?*)
  (* report_error no_pos "Failure_None not expected in gen_or" *)
  | Failure_Bot _, _ ->  m2, n2,e2
  (* report_error no_pos "Failure_None not expected in gen_or" *)
  | _, Failure_Bot _ -> m1,n1,e1
  (*report_error no_pos "Failure_None not expected in gen_or"*)
  | Failure_May m1, Failure_May m2 -> Failure_May ("OrL[\n"^m1^",\n"^m2^"\n]"),n1, None
  | Failure_May m1, Failure_Must m2 -> Failure_May ("OrL[\n"^m1^",\n"^m2^"\n]"),n1, None
  | Failure_May m, _ -> Failure_May m, n1,None
  (* demo/ex21a10-case *)
  | Failure_Must m1, Failure_May m2 -> Failure_May ("OrL[\n"^m1^",\n"^m2^"\n]"),n2, None
  | _, Failure_May m -> Failure_May m,n2,None
  | Failure_Must m1, Failure_Must m2 ->
    if (n1=sl_error) then (Failure_Must m2, n2, e2)
    else if (n2= sl_error) then (Failure_Must m1, n1, e1)
    else (Failure_Must ("OrL[\n"^m1^",\n"^m2^"\n]"), n1, e1)
  | Failure_Must m, Failure_Valid -> (Failure_May ("OrL[\n"^m^",\nvalid\n]"),n1,None)
  | Failure_Valid, Failure_Must m -> (Failure_May ("OrL[\n"^m^",\nvalid\n]"),n2,None)
  (* | _, Failure_Must m -> Failure_May ("or["^m^",unknown]") *)
  (* | Failure_Must m,_ -> Failure_May ("or["^m^",unknown]") *)
  | Failure_Valid, x  -> (m2,n2,e2)
(* | x, Failure_Valid -> x *)

let gen_lor (m1,n1,e1) (m2,n2,e2)=
  let pr (m, n , e) = (!print_failure_kind_full m) ^ ", name: " ^ n in
  let pr1 (m, n, e) = let tmp = (!print_failure_kind_full m) ^ ", name: " ^ n in
    match e with
    | None -> tmp
    | Some f -> tmp ^ "\n" ^ (!print_entail_state f)
  in
  Debug.no_2 "gen_lor" pr pr pr1 (fun x y -> gen_lor_x x y) (m1,n1,e1) (m2,n2,e2)

let gen_lor_ctx (m1,n1, (e1:context option)) (m2,n2,(e2: context option)) : (failure_kind * string * (context option)) =
  let ctx = match e1,e2 with
    | Some c1, Some c2 -> Some ( OCtx (c1, c2))
    | Some _ , None -> e1
    | None, Some _ -> e2
    | _ -> None
  in
  match m1,m2 with
  | Failure_Bot m1,  Failure_Bot m2 ->  Failure_Bot ("OrL[\n"^m1^",\n"^m2^"\n]"), n1,  ctx
  | Failure_Bot _, _ ->  m2, n2, ctx
  | _, Failure_Bot _ -> m1,n1, ctx
  | Failure_May m1, Failure_May m2 -> Failure_May ("OrL[\n"^m1^",\n"^m2^"\n]"),n1,  ctx
  | Failure_May m, _ -> Failure_May m, n1,  ctx
  | _, Failure_May m -> Failure_May m,n2,  ctx
  | Failure_Must m1, Failure_Must m2 ->
    if (n1=sl_error) then (Failure_Must m2, n2, ctx)
    else if (n2= sl_error) then (Failure_Must m1, n1, ctx)
    else (Failure_Must ("OrL[\n"^m1^",\n"^m2^"\n]"), n1, ctx)
  | Failure_Must m, Failure_Valid -> (Failure_May ("OrL[\n"^m^",\nvalid\n]"),n1,  ctx)
  | Failure_Valid, Failure_Must m -> (Failure_May ("OrL[\n"^m^",\nvalid\n]"),n2,  ctx)
  | Failure_Valid, x  -> (m2,n2,  ctx)


let cmb_lor_x m1 m2: failure_kind = match m1,m2 with
  | Failure_Bot m1,  Failure_Bot m2 ->  Failure_Bot ("lor["^m1^","^m2^"]")
  | Failure_Bot _, _ ->  m2
  | _, Failure_Bot _ -> m1
  | Failure_May m1, Failure_May m2 -> Failure_May ("lor["^m1^","^m2^"]")
  | Failure_May m, _ -> Failure_May m
  | _, Failure_May m -> Failure_May m
  | Failure_Must m1, Failure_Must m2 ->
    Failure_Must ("lor["^m1^","^m2^"]")
  | Failure_Must m, Failure_Valid -> (Failure_May ("OrL["^m^",valid]"))
  | Failure_Valid, Failure_Must m -> (Failure_May ("OrL["^m^",valid]"))
  | Failure_Valid, x  -> m2

let cmb_lor m1 m2=
  let pr1 = !print_failure_kind_full in
  Debug.no_2 "cmb_lor" pr1 pr1 pr1 (fun m1 m2 -> cmb_lor_x m1 m2) m1 m2

(*gen_ror*)
(*
  - m: failure_kind (must/may/bot/valid)
  - n: name of failure (logical/separation entailment). should reduce separation entailment
  - e: current entailment
*)
let gen_ror_x (m1, n1, e1) (m2, n2, e2) = match m1,m2 with
  | Failure_Bot m1,  Failure_Bot m2 ->  Failure_Bot ("UnionR["^m1^","^m2^"]"), n1,e1 (*combine state here?*)
  | Failure_Bot _, x -> m1,n1,e1 (* (m2,e2) *)
  | x, Failure_Bot _ -> m2,n2,e2 (*(m1,e1)*)
  | Failure_Valid, _ -> (Failure_Valid,"",None)
  | _, Failure_Valid -> (Failure_Valid,"",None)
  | Failure_Must m1, Failure_Must m2 ->
    if (n1=sl_error && e2 != None) then (Failure_Must m2, n2, e2)
    else if (n2 =sl_error && e1 != None) then(Failure_Must m1, n1, e1)
    else (Failure_Must ("UnionR["^m1^","^m2^"]"),n1, e1)
  | Failure_May m1, Failure_May m2 -> (Failure_May ("UnionR["^m1^","^m2^"]"),n1,None)
  | Failure_May _,  _ -> (m1,n1,e1)
  | _, Failure_May _ -> (m2,n2,e2)

let gen_ror (m1,n1,e1) (m2,n2,e2)=
  let pr (m, n , e) = (!print_failure_kind_full m) ^ ", name: " ^ n in
  let pr1 (m, n, e) = let tmp = (!print_failure_kind_full m) ^ ", name: " ^ n in
    match e with
    | None -> tmp
    | Some f -> tmp ^ "\n" ^ (!print_entail_state f)
  in
  Debug.no_2 "gen_ror" pr pr pr1 (fun x y -> gen_ror_x x y) (m1,n1,e1) (m2,n2,e2)

let gen_ror_ctx (m1, n1, e1) (m2, n2, e2) = match m1,m2 with
  | Failure_Bot m1,  Failure_Bot m2 ->  Failure_Bot ("UnionR["^m1^","^m2^"]"), n1,e1 (*combine state here?*)
  | Failure_Bot _, x -> m1,n1,e1 (* (m2,e2) *)
  | x, Failure_Bot _ -> m2,n2,e2 (*(m1,e1)*)
  | Failure_Valid, _ -> (Failure_Valid,"",None)
  | _, Failure_Valid -> (Failure_Valid,"",None)
  | Failure_Must m1, Failure_Must m2 ->
    if (n1=sl_error && e2 != None) then (Failure_Must m2, n2, e2)
    else if (n2 =sl_error && e1 != None) then(Failure_Must m1, n1, e1)
    else (Failure_Must ("UnionR["^m1^","^m2^"]"),n1, e1)
  | Failure_May m1, Failure_May m2 -> (Failure_May ("UnionR["^m1^","^m2^"]"),n1,None)
  | Failure_May _,  _ -> (m1,n1,e1)
  | _, Failure_May _ -> (m2,n2,e2)

(* and subsume_flow_f t1 f :bool = subsume_flow t1 f.formula_flow_interval *)

let rec contains_error_flow f =  match f with
  | Base b-> subsume_flow b.formula_base_flow.formula_flow_interval !error_flow_int
  | Exists b-> subsume_flow b.formula_exists_flow.formula_flow_interval !error_flow_int
  | Or b ->  contains_error_flow b.formula_or_f1 && contains_error_flow b.formula_or_f2

let rec contains_error_flow_es e =  contains_error_flow e.es_formula

let rec contains_error_flow_ctx c =  match c with
  | Ctx es -> contains_error_flow_es es
  | OCtx (c1,c2) -> contains_error_flow_ctx c1 || contains_error_flow_ctx c2

let rec contains_error_flow_ctx_list cl =
  List.exists contains_error_flow_ctx cl

let rec is_error_flow_x f =  match f with
  | Base b-> subsume_flow_f !error_flow_int b.formula_base_flow
  | Exists b-> subsume_flow_f !error_flow_int b.formula_exists_flow
  | Or b ->  is_error_flow_x b.formula_or_f1 && is_error_flow_x b.formula_or_f2

let is_error_flow f=
  let pr1 = !print_formula in
  Debug.no_1 "is_error_flow" pr1 string_of_bool
    (fun _ -> is_error_flow_x f) f

let rec is_mayerror_flow_x f =  match f with
  | Base b-> equal_flow_interval !mayerror_flow_int  b.formula_base_flow.formula_flow_interval
  | Exists b-> equal_flow_interval !mayerror_flow_int b.formula_exists_flow.formula_flow_interval
  (* subsume_flow_f !norm_flow_int b.formula_exists_flow *)
  | Or b ->  is_mayerror_flow_x b.formula_or_f1 || is_mayerror_flow_x b.formula_or_f2

let is_mayerror_flow f=
  let pr1 = !print_formula in
  Debug.no_1 "is_mayerror_flow" pr1 string_of_bool
    (fun _ -> is_mayerror_flow_x f) f

let rec is_top_flow f =   match f with
  | Base b-> equal_flow_interval !top_flow_int b.formula_base_flow.formula_flow_interval
  | Exists b-> equal_flow_interval !top_flow_int b.formula_exists_flow.formula_flow_interval
  | Or b ->  is_top_flow b.formula_or_f1 && is_top_flow b.formula_or_f2

let get_error_flow f = flow_formula_of_formula f
let get_top_flow f = flow_formula_of_formula f

let combine_ctx_list_err ctxs=
  let extract_failure_kind es=
    if x_add_1 is_error_flow es.es_formula then
      let msg = !print_formula es.es_formula in
      Failure_Must (msg ), msg
    else if is_mayerror_flow es.es_formula  then
      let msg = !print_formula es.es_formula in
      Failure_May (msg), msg
    else Failure_Valid,"Valid"
  in
  let rec extract_failure_kind_ctx ctx=
    match ctx with
    | (Ctx es) ->  let m,n = extract_failure_kind es in
      (m,n, Some es)
    | OCtx (ctx1, ctx2) ->
      let r1 = extract_failure_kind_ctx ctx1 in
      let r2 = extract_failure_kind_ctx ctx2 in
      gen_lor r1 r2
  in
  let rec fold_helper (* (m1,n1,e1) *) acc_r ctxi=
    let ri = extract_failure_kind_ctx ctxi in
    gen_ror acc_r ri
  in
  match ctxs with
  | [] -> None
  | ctx0::rest -> begin
      let r0 = extract_failure_kind_ctx ctx0 in
      let m,n,es = List.fold_left fold_helper r0 rest in
      match m with
      | Failure_Must msg | Failure_May msg -> Some (msg, mk_cex false)
      | _ -> None
    end

let get_must_error_from_ctx cs =
  match cs with
  | [] -> (Some ("empty residual state", mk_cex false))
  | [Ctx es] -> (match es.es_must_error with
      | None ->  begin if is_en_error_exc es
      (* !Globals.enable_error_as_exc || es.es_infer_obj # is_err_must || es.es_infer_obj # is_err_may  *)
          then
            match List.rev es.es_final_error with
            | (s1, ft, fk)::_ -> Some (s1, mk_cex true)
            | [] -> None
          else None
        end
      | Some (msg,_,cex) -> Some (msg,cex))
  | cl -> combine_ctx_list_err cl

let get_may_error_from_ctx cs =
  match cs with
  | [] -> (Some ("empty residual state", mk_cex false))
  | [Ctx es] -> (match es.es_may_error with
      | None -> None
      | Some (msg,_,cex) -> Some (msg,cex))
  | cl -> combine_ctx_list_err cl

(* let get_may_error_from_ctx cs= *)
(*   let pr1 = Cprinter.string_of_list_context in *)
(*   let pr2 (msg, _) = mgs in *)
(*   Debug.no_1 "get_may_error_from_ctx" pr1 (pr_option pr2) *)
(*       (fun _ -> get_may_error_from_ctx cs) cs *)

let rec is_ctx_error ctx=
  match ctx with
  | Ctx es ->
    (*L2: determining failure is based only on es_final_error*)
    (not (es.es_final_error == [])) (* || (is_error_flow es.es_formula) *)
  (* es_formula: may be exception *)
  (* || x_add_1 is_error_flow es.es_formula || is_mayerror_flow es.es_formula *)
  | OCtx (c1, c2) -> is_ctx_error c1 || is_ctx_error c2

let isFailCtx_gen cl =
  match cl with
  | FailCtx _ -> true
  | SuccCtx cs -> if cs = [] then true else
      (* ((get_must_error_from_ctx cs) !=None) || ((get_may_error_from_ctx cs) !=None) *)
      (* L2: in case error-infer, we return both error and succ context. temporally return valid with all (einf/ex11) *)
      (* List.exists (fun ctx -> is_ctx_error ctx) cs *)
      List.for_all (fun ctx -> is_ctx_error ctx) cs

let lst_to_opt lst =
  match List.rev lst with
  | [] -> None
  | x::_ -> Some x

let rec get_final_error_ctx ctx=
  match ctx with
  | Ctx es -> lst_to_opt es.es_final_error
  | OCtx (c1, c2) -> begin
      let e1 = get_final_error_ctx c1 in
      if e1 = None then
        get_final_error_ctx c2
      else e1
    end

let get_final_error cl=
  let rec get_failure_ctx_list cs=
    match cs with
    | ctx::rest -> begin
        let r = get_final_error_ctx ctx in
        if r = None then get_failure_ctx_list rest else r
      end
    | [] -> None
  in
  match cl with
  | FailCtx (ft,_,_) -> Some (get_short_str_fail_type ft, ft, Failure_Must "??")
  | SuccCtx cs -> if cs = [] then Some ("empty states",
                                        Trivial_Reason ({fe_kind = Failure_Must  "empty states"; fe_name = "empty states"; fe_locs=[]}, []),
                                        Failure_Must "empty states") else
      (* ((get_must_error_from_ctx cs) !=None) || ((get_may_error_from_ctx cs) !=None) *)
      get_failure_ctx_list cs

let rec get_failure_es_ft_x (ft:fail_type) : (failure_kind * (entail_state option)) =
  let rec helper ft =
    match ft with
    | Basic_Reason (fc,fe,ft) ->
      (*let _= print_endline ("fe_name: " ^ fe.fe_name) in*)
      let f = get_failure_fe fe in
      if (is_must_failure_fe fe) then (f,  fe.fe_name, Some fc.fc_current_lhs)
      else if (is_may_failure_fe fe) then (f,  fe.fe_name, Some fc.fc_current_lhs)
      else (f,fe.fe_name, None)
    | Or_Reason (f1,f2) -> gen_lor (helper f1) (helper f2)
    | And_Reason (f1,f2) -> gen_rand (helper f1) (helper f2)
    | Union_Reason (f1,f2) -> gen_ror (helper f1) (helper f2)
    | ContinuationErr _ -> (Failure_May "Continuation_Err", "Continuation", None)
    | Or_Continuation (f1,f2) -> gen_lor (helper f1) (helper f2)
    (* report_error no_pos "get_must_failure : or continuation encountered" *)
    | Trivial_Reason (fe,ft) -> (fe.fe_kind, fe.fe_name, None)
  in
  let (f, _, oes) = helper ft in (f, oes)

let get_failure_es_ft (ft:fail_type) : (failure_kind * (entail_state option)) =
  let pr1 (m, e) = let tmp = (!print_failure_kind_full m) in
    match e with
    | None -> tmp
    | Some f -> tmp ^ "\n" ^ (!print_entail_state f)
  in
  Debug.no_1 "get_failure_es_ft" !print_fail_type pr1 (fun x -> get_failure_es_ft_x x) ft

let rec get_failure_ctx_ft (ft:fail_type) : (failure_kind * (context option)) =
  let rec helper ft =
    match ft with
    | Basic_Reason (fc,fe,ft) ->
      (*let _= print_endline ("fe_name: " ^ fe.fe_name) in*)
      let f = get_failure_fe fe in
      (f,  fe.fe_name, Some (Ctx fc.fc_current_lhs))
    (* if (is_must_failure_fe fe) then (f,  fe.fe_name, Some (Ctx fc.fc_current_lhs)) *)
    (* else if (is_may_failure_fe fe) then (f,  fe.fe_name, Some (Ctx fc.fc_current_lhs)) *)
    (* else (f,fe.fe_name, None) *)
    | Or_Reason (f1,f2) -> gen_lor_ctx (helper f1) (helper f2)
    | And_Reason (f1,f2) -> gen_rand_ctx (helper f1) (helper f2)
    | Union_Reason (f1,f2) -> gen_ror_ctx (helper f1) (helper f2)
    | ContinuationErr _ -> (Failure_May "Continuation_Err", "Continuation", None)
    | Or_Continuation (f1,f2) ->  gen_lor_ctx (helper f1) (helper f2)
    (* report_error no_pos "get_must_failure : or continuation encountered" *)
    | Trivial_Reason (fe,ft) -> (fe.fe_kind, fe.fe_name, None)
  in
  let (f, _, oes) = helper ft in (f, oes)


let get_failure_ft (ft:fail_type) : (failure_kind) =
  fst (get_failure_es_ft ft)

let get_must_failure_ft f =
  match (get_failure_ft f) with
  | Failure_Must m -> Some m
  | _ -> None

let get_bot_status_ft f =
  match (get_failure_ft f) with
  | Failure_Bot m -> Some m
  | _ -> None

let get_may_failure_fe (f:fail_explaining) =
  match f.fe_kind with
  | Failure_May m
  | Failure_Must m -> Some m
  | Failure_Valid -> Some "proven valid here"
  | Failure_Bot _ -> None

(* let rec get_may_failure_ft (f:fail_type) = *)
(*   match f with *)
(*     | Basic_Reason (_,fe) -> get_may_failure_fe fe *)
(*     | Or_Reason (f1,f2) -> comb_or (get_may_failure_ft f1) (get_may_failure_ft f2) *)
(*     | Union_Reason (f1,f2) -> comb_or (get_may_failure_ft f1) (get_may_failure_ft f2) *)
(*     | And_Reason (f1,f2) -> comb_and (get_may_failure_ft f1) (get_may_failure_ft f2) *)
(*     | ContinuationErr _ -> Some "ContErr detected" *)
(*           (\* report_error no_pos "get_may_failure : continuation encountered" *\) *)
(*     | Or_Continuation (f1,f2) -> comb_or (get_may_failure_ft f1) (get_may_failure_ft f2) *)
(*           (\* report_error no_pos "get_may_failure : or continuation encountered" *\) *)
(*     | Trivial_Reason s -> Some s *)

let get_may_failure_ft f =
  match (get_failure_ft f) with
  | Failure_Must m -> Some ("must:"^m)
  | Failure_May m -> Some (m)
  | Failure_Valid -> Some ("Failure_Valid")
  | Failure_Bot m -> Some ("Failure_Bot"^m)

let get_may_failure (f:list_context) =
  match f with
  | FailCtx (ft,_,cex) ->
    let m = (get_may_failure_ft ft) in
    (match m with
     | Some s -> (Some (s, cex))
     | None ->
       let () = print_flush (!print_list_context_short f)
       in report_error no_pos "Should be a may failure here")
  | SuccCtx cs -> begin
      let s_opt = get_may_error_from_ctx cs in
      match s_opt with
      | Some (s,cex) -> Some (s, cex)
      | None -> None
    end

(* returns Some es if it is a must failure *)
let rec get_must_es_from_ft ft =
  match ft with
  | Basic_Reason (fc,fe,ft) ->
    if is_must_failure_fe fe then Some fc.fc_current_lhs
    else None
  | Or_Reason (f1,f2) ->
    let r1=(get_must_es_from_ft f1) in
    let r2=(get_must_es_from_ft f2) in
    (match r1,r2 with
     | Some _,Some _ -> r1
     | _, _ -> None)
  | And_Reason (f1,f2) | Union_Reason (f1,f2) ->
    let r1=(get_must_es_from_ft f1) in
    let r2=(get_must_es_from_ft f2) in
    (match r1,r2 with
     | Some _, _ -> r1
     | None, Some _ -> r2
     | None, None -> None)
  | _ -> None

let get_must_es_msg_ft ft =
  let msg,es = get_failure_es_ft ft in
  (* let es = get_must_es_from_ft ft in *)
  (* let msg = get_must_failure_ft ft in *)
  match es,msg with
  | Some es, Failure_Must msg -> Some (es,msg)
  | None, Failure_Must msg -> Some ((empty_es ( mkTrueFlow ()) Lab2_List.unlabelled no_pos),msg) (*may be Trivial fail*)
  (*report_error no_pos "INCONSISTENCY with get_must_es_msg_ft"*)
  | _, _ -> None

let get_must_ctx_msg_ft ft =
  let msg,ctx = get_failure_ctx_ft ft in
  (* let es = get_must_es_from_ft ft in *)
  (* let msg = get_must_failure_ft ft in *)
  match ctx,msg with
  | Some ctx1, Failure_Must msg -> Some (ctx1,msg)
  | None, Failure_Must msg -> Some (Ctx (empty_es ( mkTrueFlow ()) Lab2_List.unlabelled no_pos),msg) (*may be Trivial fail*)
  (*report_error no_pos "INCONSISTENCY with get_must_es_msg_ft"*)
  | _, _ -> None

let get_must_failure_x (ft:list_context) =
  match ft with
  | FailCtx (f, _, cex) -> begin
      let m = (get_must_failure_ft f) in
      match m with
      | Some s -> Some (s, cex)
      | _ -> None
      (* (try get_must_failure_ft f *)
      (* with a ->   *)
      (*     let () = print_flush (!print_list_context_short ft) in *)
      (*     raise a) *)
    end
  | SuccCtx cs -> begin
      let s_opt = get_must_error_from_ctx cs in
      match s_opt with
      | Some (s,cex) -> Some (s, cex)
      | None -> None
    end
(* | _ -> None *)

let get_must_failure (ft:list_context)=
  let pr1 = !print_list_context in
  let pr2 = !print_cex in
  Debug.no_1 "get_must_failure" pr1 (pr_option (pr_pair pr_id pr2))
    (fun _ -> get_must_failure_x ft) ft

let get_may_es_msg_ft ft =
  let msg,es = get_failure_es_ft ft in
  (* let es = get_must_es_from_ft ft in *)
  (* let msg = get_must_failure_ft ft in *)
  match es,msg with
  | Some es, Failure_May msg -> Some (es,msg)
  | None, Failure_May msg -> Some (empty_es ( mkTrueFlow ()) Lab2_List.unlabelled no_pos,msg) (*may be Trivial fail*)
  (*report_error no_pos "INCONSISTENCY with get_must_es_msg_ft"*)
  | _, _ -> None

let get_may_ctx_msg_ft ft =
  let msg,ctx = get_failure_ctx_ft ft in
  (* let es = get_must_es_from_ft ft in *)
  (* let msg = get_must_failure_ft ft in *)
  match ctx,msg with
  | Some ctx, Failure_May msg -> Some (ctx,msg)
  | None, Failure_May msg -> Some (Ctx (empty_es ( mkTrueFlow ()) Lab2_List.unlabelled no_pos),msg) (*may be Trivial fail*)
  (*report_error no_pos "INCONSISTENCY with get_must_es_msg_ft"*)
  | _, _ -> None

(*todo: revise, pretty printer*)
let rec get_must_failure_list_partial_context (ls:list_partial_context): (string option)=
  (*may use lor to combine the list first*)
  let los= List.map get_must_failure_partial_context ls in
  (*los contains mutilpe specs??*)
  ( match (combine_helper "UNIONR\n" los "") with
    | "" -> None
    | s -> Some s
  )

and combine_helper_x op los rs=
  match los with
  | [] -> op ^ "[\n" ^ rs ^ "\n]"
  | [os] -> let tmp=
              ( match os with
                | None -> rs
                | Some s -> rs ^ s
              ) in op ^ "[\n" ^ tmp ^ "\n]"
  | os::ss ->
    (*os contains all failed of 1 path trace*)
    let tmp=
      ( match os with
        | None -> rs
        | Some s -> rs ^ s ^ ",\n" (* ^ op *)
      ) in
    combine_helper_x op ss tmp

and combine_helper op los rs=
  match los with
  | [os] -> (match os with
      | None -> ""
      | Some s -> s
    )
  | _ -> (
      combine_helper_x op los rs
    )

and get_must_failure_partial_context ((bfl:branch_fail list), (bctxl: branch_ctx list)): (string option)=
  let helper (pt, ft)=
    let os = get_must_failure_ft ft in
    match os with
    | None -> None
    | Some (s) ->  (* let spt = !print_path_trace pt in *)
      Some ((*"  path trace: " ^spt ^ "\nlocs: " ^ (!print_list_int ll) ^*) "cause: " ^s)
  in
  match bfl with
  | [] -> None
  | fl -> let los= List.map helper fl in
    ( match (combine_helper "OrR" los "") with
      | "" -> None
      | s -> Some s
    )

(*currently, we do not use lor to combine traces,
  so just call get_may_falure_list_partial_context*)
let rec get_failure_list_partial_context_x (ls:list_partial_context): (string*failure_kind*error_type list)=
  (*may use lor to combine the list first*)
  (*return failure of 1 lemma is enough*)
  if ls==[] then ("Empty list_partial_contex", Failure_May "empty lpc", [Heap])
  else
    let (los, fk, ls_ets)= split3 (List.map get_failure_partial_context [(List.hd ls)]) in
    (*los contains path traces*)
    (combine_helper "UnionR" [List.hd los] "", List.hd fk, List.concat ls_ets)

and get_failure_list_partial_context (ls:list_partial_context): (string*failure_kind*error_type list)=
  let pr1 = !print_list_partial_context in
  let pr2 (a,_,_) = a in
  Debug.no_1 "get_failure_list_partial_context" pr1 pr2
    (fun _ -> get_failure_list_partial_context_x (ls:list_partial_context)) ls

and get_failure_branch bfl=
  let helper (pt, ft)=
    (* let spt = !print_path_trace pt in *)
    let et = match ft with
      | Basic_Reason (fc,_,_) -> if string_eq fc.fc_message mem_leak then (Mem 1) else (Heap)
      | _ -> Heap
    in
    match  (get_failure_ft ft) with
    | Failure_Must m -> (Some ((*"  path trace: " ^spt (*^ "\nlocs: " ^ (!print_list_int ll)*) ^*) "  (must) cause: " ^m),  Failure_Must m, et)
    | Failure_May m -> (Some ((*"  path trace: " ^spt (*^ "\nlocs: " ^ (!print_list_int ll)*) ^*) "  (may) cause: " ^m),  Failure_May m, et)
    | Failure_Valid -> (None, Failure_Valid, et)
    | Failure_Bot m -> (Some ((*"  path trace: " ^spt^*)"  unreachable: "^m), Failure_Bot m, et)
  in
  match bfl with
  | [] -> (None, Failure_Valid,[])
  | fl -> let los, fks, ets= split3 (List.map helper fl) in
    ( match (combine_helper "OrL" los "") with
      | "" -> None, Failure_Valid, []
      | s -> Some s, List.fold_left cmb_lor (List.hd fks) (List.tl fks), ets
    )

and get_failure_partial_context_x ((bfl:branch_fail list), succs): (string option*failure_kind*error_type list)=
  let ((s_opt, ft, e) as r) = get_failure_branch bfl in
  if !bug_detect then r else
    match s_opt with
    | None -> r
    | Some s -> begin
        match ft with
        | Failure_Must s1 -> if succs = [] then r else
            (Some ("(may) cause: [" ^s^",valid]"), Failure_May ("[" ^ s1^",valid]" ), e)
        |  _ -> r
      end

and get_failure_partial_context a: (string option*failure_kind*error_type list)=
  let pr1 = !print_partial_context in
  let pr2 (a,_,_) = match a  with | None -> "" | Some s -> s in
  Debug.no_1 "get_failure_partial_context" pr1 ( pr2)
    (fun _ -> get_failure_partial_context_x a) a

let rec get_failure_list_failesc_context (ls:list_failesc_context): (string* failure_kind*error_type list)=
  (*may use rand to combine the list first*)
  if ls==[] then ("Empty list_failesc_context", Failure_Must "empty loc",[])
  else
    let los, fks, ets= split3 (List.map get_failure_failesc_context ls(* [(List.hd ls)] *)) in
    (*los contains path traces*)
    (*combine_helper "UNION\n" los ""*)
    (*return failure of 1 lemma is enough*)
    (combine_helper "UNIONR\n" [(List.hd los)] "", List.hd fks, List.concat ets)

and get_failure_list_failesc_context_ext (rs:list_failesc_context): (string* failure_kind*error_type list)=
  let rs1 = if !Globals.enable_error_as_exc && Globals.global_efa_exc () then
      (* convert brs with error flow -> Fail *)
      List.fold_left (fun acc (fs, esc, brs) ->
          let ex_fs, rest = List.fold_left (fun (acc_fs, acc_rest) ((lbl,c, oft) as br) ->
              match oft with
              | Some ft -> (acc_fs@[(lbl, ft)], acc_rest)
              | None -> (acc_fs, acc_rest@[br])
            ) ([],[]) brs in
          acc@[(fs@ex_fs, esc,rest)]
        ) [] rs
    else rs in
  get_failure_list_failesc_context rs1

and get_failure_failesc_context ((bfl:branch_fail list), _, _): (string option*failure_kind*error_type list)=
  get_failure_branch bfl

let get_bot_status (ft:list_context) =
  match ft with
  | FailCtx (f, _,_ ) -> get_bot_status_ft f
  | SuccCtx cs -> get_bot_status_from_ctx cs

let extract_failure_msg rs=
  if not !Globals.disable_failure_explaining then
    match get_must_failure rs with
    | Some (s,cex) -> let _,ns = cmb_fail_msg ("(must) cause:"^s) cex in ns
    | _ -> (match get_may_failure rs with
        | Some (s,cex) -> let _,ns = cmb_fail_msg ("(may) cause:"^s) cex in ns
        | None -> "INCONSISTENCY : expected failure but success instead"
      )
  else ""

let is_may_failure_fe (f:fail_explaining) = (get_may_failure_fe f) != None

let rec is_may_failure_ft (f:fail_type) = (get_may_failure_ft f) != None

let is_may_failure (f:list_context) =
  let m = (get_may_failure f) in
  match m with
  | Some (_, cex) -> is_sat_fail cex
  | _ -> false

let is_bot_status (f:list_context) = (get_bot_status f) != None

let convert_must_failure_4_fail_type  (s:string) (ft:fail_type) cex : context option =
  match (get_must_es_msg_ft ft) with
  | Some (es,msg) -> Some (Ctx {es with es_must_error = Some (s^msg,ft,cex) } )
  | _ -> None

let convert_may_failure_4_fail_type  (s:string) (ft:fail_type) cex : context option =
  match (get_may_es_msg_ft ft) with
  | Some (es,msg) -> Some (Ctx {es with es_may_error = Some (s^msg,ft,cex) } )
  | _ -> None

let add_err_to_estate err es =
  {es with es_final_error = err::es.es_final_error}

let add_err_to_estate err es =
  let pr1 (m,_,_) = m in
  let pr2 e = (pr_list_brk "[" "]" pr1) e.es_final_error in
  Debug.no_2 "add_err_to_estate" pr1 pr2 pr2 add_err_to_estate err es

let repl_msg_final_error msg es =
  match (List.rev es.es_final_error) with
  | (s,_,_)::_ -> msg^";\n"^s
  | [] -> msg

let repl_msg_final_error msg es =
  let pr1 (m,_,_) = m in
  let pr2 e = (pr_list_brk "[" "]" pr1) e.es_final_error in
  Debug.no_2 "repl_msg_final_error" pr_id pr2 pr_id repl_msg_final_error msg es

let add_opt_to_estate err es =
  match err with
  | None -> es
  | Some e -> add_err_to_estate e es

let convert_must_failure_4_fail_type_new  (s:string) (ft:fail_type) cex : context option =
  let rec update_err ctx ((s1,ft,fk) as err) = match ctx with
    | Ctx es -> Ctx (x_add add_err_to_estate err es)
    | OCtx (es1, es2) -> OCtx (update_err es1 err, update_err es2 err)
  in
  match (get_must_ctx_msg_ft ft) with
  | Some (ctx, msg) -> Some (update_err ctx (s^msg, ft, Failure_Must msg))
  | _ -> None

let convert_must_failure_4_fail_type_new (s:string) (ft:fail_type) cex : context option =
  let pr = pr_option !print_context_short in
  Debug.no_2 "convert_must_failure_4_fail_type_new" pr_id !print_fail_type pr
    (fun _ _ -> convert_must_failure_4_fail_type_new s ft cex) s ft

let convert_may_failure_4_fail_type_new_x  (s:string) (ft:fail_type) cex : context option =
  let rec update_err ctx ((s1,ft,fk) as err) = match ctx with
    | Ctx es -> Ctx (x_add add_err_to_estate err es)
    | OCtx (es1, es2) -> OCtx (update_err es1 err, update_err es2 err)
  in
  match (get_may_ctx_msg_ft ft)with
  | Some (ctx, msg) -> Some (update_err ctx (s^msg,ft,  Failure_May msg))
  | _ -> None

let convert_may_failure_4_fail_type_new (s:string) (ft:fail_type) cex : context option =
  let pr = pr_option !print_context_short in
  Debug.no_2 "convert_may_failure_4_fail_type_new" pr_id !print_fail_type pr
    (fun _ _ -> convert_may_failure_4_fail_type_new_x s ft cex) s ft


(* TRUNG WHY: purpose when converting a list_context from FailCtx type to SuccCtx type? *)
let convert_maymust_failure_to_value_orig_a_x ?(mark=true) (l:list_context) : list_context =
  match l with
  | FailCtx (ft, c, cex) -> (* Loc: to check cex here*)
    (* if (\* not (is_en_error_exc_ctx c) *\) *)
    (*   not !Globals.enable_error_as_exc && not (is_en_error_exc_ctx c) *)
    (* then l *)
    (* else *)
    (* (match (get_must_es_msg_ft ft) with *)
    (*   | Some (es,msg) -> SuccCtx [Ctx {es with es_must_error = Some (msg,ft) } ]  *)
    (*   | _ ->  l) *)
    begin
      let () = Debug.ninfo_hprint (add_str "c" !print_context_short) c no_pos in
      (* should combined FailCtx \/ ValidCtx. demo/ex22-lor *)
      (* match get_final_error_ctx c with *)
      (*   | Some _ -> SuccCtx [c] *)
      (*   | None -> *) (
        match (x_add convert_must_failure_4_fail_type_new "" ft cex) with
        | Some ctx -> SuccCtx [ctx]
        | None -> begin
            match (x_add convert_may_failure_4_fail_type_new "" ft cex) with
            | Some ctx -> SuccCtx [ctx]
            | None -> l
          end
      )
    end
  | SuccCtx _ -> l

let convert_maymust_failure_to_value_orig_a ?(mark=true) (l:list_context) : list_context =
  let pr = !print_list_context_short in
  Debug.no_2 "convert_maymust_failure_to_value_orig_a" string_of_bool pr pr
    (fun _ _ -> convert_maymust_failure_to_value_orig_a_x ~mark:mark l) mark l

let convert_maymust_failure_to_value_orig ?(mark=true) (l:list_context) : list_context =
  match l with
  | FailCtx (ft, c, cex) ->
    if not (is_en_error_exc_ctx c) && not (is_err_must_exc_ctx c)
    (* not !Globals.enable_error_as_exc && not (is_en_error_exc_ctx c) *)
    then
      l
    else
    if mark then
      let r = convert_maymust_failure_to_value_orig_a l in
      match r with
      | SuccCtx [cc] -> FailCtx (ft, cc, { cex with cex_processed_mark=true})
      | _ -> r
    else
    if cex.cex_processed_mark (* already processed *)
    then SuccCtx [c]
    else convert_maymust_failure_to_value_orig_a l

  | _ -> l


let convert_maymust_failure_to_value_orig ?(mark=true) (l:list_context) : list_context =
  let pr = !print_list_context_short in
  Debug.no_2 "convert_maymust_failure_to_value_orig" string_of_bool pr pr
    (fun _ _ -> convert_maymust_failure_to_value_orig ~mark:mark l) mark l

(* let add_must_err (s:string) (fme:branch_ctx list) (e:esc_stack) : esc_stack = *)
(*   ((-1,"Must Err @"^s),fme) :: e *)

let add_must_err_to_pc (s:string) (fme:branch_ctx list) (e:branch_ctx list) : branch_ctx list =
  fme @ e

let convert_must_failure_4_branch_type  (s:string) ((pt,ft):branch_fail) : branch_ctx option =
  (* Loc: to implement cex for hip. cex should be got from branch_fail *)
  let cex = mk_cex true in
  match (convert_must_failure_4_fail_type s ft cex) with
  | Some b -> Some (pt,b, Some ft)
  | None -> None

let convert_must_failure_4_branch_fail_list  (s:string) (fl:branch_fail list) : (branch_ctx list * branch_fail list) =
  List.fold_left (fun (must_l,may_l) bf ->
      match (convert_must_failure_4_branch_type s bf) with
      | Some r -> (r::must_l, may_l)
      | None -> (must_l, bf::may_l)) ([],[]) fl

let convert_must_failure_4_failesc_context (s:string) ((fl,e,bl):failesc_context) : failesc_context =
  let (fme,fl) = convert_must_failure_4_branch_fail_list s fl in
  (fl,e,add_must_err_to_pc s fme bl)

let convert_must_failure_4_list_failesc_context (s:string) (l:list_failesc_context) : list_failesc_context =
  List.map (convert_must_failure_4_failesc_context s) l

let convert_must_failure_4_list_failesc_context (s:string) (l:list_failesc_context) : list_failesc_context =
  let pr = !print_list_failesc_context in
  Debug.no_1 "convert_must_failure_4_list_failesc_context" pr pr
    (fun _ -> convert_must_failure_4_list_failesc_context s l) l

let fold_context (f:'t -> entail_state -> 't) (a:'t) (c:context) : 't =
  let rec helper a c = match c with
    | Ctx es -> f a es
    | OCtx (c1,c2) -> helper (helper a c1) c2 in
  helper a c


let map_context (f:entail_state -> entail_state) (c:context) : context =
  let rec aux c = match c with
    | Ctx es -> Ctx (f es)
    | OCtx (c1,c2) -> OCtx (aux c1, aux c2) in
  aux c

let consistent_entail_state (es:entail_state) : bool = consistent_formula es.es_formula

let consistent_context (c:context) : bool =
  fold_context (fun a es -> (consistent_entail_state es) && a) true c

let must_consistent_context (s:string) l : unit =
  if !consistency_checking then
    let b = consistent_context l in
    if b then print_endline_quiet ("\nSuccessfully Tested Consistency at "^s)
    else report_error no_pos ("ERROR at "^s^": context inconsistent")

let must_consistent_context (s:string) l : unit =
  Gen.Profiling.do_1 "must_consistent_context"
    (must_consistent_context s) l

let consistent_branch_ctx ((_,c,_):branch_ctx) : bool = consistent_context c

let consistent_esc_stack (ls:esc_stack) : bool =
  List.for_all (fun (_,b_ls) -> List.for_all consistent_branch_ctx b_ls) ls

let consistent_failesc_context ((_,es,b_ls):failesc_context) : bool =
  let b1 = List.for_all (consistent_branch_ctx) b_ls in
  let b2 = consistent_esc_stack es in
  b1 && b2

let consistent_list_failesc_context (l:list_failesc_context) : bool =
  List.for_all (consistent_failesc_context) l

let must_consistent_list_failesc_context (s:string) l : unit =
  if !consistency_checking then
    let b = consistent_list_failesc_context l in
    if b then print_endline_quiet ("\nSuccessfully Tested Consistency at "^s)
    else report_error no_pos ("ERROR: "^s^" list_failesc context inconsistent")

(*let isStrictFalseCtx ctx = match ctx with
  | Ctx es -> isStrictConstFalse es.es_formula
  | _ -> false*)

let isAnyFalseCtx (ctx:context) : bool =
  let rec helper ctx =
    match ctx with
    | Ctx es -> isAnyConstFalse es.es_formula
    | OCtx (ctx1,ctx2) ->
      (helper ctx1) && (helper ctx2)
  in helper ctx


let get_estate_from_ctx (ctx:context) =
  let rec helper ctx =
    match ctx with
    | Ctx es -> es
    | OCtx (ctx1,ctx2) -> (helper ctx1)
  in helper ctx


(* let isAnyFalseBranchCtx (ctx:branch_ctx) : bool = match ctx with *)
(*   | _,Ctx es -> isAnyConstFalse es.es_formula *)
(*   | _ -> false *)

let isAnyFalsePartialCtx (fc,sc) = (fc=[]) &&
                                   List.for_all (fun (_,s) -> isAnyFalseCtx s) sc

let isAnyFalseFailescCtx (fc,ec,sc) = (fc=[]) &&
                                      List.for_all (fun ((_,s,_):branch_ctx) -> isAnyFalseCtx s) sc

let isAnyFalseListCtx ctx = match ctx with
  | SuccCtx lc ->List.exists isAnyFalseCtx lc
  | FailCtx _ -> false

let isStrictTrueCtx ctx = match ctx with
  | Ctx es -> isStrictConstTrue es.es_formula
  | _ -> false

let isAnyTrueCtx ctx = match ctx with
  | Ctx es -> isAnyConstTrue es.es_formula
  | _ -> false

let rec allFalseCtx ctx = match ctx with
  | Ctx es -> isAnyFalseCtx ctx
  | OCtx (c1,c2) -> (allFalseCtx c1) && (allFalseCtx c2)

let isFalseBranchCtxL (ss:branch_ctx list) =
  (ss!=[]) && (List.for_all (fun (_,c,_) -> isAnyFalseCtx c) ss )

let is_inferred_pre estate =
  not(estate.es_infer_heap==[] && estate.es_infer_pure==[] &&
      estate.es_infer_rel # is_empty_recent
        && estate.es_infer_hp_rel # is_empty
     )
(* let r = (List.length (estate.es_infer_heap))+(List.length (estate.es_infer_pure)) in *)
(* if r>0 then true else false *)

let rec is_inferred_pre_ctx ctx =
  match ctx with
  | Ctx estate -> is_inferred_pre estate
  | OCtx (ctx1, ctx2) -> (is_inferred_pre_ctx ctx1) || (is_inferred_pre_ctx ctx2)

let is_inferred_pre_ctx ctx =
  let pr = !print_context in
  let pr2 = string_of_bool in
  Debug.no_1 "is_inferred_pre_ctx" pr pr2 is_inferred_pre_ctx ctx

let remove_dupl_false (sl:branch_ctx list) =
  let (fl,nl) = (List.partition (fun (_,oc,_) ->
      (isAnyFalseCtx oc && not(x_add_1 is_inferred_pre_ctx oc)) ) sl) in
  let pr = pr_list (fun (_,oc,_) -> !print_context_short oc) in
  if not(fl==[]) && not(nl==[]) then
    x_binfo_hp (add_str "false ctx removed" pr) fl no_pos;
  if nl==[] then
    if (fl==[]) then []
    else [List.hd(fl)]
  else nl

let remove_dupl_false (sl:branch_ctx list) =
  let pr n = string_of_int(List.length n) in
  let pr l = pr_list !print_context (List.map (fun (_,c,_) -> c) l) in
  Debug.no_1 "remove_dupl_false" pr pr remove_dupl_false sl

let remove_dupl_false_context_list (sl:context list) =
  let nl = (List.filter (fun oc -> not (isAnyFalseCtx oc) ) sl) in
  if nl==[] then
    if (sl==[]) then []
    else [List.hd(sl)]
  else nl

let remove_dupl_false_pc (fl,sl) = (fl,remove_dupl_false sl)

let remove_dupl_false_fe (fl,ec,sl) = (fl,ec,remove_dupl_false sl)

let count_sat_pc_list (fs_list:list_partial_context) =
  (* let ns = List.filter (fun (fl,sl) -> not(fl==[] && isFalseBranchCtxL sl)) fs_list in *)
  let cnt_list = List.map (fun (a,b)->(List.length a)+(List.length b)) fs_list in
  List.fold_left (+) 0 cnt_list

let remove_dupl_false_pc_list (fs_list:list_partial_context) =
  let ns = List.filter (fun (fl,sl) -> not(fl==[] && isFalseBranchCtxL sl)) fs_list in
  if ns==[] then [List.hd fs_list]
  else ns

let remove_dupl_false_fe_list (fs_list:list_failesc_context) =
  let ns = List.filter (fun (fl,_,sl) -> not(fl==[] && isFalseBranchCtxL sl)) fs_list in
  if ns==[] then [List.hd fs_list]
  else ns

let rec collect_term_err ctx =
  match ctx with
  | Ctx estate ->
    (match estate.es_term_err with
     | None -> []
     | Some msg -> [msg])
  | OCtx (ctx1, ctx2) -> (collect_term_err ctx1) @ (collect_term_err ctx2)

let collect_term_err_list_partial_context (ctx:list_partial_context) =
  let r = List.map (fun (_,cl) -> List.concat (List.map (fun (_,c,_) ->
      collect_term_err c) cl)) ctx in
  List.concat r

let collect_term_err_list_partial_context (ctx:list_partial_context) =
  Debug.no_1 "collect_term_err_list_partial_context"
    !print_list_partial_context (pr_list (fun x -> x))
    collect_term_err_list_partial_context ctx

let rec collect_conc_err ctx =
  match ctx with
  | Ctx estate -> estate.es_conc_err
  | OCtx (ctx1, ctx2) -> (collect_conc_err ctx1) @ (collect_conc_err ctx2)

let collect_conc_err_list_partial_context (ctx:list_partial_context) =
  let r = List.map (fun (_,cl) -> List.concat (List.map (fun (_,c,_) ->
      collect_conc_err c) cl)) ctx in
  List.concat r

let rec collect_pre_pure ctx =
  match ctx with
  | Ctx estate -> estate.es_infer_pure
  | OCtx (ctx1, ctx2) -> (collect_pre_pure ctx1) @ (collect_pre_pure ctx2)

let rec collect_pre_ho_vars ctx =
  match ctx with
  | Ctx estate -> estate.es_ho_vars_map
  | OCtx (ctx1, ctx2) -> (collect_pre_ho_vars ctx1) @ (collect_pre_ho_vars ctx2)

let rec collect_pre_heap ctx =
  match ctx with
  | Ctx estate -> estate.es_infer_heap
  | OCtx (ctx1, ctx2) -> (collect_pre_heap ctx1) @ (collect_pre_heap ctx2)

let rec collect_templ ctx =
  match ctx with
  | Ctx estate -> estate.es_infer_templ
  | OCtx (ctx1, ctx2) -> (collect_templ ctx1) @ (collect_templ ctx2)

let rec collect_templ_assume_ctx ctx =
  match ctx with
  | Ctx estate -> estate.es_infer_templ_assume
  | OCtx (ctx1, ctx2) -> (collect_templ_assume_ctx ctx1) @ (collect_templ_assume_ctx ctx2)

let rec collect_tr_rel ctx =
  match ctx with
  | Ctx es -> (match es.es_term_res_rhs with
      | None -> []
      | Some tann -> [(es.es_formula, es.es_term_res_lhs, tann)])
  | OCtx (ctx1, ctx2) -> (collect_tr_rel ctx1) @ (collect_tr_rel ctx2)

let rec collect_tu_rel ctx =
  match ctx with
  | Ctx es -> (match es.es_term_call_rhs with
      | None -> []
      | Some tann -> [(es.es_formula, es.es_var_measures, tann)])
  | OCtx (ctx1, ctx2) -> (collect_tu_rel ctx1) @ (collect_tu_rel ctx2)

let rec collect_rel ctx =
  match ctx with
  | Ctx estate -> estate.es_infer_rel # get_stk_recent
  | OCtx (ctx1, ctx2) -> (collect_rel ctx1) @ (collect_rel ctx2)

let rec collect_hole ctx =
  match ctx with
  | Ctx estate -> estate.es_crt_holes
  | OCtx (ctx1, ctx2) -> (collect_hole ctx1) @ (collect_hole ctx2)

let rec collect_hp_rel ctx =
  match ctx with
  | Ctx estate -> estate.es_infer_hp_rel # get_stk(* _recent *)
  | OCtx (ctx1, ctx2) -> (collect_hp_rel ctx1) @ (collect_hp_rel ctx2)

let collect_hp_rel ctx =
  let rs = collect_hp_rel ctx in
  Gen.Basic.remove_dups rs

let collect_hp_rel_all ctx = match ctx with
  | SuccCtx lst -> List.map collect_hp_rel lst
  | _ -> []

let rec collect_hp_unk_map ctx =
  match ctx with
  | Ctx estate -> estate.es_infer_hp_unk_map
  | OCtx (ctx1, ctx2) -> (collect_hp_unk_map ctx1) @ (collect_hp_unk_map ctx2)

let rec update_hp_unk_map ctx0 unk_map =
  let rec helper ctx=
    match ctx with
    | Ctx estate -> Ctx {estate with
                         es_infer_hp_unk_map = estate.es_infer_hp_unk_map@ unk_map;
                        }
    | OCtx (ctx1, ctx2) -> OCtx ((helper ctx1),(helper ctx2))
  in
  helper ctx0

let rec collect_infer_vars_rel ctx =
  match ctx with
  | Ctx estate -> estate.es_infer_vars_rel
  | OCtx (ctx1, ctx2) -> (collect_infer_vars_rel ctx1) @ (collect_infer_vars_rel ctx2)

let rec collect_infer_vars ctx =
  match ctx with
  | Ctx estate -> estate.es_infer_vars
  | OCtx (ctx1, ctx2) -> (collect_infer_vars ctx1) @ (collect_infer_vars ctx2)

let rec collect_infer_post ctx =
  match ctx with
  | Ctx estate -> estate.es_infer_post
  | OCtx (ctx1, ctx2) -> (collect_infer_post ctx1) || (collect_infer_post ctx2)

let rec collect_formula ctx =
  match ctx with
  | Ctx estate -> [estate.es_formula]
  | OCtx (ctx1, ctx2) -> (collect_formula ctx1) @ (collect_formula ctx2)

let rec collect_orig_ante ctx =
  match ctx with
  | Ctx estate ->
    (match estate.es_orig_ante with
     | None -> []
     | Some ante -> [ante])
  | OCtx (ctx1, ctx2) -> (collect_orig_ante ctx1) @ (collect_orig_ante ctx2)

let rec collect_term_ann_context ctx =
  match ctx with
  | Ctx es -> (match es.es_var_measures with
      | None -> []
      | Some (t_ann, _, _) -> [t_ann])
  | OCtx (ctx1, ctx2) -> (collect_term_ann_context ctx1) @ (collect_term_ann_context ctx2)

let collect_term_ann_list_context ctx =
  match ctx with
  | FailCtx _ -> []
  | SuccCtx l_ctx ->
    List.concat (List.map (fun ctx -> collect_term_ann_context ctx) l_ctx)

let rec collect_term_err_msg_context ctx =
  match ctx with
  | Ctx es -> es.es_var_stack
  | OCtx (ctx1, ctx2) ->
    (collect_term_err_msg_context ctx1) @
    (collect_term_err_msg_context ctx2)

(* let collect_term_err_msg_list_context ctx = *)
(*   match ctx with *)
(*   | FailCtx _ -> [] *)
(*   | SuccCtx l_ctx -> *)
(*       List.concat (List.map (fun ctx -> collect_term_err_msg_context ctx) l_ctx) *)

let collect_term_ann_and_msg_list_context ctx =
  match ctx with
  | FailCtx _ -> []
  | SuccCtx l_ctx -> (List.map (fun ctx ->
      (List.exists (fun a -> match a with Fail _ -> true | _ -> false) (collect_term_ann_context ctx),
       (String.concat "\n" (collect_term_err_msg_context ctx)))) l_ctx)

(* Termination: The term_measures of an OR context
 * should only be collected once *)
let rec collect_term_measures_context ctx =
  match ctx with
  | Ctx es -> (match es.es_var_measures with
      | None -> []
      | Some (_, ml, _) -> [ml])
  | OCtx (ctx1, ctx2) ->
    let m1 = collect_term_measures_context ctx1 in
    if not (is_empty m1) then m1
    else collect_term_measures_context ctx2

let collect_term_measures_branch_ctx_list br_ctx_l =
  List.concat (List.map (fun (_, ctx) ->
      collect_term_measures_context ctx) br_ctx_l)

let collect_term_measures_list_partial_context p_ctx_l =
  List.concat (List.map (fun (_, br_ctx_l) ->
      collect_term_measures_branch_ctx_list br_ctx_l) p_ctx_l)

let rec add_pre_heap ctx =
  match ctx with
  | Ctx estate -> estate.es_infer_heap
  | OCtx (ctx1, ctx2) -> (collect_pre_heap ctx1) @ (collect_pre_heap ctx2)


let add_infer_pure_thus_estate cp es =
  let flag = true (* es.es_infer_acc # add_pure cp *) in
  if flag then
    {es with es_infer_pure_thus = CP.mkAnd es.es_infer_pure_thus cp no_pos;
    }
  else failwith (x_loc^"add_infer_pure_thus_estate")

let add_infer_rel_to_estate cp es =
  let new_cp = es.es_infer_rel # clone in
  let () = new_cp # push_list cp in
  {es with es_infer_rel = new_cp;}

let add_infer_rel_to_estate cp es =
  let pr = pr_list CP.print_lhs_rhs in
  let pr2 es = pr es.es_infer_rel # get_stk in
  Debug.no_1 "add_infer_rel_to_estate" pr pr2
    (fun _ -> add_infer_rel_to_estate cp es) cp

let add_infer_pure_to_estate cp es =
  let cp = List.filter (fun f -> not(CP.isConstTrue f)) cp in
  let old_cp = es.es_infer_pure in
  let new_cp = List.concat (List.map CP.split_conjunctions cp) in
  let new_cp = List.fold_left (fun a n ->
      (* let n = CP.norm_form n in *)
      let n =  CP.arith_simplify_new n in
      if List.exists (CP.equalFormula_f CP.eq_spec_var n) a then a else n::a) old_cp new_cp in
  let () = Debug.ninfo_hprint (add_str "cp" (pr_list !print_pure_f)) cp no_pos in
  let () = Debug.ninfo_hprint (add_str "es_infer_pure" (pr_list !print_pure_f)) new_cp no_pos in
  let flag = true (* es.es_infer_acc # add_pure_list cp *) in
  if flag then
    {es with es_infer_pure = new_cp;
             (* add inferred pre to pure_this too *)
             es_infer_pure_thus = CP.mkAnd es.es_infer_pure_thus (CP.join_conjunctions new_cp) no_pos;
    }
  else failwith (x_loc^"add_infer_pure_estate")

let add_infer_rel_to_ctx cp ctx =
  let rec helper ctx =
    match ctx with
    | Ctx es -> Ctx (x_add add_infer_rel_to_estate cp es)
    | OCtx (ctx1, ctx2) -> OCtx (helper ctx1, helper ctx2)
  in helper ctx

let add_infer_rel_to_ctx cp ctx =
  let pr0 = pr_list CP.print_lhs_rhs in
  let pr = !print_context in
  Debug.no_1 "add_infer_rel_to_ctx" pr0 pr (fun _ -> add_infer_rel_to_ctx cp ctx) cp

let add_infer_pure_to_ctx cp ctx =
  let rec helper ctx =
    match ctx with
    | Ctx es -> Ctx (add_infer_pure_to_estate cp es)
    | OCtx (ctx1, ctx2) -> OCtx (helper ctx1, helper ctx2)
  in helper ctx

let add_infer_pure_to_ctx cp ctx =
  Debug.no_1 "add_infer_pure_to_ctx"
    (pr_list !print_pure_f) pr_no
    (fun _ -> add_infer_pure_to_ctx cp ctx) cp

let add_infer_heap_to_ctx cp ctx =
  let rec helper ctx =
    match ctx with
    | Ctx es ->
      let new_cp = List.filter (fun c -> not (Gen.BList.mem_eq (*CP.equalFormula*) (=) c es.es_infer_heap)) cp in
      Ctx {es with es_infer_heap = new_cp@es.es_infer_heap;}
    | OCtx (ctx1, ctx2) -> OCtx (helper ctx1, helper ctx2)
  in helper ctx

let add_infer_pure_to_list_context cp (l : list_context) : list_context  =
  match l with
  | FailCtx _-> l
  | SuccCtx sc -> SuccCtx (List.map (x_add add_infer_pure_to_ctx cp) sc)

let add_infer_pure_to_list_context cp (l : list_context) : list_context  =
  let pr = !print_list_context_short in
  Debug.no_2 "add_infer_pure_to_list_context"
    (pr_list !print_pure_f) pr pr
    add_infer_pure_to_list_context cp l

let add_infer_heap_to_list_context cp (l : list_context) : list_context  =
  match l with
  | FailCtx _-> l
  | SuccCtx sc -> SuccCtx (List.map (add_infer_heap_to_ctx cp) sc)

let add_infer_rel_to_list_context cp (l : list_context) : list_context  =
  match l with
  | FailCtx _-> l
  | SuccCtx sc -> SuccCtx (List.map (x_add add_infer_rel_to_ctx cp) sc)

let add_infer_rel_to_list_context cp (l : list_context) : list_context  =
  let pr = !print_list_context in
  Debug.no_1 "add_infer_rel_to_list_context" pr pr (add_infer_rel_to_list_context cp) l

(* f_ctx denotes false context *)
let add_infer_pre f_ctx ctx =
  let ch = collect_pre_heap f_ctx in
  if (ch!=[]) then
    if(!Globals.pa) then add_infer_heap_to_ctx ch ctx
    else
      let () = print_endline_quiet "ERROR : non-pure heap inferred for false" in
      report_error no_pos ("add_infer_pre: non-pure inferred heap :"^(!print_context f_ctx))
  else
    let cp = collect_pre_pure f_ctx in
    if (cp!=[]) then x_add add_infer_pure_to_ctx cp ctx
    else
      let cr = collect_rel f_ctx in
      if (cr!=[]) then x_add add_infer_rel_to_ctx cr ctx
      else ctx

let add_infer_pre f_ctx ctx =
  let pr = !print_context in
  Debug.no_2 "add_infer_pre" pr pr pr add_infer_pre f_ctx ctx

let map_ctx (ctx: context) f_es: context =
  let rec helper ctx =
    match ctx with
    | Ctx es -> let es = f_es es in Ctx es
    | OCtx (es1,es2) -> OCtx (helper es1, helper es2)
  in helper ctx

let map_branch_ctx_list (ctx_lst: branch_ctx list) f_es: branch_ctx list =
  List.map ( fun (pt, ctx0, ft) ->
      let ctx0 = map_ctx ctx0 f_es in
      (pt,ctx0,ft)
    ) ctx_lst

let map_list_partial_context (ctx: list_partial_context) f_es =
  List.map (fun (lst1, lst2) ->
      let lst2 = map_branch_ctx_list lst2 f_es in
      (lst1,lst2)
    ) ctx

let choose_add_pre ctx1 ctx2 =
  (* if !Globals.temp_opt_flag2 then ctx2 *)
  (* else *) x_add add_infer_pre ctx1 ctx2

(* WN : we need to add infer_pre of false context *)
(* infer/ex/4.slk requires it *)
let mkOCtx ctx1 ctx2 pos =
  (*if (isFailCtx ctx1) || (isFailCtx ctx2) then or_fail_ctx ctx1 ctx2
    else*)  (* if isStrictTrueCtx ctx1 || isStrictTrueCtx ctx2 then *)
  (* true_ctx (mkTrueFlow ()) pos *)  (* not much point in checking
                                         for true *)
  (* else *)
  if isAnyFalseCtx ctx1 then choose_add_pre ctx1 ctx2
  else if isAnyFalseCtx ctx2 then choose_add_pre ctx2 ctx1
  else OCtx (ctx1,ctx2)

let or_context c1 c2 =
  if c1==c2 then c1
  else mkOCtx c1 c2 no_pos

let failesc_context_simplify ((l,a,cs) : failesc_context) : failesc_context =  (l,a,remove_dupl_false cs)

let failesc_context_simplify (ctx: failesc_context) : failesc_context =
  let pr = !print_failesc_context in
  Debug.no_1 "failesc_context_simplify" pr pr
    failesc_context_simplify ctx

let list_failesc_context_simplify (l : list_failesc_context) : list_failesc_context =
  List.map failesc_context_simplify l

let list_failesc_context_simplify (l : list_failesc_context) : list_failesc_context =
  let pr = !print_list_failesc_context in
  Debug.no_1 "list_failesc_context_simplify" pr pr list_failesc_context_simplify l


let mk_empty_frame () : (h_formula * int ) =
  let hole_id = fresh_int () in
  (Hole(hole_id), hole_id)

let mk_not_a_failure es =
  Basic_Reason ({
      fc_prior_steps = [];
      fc_message = "Success";
      fc_current_lhs =  es;(* empty_es (mkTrueFlow ()) Lab2_List.unlabelled  no_pos; *)
      fc_orig_conseq =  mkETrue  (mkTrueFlow ()) no_pos;
      fc_failure_pts = [];
      fc_current_conseq = mkTrue (mkTrueFlow ()) no_pos
    }, {
        fe_kind = Failure_Valid;
        fe_name = "" ;fe_locs=[]
      },
      []
    )

let invert ls =
  let foo es =
    let fc_template = {
      fc_message = "INCONSISTENCY : expected failure but success instead";
      fc_current_lhs  =  empty_es (mkTrueFlow ()) Lab2_List.unlabelled  no_pos;
      fc_prior_steps = [];
      fc_orig_conseq  = es.es_orig_conseq;
      fc_current_conseq = mkTrue (mkTrueFlow()) no_pos;
      fc_failure_pts =  []} in
    (Basic_Reason (fc_template,
                   mk_failure_must "INCONSISTENCY : expected failure but success instead" "", es.es_trace)) in
  let goo es ff = formula_subst_flow es.es_formula ff in
  let errmsg = "Expecting Failure but Success instead" in
  match ls with
  | [] -> []
  | [Ctx es] -> (match es.es_must_error with
      | None -> [Ctx {es with es_must_error = Some ("1 "^errmsg,foo es, (mk_cex true)); es_formula = goo es (mkErrorFlow())}]
      | Some _ -> [Ctx {es with es_must_error = None; es_formula = goo es (mkNormalFlow())}])
  | (Ctx es)::_ -> [Ctx {es with es_must_error = Some ("2 "^errmsg,foo es, (mk_cex true)); es_formula = goo es (mkErrorFlow())}]
  | _ -> report_error no_pos "not sure how to invert_outcome"


let invert_outcome (l:list_context) : list_context =
  match l with
  | FailCtx ft -> l
  | SuccCtx ls -> SuccCtx (invert ls)

let invert_fail_branch_must_fail (pt, ft):(branch_fail list * branch_ctx list)=
  let fk,eso = get_failure_es_ft ft in
  match (fk) with
  | Failure_Must _ ->
    begin
      match eso with
      | Some es -> ([],[(pt, Ctx es, None)])
      | None -> failwith "Cformula.invert_branch_must_fail: something is wrong"
    end
  | _ -> ([(pt,ft)], [])

let invert_ctx_branch_must_fail (pt, ctx, oft):(branch_fail)=
  let foo es =
    let fc_template = {
      fc_message = "INCONSISTENCY : expected failure but success instead";
      fc_current_lhs  =  empty_es (mkTrueFlow ()) Lab2_List.unlabelled no_pos;
      fc_prior_steps = [];
      fc_orig_conseq  = es.es_orig_conseq;
      fc_current_conseq = mkTrue (mkTrueFlow()) no_pos;
      fc_failure_pts =  []} in
    (Basic_Reason (fc_template,
                   mk_failure_must "INCONSISTENCY : expected failure but success instead" "", es.es_trace)) in
  match ctx with
  | Ctx es -> (pt, foo es)
  | _ -> report_error no_pos "not sure how to invert_outcome"

let invert_partial_context_outcome fnc_ctx_invert fnc_fail_invert (fs, bctxs):(branch_fail list * branch_ctx list)=
  let rec helper fs rs ctxs=
    match fs with
    | [] -> rs, ctxs
    | bf::bs -> let r1,r2 = fnc_fail_invert bf in
      helper bs (rs@r1) (ctxs@r2)
  in
  match fs with
  | [] ->(*if fs = empty ==> invert Valid => must failure*)
    (fs@(List.map fnc_ctx_invert bctxs),[])
  | _ -> (*otherwises*)
    let fb, cb = helper fs [] bctxs in (fb,cb)

let invert_list_partial_context_outcome fnc_ctx_invert fnc_fail_invert cl=
  List.map (invert_partial_context_outcome fnc_ctx_invert fnc_fail_invert) cl

let empty_ctx flowt lbl pos = Ctx (empty_es flowt lbl(*Lab2_List.unlabelled*) pos)

let false_es_with_flow_and_orig_ante es flowt f pos =
  let new_f = mkFalse flowt pos in
  {(empty_es flowt Lab2_List.unlabelled pos) with
   es_formula = new_f;
   es_orig_ante = Some f;
   es_infer_vars = es.es_infer_vars;
   es_infer_vars_rel = es.es_infer_vars_rel;
   es_infer_vars_templ = es.es_infer_vars_templ;
   es_infer_vars_hp_rel = es.es_infer_vars_hp_rel;
   es_infer_vars_sel_hp_rel = es.es_infer_vars_sel_hp_rel;
   es_infer_vars_sel_post_hp_rel = es.es_infer_vars_sel_post_hp_rel;
   es_infer_hp_unk_map = es.es_infer_hp_unk_map;
   es_infer_vars_dead = es.es_infer_vars_dead;
   es_infer_heap = es.es_infer_heap;
   es_infer_templ = es.es_infer_templ;
   es_infer_templ_assume = es.es_infer_templ_assume;
   es_infer_pure = es.es_infer_pure;
   es_infer_rel = es.es_infer_rel # clone;
   es_infer_term_rel = es.es_infer_term_rel;
   es_infer_hp_rel = es.es_infer_hp_rel # clone;
   es_infer_pure_thus = es.es_infer_pure_thus;
   (* es_infer_acc = new infer_acc; *)
   es_var_measures = es.es_var_measures;
   (* es_infer_tnt = es.es_infer_tnt; *)
   es_infer_obj = es.es_infer_obj;
   es_term_res_lhs = es.es_term_res_lhs;
   es_term_res_rhs = es.es_term_res_rhs;
   es_term_call_rhs = es.es_term_call_rhs;
   es_ho_vars_map = es.es_ho_vars_map;
   es_crt_holes = es.es_crt_holes;
   es_group_lbl = es.es_group_lbl;
   es_term_err = es.es_term_err;
   es_conc_err = es.es_conc_err;
  }

let false_es_with_orig_ante es f pos =
  let flowt = flow_formula_of_formula f in
  false_es_with_flow_and_orig_ante es flowt f pos

let false_ctx_with_flow_and_orig_ante es flowt f pos =
  Ctx (false_es_with_flow_and_orig_ante es flowt f pos)

let false_ctx_with_orig_ante es f pos =
  Ctx (false_es_with_orig_ante es f pos)

let false_es flowt g_lbl pos =
  let x = mkFalse flowt pos in
  {(empty_es flowt g_lbl pos) with es_formula = x;}

and true_ctx flowt g_lbl pos = Ctx (empty_es flowt g_lbl pos)

(* let mkFalse_branch_ctx = ([],false_ctx mkFalseFlow no_pos) *)

let context_of_branch_ctx_list ls =
  let rec helper ls = match ls with
    | [] -> (* report_error no_pos "Current Successful context should not be empty []" *)
      (* Not sure it's right or not *)
      false_ctx_with_orig_ante (false_es mkFalseFlow (None, []) no_pos) (mkFalse mkFalseFlow no_pos) no_pos
    | [(_,c,_)] -> c
    | (_,c,_)::ts -> OCtx (c,helper ts)
  in helper ls

let succ_context_of_failesc_context (_,_,sl) = (context_of_branch_ctx_list sl)

let succ_context_of_failesc_context ((_,_,sl) as x) =
  let pr = !print_failesc_context in
  let pr2 = !print_context_short in
  Debug.no_1 "succ_context_of_failesc_context" pr pr2
    succ_context_of_failesc_context x

let succ_context_of_list_failesc_context ctx =
  List.map succ_context_of_failesc_context ctx

let or_context_list (cl10 : context list) (cl20 : context list) : context list =
  let rec helper cl1 = match cl1 with
    | c1 :: rest ->
      let tmp1 = helper rest in
      let tmp2 = List.map (or_context c1) cl20 in
      tmp2 @ tmp1
    | [] -> []
  in
  if Gen.is_empty cl20 then
    [] (* cl10 *)
  else helper cl10

let or_context_list cl10 cl20 =
  let pr = !print_context_list_short in
  Debug.no_2 "or_context_list" pr pr pr (fun _ _ -> or_context_list cl10 cl20) cl10 cl20

let mkFailContext msg estate conseq pid pos = {
  fc_prior_steps = estate.es_prior_steps ;
  fc_message = msg ;
  fc_current_lhs = estate;
  fc_orig_conseq = estate.es_orig_conseq;
  fc_failure_pts = (match pid with | Some s-> [s] | _ -> []);
  fc_current_conseq = conseq;
}

let mkFailCtx_in (ft:fail_type) (es, msg,fk) cex =
  FailCtx (ft, Ctx {es with es_final_error = es.es_final_error@[(msg, ft, fk)]}, cex)

(*simple concurrency*)
let mkFailCtx_simple msg estate conseq cex pos =
  let fail_ctx = {
    fc_message = msg;
    fc_current_lhs  = estate;
    fc_prior_steps = estate.es_prior_steps;
    fc_orig_conseq  = struc_formula_of_formula conseq pos;
    fc_current_conseq = formula_of_heap HFalse pos;
    fc_failure_pts = [];}
  in
  let fail_ex = {fe_kind = Failure_Must msg; fe_name = Globals.logical_error ;fe_locs=[]} in
  (*temporary no failure explaining*)
  mkFailCtx_in (Basic_Reason (fail_ctx,fail_ex, estate.es_trace)) ({estate with es_formula = substitute_flow_into_f !error_flow_int estate.es_formula}, msg, Failure_Must msg) cex

let mkFailCtx_vperm msg rhs_b estate conseq cex pos =
  let s = "variable permission mismatch "^msg in
  let new_estate = {estate  with es_formula = substitute_flow_into_f
                                     !top_flow_int estate.es_formula} in
  mkFailCtx_in (Basic_Reason (mkFailContext s new_estate (Base rhs_b) None pos,mk_failure_may s logical_error, estate.es_trace)) (new_estate, s, Failure_May s) cex

let mk_fail_partial_context_label (ft:fail_type) (lab:path_trace) : (partial_context) = ([(lab,ft)], [])

(* let mk_partial_context (c:context) : (partial_context) = ([], [ ([], c) ] )  *)

let mk_partial_context (c:context) (lab:path_trace) : (partial_context) = ([], [ (lab, c, None) ] )
let mk_failesc_context (c:context) (lab:path_trace) esc : (failesc_context) = ([], esc,[ (lab, c, None) ] )

(* WN : this seems weird *)
(* let rec is_empty_esc_stack (e:esc_stack) : bool = match e with *)
(*   | [] -> false *)
(*   | (_,[])::t -> is_empty_esc_stack t *)
(*   | (_,h::t)::_ -> true *)

let rec is_empty_esc_stack (e:esc_stack) : bool = match e with
  | [] -> true
  | (_,[])::t -> is_empty_esc_stack t
  | (_,h::t)::_ -> false

let colapse_esc_stack (e:esc_stack) : branch_ctx list =
  List.fold_left (fun a (_,c)-> a@c) [] e

let push_esc_elem  (e:esc_stack) (b:branch_ctx list): esc_stack =
  match b with
  | [] -> e
  | _ ->
    match e with
    | [] -> [((0,""),b)]
    | (lbl,h)::t-> (lbl,b@h)::t

let push_esc_level (e:esc_stack) lbl : esc_stack = (lbl,[])::e

let pop_esc_level (e:esc_stack) lbl : (esc_stack * branch_ctx list) = match e with
  | (lbl,s)::t -> (t,s)
  | _ -> Error.report_error {Err.error_loc = no_pos;
                             Err.error_text = "error in popping exception contexts \n"}

(*
type: ((('a * 'b) * 'c) list * context) list ->
  ((('a * 'b) * 'c) list * context) list ->
  ((('a * 'b) * 'c) list * context) list
*)

let or_fail_type_opt oft1 oft2=
  match oft1, oft2 with
  |Some ft1, Some ft2 -> Some (Or_Reason (ft1,ft2))
  | Some _ , None -> oft1
  | None, Some _ -> oft2
  | _ -> None

let rec merge_success s1 s2 = match s1,s2 with
  | [],xs | xs,[] -> xs
  (* List.filter (fun (l,_) -> not (List.mem l pt_fail_list)) xs *)
  | (l1,b1,ft1)::z1,(l2,b2,ft2)::z2 ->
    if path_trace_eq l1 l2 then
      let res = merge_success z1 z2 in
      ((l1,or_context b1 b2, or_fail_type_opt ft1 ft2)::res)
    else if path_trace_lt l1 l2 then
      let res = merge_success z1 s2 in
      (l1,b1,ft1)::res
    else let res = merge_success s1 z2 in
      (l2,b2,ft2)::res

let pop_esc_level_list (l:list_failesc_context) lbl : list_failesc_context =
  List.map (fun (fl,el,sl)->
      let ne,el = pop_esc_level el lbl in
      (fl,ne, merge_success el sl)) l

let pop_esc_level_list (l:list_failesc_context) lbl : list_failesc_context =
  let pr = pr_list !print_failesc_context in
  Debug.no_1 "pop_esc_level_list" pr pr
    (fun _ -> pop_esc_level_list l lbl) l


let mk_list_partial_context_label (c:list_context) (lab:path_trace): (list_partial_context) =
  match c with
  | FailCtx (fr,_,_) ->  [( [(lab,fr)] ,[])]
  | SuccCtx cl -> List.map (fun c -> mk_partial_context c lab) cl

let mk_list_partial_context (c:list_context) : (list_partial_context) =
  mk_list_partial_context_label c []



let repl_label_list_partial_context (lab:path_trace) (cl:list_partial_context) : list_partial_context
  = List.map (fun (fl,sl) -> (fl, List.map (fun (_,c, oft) -> (lab,c, oft)) sl)) cl



let isAnyFalseCtx (ctx:context) : bool = match ctx with
  | Ctx es -> isAnyConstFalse es.es_formula
  | _ -> false

(* WN : need to choose the weaker pre of the two *)
let merge_false es1 es2 = es1
(* { es1 with *)
(*     (\* all inferred must be concatenated from different false *\) *)
(*     es_infer_pure = es1.es_infer_pure@es2.es_infer_pure; *)
(*     es_infer_rel = es1.es_infer_rel@es2.es_infer_rel; *)
(*     es_infer_heap = es1.es_infer_heap@es2.es_infer_heap; *)
(*     es_infer_hp_rel = es1.es_infer_hp_rel@es2.es_infer_hp_rel *)
(*  } *)

let merge_false_ctx c1 c2 =
  match c1,c2 with
  | Ctx e1, Ctx e2 -> Ctx (merge_false e1 e2)
  | _,_ -> (Debug.info_zprint (lazy  "warning on merge_false") no_pos; c1)

(* let anyPreInCtx c = is_inferred_pre_ctx c *)

(* let proc_left t1 t2 = *)
(*     match t1 with *)
(*       | [] -> Some t2 *)
(*       | [c1] -> *)
(*             if isAnyFalseCtx c1 then *)
(*               (\* let () = print_endline ("FalseCtx") in *\) *)
(*               if is_inferred_pre_ctx c1 then *)
(*                 (\* let () = print_endline ("Inferred") in *\) *)
(*                 Some t2 (\* drop FalseCtx with Pre *\) *)
(*               else *)
(*                 (\* let () = print_endline ("NOT Inferred") in *\) *)
(*                 Some t1 (\* keep FalseCtx wo Pre *\) *)
(*             else None *)
(*       | _ -> None *)

let proc_left t1 t2 =
  match t1 with
  | [] -> Some t2
  | [c1] ->
    if isAnyFalseCtx c1 then
      if x_add_1 is_inferred_pre_ctx c1 then
        match t2 with
        | [c2] ->
          if isAnyFalseCtx c2
             && x_add_1 is_inferred_pre_ctx c2
             (* both t1 and t2 are FalseCtx with Pre *)
          then Some [merge_false_ctx c1 c2]
          else Some t2 (* drop FalseCtx t1 with Pre *)
        | _ -> Some t1 (* only t1 is FalseCtx with Pre *)
      else Some t1 (* keep FalseCtx wo Pre *)
    else None
  | _ -> None

(* remove false with precondition *)
let simplify_ctx_elim_false_dupl t1 t2 =
  match proc_left t1 t2 with
  | Some r1 -> r1
  | None ->
    (match proc_left t2 t1 with
     (* | Some r2 -> r2 *) (*why t1 is missing???*)
     (*LDK: what if t1=[true] and t2=[false]*)
     | Some r2 -> t1 (*LDK: remove t2*)
     | None -> t1@t2)

let simplify_ctx_elim_false_dupl t1 t2 =
  let pr = !print_context_list_short in
  Debug.no_2 "simplify_ctx_elim_false_dupl" pr pr pr simplify_ctx_elim_false_dupl t1 t2

(*context set union*)
let list_context_union_x c1 c2 =
  let simplify x = (* context_list_simplify *) x in
  match c1,c2 with
  | FailCtx (t1, c1, cex1), FailCtx (t2, c2, cex2) -> (*FailCtx (Or_Reason (t1,t2))*)
    if ((is_cont t1) && not(is_cont t2)) then FailCtx (t1,c1 ,cex1)
    else if ((is_cont t2) && not(is_cont t1)) then FailCtx (t2, c2,cex2)
    else if (is_cont t1) && (is_cont t2) then FailCtx (Or_Continuation (t1,t2), OCtx (c1,c2), cex_union cex1 cex2 )
    else FailCtx (Union_Reason (t1,t2), OCtx (c1,c2), cex_union cex1 cex2)  (* for UNION, we need to priorities MAY bug *)
  (*FailCtx (And_Reason (t1,t2))   *)
  | FailCtx t1 ,SuccCtx t2 -> SuccCtx (simplify t2)
  | SuccCtx t1 ,FailCtx t2 -> SuccCtx (simplify t1)
  | SuccCtx t1 ,SuccCtx t2 ->
    (* if contains_error_flow_ctx_list t1 then *)
    (*   if contains_error_flow_ctx_list t2  *)
    (*   then failwith "to implement union_error" *)
    (*   else SuccCtx (simplify t2) *)
    (* else *)
    (* if contains_error_flow_ctx_list t2 then SuccCtx (simplify t2) *)
    (* else  *)
    SuccCtx (simplify_ctx_elim_false_dupl t1 t2)

let list_context_union c1 c2 =
  let pr = !print_list_context(* _short *) in
  Debug.no_2_opt (fun _ -> not(isFailCtx c1 ||  isFailCtx c2) )  "list_context_union"
    pr pr pr
    list_context_union_x c1 c2

let rec union_context_left_x c_l: list_context = (* match (List.length c_l) with *) match c_l with
  | [] ->  (* Err.report_error {Err.error_loc = no_pos;   *)
    (*    Err.error_text = "union_context_left: folding empty context list \n"} *)
    (SuccCtx []: list_context)
  | [a] -> a (* (List.hd c_l) *)
  | a::rest -> (* List.fold_left list_context_union (List.hd c_l) (List.tl c_l) *)
    List.fold_left list_context_union a rest

and union_context_left c_l =
  let pr = !print_list_context in
  Debug.no_1 "union_context_left" (pr_list pr) pr union_context_left_x c_l

(*should use union_context_left directly*)
and fold_context_left_x c_l = union_context_left c_l

(*list_context or*)
and get_explaining t =
  match t with
  | Basic_Reason (f, fe, _) -> Some fe
  | Trivial_Reason _ -> None
  | Or_Reason _ -> None
  | Union_Reason _ -> None
  | And_Reason (_,_) -> None
  | ContinuationErr _ -> None
  | Or_Continuation _ -> None

and isMustFail fc = is_must_failure_ft fc


and isMayFail fc = is_may_failure_ft fc

and isMustFailCtx cl = match cl with
  | FailCtx (fc,_, cex) -> (* Loc: to check cex here*) isMustFail fc
  | SuccCtx _ -> false

and isMayFailCtx cl = match cl with
  | FailCtx (fc,_, cex) -> (* Loc: to check cex here*) isMayFail fc
  | SuccCtx _ -> false

and fold_context_left i c_l =
  let pr = !print_list_context_short in
  let pr1 x = String.concat "\n" (List.map !print_list_context_short x) in
  Debug.no_1_num i "fold_context_left" pr1 pr fold_context_left_x c_l

(* Fail U Succ --> Succ *)
(* Fail m1 U Fail m2 --> And m1 m2 *)
(* Fail or Succ --> Fail *)
(* Fail m1 or Fail m2 --> Or m1 m2 *)
(*list_context or*)

(*LOR*)
and get_first_es cs=
  let c = match cs with
    | c::_ -> c
    | [] -> Ctx (empty_es (mkTrueFlow ()) Lab2_List.unlabelled  no_pos)
  in
  let rec helper c0=
    match c0 with
    | Ctx es -> es
    | OCtx (c1,c2) -> helper c1
  in
  helper c

and or_list_context_x_new c1 c2 =
  match c1,c2 with
  | FailCtx (t1, c1, cex1) ,FailCtx (t2, c2, cex2) -> FailCtx (Or_Reason (t1,t2) , OCtx(c1, c2),
                                                               cex_lor cex1 cex2)
  | FailCtx (t1, c1, cex1) ,SuccCtx t2 ->
    if is_bot_failure_ft t1 then
      (c2 )
    else
      let t = mk_not_a_failure (get_first_es  t2) in
      FailCtx (Or_Reason (t1,t), c1 ,{cex1 with cex_processed_mark = false;})
  | SuccCtx t1 ,FailCtx (t2,c2, cex2) ->
    if is_bot_failure_ft t2 then
      c1
    else
      let t = mk_not_a_failure (get_first_es t1) in
      FailCtx (Or_Reason (t,t2),c2, {cex2 with cex_processed_mark = false;})
  | SuccCtx t1 ,SuccCtx t2 -> SuccCtx (x_add or_context_list t1 t2)

and or_list_context_x c1 c2 = match c1,c2 with
  | FailCtx (t1,c1,cex1) ,FailCtx (t2, c2,cex2) -> FailCtx (Or_Reason (t1,t2), OCtx(c1,c2),cex_lor cex1 cex2)
  | FailCtx (t1,c1,cex1) ,SuccCtx t2 ->
    let t = mk_not_a_failure (get_first_es t2)
    in
    FailCtx (Or_Reason (t1,t),c1, cex1)
  | SuccCtx t1 ,FailCtx (t2,c2,cex2) ->
    let t = mk_not_a_failure (get_first_es t1)
    in
    FailCtx (Or_Reason (t,t2), c2, cex2)
  | SuccCtx t1 ,SuccCtx t2 -> SuccCtx (x_add or_context_list t1 t2)

and and_list_context c1 c2= match c1,c2 with
  | FailCtx (t1, c1, cex1) ,FailCtx (t2, c2, cex2) -> FailCtx (And_Reason (t1,t2),OCtx(c1, c2) ,cex_land cex1 cex2)
  | FailCtx (t1,_,_) ,SuccCtx t2 ->
    c1
  | SuccCtx t1 ,FailCtx _ ->
    c2
  | SuccCtx t1 ,SuccCtx t2 -> SuccCtx (x_add or_context_list t1 t2)

and or_list_context c1 c2 =
  let pr = !print_list_context in
  Debug.no_2 "or_list_context" pr pr pr or_list_context_x_new c1 c2

(* can remove redundancy here? *)

let isFailPartialCtx (fs,ss) =
  if (Gen.is_empty fs) then false else true

let isFailFailescCtx (fs,es,ss) =
  if (Gen.is_empty fs) then false else true
(* if (Gen.is_empty ss)&&(Gen.is_empty (colapse_esc_stack es)) then true else false *)

let isFailBranchFail (_,ft) =
  match (get_failure_ft ft) with
  | Failure_Must _ -> true
  | Failure_May _ -> true
  | Failure_Valid -> false
  | Failure_Bot _ -> false

let isFailFailescCtx_new (fs,_,brs) =
  let is_fail = List.exists isFailBranchFail fs in
  if not !Globals.enable_error_as_exc then is_fail
  else
  if is_fail then is_fail else
    List.exists (fun (_,_,oft) -> oft != None) brs

let isFailPartialCtx_new (fs,ss) =
  List.exists isFailBranchFail fs

let isFailListPartialCtx cl =
  List.for_all isFailPartialCtx cl

let isFailListPartialCtx_new cl =
  List.for_all isFailPartialCtx_new cl

let isFailListFailescCtx cl =
  List.for_all isFailFailescCtx cl

let isFailListFailescCtx_new cl =
  List.for_all isFailFailescCtx_new cl

let isSuccessPartialCtx (fs,ss) =
  if (Gen.is_empty fs) then true else false

let isSuccessBranchFail (_,ft) =
  match (get_failure_ft ft) with
  | Failure_Must _ -> false
  | Failure_May _ -> false
  | Failure_Valid -> true
  | Failure_Bot _ -> true


let rec is_error_exc_ctx c=
  match c with
  | Ctx es -> is_en_error_exc es && (is_error_flow es.es_formula || is_mayerror_flow es.es_formula)
  | OCtx (c1,c2) -> is_en_error_exc_ctx c1 || is_en_error_exc_ctx c2


let isSuccBranches succ_brs=
  (* all succ branch should not subsume must, may flows *)
  succ_brs != [] && List.for_all (fun (_, c, oft) ->
      (oft = None) && not (is_error_exc_ctx c)
    ) succ_brs

let isSuccessPartialCtx_new (fs,succ_brs) =
  let is_succ = List.for_all isSuccessBranchFail fs in
  if not !Globals.enable_error_as_exc || not is_succ then is_succ else
    (* all succ branch should not subsume must, may flows *)
    (* succ_brs != [] && List.for_all (fun (_, _, oft) -> *)
    (*     oft = None *)
    (* ) succ_brs *)
    isSuccBranches succ_brs

let isSuccessFailescCtx (fs,_,_) =
  if (Gen.is_empty fs) then true else false

let isSuccessFailescCtx_new (fs,esc,succ_brs) =
  let is_succ = List.for_all isSuccessBranchFail fs in
  if not !Globals.enable_error_as_exc || not is_succ then is_succ else
    isSuccBranches succ_brs (* && List.for_all (fun (_,brs) -> *)
(*     isSuccBranches brs *)
(* ) esc *)

(* [] denotes failure *)
let isSuccessListPartialCtx cl =
  (* cl==[] || *) List.exists isSuccessPartialCtx cl

let isSuccessListPartialCtx cl =
  let pr = !print_list_partial_context in
  Debug.no_1 "isSuccessListPartialCtx" pr string_of_bool isSuccessListPartialCtx cl

let isSuccessListPartialCtx_new cl =
  (* cl==[] || *) List.exists isSuccessPartialCtx_new cl

let isSuccessListFailescCtx cl =
  (* cl==[] || *) List.exists isSuccessFailescCtx cl

let isSuccessListFailescCtx cl =
  (* let cl = list_failesc_context_simplify cl in *)
  let pr = !print_list_failesc_context in
  Debug.no_1 "isSuccessListFailescCtx" pr string_of_bool isSuccessListFailescCtx cl

let isSuccessListFailescCtx_new cl =
  (* cl==[] || *) List.exists isSuccessFailescCtx_new cl

let isNonFalseListPartialCtx cl =
  List.exists (fun (_,ss)-> ((List.length ss) >0) && not (List.for_all (fun (_,c) -> isAnyFalseCtx c) ss )) cl

let isNonFalseListFailescCtx cl =
  List.exists (fun (_,el,ss)->
      let ess = (colapse_esc_stack el)@ss in
      ((List.length ess) >0) && not (List.for_all (fun (_,c,_) -> isAnyFalseCtx c) ess )) cl

let keep_failure_failesc_context ((c,es,sc): failesc_context) : failesc_context =
  (c,[],[])

let keep_failure_list_failesc_context (lc: list_failesc_context) : list_failesc_context =
  List.map ( keep_failure_failesc_context) lc

let keep_failure_partial_context ((c,es): partial_context) : partial_context =
  (c,[])

let keep_failure_list_partial_context (lc: list_partial_context) : list_partial_context =
  List.map ( keep_failure_partial_context) lc



(* this should be applied to merging also and be improved *)
(* let count_false (sl:branch_ctx list) = List.fold_left (fun cnt (_,oc) -> if (isAnyFalseCtx oc) then cnt+1 else cnt) 0 sl *)

(*remove v=v from formula*)
let remove_true_conj_pure (p:CP.formula) =
  let ps = CP.split_conjunctions p in
  let ps1 = CP.remove_true_conj_eq ps in
  let ps2 = CP.join_conjunctions ps1 in
  ps2

(*remove v=v from formula*)
let remove_true_conj_mix_formula_x (f:MCP.mix_formula):MCP.mix_formula =
  (match f with
   | MCP.MemoF _ ->
     let () = print_string ("[cformula.ml][remove_true_conj_mix_formula] Warning: not yet support MCP.MemoF \n") in
     f
   | MCP.OnePF p_f -> (MCP.OnePF (remove_true_conj_pure p_f))
  )

(*remove v=v from formula*)
let remove_true_conj_mix_formula (f:MCP.mix_formula):MCP.mix_formula =
  Debug.no_1 "remove_true_conj_mix_formula" !print_mix_formula !print_mix_formula
    remove_true_conj_mix_formula_x f
(*remove v=v from formula*)

let remove_dupl_conj_eq_pure (p:CP.formula) =
  let ps = CP.split_conjunctions p in
  let ps1 = CP.remove_dupl_conj_eq ps in
  let ps2 = CP.join_conjunctions ps1 in
  ps2

(*TODO: considered --eps *)
(*remove v=v from formula*)
let remove_dupl_conj_eq_mix_formula_x (f:MCP.mix_formula):MCP.mix_formula =
  let nf= MCP.pure_of_mix f in
  let nf = remove_dupl_conj_eq_pure nf in
  MCP.mix_of_pure nf

(*TODO: considered --eps *)
(*remove v=v from formula*)
let remove_dupl_conj_eq_mix_formula (f:MCP.mix_formula):MCP.mix_formula =
  Debug.no_1 "remove_dupl_conj_eq_mix_formula" !print_mix_formula !print_mix_formula
    remove_dupl_conj_eq_mix_formula_x f

(*remove v=v from formula*)
let remove_dupl_conj_eq_formula_x (f:formula):formula =
  let rec helper f =
    match f with
    | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) ->
      Or ({formula_or_f1 = helper f1; formula_or_f2 = helper f2; formula_or_pos = pos})
    | Base b ->
      let new_p = remove_dupl_conj_eq_mix_formula b.formula_base_pure in
      Base {b with formula_base_pure=new_p}
    | Exists b ->
      let new_p = remove_dupl_conj_eq_mix_formula b.formula_exists_pure in
      Exists {b with formula_exists_pure=new_p}
  in helper f
(*remove v=v from formula*)
let remove_dupl_conj_eq_formula (f:formula):formula =
  Debug.no_1 "remove_dupl_conj_eq_formula" !print_formula !print_formula
    remove_dupl_conj_eq_formula_x f

(*remove v=v from formula*)
let remove_dupl_conj_estate (estate:entail_state) : entail_state =  {estate with es_pure=remove_dupl_conj_eq_mix_formula estate.es_pure}

(* Debug.no_1 "remove_dupl_false" pr pr remove_dupl_false sl *)



let rank (t:partial_context):float = match t with
  | ( [] ,[] ) -> Err.report_error {Err.error_loc = no_pos;  Err.error_text = " rank: recieved an empty partial_context\n"}
  | ( [] , _ ) -> 1.
  | ( _  ,[] ) -> 0.
  | ( l1 , l2) ->
    let fn,sn =float (List.length(l1)), float(List.length(l2)) in
    sn /.(fn +. sn)

let list_partial_context_union (l1:list_partial_context) (l2:list_partial_context):list_partial_context = x_add_1 remove_dupl_false_pc_list (l1 @ l2)

let list_failesc_context_union (l1:list_failesc_context) (l2:list_failesc_context):list_failesc_context = x_add_1 remove_dupl_false_fe_list (l1 @ l2)

let list_partial_context_union (l1:list_partial_context) (l2:list_partial_context):list_partial_context =
  let pr x = string_of_int(List.length x) in
  Debug.no_2 "list_partial_context_union" pr pr pr list_partial_context_union l1 l2

let list_failesc_context_union (l1:list_failesc_context) (l2:list_failesc_context):list_failesc_context =
  let pr x = string_of_int(List.length x) in
  Debug.no_2 "list_failesc_context_union" pr pr pr list_failesc_context_union l1 l2


let select n l =
  if n<=0 then l
  else (Gen.BList.take n l) @(List.filter (fun c-> (rank c)==1.) (Gen.BList.drop n l))

let list_partial_context_union_n (l1:list_partial_context) (l2:list_partial_context) n :list_partial_context =
  select n  (List.sort (fun a1 a2 -> truncate (((rank a2)-.(rank a1))*.1000.)) (l1 @ l2))

let rec merge_fail (f1:branch_fail list) (f2:branch_fail list) : (branch_fail list * path_trace list) =
  match f1,f2 with
  | [],xs -> xs, (List.map (fun (p,_)->p) xs)
  | xs,[] -> xs, (List.map (fun (p,_)->p) xs)
  | (l1,b1)::z1,(l2,b2)::z2 ->
    if path_trace_eq l1 l2 then
      let res,pt = merge_fail z1 z2 in
      (* let fe = {fe_kind = Failure_Bot} in *)
      ((l1,Or_Reason (b1,b2))::res, l1::pt)
    else if path_trace_lt l1 l2 then
      let res,pt = merge_fail z1 f2 in
      ((l1,b1)::res, l1::pt)
    else let res,pt = merge_fail f1 z2 in
      ((l2,b2)::res, l2::pt)

let merge_partial_context_or ((f1,s1):partial_context) ((f2,s2):partial_context) : partial_context =
  let s1 = x_add_1 remove_dupl_false s1 in
  let s2 = x_add_1 remove_dupl_false s2 in
  let (res_f,pt_fail_list) = merge_fail f1 f2 in
  let res_s = merge_success s1 s2 in
  (* print_string ("\nBefore :"^(Cprinter.summary_partial_context (f1,s1))); *)
  (* print_string ("\nBefore :"^(Cprinter.summary_partial_context (f2,s2))); *)
  (* print_string ("\nAfter :"^(Cprinter.summary_partial_context (res_f,res_s))); *)
  (res_f,res_s)

(*
type: esc_stack ->
  esc_stack -> (control_path_id_strict * branch_ctx list) list

*)
let rec merge_esc f e1 e2 =
  match e1,e2 with
  | [],[] -> []
  | (l1,b1)::z1,(l2,b2)::z2 ->
    let flag = not ((fst l1)==(fst l2)) in
    (if flag then
       print_endline_quiet ("WARNING MISMATCH at merge_esc:\n"^(!print_esc_stack e1)^"\n"^(!print_esc_stack e2)))
  ; (l1,merge_success b1 b2)::(merge_esc f z1 z2)
  (* if not ((fst l1)==(fst l2)) then  *)
  (*   Err.report_error {Err.error_loc = no_pos;  Err.error_text = "malfunction in merge failesc context lbl mismatch\n"} *)
  | _ ->
    print_string ("stack e1: "^ (f e1)^":"^" stack e2: "^(f e2)^":"^"\n");
    Err.report_error {Err.error_loc = no_pos;  Err.error_text = "mismatched number in merge_esc methd \n"}

let merge_esc f e1 e2 =
  let pr1 x = "#"^(!print_esc_stack x)^"#" in
  Debug.no_2 "merge_esc" pr1 pr1 pr_no (fun _ _ -> merge_esc f e1 e2) e1 e2

let merge_failesc_context_or f ((f1,e1,s1):failesc_context) ((f2,e2,s2):failesc_context) : failesc_context =
  let s1 = x_add_1 remove_dupl_false s1 in
  let s2 = x_add_1 remove_dupl_false s2 in
  let (res_f,pt_fail_list) = merge_fail f1 f2 in
  let res_s = merge_success s1 s2 in
  (* WN[((0,""),[])] : this should be added at the beginning of each proc, and not here *)
  (* let e1 = match e1 with | [] -> [((0,""),[])] | _-> e1 in *)
  (* let e2 = match e2 with | [] -> [((0,""),[])] | _-> e2 in *)
  let res_e = merge_esc f e1 e2 in
  (* print_string ("\nBefore :"^(Cprinter.summary_partial_context (f1,s1))); *)
  (* print_string ("\nBefore :"^(Cprinter.summary_partial_context (f2,s2))); *)
  (* print_string ("\nAfter :"^(Cprinter.summary_partial_context (res_f,res_s))); *)
  (res_f,res_e,res_s)

let merge_failesc_context_or f (((f1,e1,s1):failesc_context) as x1) (((f2,e2,s2):failesc_context) as x2) : failesc_context =
  let pr = !print_failesc_context in
  Debug.no_2 "merge_failesc_context_or" pr pr pr
    (fun _ _ -> merge_failesc_context_or f (x1) (x2)) x1 x2


let simple_or pc1 pc2 =  ( (fst pc1)@(fst pc2),  x_add_1 remove_dupl_false ((snd pc1)@(snd pc2)) )

let list_partial_context_or_naive (l1:list_partial_context) (l2:list_partial_context) : list_partial_context =
  List.concat (List.map (fun pc1-> (List.map (simple_or pc1) l2)) l1)
(* List.concat (List.map (fun pc1-> (List.map (merge_partial_context_or pc1) l2)) l1) *)

let list_partial_context_or (l1:list_partial_context) (l2:list_partial_context) : list_partial_context =
  (* List.concat (List.map (fun pc1-> (List.map (simple_or pc1) l2)) l1) *)
  if List.length l1 = 0 then l2
  else if List.length l2 = 0 then l1
  else
    List.concat (List.map (fun pc1-> (List.map (fun pc2 -> x_add_1 remove_dupl_false_pc (merge_partial_context_or pc1 pc2)) l2)) l1)

let list_partial_context_or (l1:list_partial_context) (l2:list_partial_context) : list_partial_context =
  let pr x = string_of_int (List.length x) in
  Debug.no_2(*_loop*) "list_partial_context_or" pr pr pr list_partial_context_or l1 l2

let list_failesc_context_or f (l1:list_failesc_context) (l2:list_failesc_context) : list_failesc_context =
  List.concat (List.map (fun pc1-> (List.map (fun pc2 -> x_add_1 remove_dupl_false_fe (merge_failesc_context_or f pc1 pc2)) l2)) l1)

let list_failesc_context_or f (l1:list_failesc_context) (l2:list_failesc_context) : list_failesc_context =
  let pr = !print_list_failesc_context in
  Debug.no_2 "list_failesc_context_or"
    pr pr pr
    (fun _ _ -> list_failesc_context_or f l1 l2) l1 l2

let add_cond_label_partial_context (c_pid: control_path_id_strict) (c_opt: path_label) ((fl,sl):partial_context) =
  let sl_1 = List.map (fun (pt,ctx, oft) -> (((c_pid,c_opt)::pt),ctx, oft) ) sl in
  (fl,sl_1)

let add_cond_label_failesc_context (c_pid: control_path_id_strict) (c_opt: path_label) ((fl,esc,sl):failesc_context) =
  let sl_1 = List.map (fun (pt,ctx, oft) -> (((c_pid,c_opt)::pt),ctx, oft) ) sl in
  (fl,esc,sl_1)


let add_cond_label_list_partial_context (c_pid: control_path_id) (c_opt: path_label) (lpc:list_partial_context) =
  match c_pid with
  | None -> (print_string "empty c_pid here"; lpc)
  | Some pid -> List.map (add_cond_label_partial_context pid c_opt) lpc


let add_cond_label_list_failesc_context (c_pid: control_path_id) (c_opt: path_label) (lpc:list_failesc_context) =
  match c_pid with
  | None -> (print_string "empty c_pid here"; lpc)
  | Some pid -> List.map (add_cond_label_failesc_context pid c_opt) lpc

let add_cond_label_strict_list_failesc_context (pid: control_path_id_strict) (c_opt: path_label) (lpc:list_failesc_context) =
  List.map (add_cond_label_failesc_context pid c_opt) lpc


let rec build_context ctx f pos = match f with
  | Base _ | Exists _ ->
    let es = estate_of_context ctx pos in
    Ctx ({es with es_formula = f;es_unsat_flag =false})
  | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = _}) ->
    let c1 = build_context ctx f1 pos in
    let c2 = build_context ctx f2 pos in
    or_context c1 c2

(* 09.05.2008 ---*)

and set_context_formula (ctx : context) (f : formula) : context = match ctx with
  | Ctx es -> begin
      match f with
      | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) ->
        let cf1 = set_context_formula ctx f1 in
        let cf2 = set_context_formula ctx f2 in
        mkOCtx  cf1 cf2 pos
      | _ -> Ctx {es with es_formula = f;es_unsat_flag =false;}
    end
  | OCtx (c1, c2) ->
    let nc1 = set_context_formula c1 f in
    let nc2 = set_context_formula c2 f in
    mkOCtx nc1 nc2 (pos_of_formula f)

(* and get_estate_must_match (es : entail_state) : bool =  *)
(* 	es.es_must_match *)

(* and set_estate_must_match (es: entail_state) : entail_state = 	 *)
(* 	let es_new = {es with es_must_match = true} in *)
(* 		es_new *)

and moving_ivars_to_evars (estate:entail_state) (anode:h_formula) : entail_state =
  let arg_vars = h_fv anode in
  let (removed_ivars,remaining_ivars) = List.partition (fun v -> CP.mem v arg_vars) estate.es_ivars in
  {estate with es_evars = estate.es_evars@removed_ivars; es_ivars = remaining_ivars; }

(* and set_context_must_match (ctx : context) : context = match ctx with  *)
(*   | Ctx (es) -> Ctx(set_estate_must_match es) *)
(*   | OCtx (ctx1, ctx2) -> OCtx((set_context_must_match ctx1), (set_context_must_match ctx2)) *)

(* and set_context_must_match (ctx : context) : context =  *)
(*   set_context (fun es -> {es with es_must_match = true}) ctx *)

and set_estate f (es: entail_state) : entail_state =
  f es

and set_context f (ctx : context) : context = match ctx with
  | Ctx (es) -> Ctx(set_estate f es)
  | OCtx (ctx1, ctx2) -> mkOCtx (set_context f ctx1)  (set_context f ctx2) no_pos

and set_list_context f (ctx : list_context) : list_context = match ctx with
  | FailCtx f -> ctx
  | SuccCtx l -> let nl = List.map (set_context f) l in SuccCtx nl

and estate_opt_of_list_context (ctx : list_context) : entail_state option =
  match ctx with
  | SuccCtx (c::_) -> estate_opt_of_context c
  | _ -> None

and estate_opt_of_context (ctx : context) = match ctx with
  | Ctx es -> Some es
  | _ -> None

and estate_of_context (ctx : context) (pos : loc) = match ctx with
  | Ctx es -> es
  | _ -> Err.report_error {Err.error_loc = pos;
                           Err.error_text = "estate_of_context: disjunctive or fail context"}

and flow_formula_of_ctx (ctx : context) (pos : loc) = match ctx with
  | Ctx es -> flow_formula_of_formula es.es_formula
  | _ -> Err.report_error {Err.error_loc = pos;
                           Err.error_text = "flow_of_context: disjunctive or fail context"}

and flow_formula_of_list_context ls=
  match ls with
  | FailCtx _ -> []
  | SuccCtx cl -> begin
      try
        List.map (fun ctx -> flow_formula_of_ctx ctx no_pos) cl
      with _ -> []
    end

and set_flow_in_ctx_override (c:context) (f:flow_formula) :context = match c with
  | Ctx c1-> Ctx {c1 with es_formula = set_flow_in_formula_override f c1.es_formula}
  | OCtx (c1,c2) -> OCtx ((set_flow_in_ctx_override c1 f),(set_flow_in_ctx_override c2 f))

and change_flow_ctx from_fl to_fl ctx_list =
  let rec helper c = match c with
    | Ctx c -> Ctx {c with es_formula = substitute_flow_in_f to_fl from_fl c.es_formula;}
    | OCtx (c1,c2)-> OCtx ((helper c1), (helper c2)) in
  List.map helper ctx_list

and change_flow_into_ctx to_fl ctx =
  match ctx with
  | Ctx c -> Ctx {c with es_formula = substitute_flow_into_f to_fl c.es_formula;}
  | OCtx (c1,c2)-> OCtx ((change_flow_into_ctx to_fl c1), (change_flow_into_ctx to_fl c2))

and change_flow_into_ctx_list to_fl ctx_list =
  List.map (change_flow_into_ctx to_fl) ctx_list


and convert_must_failure_to_value (l:list_context) ante_flow conseq (bug_verified:bool): list_context =
  match l with
  | FailCtx (ft,c, cex) ->
    (match (get_must_es_msg_ft ft) with
     | Some (es,msg) ->
       begin
         match bug_verified with
         | true ->
           (*change flow to the flow at the beginning*)
           let new_ctx_lst = change_flow_into_ctx_list ante_flow [Ctx es] in
           SuccCtx new_ctx_lst
         | false ->
           (*update es_must_error*)
           SuccCtx [Ctx {es with es_must_error = Some (msg,ft,cex) } ]
       end
     | _ ->  l)
  | SuccCtx ctx_lst -> if not bug_verified then l else
      begin
        let es = empty_es (mkTrueFlow ()) Lab2_List.unlabelled no_pos in
        let fc_template = {
          fc_message = "INCONSISTENCY : expected failure but success instead";
          fc_current_lhs  =  empty_es (mkTrueFlow ()) Lab2_List.unlabelled no_pos;
          fc_prior_steps = [];
          fc_orig_conseq  = conseq;
          fc_current_conseq = mkTrue (mkTrueFlow()) no_pos;
          fc_failure_pts =  []} in
        let ft_template = (Basic_Reason (fc_template,
                                         mk_failure_must "INCONSISTENCY : expected failure but success instead" "", [])) in
        let new_ctx_lst = set_must_error_from_ctx ctx_lst "INCONSISTENCY : expected failure but success instead"
            ft_template (* (Ctx es) *) (mk_cex true) in
        SuccCtx new_ctx_lst
      end
(*23.10.2008*)

and compose_context_formula_norm_flow (ctx : context) (phi : formula) (x : CP.spec_var list)
    (force_sat:bool) flow_tr (pos : loc) : context =
  match ctx with
  | Ctx es -> begin
      if is_error_flow es.es_formula || is_mayerror_flow es.es_formula then ctx
      else
        match phi with
        | Or ({formula_or_f1 = phi1; formula_or_f2 =  phi2; formula_or_pos = _}) ->
          let new_c1 = compose_context_formula_norm_flow ctx phi1 x force_sat flow_tr pos in
          let new_c2 = compose_context_formula_norm_flow ctx phi2 x force_sat flow_tr pos in
          let res = (mkOCtx new_c1 new_c2 pos ) in
          res
        | _ -> let new_es_f,(* new_history, *)rho2 = x_add compose_formula_new es.es_formula phi x flow_tr (* es.es_history *) pos in
          Ctx {es with es_formula = new_es_f;
                       (* es_history = new_history; *)
                       (* es_subst_ref = rho2; *)
                       es_unsat_flag = (not force_sat) && es.es_unsat_flag;}
    end
  | OCtx (c1, c2) ->
    let new_c1 = compose_context_formula_norm_flow c1 phi x force_sat flow_tr pos in
    let new_c2 = compose_context_formula_norm_flow c2 phi x force_sat flow_tr pos in
    let res = (mkOCtx new_c1 new_c2 pos) in
    res

and compose_context_formula_x (ctx : context) (phi : formula) (x : CP.spec_var list)
    (force_sat:bool) flow_tr (pos : loc) : context =
  match ctx with
  | Ctx es -> begin
      match phi with
      | Or ({formula_or_f1 = phi1; formula_or_f2 =  phi2; formula_or_pos = _}) ->
        let new_c1 = compose_context_formula_x ctx phi1 x force_sat flow_tr pos in
        let new_c2 = compose_context_formula_x ctx phi2 x force_sat flow_tr pos in
        let res = (mkOCtx new_c1 new_c2 pos ) in
        res
      | _ -> let new_es_f,(* new_history, *)rho2 = x_add compose_formula_new es.es_formula phi x flow_tr (* es.es_history *) pos in
        Ctx {es with es_formula = new_es_f;
                     (* es_history = new_history; *)
                     (* es_subst_ref = rho2; *)
                     es_unsat_flag = (not force_sat) && es.es_unsat_flag;}
    end
  | OCtx (c1, c2) ->
    let new_c1 = compose_context_formula_x c1 phi x force_sat flow_tr pos in
    let new_c2 = compose_context_formula_x c2 phi x force_sat flow_tr pos in
    let res = (mkOCtx new_c1 new_c2 pos) in
    res


and compose_context_formula_d (ctx : context) (phi : formula) (x : CP.spec_var list) (force_sat:bool) flow_tr (pos : loc) : context =
  let pr1 = !print_context(*_short*) in
  let pr2 = !print_formula in
  let pr3 = !print_svl in
  Debug.no_3 "compose_context_formula" pr1 pr2 pr3 pr1
    (fun _ _ _ -> compose_context_formula_x ctx phi x force_sat flow_tr pos) ctx phi x

and compose_context_formula (ctx : context) (phi : formula) (x : CP.spec_var list) (force_sat:bool) flow_tr (pos : loc) : context =
  Gen.Profiling.do_1 "compose_context_formula" (compose_context_formula_d ctx phi x force_sat flow_tr) pos

(*TODO: expand simplify_context to normalize by flow type *)
(* and simplify_context_0 (ctx:context):context =  *)
(* 	if (allFalseCtx ctx) then ctx (\* (false_ctx (mkFalseFlow) no_pos) *\) *)
(* 								else  ctx *)

and normalize_es (f : formula) (pos : loc) (result_is_sat:bool) (es : entail_state): context =
  let pr = !print_formula in
  let pr_e = !print_entail_state in
  let pr_c = !print_context in
  Debug.no_2 "normalize_es" pr pr_e pr_c (fun _ _ -> normalize_es_x  f pos  result_is_sat es) f es


and normalize_es_x (f : formula) (pos : loc) (result_is_sat:bool) (es : entail_state): context =
  Ctx {es with es_formula = normalize 3 es.es_formula f pos; es_unsat_flag = es.es_unsat_flag&&result_is_sat}

and normalize_es_combine (f : formula) (result_is_sat:bool)(pos : loc) (es : entail_state): context =
  (* let () = print_string ("\nCformula.ml: normalize_es_combine") in *)
  Ctx {es with es_formula = normalize_combine es.es_formula f pos;
               es_unsat_flag = es.es_unsat_flag&&result_is_sat;}

and combine_and (f1:formula) (f2:MCP.mix_formula) :formula*bool = match f1 with
  | Or ({formula_or_f1 = o11; formula_or_f2 = o12; formula_or_pos = pos}) ->
    print_string ("malfunction: inner or has not been converted to a CtxOr!");
    Error.report_error {
      Error.error_loc = pos;
      Error.error_text = ("malfunction: inner or has not been converted to a CtxOr!") }
  | Base ({ formula_base_pure = p;} as b) ->
    let r1,r2 = (combine_and_pure f1 p f2) in
    (Base{b with formula_base_pure = r1;}, r2)
  | Exists ({formula_exists_qvars = evars;
             formula_exists_pure = p ;} as b) ->
    if (List.length (Gen.BList.intersect_eq (=) (MCP.mfv f2) evars))=0 then
      let r1,r2 = combine_and_pure f1 p f2 in
      (Exists {b with formula_exists_pure = r1;},r2)
    else
      let rf1 = rename_bound_vars f1 in
      (combine_and rf1 f2)

and normalize_no_rename_context_formula (ctx : context) (p : MCP.mix_formula) : context =
  let rec push_pure (f:formula):formula = match f with
    | Base b-> Base {b with formula_base_pure = x_add MCP.merge_mems p b.formula_base_pure true;}
    | Exists b -> Exists {b with formula_exists_pure = x_add MCP.merge_mems p b.formula_exists_pure true;}
    | Or b -> Or {
        formula_or_f1 = push_pure b.formula_or_f1;
        formula_or_f2 = push_pure b.formula_or_f2;
        formula_or_pos = b.formula_or_pos
      }in
  match ctx with
  | Ctx es -> Ctx {es with es_formula = push_pure es.es_formula;es_unsat_flag  =es.es_unsat_flag && MCP.isConstMTrue p;}
  | OCtx (c1, c2) ->
    let nc1 = normalize_no_rename_context_formula c1 p in
    let nc2 = normalize_no_rename_context_formula c2 p in
    let res = mkOCtx nc1 nc2 no_pos in
    res

(* -- 17.05.2008 *)
and normalize_clash_es (f : formula) (pos : loc) (result_is_sat:bool)(es:entail_state): context =
  let pr = !print_formula in
  let pr_e = !print_entail_state in
  let pr_c = !print_context in
  Debug.no_2 "normalize_clash_es" pr pr_e pr_c (fun _ _ -> normalize_clash_es_x  f pos  result_is_sat es) f es

and normalize_clash_es_x (f : formula) (pos : loc) (result_is_sat:bool)(es:entail_state): context =
  (* let () = print_string ("\nCformula.ml: normalize_clash_es") in *)
  match f with
  | Or ({formula_or_f1 = phi1; formula_or_f2 =  phi2; formula_or_pos = _}) ->
    let new_c1 = normalize_clash_es phi1 pos result_is_sat es in
    let new_c2 = normalize_clash_es phi2 pos result_is_sat es in
    let res = (mkOCtx new_c1 new_c2 pos) in
    res
  | _ ->
    let n_es_formula =
      if !Globals.enable_error_as_exc && is_en_error_exc es && (x_add_1 is_error_flow es.es_formula || x_add_1 is_mayerror_flow es.es_formula) then
        es.es_formula
      else
        normalize_only_clash_rename es.es_formula f pos
    in
    Ctx {es with es_formula = n_es_formula (* normalize_only_clash_rename es.es_formula f pos *); es_unsat_flag =es.es_unsat_flag&&result_is_sat}

(* 17.05.2008 -- *)

(* and formula_of_context ctx0 = match ctx0 with *)
(*   | OCtx (c1, c2) -> *)
(* 	  let f1 = formula_of_context c1 in *)
(* 	  let f2 = formula_of_context c2 in *)
(* 		mkOr f1 f2 no_pos *)
(*   | Ctx es -> es.es_formula *)

(*LDK: add es_pure into residue*)
and formula_of_context_x ctx0 = match ctx0 with
  | OCtx (c1, c2) ->
    let f1 = formula_of_context_x c1 in
    let f2 = formula_of_context_x c2 in
    mkOr f1 f2 no_pos
  | Ctx es ->
    (* let m = CP.mk_varperm_zero es.es_var_zero_perm no_pos in          *)
    (* let mix_f = x_add MCP.merge_mems es.es_pure (MCP.mix_of_pure m) true in *)
    let mix_f = es.es_pure in
    add_mix_formula_to_formula mix_f es.es_formula

and formula_of_context ctx0 =
  let pr = !print_context_short in
  Debug.no_1 "formula_of_context" pr !print_formula formula_of_context_x ctx0

(*LDK: add es_pure into residue*)
and formula_trace_of_context_x ctx0 = match ctx0 with
  | OCtx (c1, c2) ->
    let f1,trace1 = formula_trace_of_context_x c1 in
    let f2,trace2  = formula_trace_of_context_x c2 in
    let f = mkOr f1 f2 no_pos in
    let trace = trace1@["||OR||"]@trace2 in
    (f,trace)
  | Ctx es ->
    let orig_f = es.es_formula in
    let esvm = es.es_var_measures in  (* (term_ann * CP.exp list * CP.exp list) option;  *)
    (* let m = CP.mk_varperm_zero es.es_var_zero_perm no_pos in          *)
    (* let mix_f = x_add MCP.merge_mems es.es_pure (MCP.mix_of_pure m) true in *)
    let mix_f = es.es_pure in
    let mix_f = match esvm with
      | None -> mix_f
      | Some (ta,l1,l2) ->
        let m = CP.mkPure (CP.mkLexVar ta l1 l2 no_pos) in
        x_tinfo_hp (add_str "es_var_measures:" !CP.print_formula) m no_pos;
        x_add MCP.merge_mems mix_f (MCP.mix_of_pure m) true in
    (*TO CHECK*)
    let f = add_mix_formula_to_formula mix_f orig_f in
    let trace = es.es_trace in
    x_tinfo_hp (add_str "es_formula:" !print_formula) orig_f no_pos;
    x_tinfo_hp (add_str "es_pure:" !print_mix_formula) es.es_pure no_pos;
    (f,trace)

and formula_trace_of_context ctx0 =
  let pr = !print_context_short in
  let pr2 (f,_) = !print_formula f in
  Debug.no_1 "formula_trace_of_context" pr pr2 formula_trace_of_context_x ctx0

(* -- added 16.05.2008 *)
and formula_of_list_context (ctx : list_context) : formula =  match ctx with
  | FailCtx _ -> mkTrue (mkTrueFlow()) no_pos
  | SuccCtx ls -> List.fold_left (fun a c-> mkOr (formula_of_context c) a no_pos)
                    (mkFalse (mkTrueFlow ()) no_pos) ls
(* 16.05.2008 -- *)

and list_formula_of_list_context (ctx : list_context) : list_formula =  match ctx with
  | FailCtx _ -> []
  | SuccCtx ls -> List.map (formula_of_context) ls

and list_formula_trace_of_list_context (ctx : list_context) : (context * (formula*formula_trace)) list =  match ctx with
  | FailCtx _ -> []
  | SuccCtx ls -> List.map (fun c -> (c,formula_trace_of_context c)) ls

(* filter out partial failure first *)
and list_formula_of_list_partial_context (ls : list_partial_context) : list_formula =
  let ls = List.filter (fun (f,s) -> Gen.is_empty f) ls in
  List.map (formula_of_partial_context) ls

(* assumes that all are successes, may need to filter *)
and list_formula_of_list_failesc_context (ls : list_failesc_context) : list_formula =
  let ls = List.filter (fun (f,es,s) -> Gen.is_empty f) ls in
  List.map (formula_of_failesc_context) ls

and formula_of_list_partial_context (ls : list_partial_context) : formula =
  List.fold_left (fun a c-> mkOr (formula_of_partial_context c) a no_pos)
    (mkFalse (mkTrueFlow ()) no_pos) ls

and formula_of_list_failesc_context (ls : list_failesc_context) : formula =
  List.fold_left (fun a c-> mkOr (formula_of_failesc_context c) a no_pos)
    (mkFalse (mkTrueFlow ()) no_pos) ls

(* below ignored the escaping state! *)
and formula_of_failesc_context ((_,_,sl) : failesc_context) : formula =
  List.fold_left (fun a (_,c, _)-> mkOr (formula_of_context c) a no_pos)
    (mkFalse (mkTrueFlow ()) no_pos) sl

and formula_of_partial_context ((fl,sl) : partial_context) : formula =
  List.fold_left (fun a (_,c,_)-> mkOr (formula_of_context c) a no_pos)
    (mkFalse (mkTrueFlow ()) no_pos) sl

and disj_count_ctx (ctx0 : context) = match ctx0 with
  | OCtx (c1, c2) ->
    let t1 = disj_count_ctx c1 in
    let t2 = disj_count_ctx c2 in
    1 + t1 + t2
  | Ctx es -> disj_count es.es_formula

(*
and find_type_var (tc : h_formula) (v : ident) : CP.spec_var option = match tc with
  | Star ({h_formula_star_h1 = h1;
		   h_formula_star_h2 = h2}) -> begin
	  let tmp1 = find_type_var h1 v in
		match tmp1 with
		  | Some _ -> tmp1
		  | None -> find_type_var h2 v
	end
  | DataNode ({h_formula_data_arguments = args}) -> Some (List.hd args)
  | ViewNode _ | HTrue | HFalse -> None
*)

let rec set_flow_in_context_override f_f ctx = match ctx with
  | Ctx es -> Ctx {es with es_formula = (set_flow_in_formula_override f_f es.es_formula)}
  | OCtx (c1,c2) -> OCtx ((set_flow_in_context_override f_f c1),(set_flow_in_context_override f_f c2))



(* order nodes in topological order *)

module Node = struct
  type t = h_formula
  let compare = compare
  let hash = Hashtbl.hash
  let equal = (=)
end

module NG = Graph.Imperative.Digraph.Concrete(Node)
module TopoNG = Graph.Topological.Make(NG)

(*
  return the same formula with nodes rearranged in topological
  order based on the points-to relation of the heap nodes.
*)
(*
let topologize_formula (h0 : h_formula) : h_formula =
  let g = NG.create () in
*)

(*************************************************************************************************************************
   	05.06.2008:
   	Utilities for existential quantifier elimination:
   	- before we were only searching for substitutions of k form v1 = v2 and then substitute ex v1. P(v1) --> P(v2)
   	- now, we want to be more aggressive and search for substitutions of the form v1 = exp2; however, we can only apply these substitutions to the pure part
   	(due to the way shape predicates are recorded --> root pointer and args are suppose to be spec vars)
 *************************************************************************************************************************)
let rec subst_exp_x sst (f : formula) = match sst with
  | s :: rest ->
    let new_f = subst_exp_x rest (apply_one_exp s f) in
    (*let fv_new_f = fv new_f in
      		 	if List.mem (fst s) fv_new_f then
      		 		let f = add_quantifiers [(fst s)] new_f in
      		 		let qvars, base_f = split_quantifiers f in
      		 		let h, p, t = split_components base_f in
      		 	 		mkExists qvars h (CP.mkAnd p (CP.mkEqExp (CP.mkVar (fst s) no_pos) (snd s) no_pos) no_pos) t no_pos
      			else*) new_f
  | [] -> f

and subst_exp sst (f : formula) =
  let pr1 = !print_formula in
  let pr2 = pr_pair !CP.print_sv !CP.print_exp in
  Debug.no_2 "subst_exp" (pr_list pr2) pr1 pr1
  subst_exp_x sst f

and subst_var_exp (fr, t) (o : CP.spec_var) =
  if CP.eq_spec_var fr o then t else o

and apply_one_exp_one_formula ((fr, t) as s : (CP.spec_var * CP.exp)) (f : one_formula) =
  let df = f.formula_delayed in
  let ndf = MCP.memo_apply_one_exp (fr, t) df in
  let base = formula_of_one_formula f in
  let rs = apply_one_exp s base in (*TO CHECK: how about formula_thread*)
  let one_f = (one_formula_of_formula rs f.formula_thread ndf) in
  {one_f with formula_ref_vars = f.formula_ref_vars}

and apply_one_exp ((fr, t) as s : (CP.spec_var * CP.exp)) (f : formula) = match f with
  | Or ({ formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos }) ->
    Or ({ formula_or_f1 = apply_one_exp s f1; formula_or_f2 = apply_one_exp s f2; formula_or_pos = pos })
  | Base ({
      formula_base_heap = h;
      formula_base_pure = p;
      formula_base_vperm = vp;
      formula_base_type = t;
      formula_base_and = a;
      formula_base_flow = fl;
      formula_base_label = lbl;
      formula_base_pos = pos }) ->
    Base ({
        formula_base_heap = h;
        formula_base_vperm = vp;
        formula_base_pure = MCP.memo_apply_one_exp s p;
        formula_base_and = List.map (apply_one_exp_one_formula s) a;
        formula_base_flow = fl;
        formula_base_type = t;
        formula_base_label = lbl;
        formula_base_pos = pos})
  | Exists ({
      formula_exists_qvars = qsv;
      formula_exists_heap = qh;
      formula_exists_vperm = vp;
      formula_exists_pure = qp;
      formula_exists_type = tconstr;
      formula_exists_and = a;
      formula_exists_flow = fl;
      formula_exists_label = lbl;
      formula_exists_pos = pos }) ->
    if List.mem (CP.name_of_spec_var fr) (List.map CP.name_of_spec_var qsv) then f
    else
      Exists ({
          formula_exists_qvars = qsv;
          formula_exists_heap =  qh;
          formula_exists_vperm = vp;
          formula_exists_pure = MCP.memo_apply_one_exp s qp;
          formula_exists_type = tconstr;
          formula_exists_and = List.map (apply_one_exp_one_formula s) a;
          formula_exists_flow = fl;
          formula_exists_label = lbl;
          formula_exists_pos = pos })

let rec struc_to_formula_gen (f:struc_formula):(formula*formula_label option list) list =
  let rec get_label_f f = match f with
    | Or b-> (get_label_f b.formula_or_f1)@(get_label_f b.formula_or_f2)
    | Base{formula_base_label = l}| Exists{formula_exists_label = l} -> [l]in
  match f with
  | ECase b->
    let r = List.concat (List.map
                           (fun (c1,c2)->
                              if (isConstEFalse c2) then []
                              else
                                let np = (MCP.memoise_add_pure_N (MCP.mkMTrue b.formula_case_pos) c1) in
                                let npf = mkBase HEmp np CVP.empty_vperm_sets TypeTrue (mkTrueFlow ()) [] b.formula_case_pos in
                                let l = struc_to_formula_gen c2 in
                                List.map (fun (c1,c2) -> (normalize_combine npf c1 no_pos,c2)) l) b.formula_case_branches) in
    (* List.map (fun (c1,c2)-> ( push_exists b.formula_case_exists c1,c2)); *) r
  | EBase b->
    let nf,nl = b.formula_struc_base,(get_label_f b.formula_struc_base) in
    let f c = push_exists b.formula_struc_exists (normalize_combine nf c b.formula_struc_pos) in
    let lc = fold_opt struc_to_formula_gen b.formula_struc_continuation in
    (match lc with
     | [] -> [(f nf, nl)]
     | _ -> List.map (fun (c1,c2)-> (f c1,nl@c2)) lc)
  | EAssume b-> [(b.formula_assume_simpl,[None])]
  | EInfer b -> struc_to_formula_gen b.formula_inf_continuation
  | EList b -> fold_l_snd struc_to_formula_gen b

(* let struc_to_formula f0 :formula = formula_of_disjuncts (fst (List.split (struc_to_formula_gen f0))) *)
(* TO-CHECK : why is above overridden *)
let mkOr_pure f1 f2 pos =
  if isStrictConstTrue f1 || isStrictConstTrue f2 then
    mkTrue (mkTrueFlow ()) pos
  else if isAnyConstFalse f1 then f2
  else if isAnyConstFalse f2 then f1
  else
    match f1,f2 with
    | Base b1,Base b2 ->
      if b1.formula_base_heap = b2.formula_base_heap then
        Base {b1 with formula_base_pure =
                        MCP.mkOr_mems b1.formula_base_pure b2.formula_base_pure}
      else
        Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos})
    | _,_ ->
      Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos})

let disj_of_list_pure (xs : formula list) pos : formula =
  let rec helper xs r = match xs with
    | [] -> r
    | x::xs -> mkOr_pure x (helper xs r) pos
  in
  match xs with
  | [] -> mkTrue (mkTrueFlow ()) pos
  | x::xs -> helper xs x

let rec split_conjuncts (f:formula):formula list = match f with
  | Or b -> (split_conjuncts b.formula_or_f1)@(split_conjuncts b.formula_or_f2)
  | _ -> [f]

let list_of_disjuncts f = split_conjuncts f

let join_conjunct_opt l = match l with
  | [] -> None
  | h::t -> Some (List.fold_left (fun a c -> mkOr c a no_pos) h t)

let join_star_conjunctions (hs : h_formula list) : h_formula  =
  List.fold_left (fun a c-> mkStarH a c no_pos ) HEmp hs

let join_star_conjunctions_opt_x (hs : h_formula list) : (h_formula option)  =
  match hs with
  | [] -> None
  | x::xs -> Some (List.fold_left (fun a c -> mkStarH a c no_pos  ) x xs)


let join_star_conjunctions_opt (hs : h_formula list) : (h_formula option)  =
  let rec pr1 xs =
    match xs with
    | [] -> ""
    | x::xs1 -> (!print_h_formula x) ^ "|*|" ^ pr1 xs1
  in
  let pr2 = pr_option !print_h_formula in
  Debug.no_1 "join_star_conjunctions_opt" pr1 pr2
    join_star_conjunctions_opt_x hs

let split_all_conjunctions (f:h_formula) : (h_formula list) =
  let rec helper f =
    match f with
    | Star({h_formula_star_h1 = h1;
            h_formula_star_h2 = h2;})
    | StarMinus({h_formula_starminus_h1 = h1;
                 h_formula_starminus_h2 = h2;})
    | Conj({h_formula_conj_h1 = h1;
            h_formula_conj_h2 = h2;}) ->
      let res1 = helper h1 in
      let res2 = helper h2 in
      (res1@res2)
    | _ -> [f]
  in helper f

let split_star_conjunctions (f:h_formula): (h_formula list) =
  let rec helper f =
    match f with
    | Star({h_formula_star_h1 = h1;
            h_formula_star_h2 = h2;
            h_formula_star_pos = pos;}) ->
      let res1 = helper h1 in
      let res2 = helper h2 in
      (res1@res2)
    | _ -> [f]
  in
  helper f

let split_star_conjunctions (f:h_formula): (h_formula list) =
  let rec pr xs =
    match xs with
    | [] -> ""
    | x::xs1 -> (!print_h_formula x) ^ "|*|" ^ pr xs1
  in
  Debug.no_1 "split_star_conjunctions" !print_h_formula pr
    split_star_conjunctions f

let type_of_formula (f: formula) : formula_type =
  if (isAnyConstFalse f) then Simple
  else match f with
    | Base b  ->
      let h = b.formula_base_heap in
      let hs = split_star_conjunctions h in
      if ((List.length hs)>1) then Complex
      else Simple
    | Exists e ->
      let h = e.formula_exists_heap in
      let hs = split_star_conjunctions h in
      if ((List.length hs)>1) then Complex
      else Simple
    | _ -> Complex


let type_of_formula (f: formula) : formula_type =
  let pr1 = !print_formula in
  let pr2 = !print_formula_type in
  Debug.no_1 "type_of_formula" pr1 pr2 type_of_formula f

let struc_to_view_un_s (f0:struc_formula):(formula*formula_label) list =
  let ifo = (struc_to_formula_gen f0) in
  List.map (fun (c1,c2)->
      let c2 = List.fold_left (fun a c2-> match c2 with | None -> a | Some s-> s::a) [] c2 in
      match c2 with
      | [x] -> (c1,x)
      (* | []  -> (c1,fresh_formula_label "") (\* andreea: To check if this is correct *\) *)
      | _ ->  Err.report_error {Err.error_loc = no_pos;  Err.error_text = " mismatch in view labeling \n"} ) ifo

let struc_to_view_un_s (f0:struc_formula):(formula*formula_label) list =
  let pr1 = !print_struc_formula in
  let pr2 = pr_list (pr_pair !print_formula !print_formula_label) in
  Debug.no_1 "struc_to_view_un_s" pr1 pr2  struc_to_view_un_s f0

(* proc will convert implicit/explicit vars to existential *)
let rec struc_to_formula_x (f:struc_formula):formula = match f with
  | ECase b->
    let r =
      if (List.length b.formula_case_branches) >0 then
        List.fold_left (fun a (c1,c2)->
            if (isConstEFalse c2) then a
            else
              let c1 = MCP.memoise_add_pure_N (MCP.mkMTrue no_pos) c1 in
              (mkOr a (normalize_combine (mkBase HEmp c1 CVP.empty_vperm_sets TypeTrue (mkTrueFlow ()) [] b.formula_case_pos ) (struc_to_formula_x c2) b.formula_case_pos)
                 b.formula_case_pos) ) (mkFalse (mkFalseFlow) b.formula_case_pos) b.formula_case_branches
      else mkTrue (mkTrueFlow ()) b.formula_case_pos in
    (* push_exists b.formula_case_exists *) r
  | EBase b->
    let e = match b.formula_struc_continuation with
      | Some e -> normalize_combine b.formula_struc_base (struc_to_formula_x e) b.formula_struc_pos
      | None -> b.formula_struc_base in
    (* is it necessary to also push the implicit vars? *)
    push_exists (b.formula_struc_explicit_inst@b.formula_struc_implicit_inst@b.formula_struc_exists) e
  | EAssume b -> b.formula_assume_simpl
  | EInfer b -> struc_to_formula_x b.formula_inf_continuation
  | EList b -> formula_of_disjuncts (fold_l_snd (fun c-> [struc_to_formula_x c]) b)

and struc_to_formula f0 :formula =
  let pr1 = !print_struc_formula in
  let pr2 = !print_formula in
  Debug.no_1 "struc_to_formula" pr1 pr2 struc_to_formula_x f0

let rec normalize_struc cont base: struc_formula = match cont with
  | ECase b ->
    ECase {b with formula_case_branches =
                    List.map (fun (p,c) -> (p, normalize_struc c base)) b.formula_case_branches}
  | EBase b ->
    let new_base = normalize_combine base.formula_struc_base b.formula_struc_base base.formula_struc_pos in
    EBase {b with formula_struc_base = new_base}
  (* (match b.formula_struc_continuation with *)
  (*   | None -> EBase base *)
  (*   | Some c -> normalize_struc c {b with formula_struc_base = new_base}) *)
  | EAssume _ -> EBase base
  | EInfer b ->
    EInfer {b with formula_inf_continuation = normalize_struc b.formula_inf_continuation base}
  | EList b -> EList (List.map (fun (l,c) -> (l,normalize_struc c base)) b)

(* Convert struc_formula to pre/post structure *)
let rec struc_to_prepost_x (f:struc_formula): struc_formula = match f with
  | ECase b ->
    ECase {b with formula_case_branches =
                    List.map (fun (p,c) -> (p, struc_to_prepost_x c)) b.formula_case_branches}
  | EBase b ->
    let new_b = match b.formula_struc_continuation with
      | None -> f
      | Some c -> normalize_struc c b
    in
    new_b
  | EAssume _ -> f
  | EInfer b -> EInfer {b with formula_inf_continuation = struc_to_prepost b.formula_inf_continuation}
  | EList b -> EList (List.map (fun (l,c) -> (l,struc_to_prepost_x c)) b)

and struc_to_prepost f0 : struc_formula =
  let pr = !print_struc_formula in
  Debug.no_1 "struc_to_prepost" pr pr struc_to_prepost_x f0

(* An Hoa : construct pre-condition from a structured spec formula *)
let rec struc_to_precond_formula (f : struc_formula) : formula = match f with
  | ECase b ->
    let fold_function a (c1, c2) = if (isConstEFalse c2) then a
      else
        let c1 = MCP.memoise_add_pure_N (MCP.mkMTrue no_pos) c1 in
        (mkOr a (normalize_combine (mkBase HEmp c1 CVP.empty_vperm_sets TypeTrue (mkTrueFlow ()) [] b.formula_case_pos) (struc_to_precond_formula c2) b.formula_case_pos)
           b.formula_case_pos) in
    let r = if (List.length b.formula_case_branches) >0 then
        List.fold_left fold_function (mkFalse (mkFalseFlow) b.formula_case_pos) b.formula_case_branches
      else mkTrue (mkTrueFlow ()) b.formula_case_pos in
    (* push_exists b.formula_case_exists *) r
  | EBase b ->
    let e = match b.formula_struc_continuation with
      | None -> b.formula_struc_base
      | Some e-> normalize_combine b.formula_struc_base (struc_to_precond_formula e) b.formula_struc_pos in
    push_exists (b.formula_struc_explicit_inst@b.formula_struc_implicit_inst@b.formula_struc_exists) e
  | EAssume _ -> (* Eliminate assume by making it true *) formula_of_heap HEmp no_pos
  | EInfer b -> struc_to_precond_formula b.formula_inf_continuation
  | EList b -> formula_of_disjuncts (fold_l_snd (fun c-> [struc_to_precond_formula c]) b)
(* An Hoa : end of pre-condition construction *)

and s_formula_to_struc (f:formula):struc_formula =
    EBase {
        formula_struc_explicit_inst =[];
        formula_struc_implicit_inst = [];
        formula_struc_exists = [];
        formula_struc_base = f;
        formula_struc_is_requires = false;
        formula_struc_continuation = None;
        formula_struc_pos = pos_of_formula f}

and s_formula_of_struc (f:struc_formula):formula =
  match f with
  |  EBase { formula_struc_base = f} -> f
  | _ -> failwith "struc formula insnot simple"

and formula_to_struc_formula (f:formula):struc_formula =
  let rec helper (f:formula):struc_formula = match f with
    | Base b-> EBase {
        formula_struc_explicit_inst =[];
        formula_struc_implicit_inst = [];
        formula_struc_exists = [];
        formula_struc_base = f;
        formula_struc_is_requires = false;
        formula_struc_continuation = None;
        formula_struc_pos = b.formula_base_pos}
    | Exists b-> EBase {
        formula_struc_explicit_inst =[];
        formula_struc_implicit_inst = [];
        formula_struc_exists = [];
        formula_struc_base = f;
        formula_struc_is_requires = false;
        formula_struc_continuation = None;
        formula_struc_pos = b.formula_exists_pos}
    | Or b-> mkEList_flatten [helper b.formula_or_f1; helper b.formula_or_f2] in
  (helper f)

and plug_ref_vars (w:Cpure.spec_var list) (f:struc_formula) :struc_formula =
  let rec filter_quantifiers w f = match f with
    | Base _ -> f
    | Exists b -> Exists {b with formula_exists_qvars = Gen.BList.difference_eq (=) b.formula_exists_qvars w;}
    | Or b -> Or {b with
                  formula_or_f1 = filter_quantifiers w b.formula_or_f1;
                  formula_or_f2 = filter_quantifiers w b.formula_or_f2;}in
  let rec filter_quantifiers_struc w f = match f with
    | EBase b -> EBase {b with
                        formula_struc_base = filter_quantifiers w b.formula_struc_base;
                        formula_struc_exists = Gen.BList.difference_eq (=) b.formula_struc_exists w;
                        formula_struc_continuation = map_opt (filter_quantifiers_struc w) b.formula_struc_continuation;}
    | ECase b -> ECase {b with formula_case_branches = map_l_snd (filter_quantifiers_struc w) b.formula_case_branches;}
    | _ -> f in
  match f with
  | EAssume b->  EAssume { b with
                           formula_assume_simpl = filter_quantifiers w b.formula_assume_simpl;
                           formula_assume_vars = w;
                           formula_assume_struc = filter_quantifiers_struc w b.formula_assume_struc;}
  | ECase b -> ECase {b with formula_case_branches = map_l_snd (plug_ref_vars w) b.formula_case_branches;}
  | EBase b -> EBase {b with formula_struc_continuation = map_opt (plug_ref_vars w) b.formula_struc_continuation}
  | EInfer b -> EInfer {b with formula_inf_continuation = plug_ref_vars w b.formula_inf_continuation}
  | EList b -> EList (map_l_snd (plug_ref_vars w) b)


and count_or c = match c with
  | Ctx _ -> 1
  | OCtx (c1,c2) -> (count_or c1)+(count_or c2)

and find_false_ctx ctx pos =
  match ctx with
  | FailCtx _ -> ()
  | SuccCtx ctx ->
    if (List.exists isAnyFalseCtx ctx) then
      false_ctx_line_list := Gen.BList.remove_dups_eq (=) (pos::!false_ctx_line_list) else ()

and find_false_list_failesc_ctx (ctx:list_failesc_context) pos =
  if (List.exists isAnyFalseFailescCtx ctx) then
    false_ctx_line_list := Gen.BList.remove_dups_eq (=) (pos::!false_ctx_line_list)
  else ()


and guard_vars (f:struc_formula) =
  let rdv = Gen.BList.remove_dups_eq (=) in
  match f with
  | ECase b-> rdv (List.fold_left (fun a (c1,c2)-> a@(Cpure.fv c1)@(guard_vars c2)) [] b.formula_case_branches)
  | EBase b -> Gen.BList.difference_eq (=) (fold_opt guard_vars b.formula_struc_continuation) b.formula_struc_exists
  | EAssume _-> []
  | EInfer b -> guard_vars b.formula_inf_continuation
  | EList b-> rdv (fold_l_snd guard_vars b)

and set_unsat_flag (ctx:context) (nf:bool):context = match ctx with
  | OCtx(c1,c2)-> OCtx ((set_unsat_flag c1 nf),(set_unsat_flag c2 nf))
  | Ctx c-> Ctx {c with es_unsat_flag = nf}

and filter_heap (f:formula):formula option = match f with
  | Or b-> begin
      match (filter_heap b.formula_or_f1) with
      | None -> None (*(filter_heap b.formula_or_f2)*)
      | Some d1-> match (filter_heap b.formula_or_f2) with
        | None -> None
        | Some d2 -> Some (mkOr d1 d2 b.formula_or_pos)
    end
  | Base b-> begin
      match b.formula_base_heap with
      | Star _
      | StarMinus _
      | Conj _
      | ConjStar _
      | ConjConj _
      | Phase _
      | DataNode _
      | ViewNode _
      | ThreadNode _
      | HRel _ (*vp*)
      | Hole _ | FrmHole _ -> None
      | HTrue
      | HFalse
      | HEmp | HVar _ (* TODO;HO *)
        -> Some f
    end
  | Exists b->
    begin
      match b.formula_exists_heap with
      | Star _
      | StarMinus _
      | Conj _
      | ConjStar _
      | ConjConj _
      | Phase _
      | DataNode _
      | ViewNode _
      | ThreadNode _
      | HRel _ (*vp*)
      | Hole _ | FrmHole _ -> None
      | HTrue
      | HFalse
      | HEmp | HVar _-> Some f
    end

and set_es_evars (c:context)(v:Cpure.spec_var list):context =
  match c with
  | OCtx (c1,c2)-> OCtx ((set_es_evars c1 v),(set_es_evars c2 v))
  | Ctx e -> Ctx {e with es_evars = v}


and case_to_disjunct f  =
  let pr = !print_struc_formula in
  Debug.no_1 "case_to_disjunct" pr pr case_to_disjunct_x f

and case_to_disjunct_x (f:struc_formula):struc_formula  =
  let rec push_pure_x c (f:struc_formula):struc_formula =  match f with
    | ECase _ -> f (*this should never occur*)
    | EBase b-> EBase {b with formula_struc_base =
                                normalize_combine
                                  b.formula_struc_base
                                  (formula_of_pure_N c no_pos)
                                  no_pos}
    | EList b -> EList (map_l_snd (push_pure_x c) b)
    | _ ->  EBase {
        formula_struc_explicit_inst = [];
        formula_struc_implicit_inst = [];
        formula_struc_exists = [];
        formula_struc_base = formula_of_pure_N c no_pos;
        formula_struc_is_requires = true;
        formula_struc_continuation = Some f;
        formula_struc_pos = no_pos;}
  in
  let push_pure c f = Debug.no_2 "push_pure" !print_pure_f !print_struc_formula !print_struc_formula push_pure_x c f in
  match f with
  | ECase b->
    let l = List.map (fun (c1,c2)-> push_pure c1 (case_to_disjunct_x c2)) b.formula_case_branches in
    (match l with
     | [] -> failwith "unexpected empty case struc"
     | _ -> mkEList_flatten l)
  | EBase b-> EBase {b with formula_struc_continuation = map_opt case_to_disjunct_x b.formula_struc_continuation}
  | EList b -> EList (map_l_snd case_to_disjunct_x b)
  | _ -> f

(* start label - can be simplified *)
let get_start_label ctx = match ctx with
  | FailCtx _ -> ""
  | SuccCtx sl ->
    let rec helper c= match c with
      | Ctx e -> if (List.length e.es_path_label)==0 then "" else snd(fst (Gen.BList.list_last e.es_path_label))
      | OCtx (c1,c2) -> helper c1 in
    helper (List.hd sl)

let get_start_partial_label (ctx:list_partial_context) =
  let rec helper c= match c with
    | Ctx e -> if (List.length e.es_path_label)==0 then "" else snd(fst (Gen.BList.list_last e.es_path_label))
    | OCtx (c1,c2) -> helper c1 in
  let pc = List.hd ctx in
  if (rank pc) < 1. then ""
  else let (_,ls) = pc in
    (* helper (snd (List.hd ls)) *)
    let _,ctx, _ = (List.hd ls) in
    helper (ctx)


let rec replace_heap_formula_label nl f = match f with
  | Star b -> Star {b with
                    h_formula_star_h1 = replace_heap_formula_label nl b.h_formula_star_h1;
                    h_formula_star_h2 = replace_heap_formula_label nl b.h_formula_star_h2; }
  | StarMinus b -> StarMinus {b with
                              h_formula_starminus_h1 = replace_heap_formula_label nl b.h_formula_starminus_h1;
                              h_formula_starminus_h2 = replace_heap_formula_label nl b.h_formula_starminus_h2; }
  | Phase b -> Phase {b with
                      h_formula_phase_rd = replace_heap_formula_label nl b.h_formula_phase_rd;
                      h_formula_phase_rw = replace_heap_formula_label nl b.h_formula_phase_rw; }
  | Conj b -> Conj {b with
                    h_formula_conj_h1 = replace_heap_formula_label nl b.h_formula_conj_h1;
                    h_formula_conj_h2 = replace_heap_formula_label nl b.h_formula_conj_h2; }
  | ConjStar b -> ConjStar {b with
                            h_formula_conjstar_h1 = replace_heap_formula_label nl b.h_formula_conjstar_h1;
                            h_formula_conjstar_h2 = replace_heap_formula_label nl b.h_formula_conjstar_h2; }
  | ConjConj b -> ConjConj {b with
                            h_formula_conjconj_h1 = replace_heap_formula_label nl b.h_formula_conjconj_h1;
                            h_formula_conjconj_h2 = replace_heap_formula_label nl b.h_formula_conjconj_h2; }
  | DataNode b -> DataNode {b with h_formula_data_label = (nl ())}
  | ViewNode b -> ViewNode {b with h_formula_view_label = (nl ())}
  | ThreadNode b -> ThreadNode {b with h_formula_thread_label = (nl ())}
  | HRel (r, args, pos) -> HRel(r, args, pos) (*vp*)
  | HTrue
  | HFalse
  | HEmp
  | Hole _ | FrmHole _ | HVar _ -> f

and replace_formula_label1 nl f = match f with
  | Base b->Base {b with
                  formula_base_heap = replace_heap_formula_label nl b.formula_base_heap ;
                  formula_base_pure = MCP.replace_mix_formula_label nl b.formula_base_pure ;}
  | Exists b->Exists {b with
                      formula_exists_heap = replace_heap_formula_label nl b.formula_exists_heap ;
                      formula_exists_pure = MCP.replace_mix_formula_label nl b.formula_exists_pure ;}
  | Or b -> Or {b with
                formula_or_f1 = replace_formula_label1 nl b.formula_or_f1;
                formula_or_f2 = replace_formula_label1 nl b.formula_or_f2;	}

let rec replace_struc_formula_label1 nl f =  match f with
  | EBase b -> EBase {b with
                      formula_struc_base = replace_formula_label1 nl b.formula_struc_base;
                      formula_struc_continuation = map_opt (replace_struc_formula_label1 nl) b.formula_struc_continuation}
  | ECase b ->
    let new_br = List.map
        (fun (c1,c2)->
           ((CP.replace_pure_formula_label nl c1), (replace_struc_formula_label1 nl c2))
        ) b.formula_case_branches in
    ECase { b with formula_case_branches = new_br;}
  | EAssume b-> EAssume {b with
                         formula_assume_simpl = replace_formula_label1 nl b.formula_assume_simpl;
                         formula_assume_struc = replace_struc_formula_label1 nl b.formula_assume_struc;}
  | EInfer b -> EInfer {b with formula_inf_continuation = replace_struc_formula_label1 nl b.formula_inf_continuation}
  | EList b -> EList (map_l_snd (replace_struc_formula_label1 nl) b)


and replace_struc_formula_label nl f = replace_struc_formula_label1 (fun c -> nl) f
and replace_struc_formula_label_fresh f = replace_struc_formula_label1 (fun c -> (fresh_branch_point_id "")) f
and replace_formula_label nl f = replace_formula_label1 (fun c -> nl) f
and replace_formula_label_fresh f = replace_formula_label1 (fun c -> (fresh_branch_point_id "")) f

and residue_labels_in_formula f =
  let rec residue_labels_in_heap f = match f with
    | Star b -> (residue_labels_in_heap b.h_formula_star_h1) @ (residue_labels_in_heap b.h_formula_star_h2)
    | StarMinus b -> (residue_labels_in_heap b.h_formula_starminus_h1) @ (residue_labels_in_heap b.h_formula_starminus_h2)
    | Conj b -> (residue_labels_in_heap b.h_formula_conj_h1) @ (residue_labels_in_heap b.h_formula_conj_h2)
    | ConjStar b -> (residue_labels_in_heap b.h_formula_conjstar_h1) @ (residue_labels_in_heap b.h_formula_conjstar_h2)
    | ConjConj b -> (residue_labels_in_heap b.h_formula_conjconj_h1) @ (residue_labels_in_heap b.h_formula_conjconj_h2)
    | Phase b -> (residue_labels_in_heap b.h_formula_phase_rd) @ (residue_labels_in_heap b.h_formula_phase_rw)
    | DataNode b -> (match b.h_formula_data_label with Some s-> [s] | _ -> [])
    | ViewNode b -> (match b.h_formula_view_label with Some s-> [s] | _ -> [])
    | ThreadNode b -> (match b.h_formula_thread_label with Some s-> [s] | _ -> [])
    | HRel _
    | HTrue
    | HFalse
    | HEmp
    | Hole _ | FrmHole _ | HVar _ -> []
  in match f with
  | Base b-> residue_labels_in_heap b.formula_base_heap
  | Exists b->residue_labels_in_heap b.formula_exists_heap
  | Or b -> (residue_labels_in_formula b.formula_or_f1) @ (residue_labels_in_formula b.formula_or_f2)

let get_node_label n =  match n with
  | DataNode b -> b.h_formula_data_label
  | ViewNode b -> b.h_formula_view_label
  | _ -> None


(* generic transform for heap formula *)
let trans_h_formula (e2:h_formula) (arg:'a) (f:'a->h_formula->(h_formula * 'b) option)
    (f_args:'a->h_formula->'a)(f_comb:'b list -> 'b) :(h_formula * 'b) =
  let rec helper (e:h_formula) (arg:'a) =
    let pr = !print_h_formula in
    (* let () = x_tinfo_hp (add_str "helper" pr) e no_pos in *)
    let r =  f arg e in
    match r with
    | Some (e1,v) -> (e1,v)
    | None  -> let new_arg = f_args arg e in
      match e with
      | Star s ->
        let (e1,r1)=helper s.h_formula_star_h1 new_arg in
        let (e2,r2)=helper s.h_formula_star_h2 new_arg in
        (* let () = x_tinfo_hp (add_str "star(h1)" pr) e1 no_pos in *)
        (* let () = x_tinfo_hp (add_str "star(h2)" pr) e2 no_pos in *)
        let newhf = (match e1,e2 with
            (* | (HEmp,HEmp) -> HEmp *)
            | (HEmp,_) -> e2
            | (_,HEmp) -> e1
            | (HFalse,_) -> HFalse
            | (_,HFalse) -> HFalse
            | (HTrue,HTrue) -> HTrue
            | _ -> Star {s with h_formula_star_h1 = e1;
                                h_formula_star_h2 = e2;})
        in (newhf, f_comb [r1;r2])
      | StarMinus s ->
        let (e1,r1)=helper s.h_formula_starminus_h1 new_arg in
        let (e2,r2)=helper s.h_formula_starminus_h2 new_arg in
        (StarMinus {s with h_formula_starminus_h1 = e1;
                           h_formula_starminus_h2 = e2;},f_comb [r1;r2])
      | Conj s ->
        let (e1,r1)=helper s.h_formula_conj_h1 new_arg in
        let (e2,r2)=helper s.h_formula_conj_h2 new_arg in
        (Conj {s with h_formula_conj_h1 = e1;
                      h_formula_conj_h2 = e2;},f_comb [r1;r2])
      | ConjStar s ->
        let (e1,r1)=helper s.h_formula_conjstar_h1 new_arg in
        let (e2,r2)=helper s.h_formula_conjstar_h2 new_arg in
        (ConjStar {s with h_formula_conjstar_h1 = e1;
                          h_formula_conjstar_h2 = e2;},f_comb [r1;r2])
      | ConjConj s ->
        let (e1,r1)=helper s.h_formula_conjconj_h1 new_arg in
        let (e2,r2)=helper s.h_formula_conjconj_h2 new_arg in
        (ConjConj {s with h_formula_conjconj_h1 = e1;
                          h_formula_conjconj_h2 = e2;},f_comb [r1;r2])
      | Phase s ->
        let (e1,r1)=helper s.h_formula_phase_rd new_arg in
        let (e2,r2)=helper s.h_formula_phase_rw new_arg in
        (Phase {s with h_formula_phase_rd = e1;
                       h_formula_phase_rw = e2;},f_comb [r1;r2])
      | DataNode _
      | ViewNode _
      | ThreadNode _
      | HRel _
      | Hole _ | FrmHole _
      | HTrue
      | HFalse
      | HEmp | HVar _ -> (e, f_comb [])
  in (helper e2 arg)

let map_h_formula_args (e:h_formula) (arg:'a) (f:'a -> h_formula -> h_formula option) (f_args: 'a -> h_formula -> 'a) : h_formula =
  let f1 ac e = push_opt_void_pair (f ac e) in
  fst (trans_h_formula e arg f1 f_args voidf)

(*this maps an expression without passing an argument*)
let map_h_formula (e:h_formula) (f:h_formula->h_formula option) : h_formula =
  map_h_formula_args e () (fun _ e -> f e) idf2


(*this computes a result from expression passing an argument*)
let fold_h_formula_args (e:h_formula) (init_a:'a) (f:'a -> h_formula-> 'b option) (f_args: 'a -> h_formula -> 'a) (comb_f: 'b list->'b) : 'b =
  let f1 ac e = match (f ac e) with
    | Some r -> Some (e,r)
    | None ->  None in
  snd(trans_h_formula e init_a f1 f_args comb_f)

(*this computes a result from expression without passing an argument*)
let fold_h_formula (e:h_formula) (f:h_formula-> 'b option) (comb_f: 'b list->'b) : 'b =
  fold_h_formula_args e () (fun _ e-> f e) voidf2 comb_f

let keep_hrel_x e =
  let f hf = match hf with
    | HRel _ -> Some [hf]
    | _ -> None
  in
  fold_h_formula e f List.concat

let keep_hrel e=
  let pr1 = !print_h_formula in
  Debug.no_1 "keep_hrel" pr1 (pr_list pr1)
    (fun _ -> keep_hrel_x e) e

(* TODO:WN:HVar *)
let extract_single_hvar (hf: h_formula) : CP.spec_var option =
  let f hf = match hf with
    | HVar (v,_) -> Some v
    | _ -> None
  in
  f hf

let extract_hvar (hf: h_formula) : CP.spec_var list =
  let f hf = match hf with
    | HVar (v,_) -> Some [v]
    | _ -> None
  in
  fold_h_formula hf f List.concat

let extract_hvar_f_x (f0:formula) : CP.spec_var list =
  let rec helper f=
    match f with
    | Base ({ formula_base_heap = h1; })
    | Exists ({formula_exists_heap = h1; }) -> extract_hvar h1
    | _ -> report_error no_pos "extract_hvar: OR unexpected, expect HVar only"
  in helper f0

(* TODO:WN need to check pure & others are empty *)
let extract_single_hvar_f (f0:formula) : CP.spec_var option =
  let rec helper f=
    match f with
    | Base ({ formula_base_heap = h1; formula_base_vperm=vp; formula_base_pure =pf;})
    | Exists ({formula_exists_heap = h1; formula_exists_vperm=vp; formula_exists_pure =pf;})
      ->
      let () = x_tinfo_hp (add_str "residue:vp" !print_vperm_sets) vp no_pos in
      let () = x_tinfo_hp (add_str "residue:pure" !print_mix_formula) pf no_pos in
      if CVP.is_empty_vperm_sets vp then
        extract_single_hvar h1
      else None
    | _ -> report_error no_pos "extract_hvar: OR unexpected, expect single HVar only"
  in helper f0

let extract_hvar_f (f0:formula) : CP.spec_var list =
  let pr1 = !print_formula in
  let pr2 = !CP.print_svl in
  Debug.no_1 "extract_hvar_f" pr1 pr2
    (fun _ ->  extract_hvar_f_x f0) f0

(*get hvars whose spec_var belong to vars*)
(* TODO:WN:HVar *)
let get_hvar_x e vars =
  let f hf = match hf with
    | HVar (v,_) -> if (Gen.BList.mem_eq CP.eq_spec_var v vars) then Some [hf] else None
    | _ -> None
  in
  fold_h_formula e f List.concat

(*get hvars whose spec_var belong to vars*)
let get_hvar e vars =
  let pr1 = !print_h_formula in
  Debug.no_2 "get_hvar" pr1 !print_svl (pr_list pr1)
    get_hvar_x e vars

(*drop hvars whose spec_var belong to vars*)
let drop_hvar_x hf vars =
  let func hf = match hf with
    | HVar (v,_) -> if (Gen.BList.mem_eq CP.eq_spec_var v vars) then Some HEmp else None
    | _ -> None
  in
  map_h_formula hf func
(* fold_h_formula e f List.concat *)

let drop_hvar e vars =
  let pr1 = !print_h_formula in
  Debug.no_2 "drop_hvar" pr1 !print_svl pr1
    drop_hvar_x e vars

let rec subst_one_hvar_hf_x (hf:h_formula) ((f,t) : CP.spec_var * formula) : h_formula =
  let func hf = match hf with
    | ViewNode vn ->
      let ho_args = List.map (trans_rflow_formula (fun f_base -> subst_one_hvar f_base (f,t)))
          vn.h_formula_view_ho_arguments in
      Some (ViewNode {vn with h_formula_view_ho_arguments = ho_args;})
    | _ -> None
  in
  map_h_formula hf func

(*subst ho_vars in ViewNode*)
and subst_one_hvar_hf (hf:h_formula) ((f,t) : CP.spec_var * formula) : h_formula =
  let pr1 = !print_h_formula in
  let pr2 = pr_pair !print_sv !print_formula in
  Debug.no_2 "subst_one_hvar_hf" pr1 pr2 pr1
    subst_one_hvar_hf_x hf  (f,t)

and subst_one_hvar_x f0 ((f,t) : CP.spec_var * formula) : formula =
  let rec helper f0=
    match f0 with
    | Base fb ->
      let hvars = get_hvar fb.formula_base_heap [f] in
      let fs = List.map (fun h -> match h with
          | HVar _ -> t
          | _ -> report_error no_pos "subst_hvar: expect HVar only"
        ) hvars in
      let n_h = drop_hvar fb.formula_base_heap [f] in
      (*subst ho_vars in n_h*)
      let n_h = subst_one_hvar_hf n_h (f,t) in
      (* let n_h = if (n_h=[]) then HEmp else List.hd n_h in (\*TOCHECK*\) *)
      (*Potential issues to consider: (1) duplicated HVars, (2) renaming of existential vars*)
      let n_f = Base {fb with formula_base_heap = n_h} in
      let n_f2 = List.fold_left (fun f1 f2 -> normalize_combine f1 f2 no_pos) n_f fs in
      n_f2
    | Exists _ ->
      let qvars, base = split_quantifiers f0 in
      let base = helper base in
      add_quantifiers qvars base
    | Or orf -> Or {orf with formula_or_f1 = helper orf.formula_or_f1 ;
                             formula_or_f2 = helper orf.formula_or_f2;}
  in
  helper f0

and subst_one_hvar f0 ((f,t) : CP.spec_var * formula) : formula =
  let pr1 = !print_formula in
  let pr2 = pr_pair !print_sv !print_formula in
  Debug.no_2 "subst_one_hvar" pr1 pr2 pr1
    subst_one_hvar_x f0 (f,t)

and subst_hvar_x f0 subst=
  List.fold_left (fun f (fr,t) -> subst_one_hvar f (fr,t)) f0 subst

and subst_hvar f subst =
  let pr1 = !print_formula in
  let pr2 = pr_list (pr_pair !print_sv !print_formula) in
  Debug.no_2 "subst_hvar" pr1 pr2 pr1
    subst_hvar_x f subst

(* subst and clear hvar in es *)
and subst_hvar_es_x es subst : context =
  let new_es_f = subst_hvar es.es_formula subst in
  let rec helper f =
    match f with
    | Or ({formula_or_f1 = f1; formula_or_f2 =  f2; formula_or_pos = pos}) ->
      let c1 = helper f1 in
      let c2 = helper f2 in
      let res = (mkOCtx c1 c2 pos ) in
      res
    | _ ->
      Ctx {es with es_formula = f; es_ho_vars_map = [];}
  in helper new_es_f

and subst_hvar_es es subst : context =
  let pr1 = !print_entail_state in
  let pr2 = pr_list (pr_pair !print_sv !print_formula) in
  let pr_out = !print_context in
  Debug.no_2 "subst_hvar_es" pr1 pr2 pr_out
    subst_hvar_es_x es subst

(* transform heap formula *)
let rec transform_h_formula (f:h_formula -> h_formula option) (e:h_formula):h_formula =
  let r =  f e in
  match r with
  | Some e1 -> e1
  | None  -> (
      match e with
      | Star s ->
        let new_h1 = transform_h_formula f s.h_formula_star_h1 in
        let new_h2 = transform_h_formula f s.h_formula_star_h2 in
        Star {s with h_formula_star_h1 = new_h1;
                     h_formula_star_h2 = new_h2;}
      | StarMinus s ->
        let new_h1 = transform_h_formula f s.h_formula_starminus_h1 in
        let new_h2 = transform_h_formula f s.h_formula_starminus_h2 in
        StarMinus {s with h_formula_starminus_h1 = new_h1;
                          h_formula_starminus_h2 = new_h2;}
      | Conj s ->
        let new_h1 = transform_h_formula f s.h_formula_conj_h1 in
        let new_h2 = transform_h_formula f s.h_formula_conj_h2 in
        Conj {s with h_formula_conj_h1 = new_h1;
                     h_formula_conj_h2 = new_h2;}
      | ConjStar s ->
        let new_h1 = transform_h_formula f s.h_formula_conjstar_h1 in
        let new_h2 = transform_h_formula f s.h_formula_conjstar_h2 in
        ConjStar {s with h_formula_conjstar_h1 = new_h1;
                         h_formula_conjstar_h2 = new_h2;}
      | ConjConj s ->
        let new_h1 = transform_h_formula f s.h_formula_conjconj_h1 in
        let new_h2 = transform_h_formula f s.h_formula_conjconj_h2 in
        ConjConj {s with h_formula_conjconj_h1 = new_h1;
                         h_formula_conjconj_h2 = new_h2;}
      | Phase s ->
        let new_rd = transform_h_formula f s.h_formula_phase_rd in
        let new_rw = transform_h_formula f s.h_formula_phase_rw in
        Phase {s with h_formula_phase_rd = new_rd;
                      h_formula_phase_rw = new_rw;}
      | DataNode _
      | ViewNode _
      | ThreadNode _
      | HRel _
      | Hole _ | FrmHole _
      | HTrue
      | HFalse
      | HEmp | HVar _ -> e
    )

let transform_formula_x f (e:formula):formula =
  let rec helper f e =
    let (_, f_f, f_h_f, f_p_t) = f in
    let r =  f_f e in
    match r with
    | Some e1 -> e1
    | None  ->
      match e with
      | Base b ->
        Base{b with
             formula_base_heap = transform_h_formula f_h_f b.formula_base_heap;
             formula_base_pure =  MCP.transform_mix_formula f_p_t b.formula_base_pure;}
      | Or o ->
        Or {o with
            formula_or_f1 = helper f o.formula_or_f1;
            formula_or_f2 = helper f o.formula_or_f2;}
      | Exists e ->
        Exists {e with
                formula_exists_heap = transform_h_formula f_h_f e.formula_exists_heap;
                formula_exists_pure = MCP.transform_mix_formula f_p_t e.formula_exists_pure;}
  in helper f e


let transform_formula f (e:formula):formula =
  let pr = !print_formula in
  (* Debug.no_2 "transform_formula" (fun _ -> "f") pr pr *) transform_formula_x f e

let transform_formula_w_perm_x (f:formula -> formula option) (e:formula) (permvar:cperm):formula =
  let r =  f e in
  match r with
  | Some e1 -> e1
  | None  -> e

let transform_formula_w_perm (f:formula -> formula option) (e:formula) (permvar:cperm):formula =
  let pr = !print_formula in
  Debug.no_3 "transform_formula_w_perm"
    (fun _ -> "f") pr (pr_none) pr
    transform_formula_w_perm_x f e permvar

let transform_formula_w_perm_x (f:formula -> formula option) (e:formula) (permvar:cperm_var):formula =
  let r =  f e in
  match r with
  | Some e1 -> e1
  | None  -> e


let transform_formula_w_perm (f:formula -> formula option) (e:formula) (permvar:cperm_var):formula =
  let pr = !print_formula in
  Debug.no_3 "transform_formula_w_perm"
    (fun _ -> "f") pr !print_spec_var pr
    transform_formula_w_perm_x f e permvar

let rec trans2_formula f (e:formula):formula =
  let (f_h_f, f_p_t) = f in
  match e with
  | Base b ->
    Base{b with
         formula_base_heap = transform_h_formula f_h_f b.formula_base_heap;
         formula_base_pure =  MCP.transform_mix_formula f_p_t b.formula_base_pure;}
  | Or o -> Or {o with
                formula_or_f1 = trans2_formula f o.formula_or_f1;
                formula_or_f2 = trans2_formula f o.formula_or_f2;}
  | Exists e ->
    Exists {e with
            formula_exists_heap = transform_h_formula f_h_f e.formula_exists_heap;
            formula_exists_pure = MCP.transform_mix_formula f_p_t e.formula_exists_pure;}

let foldheap (h:h_formula -> 'a) (f_comb: 'a list -> 'a)  (e:h_formula) : 'a =
  let rec helper e =
    match e with
    | Star s ->
      let new_a1 = helper s.h_formula_star_h1 in
      let new_a2 = helper s.h_formula_star_h2 in
      f_comb [new_a1;new_a2]
    | StarMinus s ->
      let new_a1 = helper s.h_formula_starminus_h1 in
      let new_a2 = helper s.h_formula_starminus_h2 in
      f_comb [new_a1;new_a2]
    | Conj s ->
      let new_a1 = helper s.h_formula_conj_h1 in
      let new_a2 = helper s.h_formula_conj_h2 in
      f_comb [new_a1;new_a2]
    | ConjStar s ->
      let new_a1 = helper s.h_formula_conjstar_h1 in
      let new_a2 = helper s.h_formula_conjstar_h2 in
      f_comb [new_a1;new_a2]
    | ConjConj s ->
      let new_a1 = helper s.h_formula_conjconj_h1 in
      let new_a2 = helper s.h_formula_conjconj_h2 in
      f_comb [new_a1;new_a2]
    | Phase s ->
      let new_a1 = helper s.h_formula_phase_rd in
      let new_a2 = helper s.h_formula_phase_rw in
      f_comb [new_a1;new_a2]
    | DataNode _
    | ViewNode _
    | ThreadNode _
    | HRel _
    | Hole _ | FrmHole _
    | HTrue
    | HFalse
    | HEmp | HVar _ -> h e
  in helper e


let foldheap_formula (h:h_formula -> 'a) (f_comb: 'a list -> 'a)  (e:formula) : 'a =
  let rec helper e =
    match e with
    | Base {formula_base_heap = e} -> h e
    | Or { formula_or_f1 = e1; formula_or_f2 = e2} -> f_comb [helper e1;helper e2]
    | Exists {formula_exists_heap = e} -> h e
  in helper e


let rec foldheap_struc_formula (h:h_formula -> 'a) (f_comb: 'a list -> 'a)  (e:struc_formula): 'a =
  let h_f = fun c-> [foldheap_struc_formula h f_comb c] in
  match e with
  | ECase b -> f_comb(fold_l_snd h_f b.formula_case_branches)
  | EBase b -> f_comb ((foldheap_formula h f_comb b.formula_struc_base)::(fold_opt h_f b.formula_struc_continuation))
  | EAssume b -> foldheap_formula h f_comb b.formula_assume_simpl
  | EInfer b -> foldheap_struc_formula h f_comb b.formula_inf_continuation
  | EList b ->  f_comb (fold_l_snd h_f b)

(*
  type: formula ->
  'a ->
  'c * ('a -> formula -> (formula * 'b) option) *
  ('a -> h_formula -> (h_formula * 'b) option) *
  (('a -> Cpure.formula -> (Cpure.formula * 'b) option) *
   ('a -> Cpure.b_formula -> (Cpure.b_formula * 'b) option) *
   ('a -> Cpure.exp -> (Cpure.exp * 'b) option)) *
  (('a -> Mcpure_D.memoised_group -> (Mcpure_D.memoised_group * 'b) option) *
   (Mcpure_D.memoised_constraint -> 'd -> Mcpure_D.memoised_constraint * 'b) *
   ('d -> Mcpure_D.var_aset -> Mcpure_D.var_aset * 'b list) *
   (Cpure.formula -> 'd -> Cpure.formula * 'b) *
   (Cpure.spec_var -> 'd -> Cpure.spec_var * 'b)) ->
  'e * ('a -> formula -> 'a) * ('a -> h_formula -> 'a) *
  (('a -> Cpure.formula -> 'a) * ('a -> Cpure.b_formula -> 'a) *
   ('a -> Cpure.exp -> 'a)) *
  ('a -> Mcpure_D.memoised_group -> 'd) -> ('b list -> 'b) -> formula * 'b
*)

let trans_formula (e: formula) (arg: 'a) f f_arg f_comb: (formula * 'b) =
  let f_struc_f, f_f, f_heap_f, f_pure, f_memo = f in
  let f_struc_f_arg, f_f_arg, f_heap_f_arg, f_pure_arg, f_memo_arg = f_arg in
  let trans_heap (e: h_formula) (arg: 'a) : (h_formula * 'b) = trans_h_formula e arg f_heap_f f_heap_f_arg f_comb in
  let trans_mix (e: MCP.mix_formula) (arg: 'a) : (MCP.mix_formula * 'b) =
    MCP.trans_mix_formula e arg (f_memo,f_pure) (f_memo_arg,f_pure_arg) f_comb in
  let rec trans_f (e: formula) (arg: 'a) : (formula * 'b) =
    let r = f_f arg e in
    match r with
    | Some e1 -> e1
    | None ->
      let new_arg = f_f_arg arg e in
      match e with
      | Base b ->
        let new_heap, v1 = trans_heap b.formula_base_heap new_arg in
        let new_pure, v2 = trans_mix b.formula_base_pure new_arg in
        let new_base = Base { b with
                              formula_base_heap = new_heap;
                              formula_base_pure = new_pure; }
        in
        (new_base, f_comb [v1; v2])
      | Or o ->
        let nf1, v1 = trans_f o.formula_or_f1 new_arg in
        let nf2, v2 = trans_f o.formula_or_f2 new_arg in
        let new_or = Or { o with
                          formula_or_f1 = nf1;
                          formula_or_f2 = nf2; }
        in
        (new_or, f_comb [v1; v2])
      | Exists e ->
        let new_heap, v1 = trans_heap e.formula_exists_heap new_arg in
        let new_pure, v2 = trans_mix e.formula_exists_pure new_arg in
        let new_exists = Exists { e with
                                  formula_exists_heap = new_heap;
                                  formula_exists_pure = new_pure;}
        in
        (new_exists, f_comb [v1; v2])
  in
  trans_f e arg


let fold_formula (e: formula) f (f_comb: 'b list -> 'b) : 'b =
  let trans_opt_f f = (fun _ e -> push_opt_val_rev (f e) e) in
  let trans_f f = (fun e _ -> (e, (f e))) in
  let trans_rev_f f = (fun _ e -> (e, (f e))) in
  let f_f, f_h_f, (f_p_f, f_p_b, f_p_e), (f_mg, f_mc, f_va, f_m_f, f_m_v) = f in
  let n_f =
    voidf,
    trans_opt_f f_f, trans_opt_f f_h_f,
    (trans_opt_f f_p_f, trans_opt_f f_p_b, trans_opt_f f_p_e),
    (trans_opt_f f_mg, trans_f f_mc, trans_rev_f f_va, trans_f f_m_f, trans_f f_m_v)
  in
  let f_arg = voidf2, voidf2, voidf2, (voidf2, voidf2, voidf2), voidf2 in
  snd (trans_formula e () n_f f_arg f_comb)

(* let map_formula_args (e: formula) (arg:'a) (f:'a -> formula -> formula option) (f_args: 'a -> formula -> 'a) : formula = *)
(*   let f1 ac e = push_opt_void_pair (f ac e) in *)
(*   fst (trans_formula e arg f1 f_args voidf) *)


(* let map_formula (e: formula) f f_comb: (formula * 'b) = *)
(*   let f_struc_f, f_f, f_heap_f, f_pure, f_memo = f in *)
(*   let n_f_struc_f _ e = f_struc_f e in *)
(*   let n_f_f _ e = f_f e in *)
(*   let n_f_heap_f _ e = f_heap_f e in *)
(*   let (f_pure_1,f_pure_2,f_pure_3) = f_pure in *)
(*   let n_f_pure =  (fun _ e -> f_pure_1 e,fun _ e -> f_pure_3 e,fun _ e -> f_pure_3 e) in *)
(*   let (f_memo_1,f_memo_2,f_memo_3,f_memo_4,f_memo_5) = f_memo  in *)
(*   let n_f_memo =  (fun _ e -> f_memo_1 e,fun e _ -> f_memo_2 e,fun _ e -> f_memo_3 e,fun e _ -> f_memo_4 e,fun e _ -> f_memo_5 e) in *)
(*   let new_f = (n_f_struc_f, n_f_f, n_f_heap_f, n_f_pure, n_f_memo) in *)
(*   let no_f _ _ = () in *)
(*   let new_f_arg = (no_f,no_f,no_f,(no_f,no_f,no_f),no_f) in *)
(*   trans_formula e () new_f new_f_arg f_comb *)

(*
  type: (struc_formula -> struc_formula option) * (formula -> formula option) *
  (h_formula -> h_formula option) *

  ((Mcpure_D.memo_pure -> Mcpure_D.memo_pure option) *
   (Mcpure_D.var_aset -> Mcpure_D.var_aset option) *
   (CP.formula -> CP.formula option) *
   (Cpure.b_formula -> Cpure.b_formula option) * (CP.exp -> CP.exp option)) ->
  struc_formula -> struc_formula
*)

let rec transform_struc_formula f (e:struc_formula) :struc_formula =
  let (f_e_f, f_f, f_h_f, f_p_t) = f in
  let r = f_e_f e in
  match r with
  | Some e1 -> e1
  | None -> match e with
    | ECase c ->
      let br' =
        List.map (fun (c1,c2)-> ((CP.transform_formula f_p_t c1),(transform_struc_formula f c2))) c.formula_case_branches in
      ECase {c with formula_case_branches = br';}
    | EBase b -> EBase{b with
                       formula_struc_base = transform_formula f b.formula_struc_base;
                       formula_struc_continuation = map_opt (transform_struc_formula f) b.formula_struc_continuation;
                      }
    | EAssume b-> EAssume {b with
                           formula_assume_simpl = transform_formula f b.formula_assume_simpl;
                           formula_assume_struc = transform_struc_formula f b.formula_assume_struc;}
    | EInfer b -> EInfer {b with formula_inf_continuation = transform_struc_formula f b.formula_inf_continuation;}
    | EList b -> EList (map_l_snd (transform_struc_formula f) b)


let rec transform_struc_formula_w_perm f (permvar:cperm_var) (e:struc_formula) :struc_formula =
  let (f_e_f, f_f, f_h_f, f_p_t) = f in
  let r = f_e_f e in
  match r with
  | Some e1 -> e1
  | None -> match e with
    | ECase c ->
      let br' =
        List.map (fun (c1,c2)-> ((CP.transform_formula f_p_t c1),(transform_struc_formula_w_perm f permvar c2))) c.formula_case_branches in
      ECase {c with formula_case_branches = br';}
    | EBase b -> EBase{b with
                       formula_struc_base = transform_formula_w_perm f_f b.formula_struc_base permvar;
                       formula_struc_continuation = map_opt (transform_struc_formula_w_perm f permvar) b.formula_struc_continuation;
                      }
    | EAssume b-> EAssume {b with
                           formula_assume_simpl = transform_formula_w_perm f_f b.formula_assume_simpl permvar;
                           formula_assume_struc = transform_struc_formula_w_perm f permvar b.formula_assume_struc;}
    | EInfer b -> EInfer {b with formula_inf_continuation = transform_struc_formula_w_perm f permvar b.formula_inf_continuation;}
    | EList b -> mkEList_no_flatten (map_l_snd (transform_struc_formula_w_perm f permvar) b)


let rec trans_struc_formula (e: struc_formula) (arg: 'a) f f_arg f_comb : (struc_formula * 'b) =
  let f_struc_f, f_f, f_h_formula, f_pure, f_memo = f in
  let f_struc_f_arg, f_f_arg, f_h_f_arg, f_pure_arg, f_memo_arg = f_arg in
  let trans_pure (e: CP.formula) (arg: 'a) : (CP.formula * 'b) = CP.trans_formula e arg f_pure f_pure_arg f_comb in
  let trans_struc (arg: 'a) (e: struc_formula)  : (struc_formula * 'b) = trans_struc_formula e arg f f_arg f_comb in
  let trans_f (e: formula) (arg: 'a) : (formula * 'b) = trans_formula e arg f f_arg f_comb in
  match f_struc_f arg e with
  | Some e1 -> e1
  | None ->
    let new_arg = f_struc_f_arg arg e in
    match e with
    | ECase c ->
      let helper ((e1,e2): CP.formula * struc_formula): (CP.formula * struc_formula) * 'b =
        let ne1, v1 = trans_pure e1 new_arg in
        let ne2, v2 = trans_struc new_arg e2  in
        ((ne1, ne2), f_comb [v1; v2])in
      let new_case_branches, vals = List.split (List.map helper c.formula_case_branches) in
      (ECase {c with formula_case_branches = new_case_branches}, f_comb vals)
    | EBase b ->
      let new_base, v1 = trans_f b.formula_struc_base new_arg in
      let new_cont, l = match b.formula_struc_continuation with
        | None -> (None,[v1])
        | Some b-> let r1,r2 = trans_struc new_arg b in (Some r1, [v1;r2]) in
      (EBase { b with formula_struc_base = new_base; formula_struc_continuation = new_cont; }, f_comb l)
    | EAssume b ->
      let ne, r = trans_f b.formula_assume_simpl new_arg in
      let n_struc, _ = trans_struc new_arg b.formula_assume_struc  in
      let b = {b with formula_assume_simpl=ne; formula_assume_struc = n_struc} in
      (EAssume b, f_comb [r])
    | EInfer b ->
      let new_cont, val3 = trans_struc new_arg b.formula_inf_continuation  in
      (EInfer {b with formula_inf_continuation = new_cont}, f_comb [val3])
    | EList b ->
      let ne,vals = map_l_snd_res (trans_struc new_arg) b in
      (mkEList_no_flatten ne, f_comb vals)

let conv f = fun a x -> match (f a x) with
  | None -> None
  | Some r -> Some (r,())


(*
type: struc_formula ->
  'a ->
  ('a -> struc_formula -> (struc_formula * 'b) option) *
  ('a -> formula -> (formula * 'b) option) *
  ('a -> h_formula -> (h_formula * 'b) option) *

  (('a -> CP.formula -> (CP.formula * 'b) option) *
   ('a -> Cpure.b_formula -> (Cpure.b_formula * 'b) option) *
   ('a -> CP.exp -> (CP.exp * 'b) option)) *


->
  ('a -> struc_formula -> 'a) * ('a -> formula -> 'a) *
  ('a -> h_formula -> 'a) *
  (('a -> CP.formula -> 'a) * ('a -> Cpure.b_formula -> 'a) *
   ('a -> CP.exp -> 'a)) *
  ('a -> Mcpure_D.memoised_group -> 'a) ->
  ('b list -> 'b) -> struc_formula * 'b


*)

let conv2 f a e =
  match f a e with
  | None -> None
  | Some (e,_) -> (Some e)


(*
struc_formula ->
  'a ->
  ('a -> struc_formula -> struc_formula option) *
  ('a -> formula -> formula option) * ('a -> h_formula -> h_formula option) *
  (('a -> CP.formula -> CP.formula option) *
   ('a -> Cpure.b_formula -> Cpure.b_formula option) *
   ('a -> CP.exp -> CP.exp option)) *



  (('a -> Mcpure_D.memoised_group -> (Mcpure_D.memoised_group * 'b) option) *
   (Mcpure_D.memoised_constraint -> 'a -> Mcpure_D.memoised_constraint * 'b) *
   ('a -> Mcpure_D.var_aset -> Mcpure_D.var_aset * 'b list) *
   (Cpure.formula -> 'a -> Cpure.formula * 'b) *
   (Cpure.spec_var -> 'a -> Cpure.spec_var * 'b)) ->


  (('a ->
    Mcpure_D.memoised_group ->
      ((Mcpure_D.memoised_group * unit) * 'b) option) *
   ('a ->
    Mcpure_D.memoised_constraint ->
    (Mcpure_D.memoised_constraint * unit) * 'c) *
   ('a -> Mcpure_D.var_aset -> (Mcpure_D.var_aset * unit list) * 'd) *

   ('a -> Cpure.formula -> (Cpure.formula * unit) * 'e) *
   ('a -> Cpure.spec_var -> (Cpure.spec_var * unit) * 'f)) ->
  ('a -> struc_formula -> 'a) * ('a -> formula -> 'a) *
  ('a -> h_formula -> 'a) *
  (('a -> CP.formula -> 'a) * ('a -> Cpure.b_formula -> 'a) *
   ('a -> CP.exp -> 'a)) *
  ('a -> Mcpure_D.memoised_group -> 'a) -> 'g -> struc_formula
*)

let conv2a f e a = let (r,x) = f a e in r
let conv3 f a e = let (r,x) = f a e in r
(* let conv3a f a e = let (r,x) = f a e in r *)

(* let map_struc_formula (e: struc_formula) arg f f_arg f_comb : struc_formula  = *)
(*   let conv2 f a e = match f a e with Some (e1,_) -> e1 | None -> None in *)
(*   let f_struc_f, f_f, f_h_formula, (f_p1,f_p2,f_p3), (f_m1,f_m2,f_m3,f_m4,f_m5) = f in (\* f -> f option *\) *)
(*   let f_memo = (conv2 f_m1, conv2a f_m2, conv3 f_m3, conv2a f_m4, conv2a f_m5) in *)
(*   let f_conv = (conv f_struc_f, conv f_f, conv f_h_formula, (conv f_p1,conv f_p2,conv f_p3), f_memo) in *)
(*   let f_comb _ = () in *)
(*   let (e,_) = trans_struc_formula e arg f_conv f_arg f_comb in *)
(*   e *)

let rec transform_context f (c:context):context =
  match c with
  | Ctx e ->
    (f e)
  | OCtx (c1,c2) ->
    mkOCtx (transform_context f c1)(transform_context f c2) no_pos

let trans_context (c: context) (arg: 'a)
    (f: 'a -> context -> (context * 'b) option)
    (f_arg: 'a -> context -> 'a)
    (f_comb: 'b list -> 'b)
  : (context * 'b) =
  (* let () = x_winfo_pp "trans_context not working" no_pos in *)
  (* if !Globals.warn_trans_context then failwith "trans_context not working?" *)
  (* else *)
    let rec trans_c (c: context) (arg: 'a) : (context * 'b) =
      let r = f arg c in
      match r with
      | Some c1 -> c1
      | None ->
        let new_arg = f_arg arg c in
        match c with
        | Ctx _ -> (c, f_comb [])
        | OCtx (c1, c2) ->
          let nc1, v1 = trans_c c1 new_arg in
          let nc2, v2 = trans_c c2 new_arg in
          (mkOCtx nc1 nc2 no_pos, f_comb [v1; v2])
    in
    trans_c c arg

let trans_list_context (c: list_context) (arg: 'a) f_c f_c_arg f_comb: (list_context * 'b) =
  match c with
  | FailCtx fc -> (c, f_comb [])
  | SuccCtx sc ->
    let n_sc, acc = List.split (List.map (fun c -> trans_context c arg f_c f_c_arg f_comb) sc) in
    (SuccCtx sc, f_comb acc)

let trans_branch_ctx (c: branch_ctx) (arg: 'a) f_c f_c_arg f_comb : (branch_ctx * 'b) =
  let trace, ctx, oft = c in
  let n_ctx, acc = trans_context ctx arg f_c f_c_arg f_comb in
  ((trace, n_ctx, oft), acc)

let trans_failesc_context (c: failesc_context) (arg: 'a) f_c f_c_arg f_comb : (failesc_context * 'b) =
  let bf, es, bc = c in
  let n_bc, acc = List.split (List.map (fun c -> trans_branch_ctx c arg f_c f_c_arg f_comb) bc) in
  ((bf, es, n_bc), f_comb acc)

(* type: list_failesc_context -> *)
(*   'a -> *)
(*   ('a -> context -> (context * 'b) option) -> *)
(*   ('a -> context -> 'a) -> ('b list -> 'b) -> list_failesc_context * 'b *)
let trans_list_failesc_context (c: list_failesc_context)
    (arg: 'a) f_c f_c_arg f_comb : (list_failesc_context * 'b) =
  let n_c, acc = List.split (List.map (fun ctx -> trans_failesc_context ctx arg f_c f_c_arg f_comb) c) in
  (n_c, f_comb acc)

let trans_partial_context (c: partial_context) (arg: 'a) f_c f_c_arg f_comb: (partial_context * 'b) =
  let bf, bc = c in
  let n_bc, acc = List.split (List.map (fun c -> trans_branch_ctx c arg f_c f_c_arg f_comb) bc) in
  ((bf, n_bc), f_comb acc)

let trans_list_partial_context (c: list_partial_context)
    (arg: 'a) f_c f_c_arg f_comb : (list_partial_context * 'b) =
  let n_c, acc = List.split (List.map (fun ctx -> trans_partial_context ctx arg f_c f_c_arg f_comb) c) in
  (n_c, f_comb acc)

let rec transform_fail_ctx f (c:fail_type) : fail_type =
  match c with
  | Trivial_Reason _ -> c
  | Basic_Reason (br,fe,ft) -> Basic_Reason ((f br), fe, ft)
  | ContinuationErr (br,ft) -> ContinuationErr (f br, ft)
  | Or_Reason (ft1,ft2) -> Or_Reason ((transform_fail_ctx f ft1),(transform_fail_ctx f ft2))
  | Union_Reason (ft1,ft2) -> Union_Reason ((transform_fail_ctx f ft1),(transform_fail_ctx f ft2))
  | Or_Continuation (ft1,ft2) -> Or_Continuation ((transform_fail_ctx f ft1),(transform_fail_ctx f ft2))
  | And_Reason (ft1,ft2) -> And_Reason ((transform_fail_ctx f ft1),(transform_fail_ctx f ft2))

let transform_list_context f (c:list_context):list_context =
  let f_c,f_f = f in
  match c with
  | FailCtx (fc, c, cex) -> FailCtx ((transform_fail_ctx f_f fc), c, cex) (* Loc: to check cex here *)
  | SuccCtx sc -> SuccCtx ((List.map (transform_context f_c)) sc)

let transform_partial_context f ((fail_c, succ_c):partial_context) : partial_context =
  let f_c,f_f = f in
  let f_res = List.map (fun (lbl, f_t) -> (lbl, transform_fail_ctx f_f f_t )) fail_c in
  let s_res = List.map (fun (lbl, ctx, oft) -> (lbl, transform_context f_c ctx, oft) ) succ_c in
  (f_res,s_res)

let transform_branch_ctx f_es (ls:branch_ctx list): branch_ctx list =
  let rs = List.map (fun (lbl, ctx, oft) -> (lbl, transform_context f_es ctx, oft) ) ls in
  rs

let transform_failesc_context f ((fail_c,esc_c, succ_c):failesc_context): failesc_context =
  let ff,fe,fs = f in
  let rf = List.map (fun (lbl, ctx) -> (lbl, transform_fail_ctx ff ctx) ) fail_c in
  let re = fe esc_c in
  (* let rs = List.map (fun (lbl, ctx) -> (lbl, transform_context fs ctx) ) succ_c in *)
  let rs = transform_branch_ctx fs succ_c in
  (rf, re,rs)

let transform_list_partial_context f (c:list_partial_context):list_partial_context =
  List.map (transform_partial_context f) c

let transform_list_failesc_context
    (f:(fail_context -> fail_context) * (esc_stack -> esc_stack) * (entail_state -> context))
    (c:list_failesc_context): list_failesc_context =
  List.map (transform_failesc_context f) c


let push_esc_level_list (l:list_failesc_context) idf lbl : list_failesc_context =
  transform_list_failesc_context (idf,(fun c-> push_esc_level c lbl),(fun x-> Ctx x)) l

(*use with care, it destroyes the information about exception stacks , preferably do not use except in check specs*)
let list_failesc_to_partial (c:list_failesc_context): list_partial_context =
  List.map (fun (fl,el,sl) -> (fl,(colapse_esc_stack el)@sl)) c

let rec fold_fail_context f (c:fail_type) =
  (*let f_br,f_or,f_and = f in*)
  match c with
  | Trivial_Reason _ -> f c []
  | Basic_Reason br -> f c []
  | ContinuationErr br -> f c []
  | Or_Reason (ft1,ft2) | Union_Reason (ft1,ft2) -> f c [(fold_fail_context f ft1);(fold_fail_context f ft2)]
  | Or_Continuation (ft1,ft2) -> f c [(fold_fail_context f ft1);(fold_fail_context f ft2)]
  | And_Reason (ft1,ft2) -> f c [(fold_fail_context f ft1);(fold_fail_context f ft2)]


let rename_labels transformer e =
  let n_l_f n_l = match n_l with
    | None -> (fresh_branch_point_id "")
    | Some (_,s) -> (fresh_branch_point_id s) in
  let f_e_f e = None in
  let f_f e = None in
  let rec f_h_f e = match e with
    | Star s -> None
    | StarMinus s -> None
    | Conj s -> None
    | ConjStar s -> None
    | ConjConj s -> None
    | Phase s -> None
    | DataNode d -> Some (DataNode {d with h_formula_data_label = n_l_f d.h_formula_data_label})
    | ViewNode v -> Some (ViewNode {v with h_formula_view_label = n_l_f v.h_formula_view_label})
    | ThreadNode t -> Some (ThreadNode {t with h_formula_thread_label = n_l_f t.h_formula_thread_label})
    | HRel _
    | Hole _ | FrmHole _
    | HTrue
    | HFalse
    | HEmp | HVar _-> Some e in
  let f_m e = None in
  let f_a e = None in
  let f_b e = Some e in
  let f_e e = Some e in
  let f_p_f e =
    match e with
    | CP.BForm (b,f_l) -> Some (CP.BForm (b,(n_l_f f_l)))
    | CP.And _
    | CP. AndList _ -> None
    | CP.Or (e1,e2,f_l,l) -> (Some (CP.Or (e1,e2,(n_l_f f_l),l)))
    | CP.Not (e1,f_l, l) -> (Some (CP.Not (e1,(n_l_f f_l),l)))
    | CP.Forall (v,e1,f_l, l) -> (Some (CP.Forall (v,e1,(n_l_f f_l),l)))
    | CP.Exists (v,e1,f_l, l) -> (Some (CP.Exists (v,e1,(n_l_f f_l),l)))in
  transformer (f_e_f,f_f,f_h_f,(f_m,f_a,f_p_f,f_b,f_e)) e

let rename_labels_struc (e:struc_formula):struc_formula = rename_labels transform_struc_formula e
let rename_labels_formula (e:formula):formula = rename_labels transform_formula e

let rename_labels_formula_ante  e=
  let n_l_f n_l = match n_l with
    | None -> (fresh_branch_point_id "")
    | Some (_,s) -> (fresh_branch_point_id s) in
  let f_e_f e = None in
  let f_f e = None in
  let rec f_h_f e = match e with
    | Conj s -> None
    | ConjStar s -> None
    | ConjConj s -> None
    | Phase s -> None
    | Star s -> None
    | StarMinus s -> None
    | DataNode d -> Some (DataNode {d with h_formula_data_label = n_l_f d.h_formula_data_label})
    | ViewNode v -> Some (ViewNode {v with h_formula_view_label = n_l_f v.h_formula_view_label})
    | ThreadNode t -> Some (ThreadNode {t with h_formula_thread_label = n_l_f t.h_formula_thread_label})
    | HRel _
    | Hole _ | FrmHole _
    | HTrue
    | HFalse
    | HEmp | HVar _ -> Some e in
  let f_m e = None in
  let f_a e = None in
  let f_b e = Some e in
  let f_e e = Some e in
  let f_p_f e = Some e in

  transform_formula (f_e_f,f_f,f_h_f,(f_m,f_a,f_p_f,f_b,f_e)) e

let rec erase_propagated f =
  let f_e_f e = None in
  let f_f e = None in
  let rec f_h_f e =  None in
  let f_memo e =  Some (MCP.cons_filter e MCP.isImplT) in
  let f_aset e = Some e in
  let f_formula e = Some e in
  let f_b_formula e = Some e in
  let f_exp e = Some e in
  transform_struc_formula (f_e_f,f_f,f_h_f,(f_memo,f_aset, f_formula, f_b_formula, f_exp)) f



(* type: ((CP.spec_var * h_formula) * CP.spec_var list) list -> *)
(*   CP.formula list -> list_context -> list_context option *)

(* and add_infer_hp_contr_to_list_context h_arg_map cp (l:list_context) : list_context option = *)
(*   let pr1 = pr_list pr_none in *)
(*   let pr2 = pr_list !CP.print_formula in *)
(*   let pr3 = !print_list_context in *)
(*   Debug.no_3 "add_infer_hp_contr_to_list_context" pr1 pr2 pr3 (pr_option pr3) *)
(*       add_infer_hp_contr_to_list_context_x h_arg_map cp l *)

(* and add_infer_hp_contr_to_list_context_x h_arg_map cp (l:list_context) : list_context option=  *)
(* 	 (\* let new_cp = List.concat (List.map CP.split_conjunctions cp) in *\) *)
(* 	 let new_cp = List.map CP.arith_simplify_new cp in *)
(* 	 try *)
(* 		 let new_rels = List.map (fun c-> *)
(* 			let fv = CP.fv c in *)
(* 			let new_hd = List.filter (fun (_,vl)-> Gen.BList.overlap_eq CP.eq_spec_var fv vl) h_arg_map in *)
(* 			match new_hd with *)
(* 			 | [((h,hf),h_args)] ->  *)
(* 				if (Gen.BList.list_setequal_eq CP.eq_spec_var fv (List.concat (snd (List.split new_hd)))) then *)
(* 				mkHprel (CP.HPRelDefn h) h_args [] []  (formula_of_heap hf no_pos) (formula_of_pure_N c no_pos)  				 *)
(* 				else raise Not_found *)
(* 			| _ -> raise Not_found ) new_cp in *)
(*                  (\* let () = rel_ass_stk # push_list (new_rels) in *\) *)
(*                  (\* let () = Log.current_hprel_ass_stk # push_list (new_rels) in *\) *)
(* 		 let scc_f es = Ctx {es with es_infer_hp_rel = new_rels@es.es_infer_hp_rel;} in *)
(* 		 Some (transform_list_context (scc_f, (fun a -> a)) l) *)
(* 	 with Not_found -> None *)

and pop_expl_impl_context (expvars : CP.spec_var list) (impvars : CP.spec_var list) (ctx : list_context)  : list_context =
  transform_list_context ((fun es -> Ctx{es with
                                         es_gen_expl_vars = Gen.BList.difference_eq CP.eq_spec_var es.es_gen_expl_vars expvars;
                                         es_gen_impl_vars = Gen.BList.difference_eq CP.eq_spec_var es.es_gen_impl_vars impvars;
                                         es_evars = Gen.BList.difference_eq (=) es.es_evars expvars;
                                        }), fun c->c) ctx

and push_exists_list_context (qvars : CP.spec_var list) (ctx : list_context) : list_context =
  transform_list_context ((fun es -> Ctx{es with es_formula = push_exists qvars es.es_formula}),(fun c->c)) ctx


and push_exists_list_partial_context (qvars : CP.spec_var list) (ctx : list_partial_context) : list_partial_context =
  transform_list_partial_context ((fun es -> Ctx{es with es_formula = push_exists qvars es.es_formula}),(fun c->c)) ctx

and fresh_view_list_partial_context (ctx : list_partial_context) : list_partial_context =
  transform_list_partial_context ((fun es -> Ctx{es with es_formula = fresh_view es.es_formula}),(fun c->c)) ctx

and push_exists_list_failesc_context_x (qvars : CP.spec_var list) (ctx : list_failesc_context) : list_failesc_context =
  transform_list_failesc_context (idf,idf,(fun es -> Ctx{es with es_formula = push_exists qvars es.es_formula})) ctx

and push_exists_list_failesc_context (qvars : CP.spec_var list) (ctx : list_failesc_context) : list_failesc_context =
  let pr1 = !print_list_failesc_context in
  let pr2 = pr_list !CP.print_sv in
  Debug.no_2 "push_exists_list_failesc_context" pr2 pr1 pr1
    push_exists_list_failesc_context_x qvars ctx

and push_exists_context_x (qvars : CP.spec_var list) (ctx : context) : context =
  transform_context (fun es -> Ctx{es with es_formula = push_exists qvars es.es_formula}) ctx

and push_exists_context_d (qvars : CP.spec_var list) (ctx : context) : context =
  let pr = !print_context in
  Debug.no_2 "push_exists_context" (pr_list !print_sv) pr pr
    push_exists_context_x qvars ctx

and push_exists_context (qvars : CP.spec_var list) (ctx : context) : context =
  Gen.Profiling.do_1 "push_exists_context" (push_exists_context_d qvars) ctx

and get_exists_context (ctx : context) : CP.spec_var list =
  let rec helper ctx =
    match ctx with
    | Ctx e ->
      get_exists e.es_formula
    | OCtx (c1,c2) ->
      let evars1 = helper c1 in
      let evars2 = helper c2 in
      (evars1@evars2)
  in helper ctx

and push_expl_impl_context (expvars : CP.spec_var list) (impvars : CP.spec_var list) (ctx : context)  : context =
  transform_context (fun es -> Ctx{es with
                                   es_gen_expl_vars = es.es_gen_expl_vars @ expvars;
                                   es_gen_impl_vars = es.es_gen_impl_vars @ impvars;
                                   (*es_evars = es.es_evars@ expvars;*)}) ctx

and impl_to_expl es vl : entail_state =
  let im, il = List.partition (fun c-> List.mem c vl) es.es_gen_impl_vars in
  {es with
   es_gen_expl_vars = es.es_gen_expl_vars @ im;
   es_gen_impl_vars = il;}


and pop_exists_context (qvars : CP.spec_var list) (ctx : list_context) : list_context =
  transform_list_context ((fun es -> Ctx{es with es_formula = pop_exists qvars es.es_formula}),(fun c->c)) ctx

and pop_exists_estate (qvars : CP.spec_var list) (es : entail_state) : entail_state =
  let new_es = {es with
                es_evars = (List.filter (fun x -> not (List.exists (fun y -> (CP.eq_spec_var x y)) qvars)) es.es_evars);
                es_formula = pop_exists qvars es.es_formula
               }
  in new_es

(* add a list of existential vars, evars, to each context in the list ctx *)
and add_exist_vars_to_ctx_list (ctx : list_context) (evars	: CP.spec_var list) : list_context =
  transform_list_context ((fun es-> Ctx{es with es_formula = (add_quantifiers evars es.es_formula)}),(fun c->c)) ctx


and change_ret_flow_ctx ctx_list =
  transform_list_context ((fun es -> Ctx{es with es_formula = substitute_flow_in_f !norm_flow_int !ret_flow_int es.es_formula;})
                         ,(fun c->c)) ctx_list

and change_ret_flow_partial_ctx ctx_list =
  transform_list_partial_context ((fun es -> Ctx{es with es_formula = substitute_flow_in_f !norm_flow_int !ret_flow_int es.es_formula;})
                                 ,(fun c->c)) ctx_list

and change_ret_flow_failesc_ctx ctx_list =
  transform_list_failesc_context
    (idf,idf,(fun es -> Ctx{es with es_formula = substitute_flow_in_f !norm_flow_int !ret_flow_int es.es_formula;})) ctx_list

let add_both_path (s,pi2) i e =
  Ctx { e
        with es_path_label = (s,pi2)::e.es_path_label;
             es_cond_path = if i<0 then e.es_cond_path else i::e.es_cond_path
      }
let add_one_path i e =
  Ctx { e
        with es_cond_path = i::e.es_cond_path
      }

let add_path_id ctx ((pi1,pi2)) i =
  match pi1 with
  | None -> if i<0 then ctx else transform_context (add_one_path i) ctx
  | Some s -> transform_context (add_both_path (s,pi2) i) ctx

let add_path_id ctx ((pi1,pi2)as p) i =
  let pr1 = pr_pair (pr_option pr_none) string_of_int in
  let pr2 = string_of_int in
  Debug.no_2 "add_path_id" pr1 pr2 pr_none (fun _ _ -> add_path_id ctx p i) p i

let add_path_id_ctx_list c (pi1,pi2) i  =
  match pi1 with
  | None -> if i<0 then c else transform_list_context (add_one_path i,idf) c
  | Some s ->	 transform_list_context ((add_both_path (s,pi2) i),idf) c

let add_path_id_ctx_partial_list (c:list_partial_context) (pi1,pi2) i : list_partial_context =
  match pi1 with
  | None -> if i<0 then c else transform_list_partial_context (add_one_path i,idf) c
  | Some s ->	 transform_list_partial_context ((add_both_path (s,pi2) i),idf) c
(* match pi1 with *)
(*   | None -> c *)
(*   | Some s ->	       *)
(*       let fct e = Ctx{e with  *)
(*           es_path_label = (s,pi2)::e.es_path_label; *)
(*           es_cond_path = i::e.es_cond_path *)
(*       } in     *)
(*       transform_list_partial_context (fct,(fun c-> c)) c *)

let add_path_id_ctx_failesc_list (c:list_failesc_context) (pi1,pi2) i : list_failesc_context =
  match pi1 with
  | None -> if i<0 then c else transform_list_failesc_context (idf,idf,add_one_path i) c
  | Some s ->	 transform_list_failesc_context (idf,idf,(add_both_path (s,pi2) i)) c
(* match pi1 with *)
(*   | None -> c *)
(*   | Some s ->	       *)
(*       let fct e = Ctx{e with  *)
(*           es_path_label = (s,pi2)::e.es_path_label; *)
(*           es_cond_path = i::e.es_cond_path *)
(*       } in     *)
(*       transform_list_failesc_context (idf,idf,fct) c *)

let proc_esc_stack pid f_es es =
  List.map (fun ((p,l) as e) ->
      if eq_control_path_id p pid then
        (* Debug.info_hprint (add_str "proc_esc_stack(=pid)" Cprinter.string_of_esc_stack_lvl) e no_pos; *)
        (p,transform_branch_ctx f_es l)
      else e
    ) es

let change_flow_w_flag f b fl=
  if b then
    substitute_flow_into_f fl f
  else f

let normalize_max_renaming_list_partial_context f pos b ctx =
  (* let () = print_string("cris: normalize 11\n") in *)
  if !max_renaming then transform_list_partial_context ((normalize_es f pos b),(fun c->c)) ctx
  else transform_list_partial_context ((normalize_clash_es f pos b),(fun c->c)) ctx


let normalize_max_renaming_list_failesc_context_4_bind pid f pos b ctx =
  let norm_es = if !max_renaming then normalize_es f pos b else normalize_clash_es f pos b in
  let f_esc = proc_esc_stack pid norm_es in
  transform_list_failesc_context (idf,f_esc,norm_es) ctx
(* if !max_renaming then transform_list_failesc_context (idf,f_esc,(normalize_es f pos b)) ctx *)
(*   else transform_list_failesc_context (idf,f_esc,(normalize_clash_es f pos b)) ctx *)


let normalize_max_renaming_list_failesc_context_4_bind pid f pos b ctx =
  let pr_f = !print_formula in
  let pr_ctx = pr_list !print_failesc_context in
  Debug.no_2 "normalize_max_renaming_list_failesc_context_4_bind"
    pr_f pr_ctx pr_ctx
    (fun _ _ -> normalize_max_renaming_list_failesc_context_4_bind pid f pos b ctx) f ctx

let normalize_max_renaming_list_failesc_context f pos b ctx =
  (* let () = print_string("cris: normalize 12\n") in *)
  if !max_renaming then transform_list_failesc_context (idf,idf,(normalize_es f pos b)) ctx
  else transform_list_failesc_context (idf,idf,(normalize_clash_es f pos b)) ctx

let combine_pure_list_failesc_context f pos b ctx =
  let combine_pure_es f pos b es=
    Ctx {es with es_formula = mkAnd_pure es.es_formula f pos;}
  in
  transform_list_failesc_context (idf,idf,(combine_pure_es f pos b)) ctx

let normalize_max_renaming_list_failesc_context f pos b ctx =
  let pr_f = !print_formula in
  let pr_ctx = pr_list !print_failesc_context in
  Debug.no_2 "normalize_max_renaming_list_failesc_context"
    pr_f pr_ctx pr_ctx
    (fun _ _ -> normalize_max_renaming_list_failesc_context f pos b ctx) f ctx

let normalize_max_renaming_list_failesc_context f pos b ctx =
  (* let () = print_string("cris: normalize 13\n") in *)
  Gen.Profiling.do_2 "normalize_max_renaming_list_failesc_context" (normalize_max_renaming_list_failesc_context f pos) b ctx

let normalize_max_renaming f pos b ctx =
  (* let () = print_string("cris: normalize 14\n") in *)
  if !max_renaming then transform_list_context ((normalize_es f pos b),(fun c->c)) ctx
  else transform_list_context ((normalize_clash_es f pos b),(fun c->c)) ctx

let normalize_max_renaming_s f pos b ctx =
  (* let () = print_string("cris: normalize 15\n") in *)
  if !max_renaming then transform_context (normalize_es f pos b) ctx
  else transform_context (normalize_clash_es f pos b) ctx

(*
  to be used in the type-checker. Before checking post condition,
  the history of es_pure must be cleared.
  TO CHECK: this should be done for each entailment
*)
let clear_entailment_es_pure (es :entail_state) = {es with es_pure = MCP.mkMTrue no_pos;}

(*
  to be used in the type-checker. After every entailment, the history of vars
  must be cleared.
*)

let clear_entailment_vars (es :entail_state) : entail_state =
  {es with (* es_history = es.es_history@[es.es_heap]; *)
   es_heap = HEmp;
   es_evars = [];
   es_ivars = [];
   es_gen_expl_vars = [];
   es_gen_impl_vars = [];
   es_subst = ([],[]);
  }

let clear_entailment_history_es_es (es :entail_state) : entail_state =
  {es with (* es_history = es.es_history@(get_hdnodes_hrel_hf es.es_heap); *)
   es_heap = HEmp;
  }


let clear_entailment_history_es2 xp (es :entail_state) :entail_state =
  (* TODO : this is clearing more than es_heap since qsort-tail.ss fails otherwise *)
  let hf = es.es_heap in
  (* let old_history =  if is_data hf then es.es_history@[hf] else es.es_history in *)
  (* let old_history =  [] in *)
  (* adding xpure0 of es_heap into es_formula *)
  let es_f = match xp hf with
    | None -> es.es_formula
    | Some (mf,svl,mm)  -> mkAnd_pure es.es_formula mf no_pos
  in
  {(empty_es (mkTrueFlow ()) es.es_group_lbl no_pos) with
   es_formula = es_f;
   (* es_history = old_history; *)
   es_path_label = es.es_path_label;
   es_prior_steps = es.es_prior_steps;
   es_var_measures = es.es_var_measures;
   (* es_infer_tnt = es.es_infer_tnt; *)
   es_infer_obj = es.es_infer_obj;
   es_term_res_lhs = es.es_term_res_lhs;
   es_crt_holes = es.es_crt_holes;
   es_ho_vars_map  = es.es_ho_vars_map  ;
   (* WN : what is the purpose of es_var_stack?*)
   (* es_term_call_rhs = es.es_term_call_rhs; *)
   es_var_stack = es.es_var_stack;
   es_pure = es.es_pure;
   es_infer_vars = es.es_infer_vars;
   es_infer_vars_rel = es.es_infer_vars_rel;
   es_infer_vars_templ = es.es_infer_vars_templ;
   es_infer_vars_hp_rel = es.es_infer_vars_hp_rel;
   es_infer_vars_sel_hp_rel = es.es_infer_vars_sel_hp_rel;
   es_infer_vars_sel_post_hp_rel = es.es_infer_vars_sel_post_hp_rel;
   es_infer_hp_unk_map = es.es_infer_hp_unk_map;
   es_infer_heap = es.es_infer_heap;
   es_infer_pure = es.es_infer_pure;
   es_infer_rel = es.es_infer_rel # clone;
   es_infer_term_rel = es.es_infer_term_rel;
   es_infer_templ_assume = es.es_infer_templ_assume;
   es_infer_hp_rel = es.es_infer_hp_rel # clone;
   es_group_lbl = es.es_group_lbl;
   es_term_err = es.es_term_err;
   es_conc_err = es.es_conc_err;
   es_var_zero_perm = es.es_var_zero_perm;}

(*
  to be used in the type-checker. After every entailment, the history of consumed nodes
  must be cleared.
*)

let clear_entailment_history_es xp (es :entail_state) :context =
  (* TODO : this is clearing more than es_heap since qsort-tail.ss fails otherwise *)
  let hf = es.es_heap in
  (* let old_history =  if is_data hf then es.es_history@[hf] else es.es_history in *)
  (* let old_history =  if (\*is_data*\) is_empty_heap hf then es.es_history else es.es_history@(get_hdnodes_hrel_hf hf) in *)
  (* adding xpure0 of es_heap into es_formula *)
  let es_f = match xp hf with
    | None -> es.es_formula
    | Some (mf,svl,mm)  -> mkAnd_pure es.es_formula mf no_pos
  in
  Ctx {
    (* es with es_heap=HTrue;} *)
    (* WN : why is this duplicated? *)
    (empty_es (mkTrueFlow ()) es.es_group_lbl no_pos) with
    es_formula = es_f;
    (* es_heap = hf; *)
    (* es_history = old_history; *)
    es_path_label = es.es_path_label;
    es_cond_path = es.es_cond_path ;
    es_prior_steps = es.es_prior_steps;
    es_var_measures = es.es_var_measures;
    (* es_infer_tnt = es.es_infer_tnt; *)
    es_must_error = es.es_must_error;
    es_may_error = es.es_may_error;
    es_final_error = es.es_final_error;
    es_infer_obj = es.es_infer_obj;
    es_term_res_lhs = es.es_term_res_lhs;
    es_crt_holes = es.es_crt_holes;
    es_ho_vars_map = es.es_ho_vars_map;
    es_term_res_rhs = es.es_term_res_rhs;
    es_term_call_rhs = es.es_term_call_rhs;
    (* WN : what is the purpose of es_var_stack?*)
    es_var_stack = es.es_var_stack;
    es_pure = es.es_pure;
    es_infer_vars = es.es_infer_vars;
    es_infer_vars_rel = es.es_infer_vars_rel;
    es_infer_vars_templ = es.es_infer_vars_templ;
    es_infer_vars_hp_rel = es.es_infer_vars_hp_rel;
    es_infer_vars_sel_hp_rel = es.es_infer_vars_sel_hp_rel;
    es_infer_vars_sel_post_hp_rel = es.es_infer_vars_sel_post_hp_rel;
    es_infer_hp_unk_map = es.es_infer_hp_unk_map;
    es_infer_heap = es.es_infer_heap;
    es_infer_templ = es.es_infer_templ;
    es_infer_pure = es.es_infer_pure;
    es_infer_rel = es.es_infer_rel # clone;
    es_infer_term_rel = es.es_infer_term_rel;
    es_infer_templ_assume = es.es_infer_templ_assume;
    es_infer_hp_rel = es.es_infer_hp_rel # clone;
    es_group_lbl = es.es_group_lbl;
    es_term_err = es.es_term_err;
    es_var_zero_perm = es.es_var_zero_perm;
    es_conc_err = es.es_conc_err;
  }

let  clear_entailment_history_es xp (es :entail_state) :context =
  let pr_es  = !print_entail_state in
  let pr_ctx = !print_context in
  Debug.no_1 "clear_entailment_history_es"
    pr_es pr_ctx
    (fun _ -> clear_entailment_history_es xp es) es

let clear_entailment_history xp (ctx : context) : context =
  transform_context (clear_entailment_history_es xp) ctx

let clear_entailment_history xp (ctx : context) : context =
  let pr_ctx = !print_context in
  Debug.no_1 "clear_entailment_history"
    pr_ctx pr_ctx
    (fun _ -> clear_entailment_history xp ctx) ctx

let clear_entailment_history_list xp (ctx : list_context) : list_context =
  transform_list_context (clear_entailment_history_es xp,(fun c->c)) ctx

let clear_entailment_history_partial_list xp (ctx : list_partial_context) : list_partial_context =
  transform_list_partial_context (clear_entailment_history_es xp,(fun c->c)) ctx

let clear_entailment_history_failesc_list xp (ctx : list_failesc_context) : list_failesc_context =
  transform_list_failesc_context (idf,idf,clear_entailment_history_es xp) ctx

let fold_partial_context_left_or (c_l:(list_partial_context list)) = match (List.length c_l) with
  | 0 ->  Err.report_error {Err.error_loc = no_pos;
                            Err.error_text = "folding or empty partial context list \n"}
  | 1 -> (List.hd c_l)
  | _ -> List.fold_left (fun a c->  list_partial_context_or a c)
           (List.hd c_l) (List.tl c_l)

let fold_partial_context_left_union (c_l:(list_partial_context list)) = match (List.length c_l) with
  | 0 ->  Err.report_error {Err.error_loc = no_pos;
                            Err.error_text = "folding union empty partial context list \n"}
  | 1 -> (List.hd c_l)
  | _ -> List.fold_left (fun a c->  list_partial_context_union a c) (List.hd c_l) (List.tl c_l)

(* convert entail state to ctx with nf flow and quantify eres
   variable *)
(* need also a binding to catch handler's bound var *)
let conv_elim_res (cvar:typed_ident option)  (c:entail_state)
    (elim_ex_fn: context -> context) =
  let res_typ, b_rez = get_exc_result_type c.es_formula in
  let ctx = (Ctx {c with es_formula =
                           (substitute_flow_into_f !norm_flow_int c.es_formula) } )  in
  match cvar with
  | None -> ctx
  | Some (cvt,cvn) ->
    if not(b_rez) then ctx
    else begin
      let vsv_f = formula_of_pure_N (CP.mkEqVar (CP.SpecVar (res_typ, cvn, Primed)) (CP.mkeRes res_typ) no_pos) no_pos in
      let ctx1 = normalize_max_renaming_s vsv_f no_pos true ctx in
      let ctx1 = push_exists_context [CP.mkeRes res_typ] ctx1 in
      if !Globals.elim_exists_ff then elim_ex_fn ctx1 else  ctx1
    end

let conv_elim_res (cvar:typed_ident option)  (c:entail_state)
    (elim_ex_fn: context -> context) =
  let pr1 = pr_option (pr_pair string_of_typ pr_id) in
  let pr2 = !print_entail_state in
  Debug.no_2 "conv_elim_res" pr1 pr2 !print_context_short
    (fun _ _ -> conv_elim_res cvar c elim_ex_fn) cvar c

(* convert entail state to ctx with nf flow *)
let conv (c:entail_state) (nf(* :nflow *)) = (Ctx {c
                                                   with es_formula =
                                                          (substitute_flow_into_f nf c.es_formula) } )

let conv_lst (c:entail_state) (nf_lst(*: nflow list *)) =
  match nf_lst with
  | [] -> None
  | x::xs -> Some (List.fold_left (fun acc_ctx y -> mkOCtx (conv c y) acc_ctx no_pos) (conv c x)  xs)

let rec splitter (c:context)
    (nf(* :nflow *)) (cvar:typed_ident option)  (elim_ex_fn: context -> context)
    (* : (context option, context option) (\* caught under nf flow, escaped from nf flow*\)   *)
  =
  let rec helper c =
    match c with
    | Ctx b ->
      let ff =(flow_formula_of_ctx c no_pos) in
      (* if (is_eq_flow nf !c_flow_int) then (None,Some c) else *)
      if (subsume_flow nf ff.formula_flow_interval) then  (Some
                                                             (conv_elim_res cvar b elim_ex_fn),None) (* change caught item to normal flow *)
      else if not(overlapping nf ff.formula_flow_interval) ||
              equal_flow_interval !error_flow_int ff.formula_flow_interval ||
              equal_flow_interval !mayerror_flow_int ff.formula_flow_interval
      then (None,Some c)
      else (* let t_caught = intersect_flow nf
              ff.formula_flow_interval in *)
        let t_escape_lst = subtract_flow_list ff.formula_flow_interval nf in
        (Some (conv_elim_res cvar b elim_ex_fn), (* change caught item to normal flow *)
         conv_lst b t_escape_lst)
    | OCtx (b1,b2) ->
      let (r11,r12) = helper b1 in
      let (r21,r22) = helper b2 in
      let r1 = match (r11,r21) with
        | None, None -> None
        | Some c, None -> Some c
        | None, Some c -> Some c
        | Some c1, Some c2 -> Some (mkOCtx c1 c2 no_pos)	in
      let r2 = match (r12,r22) with
        | None, None -> None
        | Some c, None -> Some c
        | None, Some c -> Some c
        | Some c1, Some c2 -> Some (mkOCtx c1 c2 no_pos) in
      (r1,r2) in
  helper c

let splitter_wrapper p c nf cvar elim_ex_fn fn_esc oft =
  let r_caught,r_esc = splitter c nf cvar elim_ex_fn in
  match (r_esc,r_caught) with
  | None, None -> Err.report_error {Err.error_loc = no_pos;
                                    Err.error_text = "Split can not return both empty contexts\n"}
  | Some cl,None -> ([(p,fn_esc cl,oft)],[])
  | None, Some c -> ([],[(p,c,oft)])
  | Some cl,Some c ->  ([(p,fn_esc cl,oft)],[(p,c,oft)])

(* fn transforms context to list of partial context *)
(* fn_esc is being applied to context that escapes; for try-catch construct it may add (pid,0) label to it *)

let splitter_failesc_context  (nf(* :nflow *)) (cvar:typed_ident option) (fn_esc:context -> context)
    (elim_ex_fn: context -> context) (pl :list_failesc_context) : list_failesc_context =
  List.map (fun (fl,el,sl)->
      let r = List.map (fun (p,c, oft)->
          let npt, nctx = splitter_wrapper p c nf cvar elim_ex_fn fn_esc oft in
          (npt, nctx)
        ) sl in
      let re,rs = List.split r in
      (fl,push_esc_elem el (List.concat re),(List.concat rs))) pl

let splitter_failesc_context  (nf(* :nflow *)) (cvar:typed_ident option) (fn_esc:context -> context)
    (elim_ex_fn: context -> context) (pl :list_failesc_context) : list_failesc_context =
  let pr = !print_list_failesc_context in
  let pr2 = !print_flow in
  Debug.no_2 "splitter_failesc_context" pr2 pr pr (fun _ _ -> splitter_failesc_context nf cvar fn_esc elim_ex_fn pl) nf pl
(*
splitter_failesc_context inp1 :(23,24)
                                                                 success
                                                                    v
splitter_failesc_context inp2 : List of Failesc Context: [FEC(0, 0, 1  )]
Successful States:
 State:EXISTS(xv': v_e1_22_548'::e1@M[Orig] * x'::node<xv',b>@M[Orig]&x=x' & y=y' & a=xv_561 & xv'=2 & eres=v_e1_22_548'&{FLOW,(19,20)=e1})[]
                                                                     escape
                                                                        v
splitter_failesc_context@15 EXIT out : List of Failesc Context: [FEC(0, 1, 0 )]
Escaped States:
 Try-Block:0::
  State:EXISTS(xv': v_e1_22_548'::e1@M[Orig] * x'::node<xv',b>@M[Orig]&x=x' & y=y' & a=xv_561 & xv'=2 & eres=v_e1_22_548'&{FLOW,(19,20)=e1})[]
*)

let splitter_partial_context  (nf(* :nflow *)) (cvar:typed_ident option)
    (fn:  path_trace -> context ->  list_partial_context) (fn_esc:context -> context)
    (elim_ex_fn: context -> context) ((fl,sl):partial_context) : list_partial_context =

  let r = List.map (fun (l,c, oft)->
      let r1,r2 = splitter c nf cvar elim_ex_fn in
      let r1 = match r1 with
        | Some c-> Some (fn l c )  (* CF.SuccCtx[(CF.simplify_context c)] *)
        | None -> None in
      match (r1,r2) with
      | None, None -> Err.report_error {Err.error_loc = no_pos;
                                        Err.error_text = "Split can not return both empty contexts\n"}
      | Some cl,None -> cl
      | None, Some c -> [mk_partial_context   (fn_esc c) l]
      | Some cl,Some c ->  list_partial_context_or cl  [(mk_partial_context (fn_esc c) l)]
    ) sl
  in
  list_partial_context_or [ (fl, []) ] (fold_partial_context_left_or r)

let add_to_steps (ss:steps) (s:string) = s::ss
let get_prior_steps (c:context) =
  match c with
  | Ctx es -> es.es_prior_steps
  | OCtx _ -> print_string "Warning : OCtx with get_prior_steps \n"; [] ;;

let add_to_context (c:context) (s:string) =
  (* set_context (fun es -> {es with es_prior_steps = add_to_steps es.es_prior_steps s;}) c *)
  match c with
  | Ctx es -> Ctx {es with es_prior_steps = add_to_steps es.es_prior_steps s; }
  | OCtx _ ->  (* let () = Error.report_warning { *)
    (*             Error.error_loc = !post_pos; *)
    (*             Error.error_text = "[add_to_context] unexpected dealing with OCtx." *)
    (*           } in *)
    (* let () = print_endline (!print_context_short c) in *)
    set_context (fun es -> {es with es_prior_steps = add_to_steps es.es_prior_steps s;}) c
;;

let add_to_context_num i (c:context) (s:string) =
  let pr x = match x with Ctx _ -> "Ctx" | OCtx _ -> "OCtx" in
  Debug.no_1_num i "add_to_context" pr pr_no (fun _ -> add_to_context c s) c

let add_to_estate (es:entail_state) (s:string) =
  {es with es_prior_steps = s::es.es_prior_steps; }

let overwrite_estate_with_steps (es:entail_state) (ss:steps) =
  {es with es_prior_steps = ss; }

let add_to_estate_with_steps (es:entail_state) (ss:steps) =
  {es with es_prior_steps = ss@es.es_prior_steps; }

let add_to_estate_with_steps (es:entail_state) (ss:steps) =
  let pr = !print_entail_state_short in
  Debug.no_1 "add_to_estate_with_steps" pr pr
    (fun _ -> add_to_estate_with_steps es ss) es

(* let rec add_post post f = match f with *)
(*  | EBase b -> *)
(*      let fec = match b.formula_struc_continuation with *)
(* 				| Some b-> add_post post b *)
(* 				| _ -> let (svs,pf,(i_lbl,s_lbl)) = post in *)
(*       EAssume (svs,pf,(fresh_formula_label s_lbl),None) in *)
(*     EBase{b with formula_struc_continuation = Some fec} *)
(*   | ECase b -> ECase {b with formula_case_branches  = List.map (fun (c1,c2)-> (c1,(add_post post c2))) b.formula_case_branches;} *)
(*   | EAssume _ -> Err.report_error {Err.error_loc = no_pos; Err.error_text = "add post found an existing post\n"} *)
(*   | EInfer b ->  EInfer {b with formula_inf_continuation = add_post post b.formula_inf_continuation} *)
(*   | EList b -> EList (map_l_snd (add_post post) b) *)

let rec add_post post f = match f with
  | EBase b ->
    let fec = match b.formula_struc_continuation with
      | Some b-> add_post post b
      | _ -> post
    in
    EBase{b with formula_struc_continuation = Some fec}
  | ECase b -> ECase {b with formula_case_branches  = List.map (fun (c1,c2)-> (c1,(add_post post c2))) b.formula_case_branches;}
  | EAssume _ -> Err.report_error {Err.error_loc = no_pos; Err.error_text = "add post found an existing post\n"}
  | EInfer b ->  EInfer {b with formula_inf_continuation = add_post post b.formula_inf_continuation}
  | EList b -> EList (map_l_snd (add_post post) b)

(* TODO *)
let rec string_of_list_of_pair_formula ls =
  match ls with
  | [] -> ""
  | (f1,f2)::[] -> (!print_formula f1)^"*"^(!print_formula f2)
  | (f1,f2)::rest -> (!print_formula f1)^"*"^(!print_formula f2)^(string_of_list_of_pair_formula rest)

(* and print_formula = ref(fun (c:formula) -> "Cprinter not initialized") *)
(* and print_struc_formula = ref(fun (c:struc_formula) -> "Cprinter not initialized") *)

(* and split_struc_formula f0 = split_struc_formula_a f0 *)

and split_struc_formula f0 = Debug.no_1 "split_struc_formula" (!print_struc_formula) (string_of_list_of_pair_formula) split_struc_formula_a f0

(* split the struc_formula into the list of pre/post pairs *)
and split_struc_formula_a (f:struc_formula):(formula*formula) list = match f with
  | ECase b->
    let r =  List.concat (List.map (fun (c1,c2)->
        let ll = split_struc_formula_a c2 in
        List.map (fun (d1,d2)-> ((normalize 4 d1 (formula_of_pure_N c1 b.formula_case_pos) b.formula_case_pos),d2)) ll) b.formula_case_branches) in
    r
  (* List.map (fun (c1,c2)-> ((push_exists b.formula_case_exists c1),(push_exists b.formula_case_exists c2))) r  *)
  | EBase b->
    let ll = fold_opt split_struc_formula_a b.formula_struc_continuation in
    let e = List.map (fun (c1,c2)-> ((normalize 5 c1 b.formula_struc_base b.formula_struc_pos),c2)) ll in
    let nf = ((*b.formula_struc_explicit_inst@b.formula_struc_implicit_inst@*)b.formula_struc_exists) in
    let e = List.map (fun (c1,c2)-> ((push_exists nf c1),(push_exists nf c2))) e in
    e
  | EAssume b-> [((mkTrue (mkNormalFlow ()) no_pos),b.formula_assume_simpl)]
  | EInfer b -> split_struc_formula_a b.formula_inf_continuation
  | EList b -> fold_l_snd split_struc_formula_a b

let rec filter_bar_branches (br:formula_label list option) (f0:struc_formula) :struc_formula = match br with
  | None -> f0
  | Some br ->
    (* let rec filter_formula (f:formula):formula list = match f with *)
    (* 	| Base {formula_base_label = lbl}  *)
    (* 	| Exists {formula_exists_label = lbl} -> (match lbl with *)
    (* 	  | None -> Err.report_error { Err.error_loc = no_pos;Err.error_text = "view is unlabeled\n"}  *)
    (* 	  | Some lbl -> if (List.mem lbl br) then (Gen.Profiling.inc_counter "total_unfold_disjs";[f]) else (Gen.Profiling.inc_counter "saved_unfolds";[])) *)
    (* 	| Or b -> ((filter_formula b.formula_or_f1)@(filter_formula b.formula_or_f2)) in    *)
    let rec filter_helper (f:struc_formula):struc_formula = match f with
      | EBase b -> (match b.formula_struc_continuation with
          | None -> report_error no_pos "barrier is unlabeled \n"
          | Some f ->
            let l = filter_helper f in
            if isConstEFalse l  then l else EBase {b with formula_struc_continuation = Some l})
      | ECase b ->
        let l = List.map (fun (c1,c2)-> (c1,filter_helper c2)) b.formula_case_branches in
        let l = List.filter (fun (_,c2)-> not (isConstEFalse c2)) l in
        if l=[] then mkEFalse (mkFalseFlow)  no_pos else ECase {b with formula_case_branches = l}
      | EAssume b-> if (List.mem b.formula_assume_lbl br) then f else mkEFalse (mkFalseFlow)  no_pos
      | EInfer b ->
        let l = filter_helper b.formula_inf_continuation in(* Need to check again *)
        if isConstEFalse l then l else EInfer {b with formula_inf_continuation = l}
      | EList b -> mkEList_no_flatten (map_l_snd filter_helper b)  in
    filter_helper f0

let rec filter_branches (br:formula_label list option) (f0:struc_formula) :struc_formula = match br with
  | None -> f0
  | Some br ->
    let rec filter_formula (f:formula):formula list =
      match f with
      | Base {formula_base_label = lbl; formula_base_flow = flowt}
      | Exists {formula_exists_label = lbl; formula_exists_flow = flowt} -> (match lbl with
          | None ->
            (* HACK : this assumed that unlabelled disj is false *)
            (* let cf = !print_formula f in *)
            if is_false_flow flowt.formula_flow_interval then []
            else (* Err.report_error { Err.error_loc = no_pos;Err.error_text = "view is unlabeled "^cf^"\n"} *)
              (* WN -> CG : is this error related to --eps or labelling? *)
              (* for unlabelled branches in lemma; keep all branches for --eps*)
              [f]
          | Some lbl ->
            if (List.mem lbl br) then (Gen.Profiling.inc_counter "total_unfold_disjs";[f])
            else (Gen.Profiling.inc_counter "saved_unfolds";[]))
      | Or b -> ((filter_formula b.formula_or_f1)@(filter_formula b.formula_or_f2)) in
    let rec filter_helper (f:struc_formula):struc_formula = match f with
      | EBase b -> (match b.formula_struc_continuation with
          | None ->
            let l = filter_formula b.formula_struc_base in
            if (l=[]) then mkEFalse (mkFalseFlow) no_pos else EBase {b with formula_struc_base = formula_of_disjuncts l}
          | Some f ->
            let l = filter_helper f in
            if isConstEFalse l  then l else EBase {b with formula_struc_continuation = Some l})
      | ECase b ->
        let l = List.map (fun (c1,c2)-> (c1,filter_helper c2)) b.formula_case_branches in
        let l = List.filter (fun (_,c2)-> not (isConstEFalse c2)) l in
        if l=[] then mkEFalse (mkFalseFlow)  no_pos else ECase {b with formula_case_branches = l}
      | EAssume b-> if (List.mem b.formula_assume_lbl br) then f else mkEFalse (mkFalseFlow)  no_pos
      | EInfer b ->
        let l = filter_helper b.formula_inf_continuation in(* Need to check again *)
        if isConstEFalse l then l else EInfer {b with formula_inf_continuation = l}
      | EList b -> mkEList_no_flatten (map_l_snd filter_helper b)  in
    filter_helper f0


let filter_branches (br:formula_label list option) (f0:struc_formula) :struc_formula =
  let pr = !print_struc_formula in
  let pr1 x = match x with
    | None -> "None"
    | Some l -> "Some"^string_of_int(List.length l) in
  Debug.no_2 "filter_branches" pr1 pr pr
    (fun _ _ -> filter_branches (br:formula_label list option) (f0:struc_formula)) br f0

let rec label_view (f0:struc_formula):struc_formula =
  let rec label_formula (f:formula):formula = match f with
    | Base b -> Base{b with formula_base_label = Some (fresh_formula_label "")}
    | Exists b -> Exists{b with formula_exists_label = Some (fresh_formula_label "")}
    | Or b -> Or{b with formula_or_f1 = label_formula b.formula_or_f1;formula_or_f2 = label_formula b.formula_or_f2;}  in
  let rec label_struc (f:struc_formula):struc_formula = match f with
    | EBase b -> EBase{b with formula_struc_continuation = map_opt label_struc b.formula_struc_continuation; formula_struc_base= label_formula b.formula_struc_base}
    | ECase b -> ECase{b with formula_case_branches = map_l_snd label_struc b.formula_case_branches}
    | EAssume b-> EAssume {b with
                           formula_assume_simpl = label_formula b.formula_assume_simpl;
                           formula_assume_struc = label_struc b.formula_assume_struc;}
    | EInfer b -> EInfer {b with formula_inf_continuation = label_struc b.formula_inf_continuation}
    | EList b -> EList (map_l_snd label_struc b) in
  label_struc f0


let add_label_opt f l =
  match f with
  | Base b -> Base { b with formula_base_label = l}
  | Exists b -> Exists  {b with formula_exists_label = l}
  | Or b -> f

let add_label_opt_struc sf l =
  match sf with
  | EBase b -> EBase {b with formula_struc_base = add_label_opt b.formula_struc_base l}
  | _ -> sf

let add_label f l = add_label_opt f (Some l)

let get_label f =
  match f with
  | Base b -> b.formula_base_label
  | Exists b -> b.formula_exists_label
  | Or b -> None

let get_label_struc sf =
  match sf with
  | EBase b -> get_label b.formula_struc_base
  | _ -> None

let get_view_branches_x (f0:struc_formula):(formula * formula_label) list=
  let rec formula_br (f:formula):(formula * formula_label) list = (
    match f with
    | Base {formula_base_label=lbl}
    | Exists {formula_exists_label=lbl} -> (match lbl with | None -> [] | Some l -> [(f,l)])
    | Or b -> (formula_br b.formula_or_f1)@(formula_br b.formula_or_f2 )
  ) in

  let rec struc_formula_br (f:struc_formula):(formula * formula_label) list = (
    match f with
    | ECase b->
      List.concat (List.map (fun (c1,c2) ->
          let np = (MCP.memoise_add_pure_N (MCP.mkMTrue b.formula_case_pos) c1) in
          let g_f = mkBase HEmp np CVP.empty_vperm_sets TypeTrue (mkTrueFlow ()) [] b.formula_case_pos in
          List.map (fun (d1,d2)->
              normalize_combine g_f d1 no_pos,d2
            ) (struc_formula_br c2)) b.formula_case_branches
        )
    | EBase b-> (
        let l_e_v =(b.formula_struc_explicit_inst@b.formula_struc_implicit_inst@b.formula_struc_exists) in
        match b.formula_struc_continuation with
        | Some l ->
          List.map (fun (c1,c2)->
              let r_f = normalize_combine b.formula_struc_base c1 b.formula_struc_pos in
              ((push_exists l_e_v r_f),c2)
            ) (struc_formula_br l)
        | None ->
          List.map (fun (c1,c2) ->
              ((push_exists l_e_v c1),c2)
            ) (formula_br b.formula_struc_base)
      )
    | EAssume _ -> []
    | EInfer b -> struc_formula_br b.formula_inf_continuation
    | EList b -> fold_l_snd struc_formula_br b
  ) in


  let res = struc_formula_br f0 in
  List.map (fun (f,lbl) -> ((add_label f lbl),lbl)) res

let get_view_branches (f0:struc_formula):(formula * formula_label) list=
  let pr_sf = !print_struc_formula in
  let pr_out = pr_list (pr_pair !print_formula string_of_formula_label) in
  Debug.no_1 "get_view_branches" pr_sf pr_out
    (fun _ -> get_view_branches_x f0) f0

let rec is_disj (f:formula) : bool = match f with
  | Base _
  | Exists _ -> false
  | Or b -> true


let get_bar_branches (f0:struc_formula):(formula * formula_label) list=

  let rec struc_formula_br (f:struc_formula):(formula * formula_label) list = match f with
    | ECase b-> List.concat
                  (List.map (fun (c1,c2) ->
                       let np = (MCP.memoise_add_pure_N (MCP.mkMTrue b.formula_case_pos) c1) in
                       let g_f = mkBase HTrue np CVP.empty_vperm_sets TypeTrue (mkTrueFlow ()) [] b.formula_case_pos in
                       List.map (fun (d1,d2)-> (normalize_combine g_f d1 no_pos,d2)) (struc_formula_br c2)) b.formula_case_branches)
    | EBase b->
      let l_e_v =(b.formula_struc_explicit_inst@b.formula_struc_implicit_inst@b.formula_struc_exists) in
      if is_disj b.formula_struc_base then report_error b.formula_struc_pos "unexpected disjunction in requires clause of a barrier def "
      else (match b.formula_struc_continuation with
          | Some l ->List.map (fun (c1,c2)->
              let r_f = normalize_combine b.formula_struc_base c1 b.formula_struc_pos in
              ((push_exists l_e_v r_f),c2)) (struc_formula_br l)
          | None -> report_error b.formula_struc_pos "barrier branch does not have post conditions")
    | EAssume b -> [(mkTrue_nf no_pos,b.formula_assume_lbl)]
    | EInfer b -> struc_formula_br b.formula_inf_continuation
    | EList b -> fold_l_snd struc_formula_br b
  in
  struc_formula_br f0

let mkEBase_with_cont (pf:CP.formula) cont loc : struc_formula =
  EBase	{
    formula_struc_explicit_inst = [];
    formula_struc_implicit_inst = [];
    formula_struc_exists = [];
    (*formula_struc_base = mkBase HTrue (MCP.OnePF (pf)) TypeTrue (mkTrueFlow ()) [("",pf)] loc;*)
    formula_struc_base = mkBase HEmp (* (MCP.OnePF (pf)) *) (MCP.mix_of_pure pf) CVP.empty_vperm_sets TypeTrue (mkNormalFlow ()) [] loc;
    formula_struc_is_requires = true;
    formula_struc_continuation = cont;
    formula_struc_pos = loc;
    (*formula_ext_complete = true;*)
  }

let propagate_perm_struc_formula_x e (permvar:cperm_var)=
  let f_e_f e = None  in
  let f_f e = Some (propagate_perm_formula e permvar) in
  let f_h_f f = None in
  let f_p_t1 e = Some e in
  let f_p_t2 e = Some e in
  let f_p_t3 e = Some e in
  let f_p_t4 e = Some e in
  let f_p_t5 e = Some e in
  let f=(f_e_f,f_f,f_h_f,(f_p_t1,f_p_t2,f_p_t3,f_p_t4,f_p_t5)) in
  transform_struc_formula_w_perm f permvar e

let propagate_perm_struc_formula e (permvar:cperm_var)=
  Debug.no_2 "propagate_perm_struc_formula"
    !print_struc_formula !print_spec_var !print_struc_formula
    propagate_perm_struc_formula_x  e permvar


let propagate_perm_struc_formula_x e (permvar:cperm_var)=
  let f_e_f e = None in
  let f_f e = Some (propagate_perm_formula e permvar) in
  let f_h_f f = None in
  let f_p_t1 e = Some e in
  let f_p_t2 e = Some e in
  let f_p_t3 e = Some e in
  let f_p_t4 e = Some e in
  let f_p_t5 e = Some e in
  let f=(f_e_f,f_f,f_h_f,(f_p_t1,f_p_t2,f_p_t3,f_p_t4,f_p_t5)) in
  transform_struc_formula_w_perm f permvar e

let propagate_perm_struc_formula e (permvar:cperm_var)=
  Debug.no_2 "propagate_perm_struc_formula"
    !print_struc_formula !print_spec_var !print_struc_formula
    propagate_perm_struc_formula_x  e permvar


and add_origs_to_node_struc (v:string) (e : struc_formula) origs =
  let f_e_f e = None  in
  let f_f e = Some (add_origs_to_node v e origs)in
  let f_h_f f = Some f in
  let f_p_t1 e = Some e in
  let f_p_t2 e = Some e in
  let f_p_t3 e = Some e in
  let f_p_t4 e = Some e in
  let f_p_t5 e = Some e in
  let f=(f_e_f,f_f,f_h_f,(f_p_t1,f_p_t2,f_p_t3,f_p_t4,f_p_t5)) in
  transform_struc_formula f e

let disable_imm_last_phase_ctx ctx =
  transform_context
    (fun es ->
       Ctx{es with es_imm_last_phase = false}
    ) ctx

and enable_imm_last_phase_ctx ctx =
  transform_context
    (fun es ->
       Ctx{es with es_imm_last_phase = true}
    ) ctx

let add_to_aux_conseq_estate es to_aux_conseq pos =
  { es with es_aux_conseq = (*match es.es_aux_conseq with
                              | None -> Some to_aux_conseq
                              | Some f -> Some*) (CP.mkAnd  (*f*) es.es_aux_conseq to_aux_conseq pos)
  }

let add_to_aux_conseq lctx to_aux_conseq pos =
  (match lctx with
   | FailCtx _ -> lctx
   | SuccCtx cl ->
     let new_cl = List.map (fun c ->
         (transform_context
            (fun es ->
               Ctx  (add_to_aux_conseq_estate es to_aux_conseq pos)
            ) c)) cl
     in SuccCtx(new_cl))


let enable_imm_last_phase lctx =
  (match lctx with
   | FailCtx _ -> lctx
   | SuccCtx cl ->
     let new_cl = List.map (fun c -> enable_imm_last_phase_ctx c) cl
     in SuccCtx(new_cl))

and disable_imm_last_phase lctx =
  (match lctx with
   | FailCtx _ -> lctx
   | SuccCtx cl ->
     let new_cl = List.map (fun c -> disable_imm_last_phase_ctx c) cl
     in SuccCtx(new_cl))


and add_to_subst lctx r_subst l_subst =
  match lctx with
  | FailCtx _ -> lctx
  | SuccCtx cl ->
    let new_cl = List.map (fun c ->
        (transform_context
           (fun es ->
              Ctx{es with
                  (* add to the substitution list *)
                  es_subst = ((fst es.es_subst)@r_subst, (snd es.es_subst)@l_subst);
                 })) c) cl
    in SuccCtx(new_cl)

let add_to_subst lctx r_subst l_subst =
  let pr = !print_svl in
  Debug.no_2 "add_to_subst" pr pr pr_none (fun _ _ -> add_to_subst lctx r_subst l_subst) r_subst l_subst

and add_to_exists_pure lctx ex_p pos =
  match lctx with
  | FailCtx _ -> lctx
  | SuccCtx cl ->
    let new_cl = List.map (fun c ->
        (transform_context
           (fun es ->
              Ctx{es with es_exists_pure =
                            match es.es_exists_pure with
                            | None -> ex_p
                            | Some p ->
                              match ex_p with
                              | None     -> Some p
                              | Some e_p -> Some (CP.mkAnd p e_p pos);}
           )) c) cl
    in SuccCtx(new_cl)

let enable_imm_last_phase lctx =
  let pr = !print_list_context in
  Debug.no_1 "enable_imm_last_phase" pr pr (fun _ -> enable_imm_last_phase lctx) lctx

let reset_original (f : formula) : formula = add_original f true
let reset_original_es x = {x with es_formula = (reset_original x.es_formula)}

let reset_original_list_partial_context (f : list_partial_context) : list_partial_context =
  let f1 x = Ctx (reset_original_es x) in
  transform_list_partial_context (f1,(fun c->c)) f

let is_no_heap_h_formula (e : h_formula) : bool =
  let f x = match x with
    | DataNode _
    | ViewNode _ -> Some false
    | _ -> None
  in
  fold_h_formula e f (List.for_all (fun x -> x))

(* let is_no_heap_struc_formula (e : struc_formula) : bool =  *)
(*   let f_struc_f _ _ = None in *)
(*   let f_f _ _ = None in *)
(*   let f_h_formula _ x = Some (x, is_no_heap_h_formula x) in *)
(*   let f_pure =  *)
(*     let f1 _ e = Some (e, true) in *)
(*     (f1,f1,f1) in *)
(*   let f_memo =  *)
(*     let f1 _ e = Some (e, true) in *)
(*     let f2 e _ = (e,true) in *)
(*     let f3 _ e = (e,[]) in *)
(*     (f1,f2,f3,f2,f2) in *)
(*   let f_arg = *)
(*     let f1 e _ = e in *)
(*     let f2 e _ = e in *)
(*     (f1,f1,f1,(f1,f1,f1),f2) in *)
(*   let f = (f_struc_f, f_f, f_h_formula, f_pure, f_memo) in *)
(*     snd(trans_struc_formula e false f f_arg (List.for_all (fun x -> x))) *)

(* let is_no_heap_struc_formula (e : struc_formula) : bool =  *)
(*   let pr = !print_struc_formula in *)
(*   Debug.no_1 "is_no_heap_struc_formula" pr string_of_bool is_no_heap_struc_formula e  *)


(* let fv_heap_in_struc (e : struc_formula) : spec_var_list =  *)
(*   let f_struc_f _ _ = None in *)
(*   let f_f _ _ = None in *)
(*   let f_h_formula _ x = Some (x, is_no_heap_h_formula x) in *)
(*   let f_pure =  *)
(*     let f1 _ e = Some (e, []) in *)
(*     (f1,f1,f1) in *)
(*   let f_memo =  *)
(*     let f1 _ e = Some (e, true) in *)
(*     let f2 e _ = (e,true) in *)
(*     let f3 _ e = (e,[]) in *)
(*     (f1,f2,f3,f2,f2) in *)
(*   let f_arg = *)
(*     let f1 e _ = e in *)
(*     let f2 e _ = e in *)
(*     (f1,f1,f1,(f1,f1,f1),f2) in *)
(*   let f = (f_struc_f, f_f, f_h_formula, f_pure, f_memo) in *)
(*     snd(trans_struc_formula e false f f_arg (List.for_all (fun x -> x))) *)

let extr_rhs_b (e:formula) =
  let h1, p1, vp1, fl1, t1,a1 = split_components e in
  let b1 = {
    formula_base_heap = h1;
    formula_base_pure = p1;
    formula_base_vperm = vp1;
    formula_base_type = t1;
    formula_base_and = a1;
    formula_base_flow = fl1;
    formula_base_label = None;
    formula_base_pos = no_pos }
  in b1

and extr_lhs_b (es:entail_state) =
  let e = es.es_formula in
  let h1, p1, vp1, fl1, t1,a1 = split_components e in
  let b1 = {
    formula_base_heap = h1;
    formula_base_pure = p1;
    formula_base_vperm = vp1;
    formula_base_type = t1;
    formula_base_and = a1;
    formula_base_flow = fl1;
    formula_base_label = None;
    formula_base_pos = no_pos }
  in b1

(** An Hoa : SECTION SIMPLIFY FORMULAE AND CONTEXT **)

let rec simplify_list_failesc_context (ctx : list_failesc_context) (bv : CP.spec_var list) =
  List.map (fun x -> simplify_failesc_context x bv) ctx

and simplify_failesc_context (ctx : failesc_context) (bv : CP.spec_var list) =
  match ctx with
  | (brfaillist,escstk,brctxlist) ->
    let newbrctxlist = List.map (fun x -> simplify_branch_context x bv) brctxlist in
    (brfaillist,escstk,newbrctxlist)

and simplify_branch_context (brctx : branch_ctx) (bv : CP.spec_var list) =
  match brctx with
  | (pathtrc, ctx, oft) ->
    let newctx = simplify_context ctx bv in
    (pathtrc, newctx, oft)

and simplify_context (ctx : context) (bv : CP.spec_var list) =
  match ctx with
  | Ctx ({ es_formula = esformula} as es) ->
    let sesfml = simplify_formula esformula bv in
    Ctx { es with es_formula = sesfml }
  | OCtx (ctx1, ctx2) ->
    OCtx (simplify_context ctx1 bv, simplify_context ctx2 bv)

and simplify_formula (f : formula) (bv : CP.spec_var list) =
  Debug.no_2 "simplify_formula " !print_formula !print_svl !print_formula simplify_formula_x f bv

and simplify_formula_x (f : formula) (bv : CP.spec_var list) =
  match f with
  | Base ({formula_base_heap = heap;
           formula_base_pure = pure;} as fb) ->
    let newheap,newpure,strrep = simplify_heap_pure heap pure bv in
    Base ({fb with formula_base_heap = newheap;
                   formula_base_pure = newpure;})
  | Or ({formula_or_f1 = f1;
         formula_or_f2 = f2;} as fo) ->
    Or ({fo with formula_or_f1 = simplify_formula f1 bv;
                 formula_or_f2 = simplify_formula f2 bv;})
  | Exists ({formula_exists_qvars = qvars;
             formula_exists_heap = heap;
             formula_exists_pure = pure;} as fe) ->
    let newheap,newpure,strrep = simplify_heap_pure heap pure bv in
    let nqvars = List.append (h_fv newheap) (MCP.mfv newpure) in (* Remove redundant quantified variables *)
    let nqvars = Gen.BList.intersect_eq CP.eq_spec_var qvars nqvars in
    Exists ({fe with formula_exists_qvars = nqvars;
                     formula_exists_heap = newheap;
                     formula_exists_pure = newpure;})

(** An Hoa : simplify a heap formula with the constraints, bv stores the base variables **)
(** STEP 1 : replace variables that could be replaced by "original variables" **)
(** STEP 2 : remove constraints concerning "unreachable" variables i.e. var without references **)
and simplify_heap_pure (h : h_formula) (p : MCP.mix_formula) (bv : CP.spec_var list) =
  let f = MCP.pure_of_mix p in
  let sst,strrep = CP.reduce_pure f bv in
  let nh = h_subst sst h in
  let np = MCP.simplify_mix_formula (MCP.memo_subst sst p) in
  (nh, np, strrep)

(** An Hoa : SECTION PARTIAL STRUCTURE **)

(**
 * An Hoa : general function to print a collection.
 **)
let string_of_set so s = "{ " ^ (String.concat " ; " (List.map so s)) ^ " }"


(**
 * An Hoa : Merge the partial heaps into a single heap node
 * For instance,
 *         h::node<#,#,a> * h::node<#,b,#>
 * reduces to h::node<#,b,a> while
 *         h::node<#,#,a> * h::node<#,#,b>
 * is transformed to False.
 * TODO implement
 **)
let rec merge_partial_heaps f = match f with
  | Base fb -> let nh = x_add_1 merge_partial_h_formula fb.formula_base_heap in
    Base { fb with formula_base_heap = nh }
  | Or fo -> 	let nf1 = merge_partial_heaps fo.formula_or_f1 in
    let nf2 = merge_partial_heaps fo.formula_or_f2 in
    Or { fo with formula_or_f1 = nf1; formula_or_f2 = nf2; }
  | Exists fe -> let nh = x_add_1 merge_partial_h_formula fe.formula_exists_heap in
    Exists { fe with formula_exists_heap = nh }

and merge_partial_h_formula f =
  Debug.no_1 "merge_partial_h_formula"
    !print_h_formula !print_h_formula
    merge_partial_h_formula_x f

and merge_partial_h_formula_x f =
  let sc = split_star_h f in
  let dns,vns = List.partition is_data sc in
  (* Collect the data pointers *)
  let dnrootptrs = List.map get_ptr_from_data dns in
  let dnrootptrs = Gen.BList.remove_dups_eq CP.eq_spec_var dnrootptrs in
  (* Partition the data nodes into groups of same pointer *)
  let dnodespart = List.map (fun x -> List.filter (fun y -> CP.eq_spec_var (get_ptr_from_data y) x) dns) dnrootptrs in
  (* Merge the data nodes in each group *)
  let merged_data_nodes = List.map merge_data_nodes_common_ptr dnodespart in
  (* Combine the parts to get the result *)
  combine_star_h (List.append merged_data_nodes vns)


(**
 * An Hoa : Splitting a h_formula by breaking the separation conjunction.
 **)
and split_star_h f = match f with
  | Star { h_formula_star_h1 = h1; h_formula_star_h2 = h2; } ->
    List.append (split_star_h h1) (split_star_h h2)
  | _ -> [f]


(**
 * An Hoa : Reverse operation of split_star_h i.e. combining nodes into a h_formula.
 * TODO express using fold_left instead.
 **)
and combine_star_h cs = match cs with
  | [] -> HEmp
  | h::t -> mkStarH h (combine_star_h t) no_pos


(**
 * An Hoa : Merge a list of data nodes with a common root pointer into either
 *          a single data node or HFalse if there is a clash (and HTrue if
 *          we are merging nothing. This case SHOULD NOT happen.)
 **)
and merge_data_nodes_common_ptr dns =
  List.fold_left merge_two_nodes HEmp dns

(*LDK: TO CHECK ??? how to deal with perms correctly
  Permissions v.s pertial fields
*)
(**
 * An Hoa : Supplementary function to merge two data nodes.
 **)
and merge_two_nodes dn1 dn2 =
  match dn1 with
  | DataNode { h_formula_data_node = dnsv1;
               h_formula_data_name = n1;
               h_formula_data_derv = dr1;
               h_formula_data_split = split1;
               h_formula_data_imm = i1;
               h_formula_data_param_imm = ann_p1;
               h_formula_data_arguments = args1;
               h_formula_data_perm = perm1;
               h_formula_data_origins = origs1;
               h_formula_data_original = orig1;
               h_formula_data_holes = holes1;
               h_formula_data_label = lb1;
               h_formula_data_remaining_branches = br1;
               h_formula_data_pruning_conditions = pc1;
               h_formula_data_pos = pos1 } -> (match dn2 with
      | DataNode { h_formula_data_node = dnsv2;
                   h_formula_data_name = n2;
                   h_formula_data_derv = dr2;
                   h_formula_data_split = split2;
                   h_formula_data_imm = i2;
                   h_formula_data_param_imm = ann_p2;
                   h_formula_data_arguments = args2;
                   h_formula_data_perm = perm2;
                   h_formula_data_origins = origs2;
                   h_formula_data_original = orig2;
                   h_formula_data_holes = holes2;
                   h_formula_data_label = lb2;
                   h_formula_data_remaining_branches = br2;
                   h_formula_data_pruning_conditions = pc2;
                   h_formula_data_pos = pos2 } ->
        (* [Internal] Check if a spec_var is a hole spec_var. *)
        (* TO DO: ??? Can not use spec_var name to tell whether it is a hole
           or not. It also depends on the positions stored in
           h_formula_data_holes *)
        let () = x_binfo_hp (add_str "holes1" (pr_list string_of_int)) holes1 no_pos in
        let () = x_binfo_hp (add_str "holes2" (pr_list string_of_int)) holes2 no_pos in
        let is_hole_specvar sv =
          let svname = CP.name_of_spec_var sv in
          svname.[0] = '#' in
        (* [Internal] Select the non-hole spec_var. *)
        (* let () = print_endline ("merge_two_nodes: \n ### args1 = " ^ (string_of_spec_var_list args1) ^ "\n ### args2 = " ^ (string_of_spec_var_list args2)) in *)
        let combine_vars sv1 sv2 =
          if (is_hole_specvar sv1) then (sv2,true)
          else if (is_hole_specvar sv2) then (sv1,true)
          else (sv1,false)
        in
        let args, not_clashes = List.split (List.map2 combine_vars args1 args2) in
        let not_clashed = List.for_all (fun x -> x) not_clashes in
        let combine_param_ann ann_p1 ann_p2 =  (*(andreeac) TOTDO: check how to combine args annotations*)
          let () = x_tinfo_pp "inside combine_param_ann" no_pos in
          match (ann_p1, ann_p2) with
          | ([], [])     -> []
          | ([], ann2)   -> ann2
          | (ann1, [])   -> ann1
          | (ann1, ann2) -> ann1 in
        let combine_param_ann ann_p1 ann_p2 =
          let pr = string_of_ann_list in
          Debug.no_2 "combine_param_ann" pr pr pr combine_param_ann ann_p1 ann_p2 in
        (* let () = print_endline ("merge_two_nodes" ^ (string_of_bool not_clashed)) in *)
        let res = DataNode { h_formula_data_node = dnsv1;
                             h_formula_data_name = n1;
                             h_formula_data_derv = dr1; (*TO CHECK*)
                             h_formula_data_split = split1; (*TO CHECK*)

                             h_formula_data_imm = i1;
                             h_formula_data_param_imm = combine_param_ann ann_p1 ann_p2;
                             h_formula_data_arguments = args;
                             h_formula_data_perm = None; (*perm1? perm2???*)
                             h_formula_data_origins = origs1; (*??? how to merge??*)
                             h_formula_data_original = orig1;(*??? how to merge??*)
                             h_formula_data_holes =
                               Gen.BList.intersect_eq (=) holes1 holes2;
                             h_formula_data_label = lb1;
                             h_formula_data_remaining_branches =
                               (match br1 with
                                | None -> br2
                                | Some l1 -> (match br2 with
                                    | None -> br1
                                    | Some l2 -> Some (List.append l1 l2)));
                             h_formula_data_pruning_conditions = List.append pc1 pc2;
                             h_formula_data_pos = no_pos } in
        if not_clashed then res else HFalse
      | HEmp -> dn1
      | HFalse -> HFalse
      | _ -> Err.report_error { Err.error_loc = no_pos; Err.error_text = ("[merge_two_nodes] Expect either HEmp or a DataNode but get " ^ (!print_h_formula dn2))} )
  | HEmp -> dn2
  | HFalse -> HFalse
  | _ -> Err.report_error { Err.error_loc = no_pos; Err.error_text = ("[merge_two_nodes] Expect either HEmp or a DataNode but get " ^ (!print_h_formula dn1)) }


(**
 * An Hoa : Create a list [x,x+1,...,x+n-1]
 **)
let rec first_naturals n x = if n = 0 then []
  else x :: (first_naturals (n-1) (x+1))


(**
 * An Hoa : Compute the indices of holes in a list of spec vars.
 **)
let compute_holes_list svs =
  let temp = first_naturals (List.length svs) 0 in
  let res = List.map2 (fun x y -> if (CP.is_hole_spec_var x) then [y] else []) svs temp in
  let res = List.flatten res in
  res

(**
 * An Hoa : Check if svs contain a non-hole variable.
 **)
(* let is_empty svs = List.for_all CP.is_hole_spec_var svs *)

let all_hole_vars svs = List.for_all CP.is_hole_spec_var svs


let mark_derv_self name f =
  let rec h_h f = match f with
    | ViewNode h ->
      if (CP.name_of_spec_var h.h_formula_view_node)="self" &&
         h.h_formula_view_name = name then
        ViewNode {h with h_formula_view_original = false }
      else f
    | Star s -> Star {s with
                      h_formula_star_h1 = h_h s.h_formula_star_h1;
                      h_formula_star_h2 = h_h s.h_formula_star_h2;}
    | StarMinus s -> StarMinus {s with
                                h_formula_starminus_h1 = h_h s.h_formula_starminus_h1;
                                h_formula_starminus_h2 = h_h s.h_formula_starminus_h2;}
    | Conj c -> Conj {c with
                      h_formula_conj_h1 = h_h c.h_formula_conj_h1;
                      h_formula_conj_h2 = h_h c.h_formula_conj_h2;}
    | ConjStar c -> ConjStar {c with
                              h_formula_conjstar_h1 = h_h c.h_formula_conjstar_h1;
                              h_formula_conjstar_h2 = h_h c.h_formula_conjstar_h2;}
    | ConjConj c -> ConjConj {c with
                              h_formula_conjconj_h1 = h_h c.h_formula_conjconj_h1;
                              h_formula_conjconj_h2 = h_h c.h_formula_conjconj_h2;}
    | Phase p -> Phase {p with
                        h_formula_phase_rd = h_h p.h_formula_phase_rd;
                        h_formula_phase_rw =  h_h p.h_formula_phase_rw;}
    | DataNode _
    | ThreadNode _
    | Hole _ | FrmHole _ | HTrue | HFalse | HEmp | HRel _ | HVar _ -> f in
  let rec h_f f = match f with
    | Or b -> Or {b with formula_or_f1 = h_f b.formula_or_f1; formula_or_f2 = h_f b.formula_or_f2; }
    | Base b-> Base {b with formula_base_heap = h_h b.formula_base_heap; }
    | Exists b-> Exists {b with formula_exists_heap = h_h b.formula_exists_heap; } in
  let rec h_struc f = match f with
    | ECase b -> ECase{b with formula_case_branches = map_l_snd h_struc b.formula_case_branches}
    | EBase b -> EBase{b with
                       formula_struc_base = h_f b.formula_struc_base;
                       formula_struc_continuation = map_opt h_struc b.formula_struc_continuation}
    | EAssume _ -> failwith "marh_derv_self: not expecting assume\n"
    | EInfer b -> EInfer{b with formula_inf_continuation = h_struc b.formula_inf_continuation}
    | EList b -> EList (map_l_snd h_struc b) in
  h_struc f


let push_case_f pf sf =
  let rec helper f = match f with
    | ECase f -> ECase {f with formula_case_branches = List.map (fun (c1,c2)-> (CP.mkAnd c1 pf no_pos, c2)) f.formula_case_branches}
    | EBase f -> EBase {f with formula_struc_continuation = map_opt helper f.formula_struc_continuation}
    | EInfer v -> EInfer {v with formula_inf_continuation = helper v.formula_inf_continuation}
    | EAssume _ -> f
    | EList b -> EList (map_l_snd helper b) in
  helper sf

(* this normalization removes EInfer from specs *)
let rec norm_specs (sp:struc_formula) : struc_formula = match sp with
  | ECase b -> ECase {b with formula_case_branches = map_l_snd norm_specs b.formula_case_branches}
  | EBase b ->  (* eliminate EBase if it is just true without existential *)
    if (isConstTrueFormula b.formula_struc_base) && b.formula_struc_explicit_inst==[] && b.formula_struc_implicit_inst==[] && b.formula_struc_exists==[]
    then match b.formula_struc_continuation with | None -> mkETrue  (mkTrueFlow ()) no_pos |Some l -> norm_specs l
    else  EBase {b with formula_struc_continuation = map_opt norm_specs b.formula_struc_continuation}
  | EAssume _ -> sp
  | EInfer b ->
    (* Template: Keep the infer vars of template for other methods in SCC *)
    let templ_vars = List.filter (fun (CP.SpecVar (t, _, _)) -> is_FuncT t) b.formula_inf_vars in
    if templ_vars = [] then norm_specs b.formula_inf_continuation (* eliminate EInfer where possible *)
    else EInfer { b with
                  formula_inf_vars = templ_vars;
                  formula_inf_continuation = norm_specs b.formula_inf_continuation }
  | EList b -> mkEList_no_flatten (map_l_snd norm_specs b)

let rec simplify_post post_fml post_vars = match post_fml with
  | Or {formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos} ->
    Or {formula_or_f1 = simplify_post f1 post_vars;
        formula_or_f2 = simplify_post f2 post_vars;
        formula_or_pos = pos}
  | _ ->
    let h, p, vp, fl, t, a = split_components post_fml in
    let p = CP.mkExists_with_simpl (* Omega.simplify *)!CP.simplify post_vars (MCP.pure_of_mix p) None no_pos in
    let post_fml = mkBase h (MCP.mix_of_pure p) vp t fl a no_pos in
    post_fml

let rec simp_ann_x heap pures = match heap with
  | Star {h_formula_star_h1 = h1;
          h_formula_star_h2 = h2;
          h_formula_star_pos = pos} ->
    let (h1,ps1) = simp_ann h1 pures in
    let (h2,ps2) = simp_ann h2 ps1 in
    (mkStarH h1 h2 pos,ps2)
  | Conj {h_formula_conj_h1 = h1;
          h_formula_conj_h2 = h2;
          h_formula_conj_pos = pos} ->
    let h1,ps1 = simp_ann h1 pures in
    let h2,ps2 = simp_ann h2 ps1 in
    (mkConjH h1 h2 pos,ps2)
  | Phase {h_formula_phase_rd = h1;
           h_formula_phase_rw = h2;
           h_formula_phase_pos = pos} ->
    let h1,ps1 = simp_ann h1 pures in
    let h2,ps2 = simp_ann h2 ps1 in
    (mkPhaseH h1 h2 pos,ps2)
  | DataNode data ->
    let imm = data.h_formula_data_imm in
    let ann_var = CP.fv_ann imm in
    if ann_var = [] then (heap,pures)
    else
      let p,res = List.partition (fun p -> CP.fv p = ann_var) pures in
      begin
        match p with
        | [] -> (DataNode {data with h_formula_data_imm = CP.mkConstAnn Lend (* 2 *)},res) (* TODOIMM andreeac: why do we replace an imm var by the lend constant?  *)
        | [hd] ->
          let is = CP.getAnn hd in
          if is = [] then (heap,pures)
          else
            (DataNode {data with h_formula_data_imm = CP.mkConstAnn (heap_ann_of_int (List.hd is))},res)
        | _ -> (heap,pures)
      end
  | ViewNode view ->
    let imm = view.h_formula_view_imm in
    let ann_var = CP.fv_ann imm in
    if ann_var = [] then (heap,pures)
    else
      let p,res = List.partition (fun p -> CP.fv p = ann_var) pures in
      begin
        match p with
        | [] -> (ViewNode {view with h_formula_view_imm = CP.mkConstAnn Lend(* 2 *)},res) (* TODOIMM why Lend here? *)
        | [hd] ->
          let is = CP.getAnn hd in
          if is = [] then (heap,pures)
          else
            (* andreeac is it obsolete?  *)
            (ViewNode {view with h_formula_view_imm = CP.mkConstAnn (heap_ann_of_int (List.hd is))},res)
        | _ -> (heap,pures)
      end
  | _ -> (heap,pures)

and simp_ann heap pures =
  (* simp_ann_x heap pures *)
  let pr1 = !print_h_formula in
  let pr2 = pr_list !print_pure_f in
  let pr3 = pr_pair pr1 pr2 in
  Debug.no_2 "simp_ann" pr1 pr2 pr3
    (fun _ _ -> simp_ann_x heap pures) heap pures

let rec simplify_fml_ann fml = match fml with
  | Or {formula_or_f1 = f1;
        formula_or_f2 = f2;
        formula_or_pos = pos} ->
    mkOr (simplify_fml_ann f1) (simplify_fml_ann f2) pos
  | Base b ->
    let sub_ann, pures = List.partition CP.isSubAnn (CP.list_of_conjs (MCP.pure_of_mix b.formula_base_pure)) in
    let (h,ps) = x_add simp_ann b.formula_base_heap sub_ann in
    let p = List.fold_left (fun p1 p2 -> CP.mkAnd p1 p2 no_pos) (CP.mkTrue no_pos) (ps@pures) in
    Base {b with formula_base_heap = h; formula_base_pure = MCP.mix_of_pure p}
  | Exists e ->
    let exists_p = MCP.pure_of_mix e.formula_exists_pure in
    let sub_ann, pures = List.partition CP.isSubAnn (CP.list_of_conjs exists_p) in
    let (h,ps) = x_add simp_ann e.formula_exists_heap sub_ann in
    let p = List.fold_left (fun p1 p2 -> CP.mkAnd p1 p2 no_pos) (CP.mkTrue no_pos) (ps@pures) in
    let rm_vars = CP.diff_svl (CP.fv exists_p) (CP.fv p) in
    Exists {e with formula_exists_qvars = CP.diff_svl e.formula_exists_qvars rm_vars;
                   formula_exists_heap = h; formula_exists_pure = MCP.mix_of_pure p}

let rec simplify_ann (sp:struc_formula) : struc_formula = match sp with
  | ECase b -> ECase {b with formula_case_branches = map_l_snd simplify_ann b.formula_case_branches}
  | EBase b -> EBase {b with formula_struc_base = simplify_fml_ann b.formula_struc_base; formula_struc_continuation = map_opt simplify_ann b.formula_struc_continuation}
  | EAssume b -> EAssume {b with
                          formula_assume_simpl = remove_lend (simplify_fml_ann b.formula_assume_simpl);
                          formula_assume_struc = simplify_ann b.formula_assume_struc;}
  | EInfer b ->
    (* report_error no_pos "Do not expect EInfer at this level" *)
    EInfer { b with formula_inf_continuation = simplify_ann b.formula_inf_continuation; }
  | EList b -> mkEList_no_flatten (map_l_snd simplify_ann b)

let rec get_vars_without_rel pre_vars f = match f with
  | Or {formula_or_f1 = f1; formula_or_f2 = f2} ->
    (get_vars_without_rel pre_vars f1) @ (get_vars_without_rel pre_vars f2)
  | Base _ ->
    let h, p, vp, fl, t, a = split_components f in
    let vars = CP.remove_dups_svl (List.concat (List.map one_formula_fv a)) in
    (h_fv h) @ (CP.fv (CP.drop_rel_formula (MCP.pure_of_mix p))) (* @ (CVP.fv vp) *) @ vars
  | Exists e ->
    let h, p, vp, fl, t, a = split_components f in
    let vars = List.concat (List.map one_formula_fv a) in
    let res = (h_fv h) @ (CP.fv (CP.drop_rel_formula (MCP.pure_of_mix p))) (* @ (CVP.fv vp) *) @ vars in
    let alias = MCP.ptr_equations_without_null p in
    let aset = CP.EMapSV.build_eset alias in
    let evars_to_del = List.concat (List.map (fun a -> if CP.intersect (CP.EMapSV.find_equiv_all a aset) pre_vars = [] then [] else [a]) e.formula_exists_qvars) in
    CP.diff_svl res evars_to_del

let simplify_ann (sp:struc_formula) : struc_formula =
  let pr = !print_struc_formula in
  Debug.no_1 "simplify_ann" pr pr simplify_ann sp


(* let normalize_varperm_formula_x (f:formula) : formula =                     *)
(*   let rec helper f = match f with                                           *)
(*     | Base b ->                                                             *)
(*         let mf = MCP.normalize_varperm_mix_formula b.formula_base_pure in   *)
(*         Base {b with formula_base_pure = mf}                                *)
(*     | Exists b ->                                                           *)
(*         let mf = MCP.normalize_varperm_mix_formula b.formula_exists_pure in *)
(*         Exists {b with formula_exists_pure = mf}                            *)
(*     | Or o ->                                                               *)
(*         let f1 = helper o.formula_or_f1 in                                  *)
(*         let f2 = helper o.formula_or_f2 in                                  *)
(*         Or {o with formula_or_f1 = f1; formula_or_f2 = f2}                  *)
(*   in helper f                                                               *)

(* let normalize_varperm_formula (f:formula) : formula =                       *)
(*   Debug.no_1 "normalize_varperm_formula"                                    *)
(*       !print_formula !print_formula                                         *)
(*       normalize_varperm_formula_x f                                         *)

let merge_flag flag1 flag2 = match flag1,flag2 with
  | _,2 -> 2
  | 2,_ -> 2
  | 0,0 -> 0
  | 1,1 -> 2
  | _ -> 1

(*let rec partition_triple fun1 fun2 lst = match lst with*)
(*  | [] -> ([],[],[])*)
(*  | l::ls -> *)
(*    let (tail1,tail2,tail3) = partition_triple fun1 fun2 ls in*)
(*    if fun1 l then (l::tail1,tail2,tail3) else*)
(*    if fun2 l then (tail1,l::tail2,tail3) else (tail1,tail2,l::tail3)*)

(*let split_triple lst = List.fold_left (fun (a1,a2,a3) (b1,b2,b3) -> (a1@[b1],a2@[b2],a3@[b3])) ([],[],[]) lst*)

let add_fst elem = fun (a1,a2,a3,a4,a5,a6) -> (elem@a1,a2,a3,a4,a5,a6)

(*let add_rd elem = fun (a1,a2,a3,a4) -> (a1,a2,elem@a3,a4)*)

let add_fourth elem = fun (a1,a2,a3,a4,a5,a6) -> (a1,a2,a3,elem@a4,a5,a6)

let add_fifth elem = fun (a1,a2,a3,a4,a5,a6) -> (a1,a2,a3,a4,elem@a5,a6)

let fold_left_6 res =
  List.fold_left (fun (a1,a2,a3,a4,a5,a6) (c1,c2,c3,c4,c5,c6) ->
      (a1@c1,a2@c2,a3@c3,a4@c4,a5@c5,merge_flag a6 c6)) ([],[],[],[],[],0) res

let fold_left_2 res =
  List.fold_left (fun (a1,a2) (c1,c2)-> (a1@c1,a2@c2)) ([],[]) res

let add_fst2 elem = fun (a1,a2) -> (elem@a1,a2)

let get_pre_rels pure =
  let conjs = CP.list_of_conjs pure in
  List.filter (fun x -> CP.is_RelForm x) conjs

let rec get_pre_pure_fml xpure_heap prog fml = match fml with
  | Base b ->
    let pure = b.formula_base_pure in
    let xpured,_,_ = x_add xpure_heap 11 prog (b.formula_base_heap) pure 1 in
    [MCP.pure_of_mix (x_add MCP.merge_mems pure xpured true)]
  | Or o -> (get_pre_pure_fml xpure_heap prog o.formula_or_f1) @ (get_pre_pure_fml xpure_heap prog o.formula_or_f2)
  | Exists e ->
    let pure = e.formula_exists_pure in
    let xpured,_,_ = x_add xpure_heap 12 prog (e.formula_exists_heap) pure 1 in
    [MCP.pure_of_mix (x_add MCP.merge_mems pure xpured true)]

let rec get_grp_post_rel_flag fml = match fml with
  | Base b -> if List.exists CP.is_rel_var (CP.fv (MCP.pure_of_mix b.formula_base_pure)) then 1 else 0
  | Or o -> merge_flag (get_grp_post_rel_flag o.formula_or_f1) (get_grp_post_rel_flag o.formula_or_f2)
  | Exists e -> if List.exists CP.is_rel_var (CP.fv (MCP.pure_of_mix e.formula_exists_pure)) then 1 else 0

let rec get_pre_post_vars' ?(vartype=Vartypes.var_with_none) (pre_vars: CP.spec_var list) xpure_heap (sp:struc_formula) prog:
  (CP.spec_var list * CP.spec_var list * CP.spec_var list * CP.spec_var list * CP.formula list * int) =
  match sp with
  | ECase b ->
    let res = List.map (fun (p,s)-> add_fst (CP.fv ~vartype p) (get_pre_post_vars ~vartype pre_vars xpure_heap s prog)) b.formula_case_branches in
    fold_left_6 res
  | EBase b ->
    let base_vars = fv ~vartype b.formula_struc_base in
    let rel_fmls = get_pre_pure_fml xpure_heap prog b.formula_struc_base in
    (match b.formula_struc_continuation with
     | None -> (base_vars,[],[],[],rel_fmls,0)
     | Some l ->  add_fifth rel_fmls (add_fst base_vars (get_pre_post_vars ~vartype (pre_vars@base_vars) xpure_heap l prog)))
  | EAssume b ->
    let f = b.formula_assume_simpl in
    let svl = b.formula_assume_vars in
    let grp_post_rel_flag = get_grp_post_rel_flag f in
    ([], (List.map CP.to_primed svl) @ (get_vars_without_rel pre_vars f),
     (List.map CP.to_primed svl) @ (fv ~vartype f),[],[],grp_post_rel_flag)
  | EInfer b -> add_fourth b.formula_inf_vars (get_pre_post_vars ~vartype pre_vars xpure_heap b.formula_inf_continuation prog)
  | EList b ->
    let l = List.map (fun (_,c)-> get_pre_post_vars ~vartype pre_vars xpure_heap c prog) b in
    fold_left_6 l

and get_pre_post_vars ?(vartype=Vartypes.var_with_none) (pre_vars: CP.spec_var list) xpure_heap (sp:struc_formula) prog =
  Debug.no_4
    "get_pre_post_vars"
    !print_svl
    (fun _ -> "xpure_heap")
    !print_struc_formula
    (fun _ -> "prog")
    (pr_hexa !print_svl !print_svl !print_svl !print_svl (pr_list !CP.print_formula) string_of_int)
    (get_pre_post_vars' ~vartype)
    pre_vars
    xpure_heap
    sp
    prog

let get_pre_post_invs_x (pre_rel_vars: CP.spec_var list) post_rel_vars get_inv_fn (sp0:struc_formula) =
  let rec helper sp lend_vnodes0=
    match sp with
    | ECase b ->
      List.fold_left (fun (r1,r2) (_, s)->
          let pre_invs,post_invs = (helper s lend_vnodes0) in
          (r1@pre_invs,r2@post_invs)
        ) ([],[]) b.formula_case_branches
    | EBase b ->
      let p = get_pure b.formula_struc_base in
      let rel_fmls0 = CP.get_list_rel_args p in
      let rel_fmls1 = List.filter (fun (rel,_) -> CP.mem_svl rel pre_rel_vars) rel_fmls0 in
      let sel_vnodes =  get_views b.formula_struc_base in
      let lend_vnodes = List.filter (fun vn -> CP.isLend vn.h_formula_view_imm) sel_vnodes in
      let  inv_exts =
        if rel_fmls1 = [] then ([]) else
          let sel_svl = List.fold_left (fun r (_,args) -> r@args) [] rel_fmls1 in
          let rel_fm = CP.filter_var p sel_svl in
          let invs = List.map (get_inv_fn sel_svl) sel_vnodes in
          let inv_ext = List.fold_left (fun p1 p2 -> CP.mkAnd p1 p2 b.formula_struc_pos) rel_fm invs in
          [inv_ext]
      in
      (*to inv*)
      (match b.formula_struc_continuation with
       | None -> inv_exts,[]
       | Some l ->
         let pre_invs,post_invs = (helper l (lend_vnodes@lend_vnodes0)) in
         let np = List.fold_left (fun p1 p2 -> CP.mkAnd p1 p2 b.formula_struc_pos)
             (CP.mkTrue no_pos) (inv_exts@pre_invs) in
         ([np],post_invs)
      )
    | EAssume b ->
      let _, bare = split_quantifiers b.formula_assume_simpl in
      let p = get_pure bare in
      let rel_fmls0 = CP.get_list_rel_args p in
      let rel_fmls1 = List.filter (fun (rel,_) -> CP.mem_svl rel post_rel_vars) rel_fmls0 in
      if rel_fmls1 = [] then ([],[]) else
        let sel_svl = List.fold_left (fun r (_,args) -> r@args) [] rel_fmls1 in
        let rel_fm = CP.filter_var p sel_svl in
        let post_vnodes =  get_views bare in
        let post_vnodes1 = Gen.BList.remove_dups_eq (fun vn1 vn2 -> CP.eq_spec_var vn1.h_formula_view_node vn2.h_formula_view_node) (lend_vnodes0@post_vnodes) in
        let post_invs = List.map (get_inv_fn sel_svl) post_vnodes1 in
        let post_inv = CP.conj_of_list (rel_fm::post_invs) no_pos in
        [],[post_inv]
    | EInfer b -> (helper b.formula_inf_continuation lend_vnodes0)
    | EList b ->
      List.fold_left (fun (r1,r2) (_,c)->
          let pre_invs,post_invs = (helper c lend_vnodes0) in
          (r1@pre_invs,r2@post_invs)
        ) ([],[]) b
  in
  let pre_invs,post_invs = helper sp0 [] in
  pre_invs,post_invs

let get_pre_post_invs (pre_rel_vars: CP.spec_var list) post_rel_vars get_inv_fn (sp:struc_formula) =
  let pr1 = pr_list_ln !CP.print_formula in
  let pr2 = !print_struc_formula in
  Debug.no_3 "get_pre_post_invs" !CP.print_svl !CP.print_svl pr2 (pr_pair pr1 pr1)
    (fun _ _ _ -> get_pre_post_invs_x pre_rel_vars post_rel_vars get_inv_fn sp)
    pre_rel_vars post_rel_vars sp

(*todo: drop sel only. now drop all*)
let drop_sel_rel sel_rel_vars f0=
  let rec drop_helper f=
    match f with
    | Base fb -> let np = CP.drop_sel_rel_formula (MCP.pure_of_mix fb.formula_base_pure) sel_rel_vars in
      Base {fb with formula_base_pure = (MCP.mix_of_pure np)}
    | Exists fe ->
      let qvars, base1 = split_quantifiers f in
      let base2 = drop_helper base1 in
      add_quantifiers qvars base2
    | Or orf ->
      Or {orf with formula_or_f1 = drop_helper orf.formula_or_f1;
                   formula_or_f2 = drop_helper orf.formula_or_f2;
         }
  in
  drop_helper f0

let rec get_pre_post_vars_simp (pre_vars: CP.spec_var list) (sp:struc_formula):
  (CP.spec_var list * CP.spec_var list) =
  match sp with
  | ECase b ->
    let res = List.map (fun (p,s)-> add_fst2 (CP.fv p) (get_pre_post_vars_simp pre_vars s)) b.formula_case_branches in
    fold_left_2 res
  | EBase b ->
    let base_vars = fv b.formula_struc_base in
    (match b.formula_struc_continuation with
     | None -> (base_vars,[])
     | Some l -> (add_fst2 base_vars (get_pre_post_vars_simp (pre_vars@base_vars) l)))
  | EAssume b ->
    let f = b.formula_assume_simpl in
    let svl = b.formula_assume_vars in
    ([], (List.map CP.to_primed svl) @ (get_vars_without_rel pre_vars f))
  | EInfer b -> get_pre_post_vars_simp pre_vars b.formula_inf_continuation
  | EList b ->
    let l = List.map (fun (_,c)-> get_pre_post_vars_simp pre_vars c) b in
    fold_left_2 l

(* let drop_varperm_formula (f:formula) =                                                                      *)
(*   let rec helper f =                                                                                        *)
(*     match f with                                                                                            *)
(*       | Base b-> Base {b with formula_base_pure = MCP.drop_varperm_mix_formula b.formula_base_pure}         *)
(*       | Exists b-> Exists {b with formula_exists_pure = MCP.drop_varperm_mix_formula b.formula_exists_pure} *)
(*       | Or b-> Or {b with formula_or_f1 = helper b.formula_or_f1;                                           *)
(* 	      formula_or_f2 = helper b.formula_or_f2}                                                             *)
(*   in                                                                                                        *)
(*   helper f                                                                                                  *)

(* let drop_varperm_struc_formula f =                                                                          *)
(* 	let rec helper f = match f with                                                                           *)
(* 	  | EBase b -> EBase {b with                                                                              *)
(* 		formula_struc_base = drop_varperm_formula b.formula_struc_base;                                         *)
(* 		formula_struc_continuation = map_opt helper b.formula_struc_continuation;}                              *)
(*       | ECase b -> ECase {b with formula_case_branches = map_l_snd helper b.formula_case_branches}          *)
(* 	  | EInfer b -> EInfer {b with formula_inf_continuation = helper b.formula_inf_continuation}              *)
(* 	  | EList b -> EList (map_l_snd helper b) 	                                                              *)
(* 	  | EAssume b -> EAssume {b with                                                                          *)
(* 		formula_assume_simpl = drop_varperm_formula b.formula_assume_simpl;                                     *)
(* 		formula_assume_struc = helper b.formula_assume_struc;} in                                               *)
(* 	helper f                                                                                                  *)


(* let get_varperm_formula_x (f:formula) typ : CP.spec_var list =                                              *)
(*   let rec helper f =                                                                                        *)
(*     match f with                                                                                            *)
(*       | Base b->                                                                                            *)
(*           let p = b.formula_base_pure in                                                                    *)
(*           let res = MCP.get_varperm_mix_formula p typ in                                                    *)
(*           res                                                                                               *)
(*       | Exists b->                                                                                          *)
(*           let p = b.formula_exists_pure in                                                                  *)
(*           let res = MCP.get_varperm_mix_formula p typ in                                                    *)
(*           res                                                                                               *)
(*       | Or b->                                                                                              *)
(*           let res1 = helper b.formula_or_f1 in                                                              *)
(*           let res2 = helper b.formula_or_f1 in                                                              *)
(*           (*approximation*)                                                                                 *)
(*           (match typ with                                                                                   *)
(*             | VP_Zero -> Gen.BList.remove_dups_eq CP.eq_spec_var_ident (res1@res2)                          *)
(*             | VP_Full -> Gen.BList.intersect_eq CP.eq_spec_var_ident res1 res2                              *)
(*             | VP_Value -> Gen.BList.intersect_eq CP.eq_spec_var_ident res1 res2                             *)
(*             (* TODO: Get VarPerm for @lend and @frac *)                                                     *)
(*             | VP_Lend -> []                                                                                 *)
(*             | VP_Frac _ -> []                                                                              *)
(*           )                                                                                                 *)
(*   in                                                                                                        *)
(*   helper f                                                                                                  *)

(* let get_varperm_formula (f:formula) typ : CP.spec_var list =                                                *)
(*   Debug.no_2 "get_varperm_formula"                                                                          *)
(*       !print_formula string_of_vp_ann !print_svl                                                            *)
(*       get_varperm_formula_x f typ                                                                           *)

(* (*get varperm of all concurrent threads*)                                                                   *)
(* let get_varperm_formula_all_x (f:formula) typ : CP.spec_var list =                                          *)
(*   let rec helper f =                                                                                        *)
(*     match f with                                                                                            *)
(*       | Base b->                                                                                            *)
(*           let p = b.formula_base_pure in                                                                    *)
(*           let a = b.formula_base_and in                                                                     *)
(*           let func (a: one_formula) =                                                                       *)
(*             let a_base = formula_of_one_formula a in                                                        *)
(*             (helper a_base)                                                                                 *)
(*           in                                                                                                *)
(*           (*get varperm from child threads*)                                                                *)
(*           let c_vars = List.concat (List.map func a) in                                                     *)
(*           (*get varperm from main thread*)                                                                  *)
(*           let m_vars = MCP.get_varperm_mix_formula p typ in                                                 *)
(*           (m_vars@c_vars)                                                                                   *)
(*       | Exists b->                                                                                          *)
(*           let p = b.formula_exists_pure in                                                                  *)
(*           let a = b.formula_exists_and in                                                                   *)
(*           let func (a: one_formula) =                                                                       *)
(*             let a_base = formula_of_one_formula a in                                                        *)
(*             (helper a_base)                                                                                 *)
(*           in                                                                                                *)
(*           (*get varperm from child threads*)                                                                *)
(*           let c_vars = List.concat (List.map func a) in                                                     *)
(*           (*get varperm from main thread*)                                                                  *)
(*           let m_vars = MCP.get_varperm_mix_formula p typ in                                                 *)
(*           (m_vars@c_vars)                                                                                   *)
(*       | Or b->                                                                                              *)
(*           let res1 = helper b.formula_or_f1 in                                                              *)
(*           let res2 = helper b.formula_or_f1 in                                                              *)
(*           (*approximation*)                                                                                 *)
(*           (match typ with                                                                                   *)
(*             | VP_Zero -> Gen.BList.remove_dups_eq CP.eq_spec_var_ident (res1@res2)                          *)
(*             | VP_Full -> Gen.BList.intersect_eq CP.eq_spec_var_ident res1 res2                              *)
(*             | VP_Value -> Gen.BList.intersect_eq CP.eq_spec_var_ident res1 res2                             *)
(*             (* TODO: Get VarPerm for @lend and @frac *)                                                     *)
(*             | VP_Lend -> []                                                                                 *)
(*             | VP_Frac _ -> []                                                                              *)
(*           )                                                                                                 *)
(*   in                                                                                                        *)
(*   helper f                                                                                                  *)

(* (*get varperm of all concurrent threads*)                                                                   *)
(* let get_varperm_formula_all (f:formula) typ : CP.spec_var list =                                            *)
(*   Debug.no_2 "get_varperm_formula_all"                                                                      *)
(*       !print_formula string_of_vp_ann !print_svl                                                            *)
(*       get_varperm_formula_x f typ                                                                           *)

let rec get_or_post_x rel_id (sp:struc_formula): formula list =  match sp with
  | ECase b -> fold_l_snd (get_or_post_x rel_id) b.formula_case_branches
  | EBase b -> fold_opt (get_or_post_x rel_id) b.formula_struc_continuation
  | EAssume {formula_assume_vars = svl;formula_assume_simpl = f} ->
    (match f with
     | Or _ -> if CP.intersect (fv f) rel_id = [] then [] else [f]
     | _ -> [])
  | EInfer b -> get_or_post_x rel_id b.formula_inf_continuation
  | EList b -> fold_l_snd (get_or_post_x rel_id) b

and get_or_post sp rel_id =
  let pr1 = !print_struc_formula in
  let pr2 = !print_svl in
  let pr3 = pr_list !print_formula in
  Debug.no_2 "get_or_post" pr1 pr2 pr3
    (fun _ _ -> get_or_post_x rel_id sp) sp rel_id

let unwrap_exists f =
  let rec helper f =
    match f with
    | Base b -> ([],[],f)
    | Exists b -> (b.formula_exists_qvars,
                   h_fv b.formula_exists_heap, Exists {b with formula_exists_qvars=[]} )
    | Or b ->
      let (e1,h1,f1) = helper b.formula_or_f1 in
      let (e2,h2,f2) = helper b.formula_or_f2 in
      (e1@e2,h1@h2,mkOr f1 f2 b.formula_or_pos)
  in helper f

let add_exists vs f =
  if vs==[] then f
  else match f with
    | Exists b -> Exists {b with formula_exists_qvars=(vs@b.formula_exists_qvars)}
    | _ -> report_error no_pos "expecting ExistBase formula here"

let wrap_exists svl f =
  let rec helper f =
    match f with
    | Base b ->
      let h,p,vp,fl,t,a = split_components f in
      let pos = pos_of_formula f in
      mkExists svl h p vp t fl a pos
    | Exists e -> add_exists svl f
    | Or o ->
      let f1 = o.formula_or_f1 in
      let f2 = o.formula_or_f2 in
      let pos = pos_of_formula f in
      mkOr (helper f1) (helper f2) pos
  in helper f

let is_shape_h_formula hf =
   let vnodes =  get_views (formula_of_heap hf no_pos) in
   List.for_all (fun vd -> List.for_all CP.is_node_typ vd.h_formula_view_arguments) vnodes

let shape_abs svl f0 =
  let filter_non_shape p =
    let ps = CP.list_of_conjs p in
    let ptr_ps = List.filter (fun p -> CP.is_shape p ) ps in
    CP.conj_of_list ptr_ps (CP.pos_of_formula p)
  in
  let rec helper f =
    match f with
    | Base b ->
          Base {b with formula_base_pure = MCP.mix_of_pure (filter_non_shape (MCP.pure_of_mix b.formula_base_pure))}
    | Exists e -> let quans, base_f = split_quantifiers f in
      add_quantifiers quans (helper base_f)
    | Or o ->
      let f1 = o.formula_or_f1 in
      let f2 = o.formula_or_f2 in
      mkOr (helper f1) (helper f2) o.formula_or_pos
  in helper f0

let lax_impl_of_post f =
  let (evs,hvs,bf) = unwrap_exists f in
  let impl_vs = CP.intersect evs hvs in
  let new_evs = CP.diff_svl evs impl_vs in
  (impl_vs, add_exists new_evs bf)

let lax_impl_of_post f =
  let pr = pr_pair !print_svl !print_formula  in
  Debug.no_1 "lax_impl_of_post" !print_formula pr lax_impl_of_post f

let rec lax_impl_of_struc_post f = match f with
  | EBase b ->
    let l1, f = lax_impl_of_post b.formula_struc_base in
    let fc, l2 = map_opt_res lax_impl_of_struc_post b.formula_struc_continuation in
    EBase {b with formula_struc_base = f; formula_struc_continuation = fc}, l1@l2
  | EList b ->
    let l,r = List.fold_left (fun (a1,a2) (c1,c2)->
        let c2,l = lax_impl_of_struc_post c2 in
        (c1,c2)::a1, l@a2) ([],[]) b in
    EList l,r
  | ECase b ->
    let l,r = List.fold_left (fun (a1,a2) (c1,c2)->
        let c2,l = lax_impl_of_struc_post c2 in
        (c1,c2)::a1, l@a2) ([],[]) b.formula_case_branches in
    ECase {b with formula_case_branches = l}, r
  | EInfer _
  | EAssume _ -> report_error no_pos "Unexpected structure in lax_impl_of_struc_post"

let lax_impl_of_struc_post f =
  let pr = pr_pair !print_struc_formula !print_svl  in
  Debug.no_1 "lax_impl_of_struc_post" !print_struc_formula pr lax_impl_of_struc_post f

let fv_wo_rel (f:formula) =
  let vs = fv f in
  List.filter (fun v -> let t = CP.type_of_spec_var v in not(is_RelT t) && t!=HpT) vs

(* Termination: Check whether a formula contains LexVar *)
let rec has_lexvar_formula f =
  match f with
  | Base _
  | Exists _ ->
    let _, pure_f, _, _, _, _ = split_components f in
    CP.has_lexvar (MCP.pure_of_mix pure_f)
  | Or { formula_or_f1 = f1; formula_or_f2 = f2 } ->
    (has_lexvar_formula f1) || (has_lexvar_formula f2)

(* Same as the above method except that it also tells     *)
(* whether we have unknown LexVar in precondition (TermU) *)
let rec has_unknown_pre_lexvar_formula f =
  match f with
  | Base _
  | Exists _ ->
    let _, pure_f, _, _, _, _ = split_components f in
    CP.has_unknown_pre_lexvar (MCP.pure_of_mix pure_f)
  | Or { formula_or_f1 = f1; formula_or_f2 = f2 } ->
    let has_lexvar_f1, has_unknown_f1 = has_unknown_pre_lexvar_formula f1 in
    let has_lexvar_f2, has_unknown_f2 = has_unknown_pre_lexvar_formula f2 in
    (has_lexvar_f1 || has_lexvar_f2, has_unknown_f1 || has_unknown_f2)

let has_unknown_pre_lexvar_struc sf =
  let arg = () in
  let f_arg a _ = a in
  let f_comb bl = List.exists idf bl in
  let id2 = fun a _-> (a, false) in
  let id2l = fun _ a -> (a, []) in
  let f_f _ f =
    let _, has_unknown_pre_lexvar = has_unknown_pre_lexvar_formula f in
    Some (f, has_unknown_pre_lexvar)
  in
  snd (trans_struc_formula sf arg (nonef2, f_f, nonef2, (nonef2, nonef2, nonef2), (nonef2, id2, id2l, id2, id2))
         (f_arg, f_arg, f_arg, (f_arg, f_arg, f_arg), f_arg) f_comb)

let rec has_known_pre_lexvar_formula f =
  match f with
  | Base _
  | Exists _ ->
    let _, pure_f, _, _, _, _ = split_components f in
    CP.has_known_pre_lexvar (MCP.pure_of_mix pure_f)
  | Or { formula_or_f1 = f1; formula_or_f2 = f2 } ->
    let has_known_f1 = has_known_pre_lexvar_formula f1 in
    let has_known_f2 = has_known_pre_lexvar_formula f2 in
    has_known_f1 || has_known_f2

let has_known_pre_lexvar_struc sf =
  let arg = () in
  let f_arg a _ = a in
  let f_comb bl = List.exists idf bl in
  let id2 = fun a _-> (a, false) in
  let id2l = fun _ a -> (a, []) in
  let f_f _ f =
    let has_known_pre_lexvar = has_known_pre_lexvar_formula f in
    Some (f, has_known_pre_lexvar)
  in
  snd (trans_struc_formula sf arg (nonef2, f_f, nonef2, (nonef2, nonef2, nonef2), (nonef2, id2, id2l, id2, id2))
         (f_arg, f_arg, f_arg, (f_arg, f_arg, f_arg), f_arg) f_comb)

let rec collect_term_ann f =
  match f with
  | Base _
  | Exists _ ->
    let _, pure_f, _, _, _, _ = split_components f in
    CP.collect_term_ann (MCP.pure_of_mix pure_f)
  | Or { formula_or_f1 = f1; formula_or_f2 = f2 } ->
    (collect_term_ann f1) @ (collect_term_ann f2)

let rec collect_term_ann_for_svcomp_competion_x sf =
  match sf with
  | EList els ->
    List.concat (List.map (fun (_,sf) ->
        collect_term_ann_for_svcomp_competion sf
      ) els)
  | ECase ec ->
    List.concat (List.map (fun (f,sf) ->
        (CP.collect_term_ann f) @ (collect_term_ann_for_svcomp_competion sf)
      ) ec.formula_case_branches)
  | EBase eb ->
    let r1 = collect_term_ann eb.formula_struc_base in
    let r2 = match eb.formula_struc_continuation with
      | None -> []
      | Some sf -> collect_term_ann_for_svcomp_competion sf in
    r1 @ r2
  | EAssume ea ->
    (* no collection in assume *)
    []
  (* let r1 = collect_term_ann ea.formula_assume_simpl in                      *)
  (* let r2 = collect_term_ann_for_svcomp_competion ea.formula_assume_struc in *)
  (* r1 @ r2                                                                   *)
  | EInfer ei ->
    collect_term_ann_for_svcomp_competion ei.formula_inf_continuation

and collect_term_ann_for_svcomp_competion sf =
  let pr_sf = (add_str "sf" !print_struc_formula) in
  let pr_res = (add_str "res" (pr_list !CP.print_term_ann)) in
  Debug.no_1 "collect_term_ann_for_svcomp_competion_x" pr_sf pr_res
    (fun _ -> collect_term_ann_for_svcomp_competion_x sf) sf

let collect_term_ann_fv f =
  let ann_lst = collect_term_ann f in
  List.concat (List.map CP.fv_of_term_ann ann_lst)

let rec norm_assume_with_lexvar tpost struc_f =
  let norm_f = norm_assume_with_lexvar tpost in
  match struc_f with
  | ECase ec -> ECase { ec with formula_case_branches = map_l_snd norm_f ec.formula_case_branches }
  | EBase eb -> EBase { eb with formula_struc_continuation = map_opt norm_f eb.formula_struc_continuation }
  | EAssume ea ->
    if (has_lexvar_formula ea.formula_assume_simpl) then struc_f
    else
      let lexvar = CP.mkPure (CP.mkLexVar tpost [] [] no_pos) in
      let post = fst (combine_and ea.formula_assume_simpl (MCP.mix_of_pure lexvar)) in
      EAssume { ea with
                formula_assume_simpl = post;
                formula_assume_struc = mkEBase post None no_pos }
  | EInfer ei -> EInfer { ei with formula_inf_continuation = norm_f ei.formula_inf_continuation }
  | EList el -> mkEList_no_flatten (map_l_snd norm_f el)

let norm_lexvar_for_infer uid (f: formula): formula * bool =
  let f_b _ bf =
    let (pf, il) = bf in
    match pf with
    | LexVar t_info ->
      let has_mayloop, nann = match t_info.lex_ann with
        | MayLoop _ -> true, CP.mkUTPre uid
        | _ -> false, t_info.lex_ann in
      let call_num = uid.CP.tu_call_num in
      let pos = t_info.lex_loc in
      let npf = LexVar { t_info with
                         lex_ann = nann;
                         lex_exp = if has_mayloop then (mkIConst call_num pos)::t_info.lex_exp else t_info.lex_exp;
                         lex_fid = uid.CP.tu_fname;
                         lex_tmp = uid.CP.tu_args } in
      Some ((npf, il), has_mayloop)
    | _ -> Some (bf, false)
  in
  let f_arg = (voidf2, voidf2, voidf2, (voidf2, voidf2, voidf2), voidf2) in
  let f_aset _ a = (a, []) in
  let f_m a _ = (a, false) in
  let f_trans = (nonef2, nonef2, nonef2, (nonef2, f_b, nonef2), (nonef2, f_m, f_aset, f_m, f_m)) in
  trans_formula f () f_trans f_arg or_list

let rec norm_struc_with_lexvar is_primitive is_tnt_inf uid_opt struc_f =
  let norm_f = norm_struc_with_lexvar is_primitive is_tnt_inf uid_opt in
  match struc_f with
  | ECase ec -> ECase { ec with formula_case_branches = map_l_snd norm_f ec.formula_case_branches }
  | EBase eb ->
    let cont = eb.formula_struc_continuation in
    if (has_lexvar_formula eb.formula_struc_base) then
      if not is_tnt_inf then struc_f
      else
        match uid_opt with
        | None -> struc_f
        | Some uid ->
          let norm_base, has_mayloop = norm_lexvar_for_infer uid eb.formula_struc_base in
          (* if not has_mayloop then struc_f                                                 *)
          (* else                                                                            *)
          (*   let tpost = CP.mkUTPost uid in                                                *)
          (*   EBase { eb with                                                               *)
          (*     (* MayLoop will be changed to UTPre *)                                      *)
          (*     formula_struc_base = norm_base;                                             *)
          (*     formula_struc_continuation = map_opt (norm_assume_with_lexvar tpost) cont } *)
          let tpost = CP.mkUTPost uid in
          EBase { eb with
                  (* MayLoop will be changed to UTPre *)
                  formula_struc_base = norm_base;
                  formula_struc_continuation = map_opt (norm_assume_with_lexvar tpost) cont }
    else EBase { eb with formula_struc_continuation = map_opt norm_f cont }
  | EAssume _ ->
    let lexvar, assume =
      if is_primitive then CP.mkLexVar Term [] [] no_pos, struc_f
      else if not is_tnt_inf then CP.mkLexVar (MayLoop None) [] [] no_pos, struc_f
      else
        match uid_opt with
        | None -> CP.mkLexVar (MayLoop None) [] [] no_pos, struc_f
        | Some uid ->
          let tpre = CP.mkUTPre uid in
          let tpost = CP.mkUTPost uid in
          CP.mkLexVar tpre [] [] no_pos,
          norm_assume_with_lexvar tpost struc_f
    in
    (* let assume =                              *)
    (*   if not is_tnt_inf then struc_f          *)
    (*   else                                    *)
    (*     let tpost = CP.mkUTPost uid in        *)
    (*     norm_assume_with_lexvar tpost struc_f *)
    (* in                                        *)
    mkEBase_with_cont (CP.mkPure lexvar) (Some assume) no_pos
  | EInfer ei -> EInfer { ei with formula_inf_continuation = norm_struc_with_lexvar is_primitive
                                      (is_tnt_inf || ei.formula_inf_obj # is_term) uid_opt ei.formula_inf_continuation }
  | EList el -> mkEList_no_flatten (map_l_snd norm_f el)

let norm_struc_with_lexvar is_primitive is_tnt_inf uid_opt struc_f =
  if is_primitive then norm_struc_with_lexvar is_primitive is_tnt_inf uid_opt struc_f
  else
    let pr = !print_struc_formula in
    Debug.no_2 "norm_struc_with_lexvar" string_of_bool pr pr
      (fun _ _ -> norm_struc_with_lexvar is_primitive is_tnt_inf uid_opt struc_f) is_tnt_inf struc_f

(* TNT: Add inf_obj from cmd line *)
let rec add_inf_cmd_struc is_primitive f =
  if is_primitive || Globals.infer_const_obj # is_empty then f
  else
    match f with
    | EInfer ei -> EInfer { ei with
                            formula_inf_obj = ei.formula_inf_obj # mk_or_sel Globals.infer_const_obj; }
    | EList el -> EList (List.map (fun (sld, s) -> (sld, add_inf_cmd_struc is_primitive s)) el)
    | _ -> EInfer {
        formula_inf_obj = Globals.clone_sub_infer_const_obj_sel ();
        (* Globals.infer_const_obj # clone; *)
        formula_inf_post = true (* Globals.infer_const_obj # is_post *);
        formula_inf_xpost = None;
        formula_inf_transpec = None;
        formula_inf_vars = [];
        formula_inf_continuation = f;
        formula_inf_pos = pos_of_struc_formula f }

let add_inf_cmd_struc is_primitive f =
  let pr = !print_struc_formula in
  Debug.no_1 "add_inf_cmd_struc" pr pr
    (fun _ -> add_inf_cmd_struc is_primitive f) f

let rec set_inf_obj_struc itype f =
  match f with
  | EInfer ei ->
    let () = ei.formula_inf_obj # set itype in
    EInfer ei
  | EList el -> EList (List.map (fun (sld, s) -> (sld, set_inf_obj_struc itype s)) el)
  | _ ->
    let new_inf_obj = new Globals.inf_obj_sub in
    let () = new_inf_obj # set itype in
    EInfer {
      formula_inf_obj = new_inf_obj;
      formula_inf_post = true (* Globals.infer_const_obj # is_post *);
      formula_inf_xpost = None;
      formula_inf_transpec = None;
      formula_inf_vars = [];
      formula_inf_continuation = f;
      formula_inf_pos = pos_of_struc_formula f }

let set_inf_obj_struc itype f =
  let pr = !print_struc_formula in
  Debug.no_2 "set_inf_post_term_struc" string_of_inf_const pr pr
    set_inf_obj_struc itype f

(* Termination: Add the call numbers and the implicit phase
 * variables to specifications if the option
 * --dis-call-num and --dis-phase-num are not enabled (default) *)

let rec add_term_nums_struc struc_f log_vars call_num add_phase =
  match struc_f with
  | ECase ef ->
    let n_cl, pvs  = map_l_snd_res (fun c -> add_term_nums_struc c log_vars call_num add_phase) ef.formula_case_branches in
    (ECase { ef with formula_case_branches = n_cl }, List.concat pvs)
  | EBase ef ->
    let n_cont, pvc = map_opt_res (fun c -> add_term_nums_struc c log_vars call_num add_phase) ef.formula_struc_continuation in
    let n_base, pvb = add_term_nums_formula ef.formula_struc_base log_vars call_num add_phase in
    (EBase { ef with
             formula_struc_base = n_base;
             formula_struc_continuation = n_cont}, pvb @ pvc)
  | EAssume _ -> (struc_f, [])
  | EInfer ef ->
    let n_cont, pvc = add_term_nums_struc ef.formula_inf_continuation log_vars call_num add_phase in
    (EInfer { ef with formula_inf_continuation = n_cont }, pvc)
  | EList b ->
    let n_sf, pvs = map_l_snd_res (fun c-> add_term_nums_struc c log_vars call_num add_phase) b in
    (EList n_sf, List.concat pvs)

and add_term_nums_formula f log_vars call_num add_phase =
  match f with
  | Base ({ formula_base_pure = p } as base) ->
    let p = MCP.pure_of_mix p in
    let pv = fresh_phase_var_opt add_phase in
    let n_p, n_pv = CP.add_term_nums_pure p log_vars call_num pv in
    (Base { base with formula_base_pure = MCP.mix_of_pure n_p }, n_pv)
  | Exists ({ formula_exists_pure = p } as ex) ->
    let p = MCP.pure_of_mix p in
    let pv = fresh_phase_var_opt add_phase in
    let n_p, n_pv = CP.add_term_nums_pure p log_vars call_num pv in
    (Exists { ex with formula_exists_pure = MCP.mix_of_pure n_p }, n_pv)
  | Or ({ formula_or_f1 = f1; formula_or_f2 = f2 } as orf) ->
    let n_f1, pv1 = add_term_nums_formula f1 log_vars call_num add_phase in
    let n_f2, pv2 = add_term_nums_formula f2 log_vars call_num add_phase in
    (Or { orf with formula_or_f1 = n_f1; formula_or_f2 = n_f2 }, pv1 @ pv2)

and fresh_phase_var_opt add_phase =
  if add_phase then
    let pv_name = fresh_any_name "pv" in
    Some (CP.SpecVar(Int, pv_name, Unprimed))
  else None

(* Termination: Count the number of Term in a specification *)
let rec count_term_struc (sf: struc_formula) : int = match sf with
  | ECase b -> List.fold_left (fun acc (_, sf) -> acc + (count_term_struc sf)) 0 b.formula_case_branches
  | EBase b ->(match b.formula_struc_continuation with
      | None ->count_term_formula b.formula_struc_base
      | Some l -> (count_term_formula b.formula_struc_base) + (count_term_struc l))
  | EAssume _ -> 0
  | EInfer b -> count_term_struc b.formula_inf_continuation
  | EList b -> List.fold_left (fun acc ef -> acc + (count_term_struc (snd ef))) 0 b

and count_term_formula f = match f with
  | Base b -> CP.count_term_pure (MCP.pure_of_mix b.formula_base_pure)
  | Exists b -> CP.count_term_pure (MCP.pure_of_mix b.formula_exists_pure)
  | Or b -> (count_term_formula b.formula_or_f1) + (count_term_formula b.formula_or_f2)

let get_ctx_label sctx =
  let rec helper c = match c with
    | Ctx es -> es.es_group_lbl
    | OCtx (c1,c2) -> helper c1
  in helper sctx

let update_ctx_label sctx l =
  let rec helper c = match c with
    | Ctx es -> Ctx {es with es_group_lbl = l}
    | OCtx (c1,c2) -> OCtx (helper c1,helper c2)
  in
  if Lab2_List.is_unlabelled l then sctx
  else helper sctx

let merge_struc_pre (sp:struc_formula) (pre:formula list): struc_formula =
  let rec helper sp pre = match sp with
    | ECase b -> report_error b.formula_case_pos ("Not supported nested case analysis")
    | EBase b -> sp
    | EAssume _ ->
      if isConstTrueFormula pre then sp
      else mkEBase pre (Some sp) no_pos
    | EInfer b -> EInfer {b with formula_inf_continuation = helper b.formula_inf_continuation pre}
    | EList _  -> report_error no_pos "Stages not supported" in
  match sp with
  | EList b-> (try EList (List.map2 (fun (l,e) a ->(l,helper e a)) b pre) with _ -> sp)
  | _ -> (match pre with | x::[] -> helper sp x | _ -> sp)

(*-------------------------------------------------
  init[LOCKA](self) -->
    requires self::lock<_ >
    ensures [ref ls] self::LOCKA(1)<> & ls'=union(S,{self})

  finalize[LOCKA](self) -->
    requires self::LOCKA(1)<> & (self in ls)
    ensures [ref ls] self::lock<_> & ls'=diff(ls,{self})

  acquire(self) -->
    requires [f] self::LOCKA(f)<n> & (self notin ls)
    ensures  [ref ls] self::LOCKA(f)<n> * self::cellInv<> & ls'=union(ls,{self})

  release(self) -->
    requires self::LOCKA(f)<> * self::CellInv<> & (self in ls) & 0<f<=1
    ensures  [ref ls] self::LOCKA(f)<> & ls'=diff(ls,{self})

  NEW !!!

  release(self) -->
    requires self::CellInv<> & (self in ls) & 0<f<=1
    ensures  [ref ls] ls'=diff(ls,{self})


  In order to control the number of automatic split,
  we employ the following heuristics and the original field
  of LOCK

            pre       post
  ---------------------------------
  init     |   N/A    false
  finalize |   NO      N/A
  acquire  |   NO      NO
  release  |   YES     NO

  In context.ml, we constraint the lemma application as follows:
  if (is_l_lock && is_r_lock && vr_view_orig) then
    true
  else if (is_l_lock && is_r_lock && not vr_view_orig) then
    false

  We only allow a SPLIT when the RHS is original
  -------------------------------------------------*)

(*automatically generate pre/post conditions of init[lock_sort](lock_var,lock_args) *)
let prepost_of_init_x (var:CP.spec_var) sort (args:CP.spec_var list) (lbl:formula_label) pos =
  let data_node = DataNode ({
      h_formula_data_node = var;
      h_formula_data_name = lock_name;
      h_formula_data_derv = false;
      h_formula_data_split = SPLIT0;
      h_formula_data_imm = CP.ConstAnn(Mutable);
      h_formula_data_param_imm = []; (* list should have the same size as h_formula_data_arguments *)
      h_formula_data_perm = None;
      h_formula_data_origins = [];
      h_formula_data_original = false; (*TO CHECK: tmporarily, to prohibit SPLITTING of permission*)
      h_formula_data_arguments = []; (*TO CHECK*)
      h_formula_data_holes = [];
      h_formula_data_remaining_branches = None;
      h_formula_data_pruning_conditions = [];
      h_formula_data_label = None;
      h_formula_data_pos = pos})
  in
  let uargs = List.map CP.to_unprimed args in
  let lock_node = ViewNode ({
      h_formula_view_node = var; (*Have to reserve type of view_node to finalize*)
      h_formula_view_name = sort; (*lock_sort*)
      h_formula_view_derv = false;
      h_formula_view_split = SPLIT0;
      h_formula_view_imm = CP.ConstAnn(Mutable);
      h_formula_view_perm = None;
      h_formula_view_arguments = uargs;
      h_formula_view_ho_arguments = [];
      h_formula_view_annot_arg = [];
      h_formula_view_args_orig = CP.initialize_positions_for_view_params (CP.sv_to_view_arg_list uargs);
      h_formula_view_modes = []; (*???*)
      h_formula_view_coercible = false; (*??*)
      h_formula_view_origins = [];
      h_formula_view_original = false;(*TO CHECK: tmporarily, to prohibit SPLITTING of permission*)
      h_formula_view_lhs_case = false;
      h_formula_view_unfold_num = 0;
      h_formula_view_remaining_branches = None;
      h_formula_view_pruning_conditions = [];
      h_formula_view_label = None;
      h_formula_view_pos = pos })
  in
  (****LOCKSET****)
  let ls_uvar = CP.mkLsVar Unprimed in
  let ls_pvar = CP.mkLsVar Primed in
  let ls_uvar_exp = CP.Var (ls_uvar,pos) in
  let ls_pvar_exp = CP.Var (ls_pvar,pos) in
  let var_exp = CP.Var (var,pos)in
  let bag_exp = CP.mkBag [var_exp] pos in  (* {l} *)
  let union_exp = CP.mkBagUnion [ls_uvar_exp;bag_exp] pos in (* union(ls,{l})*)
  let ls_f = CP.mkEqExp ls_pvar_exp union_exp pos in (*ls' = union(ls,{l})*)
  (**************)
  (****LOCKSET LSMU****)
  let lsmu_uvar = CP.mkLsmuVar Unprimed in
  let lsmu_pvar = CP.mkLsmuVar Primed in
  let lsmu_uvar_exp = CP.Var (lsmu_uvar,pos) in
  let lsmu_pvar_exp = CP.Var (lsmu_pvar,pos) in
  let varmu_exp = CP.Level (var,pos)in
  let bagmu_exp = CP.mkBag [varmu_exp] pos in  (* {l.mu} *)
  let unionmu_exp = CP.mkBagUnion [lsmu_uvar_exp;bagmu_exp] pos in (* union(LSMU,{l.mu})*)
  let lsmu_f = CP.mkEqExp lsmu_pvar_exp unionmu_exp pos in (*lsmu' = union(lsmu,{l.mu})*)
  (**************)
  let lock_f = if (!Globals.allow_locklevel) then
      CP.And (ls_f, lsmu_f,pos)
    else
      ls_f
  in
  (**************)
  let post = mkBase_simp lock_node (MCP.memoise_add_pure_N (MCP.mkMTrue pos) lock_f) in
  (* let post = formula_of_heap_w_normal_flow lock_node pos in *)
  let post = mkEAssume_simp [ls_uvar;lsmu_uvar] post (mkEBase post None no_pos) lbl in
  let pre = formula_of_heap_w_normal_flow data_node pos in
  EBase {
    formula_struc_explicit_inst = [];
    formula_struc_implicit_inst = [];
    formula_struc_exists = [];
    formula_struc_base = pre;
    formula_struc_is_requires = true;
    formula_struc_continuation = Some post;
    formula_struc_pos = pos}


(*automatically generate pre/post conditions of init[lock_sort](lock_var,lock_args) *)
let prepost_of_init (var:CP.spec_var) sort (args:CP.spec_var list) (lbl:formula_label) pos =
  Debug.no_3 "prepost_of_init"
    !print_sv
    (fun str -> str)
    !print_svl
    !print_struc_formula
    (fun _ _ _ -> prepost_of_init_x var sort args lbl pos) var sort args

(*automatically generate pre/post conditions of finalize[lock_sort](lock_var,lock_args) *)
let prepost_of_finalize_x (var:CP.spec_var) sort (args:CP.spec_var list) (lbl:formula_label) pos : struc_formula =
  let data_node = DataNode ({
      h_formula_data_node = var;
      h_formula_data_name = lock_name;
      h_formula_data_derv = false;
      h_formula_data_split = SPLIT0;
      h_formula_data_imm = CP.ConstAnn(Mutable);
      h_formula_data_param_imm = [];    (* list should have the same size as h_formula_data_arguments *)
      h_formula_data_perm = None;
      h_formula_data_origins = [];
      h_formula_data_original = true; (*after finalize, allow SPLIT*)
      h_formula_data_arguments = []; (*TO CHECK*)
      h_formula_data_holes = [];
      h_formula_data_remaining_branches = None;
      h_formula_data_pruning_conditions = [];
      h_formula_data_label = None;
      h_formula_data_pos = pos})
  in
  let uargs = List.map CP.to_unprimed args in
  let lock_node = ViewNode ({
      h_formula_view_node = var; (*Have to reserve type of view_node to finalize*)
      h_formula_view_name = sort; (*lock_sort*)
      h_formula_view_derv = false;
      h_formula_view_split = SPLIT0;
      h_formula_view_imm = CP.ConstAnn(Mutable);
      h_formula_view_perm = None;
      h_formula_view_arguments = uargs;
      h_formula_view_ho_arguments = [] (* todo:HO *);
      h_formula_view_annot_arg = [];
      h_formula_view_args_orig = CP.initialize_positions_for_view_params (CP.sv_to_view_arg_list uargs);
      h_formula_view_modes = []; (*???*)
      h_formula_view_coercible = false; (*??*)
      h_formula_view_origins = [];
      h_formula_view_original = false; (*NOT ALLOW SPLIT*)
      h_formula_view_lhs_case = false;
      h_formula_view_unfold_num = 0;
      h_formula_view_remaining_branches = None;
      h_formula_view_pruning_conditions = [];
      h_formula_view_label = None;
      h_formula_view_pos = pos })
  in
  (****LOCKSET****)
  let ls_uvar = CP.mkLsVar Unprimed in
  let ls_pvar = CP.mkLsVar Primed in
  let ls_uvar_exp = CP.Var (ls_uvar,pos) in
  let ls_pvar_exp = CP.Var (ls_pvar,pos) in
  let var_exp = CP.Var (var,pos)in
  let bag_exp = CP.mkBag [var_exp] pos in  (* {l} *)
  let ls_pre_f = CP.BForm (((CP.mkBagIn var ls_pvar_exp pos),None),None) in (* l in ls' *)
  let diff_exp = CP.mkBagDiff ls_uvar_exp bag_exp pos in (* diff(ls,{l})*)
  let ls_post_f = CP.mkEqExp ls_pvar_exp diff_exp pos in (*ls' = diff(ls,{l})*)
  (**************)
  (****LOCKSET****)
  let lsmu_uvar = CP.mkLsmuVar Unprimed in
  let lsmu_pvar = CP.mkLsmuVar Primed in
  let lsmu_uvar_exp = CP.Var (lsmu_uvar,pos) in
  let lsmu_pvar_exp = CP.Var (lsmu_pvar,pos) in
  let varmu_exp = CP.Level (var,pos)in
  let bagmu_exp = CP.mkBag [varmu_exp] pos in  (* {l.mu} *)
  let diffmu_exp = CP.mkBagDiff lsmu_uvar_exp bagmu_exp pos in (* diff(lsmu,{l.mu})*)
  let lsmu_post_f = CP.mkEqExp lsmu_pvar_exp diffmu_exp pos in (*ls' = diff(lsmu,{l.mu})*)
  (**************)
  let lock_post_f = if (!Globals.allow_locklevel) then
      CP.And (ls_post_f,lsmu_post_f,pos)
    else
      ls_post_f
  in
  (**************)
  let post = mkBase_simp data_node (MCP.memoise_add_pure_N (MCP.mkMTrue pos) lock_post_f) in
  (* let post = formula_of_heap_w_normal_flow data_node pos in *)
  let post = mkEAssume_simp [ls_uvar;lsmu_uvar] post (mkEBase post None no_pos) lbl in
  let pre =  mkBase_simp lock_node (MCP.memoise_add_pure_N (MCP.mkMTrue pos) ls_pre_f) in
  (* let pre = formula_of_heap_w_normal_flow lock_node pos in *)
  EBase {
    formula_struc_explicit_inst = [];
    formula_struc_implicit_inst = [];
    formula_struc_exists = [];
    formula_struc_base = pre;
    formula_struc_is_requires = true;
    formula_struc_continuation = Some post;
    formula_struc_pos = pos}

(*automatically generate pre/post conditions of finalize[lock_sort](lock_var,lock_args) *)
let prepost_of_finalize (var:CP.spec_var) sort (args:CP.spec_var list) (lbl:formula_label) pos : struc_formula =
  Debug.no_3 "prepost_of_finalize" !print_sv pr_none !print_svl
    !print_struc_formula       (fun _ _ _ -> prepost_of_finalize_x var sort args lbl pos) var sort args

let prepost_of_acquire_x (var:CP.spec_var) sort (args:CP.spec_var list) (inv:formula) (lbl:formula_label) pos : struc_formula =
  let fresh_perm_name = Cpure.fresh_old_name "f" in
  let perm_t = cperm_typ () in
  let fresh_perm =  Cpure.SpecVar (perm_t,fresh_perm_name, Unprimed) in (*LDK TO CHECK*)
  let uargs = List.map CP.to_unprimed args in
  let lock_node = ViewNode ({
      h_formula_view_node = var; (*Have to reserve type of view_node to finalize*)
      h_formula_view_name = sort; (*lock_sort*)
      h_formula_view_derv = false;
      h_formula_view_split = SPLIT0;
      h_formula_view_imm = CP.ConstAnn(Mutable);
      h_formula_view_perm = Some (Cpure.Var (fresh_perm,no_pos));
      h_formula_view_arguments = uargs;
      h_formula_view_ho_arguments = []; (* TODO:HO *)
      h_formula_view_annot_arg = [];
      h_formula_view_args_orig = CP.initialize_positions_for_view_params (CP.sv_to_view_arg_list uargs);
      h_formula_view_modes = []; (*???*)
      h_formula_view_coercible = true; (*??*)
      h_formula_view_origins = [];
      h_formula_view_original = false; (*NOT ALLOW SPLIT lemmas*)
      h_formula_view_lhs_case = false;
      h_formula_view_unfold_num = 0;
      h_formula_view_remaining_branches = None;
      h_formula_view_pruning_conditions = [];
      h_formula_view_label = None;
      h_formula_view_pos = pos })
  in
  (****waitlevel****)
  let waitlevel_var = CP.mkWaitlevelVar Primed in (*waitlevel'*)
  let waitlevel_exp = CP.mkVar waitlevel_var pos in
  let level_exp = CP.mkLevel var pos in (* level(l) == l.mu *)
  let waitlevel_gt_f = CP.mkLtExp waitlevel_exp level_exp pos in (* waitlevel'<l.mu*)
  (**************)
  (****LOCKSET****)
  let ls_uvar = CP.mkLsVar Unprimed in
  let ls_pvar = CP.mkLsVar Primed in
  let ls_uvar_exp = CP.Var (ls_uvar,pos) in
  let ls_pvar_exp = CP.Var (ls_pvar,pos) in
  let var_exp = CP.Var (var,pos)in
  let bag_exp = CP.mkBag [var_exp] pos in  (* {l} *)
  let union_exp = CP.mkBagUnion [ls_uvar_exp;bag_exp] pos in (* union(ls,{l})*)
  let ls_post_f = CP.mkEqExp ls_pvar_exp union_exp pos in (*ls' = union(ls,{l})*)
  let not_in_f = CP.BForm (((CP.mkBagNotIn var ls_pvar_exp pos),None),None) in (* l notin ls' *)
  (**************)
  (****LOCKSET LSMU****)
  let lsmu_uvar = CP.mkLsmuVar Unprimed in
  let lsmu_pvar = CP.mkLsmuVar Primed in
  let lsmu_uvar_exp = CP.Var (lsmu_uvar,pos) in
  let lsmu_pvar_exp = CP.Var (lsmu_pvar,pos) in
  let varmu_exp = CP.Level (var,pos)in
  let bagmu_exp = CP.mkBag [varmu_exp] pos in  (* {l.mu} *)
  let unionmu_exp = CP.mkBagUnion [lsmu_uvar_exp;bagmu_exp] pos in (* union(lsmu,{l.mu})*)
  let lsmu_post_f = CP.mkEqExp lsmu_pvar_exp unionmu_exp pos in (*lsmu' = union(lsmu,{l.mu})*)
  (**************)
  let lock_post_f = if (!Globals.allow_locklevel) then
      CP.And (ls_post_f,lsmu_post_f,pos)
    else
      ls_post_f
  in
  (**************)
  let read_f = mkPermInv_var () fresh_perm in
  (*POST-CONDITION*)
  let tmp = mkBase_simp lock_node (MCP.memoise_add_pure_N (MCP.mkMTrue pos) lock_post_f) in
  (* let tmp = formula_of_heap_w_normal_flow lock_node pos in *)
  let post = normalize 5 inv tmp pos in
  let post = mkEAssume_simp [ls_uvar;lsmu_uvar] post (mkEBase post None no_pos) lbl in
  (*PRE-CONDITION*)
  let pre_mf =
    if (!Globals.allow_locklevel) then
      let pre_mf = (MCP.memoise_add_pure_N (MCP.mix_of_pure not_in_f) waitlevel_gt_f) in
      let pre_mf = (MCP.memoise_add_pure_N pre_mf read_f) in
      pre_mf
    else
      (MCP.memoise_add_pure_N (MCP.mix_of_pure not_in_f) read_f)
  in
  let pre = mkBase lock_node pre_mf CVP.empty_vperm_sets TypeTrue (mkTrueFlow ()) [] pos in
  EBase {
    formula_struc_explicit_inst = [];
    formula_struc_implicit_inst = [fresh_perm]; (*instantiate f*)
    formula_struc_exists = []; (*TO CHECK: [] or args*)
    formula_struc_base = pre;
    formula_struc_is_requires = true;
    formula_struc_continuation = Some post;
    formula_struc_pos = pos}

let prepost_of_acquire (var:CP.spec_var) sort (args:CP.spec_var list) (inv:formula) (lbl:formula_label) pos : struc_formula =
  Debug.no_4 "prepost_of_acquire" !print_sv (fun str -> str) !print_svl !print_formula !print_struc_formula
    (fun _ _ _ _ -> prepost_of_acquire_x var sort args inv lbl pos) var sort args inv

let prepost_of_release_x (var:CP.spec_var) sort (args:CP.spec_var list) (inv:formula) (lbl:formula_label) pos : struc_formula =
  (* let fresh_perm_name = Cpure.fresh_old_name "f" in *)
  (* let perm_t = cperm_typ () in *)
  (* let fresh_perm =  Cpure.SpecVar (perm_t,fresh_perm_name, Unprimed) in (\*LDK TO CHECK*\) *)
  (* let uargs = List.map CP.to_unprimed args in *)
  (* let heap = ({   *)
  (*     h_formula_view_node = var; (\*Have to reserve type of view_node to finalize*\) *)
  (*     h_formula_view_name = sort; (\*lock_sort*\) *)
  (*     h_formula_view_derv = false; *)
  (*     h_formula_view_imm = CP.ConstAnn(Mutable);  *)
  (*     h_formula_view_perm = Some fresh_perm; *)
  (*     h_formula_view_arguments = uargs; *)
  (*     h_formula_view_modes = []; (\*???*\) *)
  (*     h_formula_view_coercible = false; (\*??*\) *)
  (*     h_formula_view_origins = []; *)
  (*     h_formula_view_original = false;(\*NOT ALLOW SPLIT lemmas in pre, but allow in post*\) *)
  (*     h_formula_view_lhs_case = false; *)
  (*     h_formula_view_unfold_num = 0; *)
  (*     h_formula_view_remaining_branches = None; *)
  (*     h_formula_view_pruning_conditions = []; *)
  (*     h_formula_view_label = None; *)
  (*     h_formula_view_pos = pos }) *)
  (* in *)
  (* let lock_node_post = ViewNode heap in (\*not allow SPIT in POST*\) *)
  (* let lock_node_pre = ViewNode {heap with h_formula_view_original=true} in (\*but allow SPLIT in PRE*\) *)
  (****LOCKSET****)
  let ls_uvar = CP.mkLsVar Unprimed in
  let ls_pvar = CP.mkLsVar Primed in
  let ls_uvar_exp = CP.Var (ls_uvar,pos) in
  let ls_pvar_exp = CP.Var (ls_pvar,pos) in
  let var_exp = CP.Var (var,pos)in
  let bag_exp = CP.mkBag [var_exp] pos in  (* {l} *)
  let ls_pre_f = CP.BForm (((CP.mkBagIn var ls_pvar_exp pos),None),None) in (* l in ls' *)
  let diff_exp = CP.mkBagDiff ls_uvar_exp bag_exp pos in (* diff(ls,{l})*)
  let ls_post_f = CP.mkEqExp ls_pvar_exp diff_exp pos in (*ls' = diff(ls,{l})*)
  (**************)
  (****LOCKSET MU****)
  let lsmu_uvar = CP.mkLsmuVar Unprimed in
  let lsmu_pvar = CP.mkLsmuVar Primed in
  let lsmu_uvar_exp = CP.Var (lsmu_uvar,pos) in
  let lsmu_pvar_exp = CP.Var (lsmu_pvar,pos) in
  let varmu_exp = CP.Level (var,pos)in
  let bagmu_exp = CP.mkBag [varmu_exp] pos in  (* {l.mu} *)
  let diffmu_exp = CP.mkBagDiff lsmu_uvar_exp bagmu_exp pos in (* diff(lsmu,{l.mu})*)
  let lsmu_post_f = CP.mkEqExp lsmu_pvar_exp diffmu_exp pos in (*lsmu' = diff(lsmu,{l.mu})*)
  (**************)
  let lock_post_f = if (!Globals.allow_locklevel) then
      CP.And (ls_post_f,lsmu_post_f,pos)
    else
      ls_post_f
  in
  (**************)
  (* let tmp = formula_of_heap_w_normal_flow lock_node pos in (\*not allow SPLIT in pre*\) *)
  (* let () = print_endline ("lock_node =  " ^ (!print_h_formula lock_node)) in *)
  (* let () = print_endline ("tmp =  " ^ (!print_formula tmp)) in *)
  (* let read_f = mkPermInv fresh_perm in (\*only need a certain permission to read*\) *)
  (* [S1] self::LOCKA(f)<> & ls=union(LS, {l}) & f<0<=1*)
  (* let tmp_pre = mkBase lock_node_pre (MCP.memoise_add_pure_N (MCP.OnePF ls_pre_f) read_f) TypeTrue (mkTrueFlow ()) [] pos in *)
  (*TOCHECK: ??? donot need lock_node*)
  (* let tmp_pre = mkBase HTrue (MCP.memoise_add_pure_N (MCP.OnePF ls_pre_f) read_f) TypeTrue (mkTrueFlow ()) [] pos in *)
  let tmp_pre = mkBase HTrue (MCP.memoise_add_pure_N (MCP.mkMTrue pos) ls_pre_f) CVP.empty_vperm_sets TypeTrue (mkTrueFlow ()) [] pos in
  (* let tmp_pre = mkBase lock_node (MCP.memoise_add_pure_N (MCP.mkMTrue pos) read_f) TypeTrue (mkTrueFlow ()) [] pos in *)
  (* let tmp = add_original tmp true in  (\*but allow SPLIT in post*\) *)
  (* [S1] self::LOCKA(f)<> & ls=union(LS, {l}) & f<0<=1 & inv*)
  let pre = normalize 5 inv tmp_pre pos in
  (* let pre_evars, pre_base = split_quantifiers pre in *)
  (* let post_f = mkBase_simp lock_node_post (MCP.OnePF ls_post_f) in *)
  (*TOCHECK: ??? donot need lock_node*)
  let post_f = mkBase_simp HTrue (MCP.memoise_add_pure_N (MCP.mkMTrue pos) lock_post_f) in
  let post = mkEAssume_simp [ls_uvar;lsmu_uvar] post_f (mkEBase post_f None no_pos) lbl in
  EBase {
    formula_struc_explicit_inst = [];
    formula_struc_implicit_inst = [(* fresh_perm *)](* ::pre_evars *); (*instantiate*)
    formula_struc_exists = [];
    formula_struc_base = pre (* pre_base *);
    formula_struc_is_requires = true;
    formula_struc_continuation = Some post;
    formula_struc_pos = pos}

let prepost_of_release (var:CP.spec_var) sort (args:CP.spec_var list) (inv:formula) (lbl:formula_label) pos : struc_formula =
  Debug.no_4 "prepost_of_release" !print_sv (fun str -> str) !print_svl !print_formula !print_struc_formula
    (fun _ _ _ _ -> prepost_of_release_x var sort args inv lbl pos) var sort args inv

(*IMITATE CF.COMPOSE but do not compose 2 formulas*)
(* Put post into formula_*_and of f instread*)
let compose_formula_and_x (f : formula) (post : formula) (delayed_f : MCP.mix_formula) (id: CP.spec_var) (ref_vars : CP.spec_var list) (val_vars : CP.spec_var list) pos =
  (*IMITATE CF.COMPOSE but do not compose 2 formulas*)
  (*Rename ref_vars for later join*)
  let rs = CP.fresh_spec_vars ref_vars in
  let rho1 = List.combine (List.map CP.to_unprimed ref_vars) rs in
  let rho2 = List.combine (List.map CP.to_primed ref_vars) rs in
  let new_f = x_add subst rho2 f in
  let new_post = x_add subst rho1 post in
  (* let new_f = push_exists rs new_f in (\* IMPORTANT: do not do this*\) *)
  (*Rename @value for later join*)
  (* y'=1 and x'=x+y' => y'=y_20 & y_20=1 and x'=x+y_20*)
  let fresh_vars = CP.fresh_spec_vars val_vars in
  let uprimed_vars = (List.map CP.to_unprimed fresh_vars) in
  let rho3 = List.combine val_vars uprimed_vars in
  (*x'=x+y_20*)
  let new_post2 = x_add subst rho3 new_post in
  (*y_20=1*)
  let new_f2 = x_add subst rho3 new_f in
  (*y'=y_20*)
  let func v1 v2 =
    Cpure.BForm (((Cpure.Eq (
        (Cpure.Var (v1,no_pos)),
        (Cpure.Var (v2,no_pos)),
        no_pos
      )),None), None)
  in
  let new_f3 = List.fold_left (fun f (v1,v2) ->
      let eq_f = func v1 v2 in
      (add_pure_formula_to_formula eq_f f)
    ) new_f2 rho3 in
  (*---------------------------------------------------*)
  (*NORMALIZE: f1 and (f2 or f3) ===> (f1 and f2) or (f1 and f3)*)
  let rec helper f post =
    match post with
    | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) ->
      Or ({formula_or_f1 = helper f f1; formula_or_f2 =  helper f f2; formula_or_pos = pos}) (*This case can not happen*)
    | _ ->
      (*Base or Exists*)
      let qvars,base = split_quantifiers post in
      let one_f = one_formula_of_formula base id delayed_f in
      let one_f = {one_f with formula_ref_vars = ref_vars;} in
      (*add thread id*)
      (* let () = print_endline ("\nLDK:" ^ (Cprinter.string_of_one_formula one_f)) in *)
      let evars = (* ref_vars@ *)qvars in (*TO CHECK*)
      let f1 = add_quantifiers evars f in
      let f2 = add_formula_and [one_f] f1 in
      f2
  in
  helper new_f3 new_post2

let compose_formula_and (f : formula) (post : formula) (delayed_f : MCP.mix_formula) (id: CP.spec_var) (ref_vars : CP.spec_var list) (val_vars : CP.spec_var list) pos =
  Debug.no_3 "compose_formula_and"
    !print_formula
    !print_formula
    !print_mix_formula
    !print_formula
    (fun _ _ _ -> compose_formula_and_x f post delayed_f id ref_vars val_vars pos) f post delayed_f

(*add the post condition (phi) into formul_*_and *)
(*special compose_context_formula for concurrency*)
(*Ctx es o (f1 or f2) -> OCtx (es o f1) (es o f2)*)
let compose_context_formula_and (ctx : context) (phi : formula) (delayed_f: MCP.mix_formula) (id: CP.spec_var) (ref_vars : CP.spec_var list) pos =
  let rec helper ctx phi =
    (match ctx with
     | Ctx es -> begin
         match phi with
         | Or ({formula_or_f1 = phi1; formula_or_f2 =  phi2; formula_or_pos = _}) ->
           let new_c1 = helper ctx phi1 in
           let new_c2 = helper ctx phi2 in
           let res = (mkOCtx new_c1 new_c2 pos ) in
           res
         | _ ->
           (*collect @var for later use *)
           (*NOTE THAT es.pure might not INCLUDE VARPERM INFO*)
           (* let val_vars = MCP.get_varperm_mix_formula es.es_pure VP_Value in *)
           let _, _, vps, _, _, _ = split_components es.es_formula in
           let val_vars = vps.CVP.vperm_value_vars in
           (*then clear entail_*)
           let es = clear_entailment_history_es_es es in
           let f = es.es_formula in
           (*   (\*IMITATE CF.COMPOSE but do not compose 2 formulas*\) *)
           let f2 = compose_formula_and f phi delayed_f id ref_vars val_vars pos in
           let new_es = {es with
                         es_formula = f2;
                         es_unsat_flag =false;}
           in
           Ctx new_es
       end
     | OCtx (c1, c2) ->
       let new_c1 = helper c1 phi in
       let new_c2 = helper c2 phi in
       let res = (mkOCtx new_c1 new_c2 pos) in
       res
    )
  in
  helper ctx phi


let has_formula_and (f : formula) : bool =
  let rec helper f = match f with
    | Base {formula_base_and = a}
    | Exists {formula_exists_and = a} ->
      (a!=[])
    | Or {formula_or_f1 = f1; formula_or_f2 =f2} ->
      (helper f1) || (helper f2) (*approximation*)
  in helper f

let rec norm_one_formula_vperm one_f ref_vars :(one_formula * CP.spec_var list) =
  Debug.no_2 "norm_one_formula_vperm"
    !print_one_formula !print_svl (pr_pair !print_one_formula !print_svl)
    norm_one_formula_vperm_x one_f ref_vars

and norm_one_formula_vperm_x one_f ref_vars :(one_formula * CP.spec_var list) =
  let h = one_f.formula_heap in
  let p = one_f.formula_pure in
  let pos = one_f.formula_pos in
  (*note that for each child formula x, only @full is allowed*)
  (* let r_vars = MCP.get_varperm_mix_formula p VP_Full in *)
  let r_vars = [] in (* TODO *)
  let diff_r_vars = Gen.BList.difference_eq CP.eq_spec_var_ident r_vars ref_vars in
  if (diff_r_vars!=[]) then
    let msg = "@val permissions not matched. Variables " ^ (!print_svl diff_r_vars) ^ " are not passed by ref" in
    Error.report_error { Error.error_loc = pos;Error.error_text = "VPERM specification is not correct. " ^ msg ^ "\n" ^ (!print_one_formula one_f)}
  else
    let child_fv = (h_fv h @ MCP.mfv p)in
    (*Detect @full variables by its name and primedness*)
    let child_r_vars = Gen.BList.intersect_eq CP.eq_spec_var_ident child_fv ref_vars in
    let child_r_vars = Gen.BList.remove_dups_eq CP.eq_spec_var_ident child_r_vars in
    let child_r_vars = List.map CP.to_primed child_r_vars in
    (* let new_p = MCP.drop_varperm_mix_formula p in         *)
    (* let ref_f = CP.mk_varperm VP_Full child_r_vars pos in *)
    (* let new_p = MCP.memoise_add_pure_N new_p ref_f in     *)
    let new_p = p in
    (*remaining ref vars*)
    let new_ref_vars = Gen.BList.difference_eq CP.eq_spec_var_ident ref_vars child_r_vars in
    ({one_f with formula_pure = new_p},new_ref_vars)

let norm_formula_and_vperm (a:one_formula list) (ref_vars : CP.spec_var list) =
  let rec helper a ref_vars=
    match a with
    | [] -> ([],ref_vars)
    | one_f::one_fs ->
      let new_one, new_r_vars = norm_one_formula_vperm one_f ref_vars in
      let new_fs, new_r_vars2 = helper one_fs new_r_vars in
      (new_one::new_fs,new_r_vars2)
  in helper a ref_vars

(*Automatically infer VPERM spec for sequential spec*)
let rec norm_formula_vperm f ref_vars val_vars =
  Debug.no_3 "norm_formula_vperm"
    !print_formula !print_svl !print_svl !print_formula
    norm_formula_vperm_x f ref_vars val_vars

(*
  Note: main thread -> @value[val_vars] & @full[...]
  But child thread -> @full[] only (don't have @value)
*)
and norm_formula_vperm_x f ref_vars val_vars =
  let rec helper f = match f with
    | Base ({formula_base_heap =h;
             formula_base_pure = p;
             formula_base_vperm = vp;
             formula_base_and =a;
             formula_base_pos =pos} as b)->
      (*infer VPERM for the main thread*)
      (*First, @value*)
      (* let v_vars = MCP.get_varperm_mix_formula p VP_Value in *)
      let v_vars = vp.CVP.vperm_value_vars in
      let diff_v_vars = Gen.BList.difference_eq CP.eq_spec_var_ident v_vars val_vars in
      (*The specification of VPERM @value[] is not correct*)
      if (diff_v_vars!=[]) then
        let msg = "@val permissions not matched. Variables " ^ (!print_svl diff_v_vars) ^ " are not passed by value" in
        Error.report_error { Error.error_loc = pos;Error.error_text = "VPERM specification is not correct. " ^ msg ^ "\n" ^ (!print_formula f)}
      else
        (* let new_p = MCP.drop_varperm_mix_formula p in      *)
        (* let val_f = CP.mk_varperm VP_Value val_vars pos in *)
        (* let new_p = MCP.memoise_add_pure_N new_p val_f in  *)
        let new_p = p in
        (*Second, @full[...]*)
        (*INFER @full for child threads first*)
        (* child threads first, remaining ref vars in ref_vars1*)
        let new_a, new_ref_vars = norm_formula_and_vperm a ref_vars in
        (*Then, main thread*)
        (* let r_vars = MCP.get_varperm_mix_formula p VP_Full in *)
        let r_vars = vp.CVP.vperm_full_vars in
        let diff_r_vars = Gen.BList.difference_eq CP.eq_spec_var_ident r_vars new_ref_vars in
        if (diff_r_vars!=[]) then
          let msg = "@full[...] permissions not matched. Variables " ^ (!print_svl diff_r_vars) ^ " are not passed by ref" in
          Error.report_error { Error.error_loc = pos;Error.error_text = "VPERM specification is not correct. " ^ msg ^ "\n" ^ (!print_formula f)}
        else
          (*The remaining ref vars belong to the main thread*)
          (* let ref_f = CP.mk_varperm VP_Full new_ref_vars pos in *)
          (* let new_p = MCP.memoise_add_pure_N new_p ref_f in     *)
          (* TODO: VPerm *)
          Base {b with formula_base_pure = new_p; formula_base_and = new_a}
    | Exists e ->
      let b = Base  {
          formula_base_heap = e.formula_exists_heap;
          formula_base_vperm = e.formula_exists_vperm;
          formula_base_pure = e.formula_exists_pure;
          formula_base_type = e.formula_exists_type;
          formula_base_and = e.formula_exists_and;
          formula_base_flow = e.formula_exists_flow;
          formula_base_label = e.formula_exists_label;
          formula_base_pos = e.formula_exists_pos}
      in
      let new_b = helper b in
      (add_quantifiers e.formula_exists_qvars new_b)
    | Or ({formula_or_f1 = f1; formula_or_f2 =f2} as o) ->
      let new_f1 = helper f1 in
      let new_f2 = helper f2 in
      Or {o with formula_or_f1 = new_f1; formula_or_f2 = new_f2}
  in helper f

(*Automatically infer VPERM spec for sequential spec*)
let rec norm_struc_vperm struc_f ref_vars val_vars =
  Debug.no_3 "norm_struc_vperm"
    !print_struc_formula !print_svl !print_svl !print_struc_formula
    norm_struc_vperm_x struc_f ref_vars val_vars

(*
  Infer varperm
  Users provide partial (or no) vperm annotations.
  Partial -> consistency check and infer the rest
  No -> infer all
*)
and norm_struc_vperm_x struc_f ref_vars val_vars = match struc_f with
  | ECase ({ formula_case_branches = cl } as ef) ->
    let n_cl = List.map (fun (c, sf) ->
        (c, norm_struc_vperm sf ref_vars val_vars)) cl in
    ECase { ef with formula_case_branches = n_cl }
  | EBase ef ->
    let b = ef.formula_struc_base in
    let cont = ef.formula_struc_continuation in
    let pos = ef.formula_struc_pos in
    if not (has_formula_and b) then
      (*sequential pre-condition*)
      (*INDEED, we can also use "norm_formula_vperm" in this case*)
      (* let r_vars = get_varperm_formula b VP_Full in  *)
      (* let v_vars = get_varperm_formula b VP_Value in *)
      (* TODO: VPerm *)
      let vps = CVP.empty_vperm_sets in
      let r_vars = vps.CVP.vperm_full_vars in
      let v_vars = vps.CVP.vperm_value_vars in
      let diff_r_vars = Gen.BList.difference_eq CP.eq_spec_var_ident r_vars ref_vars in
      let diff_v_vars = Gen.BList.difference_eq CP.eq_spec_var_ident v_vars val_vars in
      (*The specification of VPERM is not correct*)
      if (diff_r_vars!=[] || diff_v_vars!=[]) then
        let m1 = if diff_r_vars!=[] then "@full permissions not matched." else "" in
        let m2 = if diff_v_vars!=[] then "@val permissions not matched." else "" in
        Error.report_error { Error.error_loc = pos;Error.error_text = "VPERM specification is not correct. " ^ m1 ^ m2 ^ "\n" ^ (!print_struc_formula struc_f)}
      else
        (* let new_b = drop_varperm_formula b in                  *)
        (* let ref_f = CP.mk_varperm VP_Full ref_vars pos in      *)
        (* let val_f = CP.mk_varperm VP_Value val_vars pos in     *)
        (* let new_b = add_pure_formula_to_formula ref_f new_b in *)
        (* let new_b = add_pure_formula_to_formula val_f new_b in *)
        let new_b = b in (* TODO: VPerm *)
        let n_cont = map_opt (fun c-> norm_struc_vperm c [] []) cont in
        EBase{ef with formula_struc_base = new_b; formula_struc_continuation = n_cont}
    else
      (*concurrency spec. USERS specify this precondition.
        Proceed to check for post-condition*)
      let new_b = norm_formula_vperm ef.formula_struc_base ref_vars val_vars in
      let n_cont = map_opt (fun c-> norm_struc_vperm c [] []) cont in
      EBase{ef with formula_struc_base = new_b; formula_struc_continuation = n_cont}
  | EAssume b ->
    let vars = b.formula_assume_vars in
    let post_si = b.formula_assume_simpl in
    let post_st = b.formula_assume_struc in
    (*We have (ref) vars in the post-condition*)
    let pos = pos_of_formula post_si in
    let pvars = List.map CP.to_primed vars in
    if not (has_formula_and post_si) then
      (*sequential post-condition*)
      (* TODO: VPerm *)
      (* let r_vars = get_varperm_formula post_si VP_Full in *)
      let r_vars = [] in
      let diff_r_vars = Gen.BList.difference_eq CP.eq_spec_var_ident r_vars vars in
      if (diff_r_vars!=[]) then
        Error.report_error { Error.error_loc = pos;Error.error_text = "VPERM specification is not correct. @full permissions not matched.\n" ^ (!print_struc_formula struc_f)}
      else
        (* let new_post_si = drop_varperm_formula post_si in                        *)
        (* let new_post_st = drop_varperm_struc_formula post_st in                  *)
        (* let ref_f = CP.mk_varperm VP_Full pvars pos in                           *)
        (* let new_post_si = add_pure_formula_to_formula ref_f new_post_si in       *)
        (* let new_post_st = add_pure_formula_to_struc_formula ref_f new_post_st in *)
        (* TODO: VPerm *)
        let new_post_si = post_si in
        let new_post_st = post_st in
        EAssume {b with
                 formula_assume_simpl = new_post_si;
                 formula_assume_struc = new_post_st;}
    else
      (* let new_post_si = norm_formula_vperm post_si pvars [] in *)
      (* let new_post_st = norm_struc_vperm_x post_st pvars [] in *)
      (* TODO: VPerm *)
      let new_post_si = post_si in
      let new_post_st = post_st in
      mkEAssume_simp vars new_post_si new_post_st b.formula_assume_lbl
  (*concurrency spec. USERS specify this*)
  | EInfer ({ formula_inf_continuation = cont }) ->struc_f (*Not handle this at the moment*)
  | EList b-> EList (map_l_snd (fun c-> norm_struc_vperm_x c ref_vars val_vars) b)

(*partion a formula into delayed formula and the rest
  Indeed, donot partition: extract + rename instead
*)
and partLS (evars : CP.spec_var list) (f : formula) : MCP.mix_formula * formula =
  let pr_o = pr_pair !print_mix_formula !print_formula in
  Debug.no_2 "partLS" !print_svl !print_formula pr_o
    partLS_x evars f

and partLS_x (evars : CP.spec_var list) (f : formula) : MCP.mix_formula * formula =
  let delayed = extractLS evars f in
  let nf = removeLS f in
  (delayed,nf)

(*extract lockset constraints from a formula*)
and extractLS (evars : CP.spec_var list) (f : formula) : MCP.mix_formula =
  Debug.no_2 "extractLS" !print_svl !print_formula !print_mix_formula
    extractLS_x evars f

and extractLS_x (evars : CP.spec_var list) (f : formula): MCP.mix_formula  =
  let rec helper f =
    match f with
    | Base{ formula_base_pure = p; formula_base_vperm = vp; } ->
      let p_delayed = MCP.simplify_mix_formula (MCP.extractLS_mix_formula p) in
      (* remove formulae related to LS *)
      let p_pure = MCP.removeLS_mix_formula p in
      (* remove formulae related to lock level *)
      let p_pure = MCP.remove_level_mix_formula p_pure in
      (* remove formulae related to waitlevel *)
      let p_pure = MCP.drop_svl_mix_formula p_pure [(CP.mkWaitlevelVar Unprimed);(CP.mkWaitlevelVar Primed)] in
      (* get variables with full permission*)
      (* let full_vars = MCP.get_varperm_mix_formula p_pure VP_Full in *)
      let full_vars = vp.CVP.vperm_full_vars in
      (* remove formulae related to varperm *)
      (* let p_pure = MCP.drop_varperm_mix_formula p_pure in *)
      (* remove formulae related to floating point: may be unsound *)
      let p_pure = MCP.drop_float_formula_mix_formula p_pure in
      (*excl_vars are those who should not be delayed-checked*)
      let excl_vars = full_vars@evars in
      let p_pure = MCP.drop_svl_mix_formula p_pure excl_vars in
      x_add MCP.merge_mems p_delayed p_pure true
    | Exists{formula_exists_pure = p;
             formula_exists_vperm = vp;
             formula_exists_qvars =qvars} ->
      let p_delayed = MCP.simplify_mix_formula (MCP.extractLS_mix_formula p) in
      (* remove formulae related to LS *)
      let p_pure = MCP.removeLS_mix_formula p in
      (* remove formulae related to lock level *)
      let p_pure = MCP.remove_level_mix_formula p_pure in
      (* remove formulae related to waitlevel *)
      let p_pure = MCP.drop_svl_mix_formula p_pure [(CP.mkWaitlevelVar Unprimed);(CP.mkWaitlevelVar Primed)] in
      (* get variables with full permission*)
      (* let full_vars = MCP.get_varperm_mix_formula p_pure VP_Full in *)
      let full_vars = vp.CVP.vperm_full_vars in
      (* remove formulae related to varperm *)
      (* let p_pure = MCP.drop_varperm_mix_formula p_pure in *)
      (* remove formulae related to floating point: may be unsound TOCHECK*)
      let p_pure = MCP.drop_float_formula_mix_formula p_pure in
      (* conservatively drop formula related to exist vars: may be unsound TOCHECK *)
      (*excl_vars are those who should not be delayed-checked*)
      let excl_vars = full_vars@qvars@evars in
      let p_pure = MCP.drop_svl_mix_formula p_pure excl_vars in
      x_add MCP.merge_mems p_delayed p_pure true
    | Or {formula_or_f1 = f1; formula_or_f2 =f2} ->
      let pf1 = helper f1 in
      let pf2 = helper f2 in
      MCP.mkOr_mems pf1 pf2
  in helper f

and list_of_posts (sp:struc_formula) = match sp with
  | ECase b -> List.concat (List.map (fun (p,c) -> let res = list_of_posts c in
                                       List.map (fun (pures,post) -> ([p]@pures,post)) res) b.formula_case_branches)
  | EBase b ->
    (match b.formula_struc_continuation with
     | None -> []
     | Some f -> list_of_posts f)
  | EAssume b -> [([],b.formula_assume_simpl)]
  | EInfer b -> list_of_posts b.formula_inf_continuation
  | EList b -> List.concat (List.map (fun (_,e) -> list_of_posts e) b)

and transform_spec (sp:struc_formula) pairs = match sp with
  | ECase b -> ECase {b with formula_case_branches = (List.map (fun (p,c) ->
      let new_pairs = List.concat (List.map (fun (x,y) -> if List.hd x == p then [(List.tl x,y)] else []) pairs) in
      (p,transform_spec c new_pairs)) b.formula_case_branches)}
  | EBase b -> EBase {b with formula_struc_continuation =
                               (match b.formula_struc_continuation with
                                | None -> None
                                | Some f -> Some (transform_spec f pairs))}
  | EAssume b -> begin match pairs with
      | [([],p2)] ->
        EAssume{b with
                formula_assume_simpl = p2;
                formula_assume_struc = mkEBase p2 None no_pos;}
      | ([],p2)::_ ->(*  EList (List.map (fun (_, p2) -> (empty_spec_label_def, EAssume{b with *)
        (*         formula_assume_simpl = p2; *)
        (*         formula_assume_struc = mkEBase p2 None no_pos;}) *)
        (* ) pairs) *)
        EAssume{b with
                formula_assume_simpl = p2;
                formula_assume_struc = mkEBase p2 None no_pos;}
      | _ -> report_error no_pos "Error in transforming spec"
    end
  | EInfer b -> EInfer {b with formula_inf_continuation = transform_spec b.formula_inf_continuation pairs}
  | EList b -> EList (List.map (fun (l,e) ->(l,transform_spec e pairs)) b)

and sum_of_int_lst lst = List.fold_left (+) 0 lst

and no_of_cnts_heap heap = match heap with
  | Star h -> no_of_cnts_heap h.h_formula_star_h1 + no_of_cnts_heap h.h_formula_star_h2
  | StarMinus h -> no_of_cnts_heap h.h_formula_starminus_h1 + no_of_cnts_heap h.h_formula_starminus_h2
  | Conj h -> no_of_cnts_heap h.h_formula_conj_h1 + no_of_cnts_heap h.h_formula_conj_h2
  | ConjStar h -> no_of_cnts_heap h.h_formula_conjstar_h1 + no_of_cnts_heap h.h_formula_conjstar_h2
  | ConjConj h -> no_of_cnts_heap h.h_formula_conjconj_h1 + no_of_cnts_heap h.h_formula_conjconj_h2
  (*  | StarList h -> sum_of_int_lst (List.map (fun (_,s) -> no_of_cnts_heap (Star s)) h)*)
  | Phase h -> no_of_cnts_heap h.h_formula_phase_rd + no_of_cnts_heap h.h_formula_phase_rw
  | DataNode _ -> 1
  | ViewNode _ -> 1
  | ThreadNode _ -> 1
  | HRel _ -> 1
  | Hole _ | FrmHole _ -> 1
  | HTrue -> 1
  | HFalse -> 1
  | HEmp | HVar _ -> 0

and no_of_cnts_fml fml = match fml with
  | Or f -> no_of_cnts_fml f.formula_or_f1 + no_of_cnts_fml f.formula_or_f2
  | Base f -> no_of_cnts_heap f.formula_base_heap + CP.no_of_cnts (MCP.pure_of_mix f.formula_base_pure)
  | Exists f -> no_of_cnts_heap f.formula_exists_heap  + CP.no_of_cnts (MCP.pure_of_mix f.formula_exists_pure)

and no_of_cnts (sp:struc_formula) = match sp with
  | ECase b ->
    let nums = List.map (fun (p,c) -> CP.no_of_cnts p + no_of_cnts c) b.formula_case_branches in
    sum_of_int_lst nums
  | EBase b -> no_of_cnts_fml b.formula_struc_base +
               (match b.formula_struc_continuation with | None -> 0 | Some x -> no_of_cnts x)
  | EAssume b -> no_of_cnts_fml b.formula_assume_simpl
  | EInfer b -> no_of_cnts b.formula_inf_continuation
  | EList b ->
    let nums = List.map (fun (_,e) -> no_of_cnts e) b in
    sum_of_int_lst nums

(*remove lockset constraints from a formula*)
and removeLS (f : formula) : formula =
  Debug.no_1 "removeLS" !print_formula !print_formula
    removeLS_x f

(*remove lockset constraints from a formula*)
and removeLS_x (f : formula) : formula  =
  let rec helper f =
    match f with
    | Base ({formula_base_pure = p} as b) ->
      let np = MCP.removeLS_mix_formula p in
      let np = MCP.drop_svl_mix_formula np [(CP.mkWaitlevelVar Unprimed);(CP.mkWaitlevelVar Primed)] in
      Base {b with formula_base_pure = np}
    | Exists ({formula_exists_pure = p} as e)->
      let np = MCP.removeLS_mix_formula p in
      let np = MCP.drop_svl_mix_formula np [(CP.mkWaitlevelVar Unprimed);(CP.mkWaitlevelVar Primed)] in
      Exists {e with formula_exists_pure = np}
    | Or ({formula_or_f1 = f1; formula_or_f2 =f2} as o)->
      let nf1 = helper f1 in
      let nf2 = helper f2 in
      Or {o with formula_or_f1 = nf1; formula_or_f2 = nf2}
  in helper f

let translate_level_formula_x (f : formula) : formula =
  let rec helper f =
    match f with
    | Base b ->
      let p = b.formula_base_pure in
      let np = MCP.translate_level_mix_formula p in
      let nb = Base {b with formula_base_pure = np} in
      nb
    | Exists e ->
      let p = e.formula_exists_pure in
      let np = MCP.translate_level_mix_formula p in
      Exists {e with formula_exists_pure = np;}
    | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) ->
      let new_f1 = helper f1 in
      let new_f2 = helper f2 in
      let res = mkOr new_f1 new_f2 pos in
      res
  in helper f

let translate_level_formula (f : formula) : formula =
  Debug.no_1 "translate_level_formula"
    !print_formula !print_formula
    translate_level_formula_x f

(* translate l1=l2 into l1=l2 & level(l1)=level(l2) *)
let translate_level_eqn_formula_x (f : formula) : formula =
  let rec helper f =
    match f with
    | Base b ->
      let p = b.formula_base_pure in
      let np = MCP.translate_level_eqn_mix_formula p in
      let nb = Base {b with formula_base_pure = np} in
      nb
    | Exists e ->
      let p = e.formula_exists_pure in
      let np = MCP.translate_level_eqn_mix_formula p in
      Exists {e with formula_exists_pure = np;}
    | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) ->
      let new_f1 = helper f1 in
      let new_f2 = helper f2 in
      let res = mkOr new_f1 new_f2 pos in
      res
  in helper f

(* translate l1=l2 into l1=l2 & level(l1)=level(l2) *)
let translate_level_eqn_formula (f : formula) : formula =
  Debug.no_1 "translate_level_eqn_formula"
    !print_formula !print_formula
    translate_level_eqn_formula_x f

let translate_waitlevel_formula_x (f : formula) : formula =
  let rec helper f =
    match f with
    | Base b ->
      let p = b.formula_base_pure in
      let np = MCP.translate_waitlevel_mix_formula p in
      let nb = Base {b with formula_base_pure = np} in
      nb
    | Exists e ->
      let p = e.formula_exists_pure in
      let np = MCP.translate_waitlevel_mix_formula p in
      Exists {e with formula_exists_pure = np;}
    | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) ->
      let new_f1 = helper f1 in
      let new_f2 = helper f2 in
      let res = mkOr new_f1 new_f2 pos in
      res
  in helper f

let translate_waitlevel_formula (f : formula) : formula =
  Debug.no_1 "translate_waitlevel_formula"
    !print_formula !print_formula
    translate_waitlevel_formula_x f

let translate_waitS_rel_x (f0 : formula) : formula =
  let f_waitS_pure arg f = Some (CP.translate_waitS_pure f, []) in
  (* Ignore f_memo *)
  let f_memo = (fun _ a-> Some (a,[])),(fun a _->(a,[])),(fun _ a-> (a,[[]])),(fun a _ -> (a,[])),(fun a _ -> (a,[])) in
  let f_pure = f_waitS_pure, nonef2, nonef2 in
  let f_f = (fun _ -> None), (fun _ _-> None), (fun _ _-> None), f_pure, f_memo in
  let f_arg = voidf2, voidf2, voidf2, (voidf2, voidf2, voidf2), voidf2 in
  let arg = () in
  fst (trans_formula f0 arg f_f f_arg (fun l1 -> List.concat l1))

let translate_waitS_rel (f : formula) : formula =
  Debug.no_1 "translate_waitS_rel"
    !print_formula !print_formula
    translate_waitS_rel_x f

let translate_set_comp_rel_x (f0 : formula) : formula =
  let f_waitS_pure arg f = Some (CP.translate_set_comp_pure f, []) in
  (* Ignore f_memo *)
  let f_memo = (fun _ a-> Some (a,[])),(fun a _->(a,[])),(fun _ a-> (a,[[]])),(fun a _ -> (a,[])),(fun a _ -> (a,[])) in
  let f_pure = f_waitS_pure, nonef2, nonef2 in
  let f_f = (fun _ -> None), (fun _ _-> None), (fun _ _-> None), f_pure, f_memo in
  let f_arg = voidf2, voidf2, voidf2, (voidf2, voidf2, voidf2), voidf2 in
  let arg = () in
  fst (trans_formula f0 arg f_f f_arg (fun l1 -> List.concat l1))

let translate_set_comp_rel (f : formula) : formula =
  Debug.no_1 "translate_set_comp_rel"
    !print_formula !print_formula
    translate_set_comp_rel_x f

let infer_lsmu_formula_x (f : formula) : formula =
  let rec helper f =
    match f with
    | Base b ->
      let p = b.formula_base_pure in
      let np,evars = MCP.infer_lsmu_mix_formula p in
      let nb = Base {b with formula_base_pure = np} in
      if (evars =[]) then
        nb
      else
        push_exists evars nb
    | Exists e ->
      let p = e.formula_exists_pure in
      let np,evars = MCP.infer_lsmu_mix_formula p in
      let new_evars = e.formula_exists_qvars@evars in
      Exists {e with formula_exists_pure = np;formula_exists_qvars= new_evars}
    | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) ->
      let new_f1 = helper f1 in
      let new_f2 = helper f2 in
      let res = mkOr new_f1 new_f2 pos in
      res
  in helper f

let infer_lsmu_formula (f : formula) : formula =
  Debug.no_1 "infer_lsmu_formula"
    !print_formula !print_formula
    infer_lsmu_formula_x f

let infer_lsmu_struc_formula_x (f:struc_formula):struc_formula =
  let rec helper f =
    match f with
    | EAssume b ->
      let bf = infer_lsmu_formula b.formula_assume_simpl in
      EAssume {b with formula_assume_simpl = bf; formula_assume_struc = mkEBase bf None no_pos;}
    | ECase b -> ECase ({formula_case_branches = List.map (fun (c1,c2)-> (c1,(helper c2))) b.formula_case_branches ; formula_case_pos=b.formula_case_pos})
    | EBase b-> EBase {b with
                       formula_struc_base = infer_lsmu_formula b.formula_struc_base;
                       formula_struc_continuation =  Gen.map_opt helper b.formula_struc_continuation;
                      }
    | EInfer b -> EInfer ({b with formula_inf_continuation = helper b.formula_inf_continuation;})
    | EList b -> EList (Gen.map_l_snd helper b)
  in helper f

let infer_lsmu_struc_formula (f:struc_formula):struc_formula =
  Debug.no_1 "infer_lsmu_struc_formula"
    !print_struc_formula !print_struc_formula
    infer_lsmu_struc_formula_x f

(*drop pure constraints related to svl*)
and drop_svl (f : formula) (svl:CP.spec_var list): formula  =
  let rec helper f =
    match f with
    | Base ({formula_base_pure = p} as b) ->
      let np = MCP.drop_svl_mix_formula p svl in
      Base {b with formula_base_pure=np}
    | Exists ({formula_exists_pure = p;
               formula_exists_qvars =evars} as o) ->
      let nvars = Gen.BList.difference_eq CP.eq_spec_var svl evars in
      let np = MCP.drop_svl_mix_formula p nvars in
      Exists {o with formula_exists_pure=np}
    | Or ({formula_or_f1 = f1; formula_or_f2 =f2} as o) ->
      let nf1 = helper f1 in
      let nf2 = helper f2 in
      Or {o with formula_or_f1 = nf1; formula_or_f2 =nf2}
  in helper f

(*collect arguments of a heap node var sv, and its node name*)
let collect_heap_args_formula_x (f:formula) (sv:CP.spec_var) : (CP.spec_var list* ident) =
  let rec helper f =
    match f with
    | Base ({formula_base_heap = h;
             formula_base_pure = p;})
    | Exists ({formula_exists_heap = h;
               formula_exists_pure = p;}) ->
      let heaps = split_star_conjunctions h in
      let heaps = List.filter (fun h ->
          match h with
          | HEmp
          | HTrue -> false
          | _ -> true) heaps
      in
      let vars = MCP.find_closure_mix_formula sv p in
      let args_list = List.map (fun h ->
          let c = get_node_var h in
          let b = ((CP.eq_spec_var c sv) || (List.exists (fun v -> CP.eq_spec_var c v) vars)) in
          if (b) then [(get_node_args h, get_node_name 6 h)] else []
        ) heaps in
      let args_list = List.concat args_list in
      if args_list = [] then ([], "")
      else
        (*If there are multiple nodes with the same node_name
          (due to fractional permission).
          JUST PICKUP the first one*)
        List.hd args_list
    | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) ->
      let args1,id1 = helper f1 in
      let args2,id2 = helper f2 in
      if (args1=[] && args2!=[]) || (args1=[] && args2!=[]) || (id1!=id2) then
        report_error pos ("collect_heap_args_formula: heap_args of node " ^ (!print_sv sv) ^ (" are inconsistent"))
      else
        (*any of them*)
        (args1,id1)
  in helper f

(*collect arguments of a heap node var sv, and its node name*)
let collect_heap_args_formula (f:formula) (sv:CP.spec_var) : (CP.spec_var list * ident) =
  Debug.no_2 "collect_heap_args_formula"
    !print_formula !print_sv (pr_pair !print_svl (fun v -> v))
    collect_heap_args_formula_x f sv

let collect_all_heap_vars_formula (f: formula): CP.spec_var list =
  let rec helper f =
    match f with
    | Base ({ formula_base_heap = h; formula_base_pure = p; })
    | Exists ({ formula_exists_heap = h; formula_exists_pure = p; }) ->
      let heaps = split_star_conjunctions h in
      let heaps = List.filter (fun h ->
          match h with | HEmp | HTrue -> false | _ -> true) heaps
      in
      let heap_vars_list = List.map (fun h ->
          let sv = get_node_var h in
          let alias_sv = MCP.find_closure_mix_formula sv p in
          let args_sv = get_node_args h in
          [sv] @ alias_sv @ args_sv) heaps
      in List.concat heap_vars_list
    | Or ({ formula_or_f1 = f1; formula_or_f2 = f2; }) ->
      (helper f1) @ (helper f2)
  in helper f

(*collect arguments of a heap node var sv, and its node name*)
let collect_heap_args_context_x ctx (sv:CP.spec_var) : (CP.spec_var list * ident) =
  let rec helper ctx =
    match ctx with
    | Ctx es ->
      let args,id = collect_heap_args_formula es.es_formula sv in
      args,id
    | OCtx (ctx1, ctx2) ->
      let args1,id1 = helper ctx1 in
      let args2,id2 = helper ctx2 in
      if (args1=[] && args2!=[]) || (args1!=[] && args2=[]) || (id1<>id2) then
        report_error no_pos ("collect_heap_args_context: heap_args of node " ^ (!print_sv sv) ^ (" are inconsistent"))
      else
        (*any of them*)
        (args1,id1)
  in helper ctx

(*collect arguments of a heap node var sv, and its node name*)
let collect_heap_args_context ctx (sv:CP.spec_var) : (CP.spec_var list * ident) =
  Debug.no_2 "collect_heap_args_context"
    !print_context_short !print_sv (pr_pair !print_svl (fun v -> v))
    collect_heap_args_context_x ctx sv

let collect_heap_args_failesc_context ((fail_c,esc_c, succ_c):failesc_context) (sv:CP.spec_var) : (CP.spec_var list * ident) =
  let args_list = List.map (fun (lbl,ctx,_) -> collect_heap_args_context ctx sv) succ_c in
  (*check consistency in each context*)
  if args_list=[] then ([],"") else
    (try
       (*pickup a set of args and its non-empty node name*)
       let head_args,head_id = List.find (fun (args,id) -> (id<>"")) args_list in
       let () = List.iter (fun (args,id) ->
           if (id<>"") && (((List.length head_args) != (List.length args)) || (id!=head_id)) then
             (*if a node name is non-empty, it should be consistent with the head*)
             report_error no_pos ("collect_heap_args_failesc_context: heap_args of node " ^ (!print_sv sv) ^ (" are inconsistent"))
           else ()
         ) (List.tl args_list)
       in
       (*pickup non-empty*)
       (head_args,head_id)
     with Not_found -> ([],""))

(*collect arguments of a heap node var sv, and its node name*)
(*
  Due to SPLIT of permission, in case there are 2 context, one
  with heap node sv, the other w/o. Then pickup the one with
  heap node. The other one will become failed during verification
*)
let collect_heap_args_list_failesc_context (ctx:list_failesc_context) (sv:CP.spec_var): (CP.spec_var list * ident) =
  let args_list = List.map (fun ctx -> collect_heap_args_failesc_context ctx sv) ctx in
  (*check consistency in each failesc_context*)
  if args_list=[] then ([],"") else
    (try
       (*pickup a set of args and its non-empty node name*)
       let head_args,head_id = List.find (fun (args,id) -> (id<>"")) args_list in
       let () = List.iter (fun (args,id) ->
           if(id<>"") && (((List.length head_args) != (List.length args)) || (id<>head_id)) then
             (*if a node name is non-empty, it should be consistent with the head*)
             report_error no_pos ("collect_heap_args_list_failesc_context: heap_args of node " ^ (!print_sv sv) ^ (" are inconsistent"))
           else ()
         ) (List.tl args_list)
       in
       (*pickup non-empty*)
       (head_args,head_id)
     with Not_found -> ([],""))

let collect_node_var_formula (f:formula) =
  let rec helper (f:formula) =
    match f with
    | Exists ({ formula_exists_heap = h;})
    | Base ({formula_base_heap = h;}) ->
      let heaps = split_star_conjunctions h in
      let heaps = List.filter (fun h ->
          match h with
          | HEmp
          | HTrue -> false
          | DataNode _
          | ViewNode _
          | HRel _
          | ThreadNode _ -> true
          | _ -> report_error no_pos "collect_node_var_formula: expected"
        ) heaps
      in
      let vars = List.map (fun h -> get_node_var h) heaps in
      vars
    | Or {formula_or_f1 = f1; formula_or_f2 =f2} ->
      (helper f1)@(helper f2)
  in
  helper f

let trans_flow_formula f =
  let get_interval pf =
    let fv = Gen.BList.difference_eq CP.eq_spec_var (CP.fv pf) [CP.mk_spec_var "flow"] in
    let inf = CP.remove_redundant (CP.drop_svl_pure pf fv) in
    let il = List.sort compare (CP.get_num_int_list inf) in
    let () = Debug.ninfo_hprint (add_str "il" (pr_list string_of_int)) il no_pos in
    il
  in
  let mk_new_formula mk f =
    let h,p,vp,fl,t,a = split_components f in
    let pos = pos_of_formula f in
    let () = Debug.ninfo_hprint (add_str "p" !CP.print_formula) (MCP.pure_of_mix p) no_pos in
    let pl = CP.split_disjunctions (MCP.pure_of_mix p) in
    let () = Debug.ninfo_hprint (add_str "pl" (pr_list !CP.print_formula)) pl no_pos in
    let pils = List.map (fun pf -> (pf,get_interval pf)) pl in
    let fl = List.map (fun (pf,il) ->
        let new_flow_f = mkAndFlow (mkFlow il) fl Flow_combine in
        mk h (MCP.mix_of_pure pf) vp t new_flow_f a pos
      ) pils in
    if List.length fl = 0 then f
    else
      let fst_f = List.hd fl in
      let new_f = List.fold_left (fun acc f -> mkOr acc f pos) fst_f (List.tl fl) in
      let () = Debug.ninfo_hprint (add_str "new_f" !print_formula) new_f no_pos in
      new_f
  in
  let rec helper f =
    let () = Debug.ninfo_hprint (add_str "f" !print_formula) f no_pos in
    match f with
    | Base b ->
      mk_new_formula mkBase f
    | Or o -> Or { o with
                   formula_or_f1 = helper o.formula_or_f1;
                   formula_or_f2 = helper o.formula_or_f2
                 }
    | Exists e ->
      mk_new_formula (mkExists e.formula_exists_qvars) f
  in
  let f = helper f in
  simplify_formula (drop_svl f [CP.mk_spec_var "flow"]) []

let trans_flow_formula f =
  let pr = !print_formula in
  Debug.no_1 "trans_flow_formula" pr pr (fun _ -> trans_flow_formula f) f

let trans_flow_struc_formula sf =
  let rec helper sf =
    let () = Debug.ninfo_hprint (add_str "sf" !print_struc_formula) sf no_pos in
    match sf with
    | EList el -> EList ((List.map (fun (lbl,sf) -> (lbl,helper sf))) el)
    | ECase ec -> ECase { ec with
                          formula_case_branches = List.map (fun (pf,sf) -> (pf,helper sf)) ec.formula_case_branches
                        }
    | EBase eb ->
      let new_cont,new_base = match eb.formula_struc_continuation with
        | None -> None,trans_flow_formula eb.formula_struc_base
        | Some f -> Some (helper f),(* trans_flow_formula *) eb.formula_struc_base
      in
      EBase { eb with
              formula_struc_base = new_base;
              formula_struc_continuation = new_cont
            }
    | EInfer ei -> EInfer { ei with
                            formula_inf_continuation = helper ei.formula_inf_continuation
                          }
    | EAssume ea ->
      let pos = pos_of_struc_formula sf in
      let new_simpl = trans_flow_formula ea.formula_assume_simpl in
      let new_struc = struc_formula_of_formula new_simpl pos in
      EAssume { ea with
                formula_assume_simpl = new_simpl;
                formula_assume_struc = new_struc (* helper ea.formula_assume_struc *)
              }
  in
  let sfv = struc_fv sf in
  let () = Debug.ninfo_hprint (add_str "sfv" (pr_list !print_sv)) sfv no_pos in
  if Gen.BList.mem_eq CP.eq_spec_var (CP.mk_spec_var "flow") sfv then helper sf
  else sf

let trans_flow_struc_formula sf =
  let pr = !print_struc_formula in
  Debug.no_1 "trans_flow_struc_formula" pr pr (fun _ -> trans_flow_struc_formula sf) sf

let mkViewNode view_node view_name view_args (* view_args_orig *) pos =
  ViewNode {
      h_formula_view_node = view_node;
      h_formula_view_name = view_name;
      h_formula_view_derv = false;
      h_formula_view_split = SPLIT0;
      h_formula_view_arguments = view_args;
      h_formula_view_ho_arguments = [];   (* TODO;HO *)
      h_formula_view_annot_arg = [];
      h_formula_view_args_orig = CP.initialize_positions_for_view_params (CP.sv_to_view_arg_list view_args);
      h_formula_view_imm = CP.ConstAnn Mutable;
      h_formula_view_perm = None;
      h_formula_view_modes = [];
      h_formula_view_coercible = true;
      h_formula_view_origins = [];
      h_formula_view_original = true;
      h_formula_view_lhs_case = true;
      h_formula_view_unfold_num = 0;
      h_formula_view_remaining_branches = None;
      h_formula_view_pruning_conditions = [];
      h_formula_view_label = None;
      h_formula_view_pos = pos; }

let mkDataNode data_node data_name data_args pos =
  DataNode {
      h_formula_data_node = data_node;
      h_formula_data_name = data_name;
      h_formula_data_derv = false;
      h_formula_data_split = SPLIT0;
      h_formula_data_imm = CP.ConstAnn Mutable;
      h_formula_data_param_imm = List.map (fun _ -> CP.NoAnn) data_args;
      h_formula_data_perm = None;
      h_formula_data_origins = [];
      h_formula_data_original = false;
      h_formula_data_arguments = data_args;
      h_formula_data_holes = [];
      h_formula_data_remaining_branches = None;
      h_formula_data_pruning_conditions = [];
      h_formula_data_label = None;
      h_formula_data_pos = pos; }

let rec take_tl lst n =
  if n=0 then lst
  else
    match lst with
    | [] -> report_error no_pos "New predicate do not have enough arguments"
    | l::ls -> take_tl ls (n-1)

let tran_args ex_args args length =
  let new_args = take_tl args length in
  let new_args = CP.fresh_spec_vars new_args in
  (ex_args @ new_args, new_args)

let rec tran_spec_heap h sub_pair = match h with
  | Star {h_formula_star_h1 = h1;
          h_formula_star_h2 = h2;
          h_formula_star_pos = pos} ->
    let res1 = tran_spec_heap h1 sub_pair in
    let res2 = tran_spec_heap h2 sub_pair in
    (mkStarH (fst res1) (fst res2) pos, snd res1 @ snd res2)
  | Conj {h_formula_conj_h1 = h1;
          h_formula_conj_h2 = h2;
          h_formula_conj_pos = pos} ->
    let res1 = tran_spec_heap h1 sub_pair in
    let res2 = tran_spec_heap h2 sub_pair in
    (mkConjH (fst res1) (fst res2) pos, snd res1 @ snd res2)
  | Phase { h_formula_phase_rd = h1;
            h_formula_phase_rw = h2;
            h_formula_phase_pos = pos} ->
    let res1 = tran_spec_heap h1 sub_pair in
    let res2 = tran_spec_heap h2 sub_pair in
    (mkPhaseH (fst res1) (fst res2) pos, snd res1 @ snd res2)
  | ViewNode v ->
    let ((old_view_name, old_view_vars),(new_view_name, new_view_vars)) = sub_pair in
    if v.h_formula_view_name = old_view_name then
      let new_args = tran_args v.h_formula_view_arguments new_view_vars
          (List.length old_view_vars) in
      (ViewNode {v with h_formula_view_name = new_view_name;
                        h_formula_view_arguments = fst new_args}, snd new_args)
    else (h,[])
  | _ -> (h,[])

let rec tran_spec_fml fml sub_pair is_ebase = match fml with
  | Or {formula_or_f1 = f1;
        formula_or_f2 = f2;
        formula_or_pos = p} ->
    let res1 = tran_spec_fml f1 sub_pair is_ebase in
    let res2 = tran_spec_fml f2 sub_pair is_ebase in
    (mkOr (fst res1) (fst res2) p, snd res1 @ snd res2)
  | Base b ->
    let h, _, _, _, _, _ = split_components fml in
    let new_h = tran_spec_heap h sub_pair in
    let heap,evars = new_h in
    if evars = [] || is_ebase then
      (Base {b with formula_base_heap = heap}, evars)
    else
      (mkExists_w_lbl evars heap b.formula_base_pure b.formula_base_vperm
         b.formula_base_type b.formula_base_flow b.formula_base_and b.formula_base_pos b.formula_base_label, evars)
  | Exists e ->
    let h, _, _, _, _, _ = split_components fml in
    let new_h = tran_spec_heap h sub_pair in
    let heap,evars = new_h in
    if evars = [] || is_ebase then
      (Exists {e with formula_exists_heap = heap}, evars)
    else
      (Exists {e with formula_exists_heap = heap; formula_exists_qvars = e.formula_exists_qvars @ evars}, evars)

let rec tran_spec (sp:struc_formula) (sub_pair:((ident *CP.spec_var list)*(ident * CP.spec_var list)))  = match sp with
  | ECase b ->
    let res = List.map (fun (p,c) ->
        let r = tran_spec c sub_pair in
        ((p,fst r), snd r)) b.formula_case_branches in
    let r1,r2 = List.split res in
    (ECase {b with formula_case_branches = r1}, List.concat r2)
  | EBase b ->
    let rbase = tran_spec_fml b.formula_struc_base sub_pair true in
    let rcont = (match b.formula_struc_continuation with
        | None -> (None,[])
        | Some f -> let r = tran_spec f sub_pair in
          (Some (fst r), snd r)) in
    (EBase {b with
            formula_struc_implicit_inst = b.formula_struc_implicit_inst @ snd rbase;
            formula_struc_base = fst rbase;
            formula_struc_continuation = fst rcont},snd rbase @ snd rcont)
  | EAssume b ->
    let r = tran_spec_fml b.formula_assume_simpl sub_pair false in
    (EAssume {b with
              formula_assume_simpl = fst r ;
              formula_assume_struc = fst (tran_spec b.formula_assume_struc sub_pair)}, snd r)
  | EInfer b -> let r = tran_spec b.formula_inf_continuation sub_pair in
    (EInfer {b with formula_inf_continuation = fst r},snd r)
  | EList b -> let r = List.map (fun (l,e) ->
      let res = tran_spec e sub_pair in ((l,fst res),snd res)) b in
    let r1,r2 = List.split r in
    (EList r1, List.concat r2)

let rec add_pure_fml fml rel_fml = match fml with
  | Or {formula_or_f1 = f1;
        formula_or_f2 = f2;
        formula_or_pos = p} ->
    mkOr (add_pure_fml f1 rel_fml) (add_pure_fml f2 rel_fml) p
  | Base b ->
    let _, p, _, _, _, _ = split_components fml in
    let new_p = CP.mkAnd (MCP.pure_of_mix p) rel_fml no_pos in
    Base {b with formula_base_pure = MCP.mix_of_pure new_p}
  | Exists e ->
    let _, p, _, _, _, _ = split_components fml in
    let new_p = CP.mkAnd (MCP.pure_of_mix p) rel_fml no_pos in
    Exists {e with formula_exists_pure = MCP.mix_of_pure new_p}

let rec add_pure (sp:struc_formula) rel_fml_pre rel_fml_post = match sp with
  | ECase b -> ECase {b with formula_case_branches = (List.map (fun (p,c) ->
      (p,add_pure c rel_fml_pre rel_fml_post)) b.formula_case_branches)}
  | EBase b -> EBase {b with
                      formula_struc_base = (match rel_fml_pre with
                          | None -> b.formula_struc_base
                          | Some fml -> add_pure_fml b.formula_struc_base fml);
                      formula_struc_continuation =
                        (match b.formula_struc_continuation with
                         | None -> None
                         | Some f -> Some (add_pure f None rel_fml_post))}
  | EInfer b -> EInfer {b with formula_inf_continuation =
                                 add_pure b.formula_inf_continuation rel_fml_pre rel_fml_post}
  | EAssume b -> (match rel_fml_post with
      | None -> sp
      | Some fml -> EAssume {b with
                             formula_assume_simpl = add_pure_fml b.formula_assume_simpl fml;
                             formula_assume_struc = add_pure b.formula_assume_struc rel_fml_post rel_fml_post;})
  | EList b -> EList (List.map (fun (l,e) ->(l,add_pure e rel_fml_pre rel_fml_post)) b)

let add_pure (sp:struc_formula) rel_fml_pre rel_fml_post =
  let pr1 = !print_struc_formula in
  let pr2 = pr_option !CP.print_formula in
  Debug.no_3 "add_pure" pr1 pr2 pr2 pr1 add_pure sp rel_fml_pre rel_fml_post

(*let rec remove_rel_fml fml = match fml with*)
(*  | Or {formula_or_f1 = f1;*)
(*        formula_or_f2 = f2;*)
(*        formula_or_pos = p} ->*)
(*    let rel1, fml1 = remove_rel_fml f1 in*)
(*    let rel2, fml2 = remove_rel_fml f2 in*)
(*    rel1@rel2, mkOr fml1 fml2 p*)
(*  | Base b ->*)
(*    let _, p, _, _, _ = split_components fml in*)
(*    let rels = CP.get_RelForm (MCP.pure_of_mix p) in*)
(*    rels, Base {b with formula_base_pure = MCP.mix_drop_rel p}*)
(*  | Exists e ->*)
(*    let _, p, _, _, _ = split_components fml in*)
(*    let rels = CP.get_RelForm (MCP.pure_of_mix p) in*)
(*    rels, Exists {e with formula_exists_pure = MCP.mix_drop_rel p}*)

(*let rec remove_rel (sp:struc_formula) = match sp with*)
(*  | ECase b ->*)
(*    let res = List.map (fun (p,c) -> *)
(*      let pr_rel, po_rel, struc = remove_rel c in*)
(*      pr_rel, po_rel, [(p, struc)]) b.formula_case_branches in*)
(*    let res = List.fold_left (fun (a1,a2,a3) (b1,b2,b3) -> (a1@b1,a2@b2,a3@b3)) ([],[],[]) res in*)
(*    (fun (a1,a2,a3) -> (a1,a2,ECase {b with formula_case_branches = a3})) res*)
(*  | EBase b -> *)
(*    let pr_rel, pr_fml = remove_rel_fml b.formula_struc_base in*)
(*    let pr_rel2, po_rel, struc = match b.formula_struc_continuation with*)
(*      | None -> [],[],None*)
(*      | Some f -> (fun (a1,a2,a3) -> (a1,a2,Some a3)) (remove_rel f) in*)
(*    pr_rel@pr_rel2, po_rel, EBase {b with *)
(*      formula_struc_base = pr_fml;*)
(*      formula_struc_continuation = struc}*)
(*  | EAssume b -> *)
(*    let po_rel, po_fml = remove_rel_fml b.formula_assume_simpl in*)
(*    let pr_rel, po_rel2, struc = remove_rel b.formula_assume_struc in*)
(*    pr_rel,po_rel@po_rel2, EAssume {b with *)
(*		  formula_assume_simpl = po_fml;*)
(*		  formula_assume_struc = struc;}*)
(*  | EInfer b -> *)
(*    let pr_rel, po_rel, struc = remove_rel b.formula_inf_continuation in*)
(*    pr_rel, po_rel, EInfer {b with formula_inf_continuation = struc}*)
(*  | EList b -> *)
(*    let res = List.map (fun (l,e) -> *)
(*      let pr_rel, po_rel, struc = remove_rel e in*)
(*      pr_rel, po_rel, [(l,struc)]) b in*)
(*    let res = List.fold_left (fun (a1,a2,a3) (b1,b2,b3) -> (a1@b1,a2@b2,a3@b3)) ([],[],[]) res in*)
(*    (fun (a,b,c) -> (a,b,EList c)) res*)

let rec ctx_no_heap c = match c with
  | Ctx e->
    let rec f_no_heap f = match f with
      | Base f ->  not (is_complex_heap f.formula_base_heap)
      | Exists f -> not (is_complex_heap f.formula_exists_heap)
      | Or f -> (f_no_heap f.formula_or_f1) && (f_no_heap f.formula_or_f2) in
    f_no_heap e.es_formula
  | OCtx (c1,c2) -> (ctx_no_heap c1) && (ctx_no_heap c2)



let rec find_barr bln v f =
  (*this is copied from context, actually it is general enough to be in cpure...*)
  let rec alias (ptr_eqs : (CP.spec_var * CP.spec_var) list) : CP.spec_var list list =
    match ptr_eqs with
    | (v1, v2) :: rest ->
      let search v asets = List.partition (fun aset -> CP.mem v aset) asets in
      let av1, rest1 = search v1 (alias rest) in
      let av2, rest2 = search v2 rest1 in
      let v1v2_set = CP.remove_dups_svl (List.concat ([v1; v2] :: (av1 @ av2))) in
      v1v2_set :: rest2
    | [] -> [] in
  let tester r1 r2 = if r2=None then r1 else report_error no_pos ("formula not normalized for barrier "^v) in
  let rec p_bar_eq p = try
      List.map CP.name_of_spec_var
        (List.find (List.exists (fun c-> (String.compare v (CP.name_of_spec_var c)=0))) (alias (MCP.ptr_equations_without_null p))) with _ -> [v] in

  let rec h_bars eqs f = match f with
    | Star h ->
      let rd = h_bars eqs h.h_formula_star_h1 in
      let rw = h_bars eqs h.h_formula_star_h2 in
      (match rd with | None -> rw | _ -> tester rd rw)
    | StarMinus h ->
      let rd = h_bars eqs h.h_formula_starminus_h1 in
      let rw = h_bars eqs h.h_formula_starminus_h2 in
      (match rd with | None -> rw | _ -> tester rd rw)
    | Conj c ->
      let rd = h_bars eqs c.h_formula_conj_h1 in
      let rw = h_bars eqs c.h_formula_conj_h2 in
      (match rd with | None -> rw | _ -> tester rd rw)
    | ConjStar c ->
      let rd = h_bars eqs c.h_formula_conjstar_h1 in
      let rw = h_bars eqs c.h_formula_conjstar_h2 in
      (match rd with | None -> rw | _ -> tester rd rw)
    | ConjConj c ->
      let rd = h_bars eqs c.h_formula_conjconj_h1 in
      let rw = h_bars eqs c.h_formula_conjconj_h2 in
      (match rd with | None -> rw | _ -> tester rd rw)
    | Phase p ->
      let rd = h_bars eqs p.h_formula_phase_rd in
      let rw = h_bars eqs p.h_formula_phase_rw in
      (match rd with | None -> rw | _ -> tester rd rw)
    | DataNode d ->
      let str_eq v1 v2 = (String.compare v1 v2 ) = 0 in
      let f1 = str_eq d.h_formula_data_name in
      let f2 = str_eq (CP.name_of_spec_var d.h_formula_data_node) in
      if (List.exists f1 bln)&&(List.exists f2 eqs) then
        Some d (*(d.h_formula_data_name,d.h_formula_data_node::d.h_formula_data_arguments,d.h_formula_data_remaining_branches)*)
      else None
    | ThreadNode _ (*TOCHECK*)
    | ViewNode _ | Hole _ | FrmHole _ | HTrue | HEmp | HFalse | HRel _ | HVar _ -> None in

  match f with
  | Base f ->  h_bars (p_bar_eq f.formula_base_pure) f.formula_base_heap
  | Exists f -> h_bars (p_bar_eq f.formula_exists_pure) f.formula_exists_heap
  | Or f -> report_error no_pos "unexpected or in find barr"

let find_barr bln v f =
  Debug.no_2 "find_barr" (fun c->c) !print_formula (fun c-> "") (find_barr bln) v f


let get_bar_conds b_name self (l_f:(formula * formula_label) list): ((int option * Tree_shares.Ts.t_sh option * formula_label) list) =
  let helper (f,lbl) = match find_barr b_name self f with
    | None  -> (None,None,lbl)
    | Some bd -> match f with
      | Or _ -> report_error no_pos "unexpected or in find barr"
      | Base {formula_base_pure = p}
      | Exists {formula_exists_pure = p} ->
        let f = MCP.fold_mem_lst (CP. mkTrue no_pos) false false p in
        let perm = match bd.h_formula_data_perm with
          | None -> Some Tree_shares.Ts.top
          | Some v -> CP.get_inst_tree (List.hd (Cpure.afv v)) f in
        (CP.get_inst_int (List.hd bd.h_formula_data_arguments) f, perm, lbl) in
  List.map helper l_f

let get_bar_conds b_name self l_f =
  let string_of_lbl = (fun (c,_)-> string_of_int c) in
  Debug.no_3 "get_bar_conds" (pr_list (fun c->c)) (fun c-> c)
    (pr_list (pr_pair !print_formula string_of_lbl))
    (pr_list (pr_triple (pr_opt string_of_int) (pr_opt Tree_shares.Ts.string_of) string_of_lbl))
    get_bar_conds b_name self l_f


(* let rec is_error_flow_x f =  match f with *)
(*   | Base b-> subsume_flow_f !error_flow_int b.formula_base_flow *)
(*   | Exists b-> subsume_flow_f !error_flow_int b.formula_exists_flow *)
(*   | Or b ->  is_error_flow_x b.formula_or_f1 && is_error_flow_x b.formula_or_f2 *)

(* let is_error_flow f= *)
(*   let pr1 = !print_formula in *)
(*   Debug.no_1 "is_error_flow" pr1 string_of_bool *)
(*       (fun _ -> is_error_flow_x f) f *)

(* let rec is_mayerror_flow f =  match f with *)
(*   | Base b-> subsume_flow_f !mayerror_flow_int b.formula_base_flow *)
(*   | Exists b-> subsume_flow_f !mayerror_flow_int b.formula_exists_flow *)
(*   | Or b ->  is_mayerror_flow b.formula_or_f1 && is_mayerror_flow b.formula_or_f2  *)

(* let rec is_top_flow f =   match f with *)
(*   | Base b-> equal_flow_interval !top_flow_int b.formula_base_flow.formula_flow_interval *)
(*   | Exists b-> equal_flow_interval !top_flow_int b.formula_exists_flow.formula_flow_interval *)
(*   | Or b ->  is_top_flow b.formula_or_f1 && is_top_flow b.formula_or_f2  *)

(* let get_error_flow f = flow_formula_of_formula f *)
(* let get_top_flow f = flow_formula_of_formula f *)


let trivFlowDischarge_x ctx f =
  let rec helper fl_c ctx = match ctx with
    | Ctx es -> (match es.es_formula with
        | Base {formula_base_flow = fl_a}
        | Exists {formula_exists_flow = fl_a} ->
          is_eq_flow fl_a.formula_flow_interval fl_c.formula_flow_interval &&
          fl_a.formula_flow_link=None && fl_c.formula_flow_link=None
        | _ -> false)
    | OCtx (c1,c2)-> helper fl_c c1 && helper fl_c c2 in
  match f with
  | Base {formula_base_heap = HEmp;
          formula_base_pure = p;
          formula_base_flow = fl_c;}
  | Exists {formula_exists_heap = HEmp;
            formula_exists_pure = p;
            formula_exists_flow = fl_c;}
    -> (MCP.isTrivMTerm p || MCP.isConstMTrue p) && helper fl_c ctx
  | _ -> false

let trivFlowDischarge ctx f =
  Debug.no_2 "trivFlowDischarge" (!print_context) (!print_formula) (string_of_bool) trivFlowDischarge_x ctx f

let rec reset_unsat_flag_formula f =
  match f with
  | Base b -> Base (reset_unsat_flag_formula_base b)
  | Or o -> Or (reset_unsat_flag_formula_or o)
  | Exists e -> Exists (reset_unsat_flag_formula_exists e)

and reset_unsat_flag_formula_base b =
  { b with formula_base_pure = MCP.reset_unsat_flag_mix b.formula_base_pure }

and reset_unsat_flag_formula_or o =
  { o with
    formula_or_f1 = reset_unsat_flag_formula o.formula_or_f1;
    formula_or_f2 = reset_unsat_flag_formula o.formula_or_f2 }

and reset_unsat_flag_formula_exists e =
  { e with formula_exists_pure = MCP.reset_unsat_flag_mix e.formula_exists_pure }

let fid(c: 'a)	: ('a option) = Some c

let mark_estate_sat_slices estate svl =
  let tr_g g = Some (List.map (fun g-> {g with  Mcpure_D.memo_group_unsat =
                                                  if Gen.BList.overlap_eq CP.eq_spec_var svl g.Mcpure_D.memo_group_fv
                                                  then false
                                                  else g.Mcpure_D.memo_group_unsat}) g) in
  {estate with es_formula = transform_formula (fid,(fun c-> None),fid,(tr_g,fid, fid, fid, fid)) estate.es_formula;}

let is_emp_heap h = (match h with
    | HEmp -> true
    | HTrue -> true
    | _ -> false)

let is_term mf =
  let f = MCP.pure_of_mix mf in
  CP.is_term f

let is_emp_term f = match f with
  | Base {formula_base_pure = mf;
          formula_base_heap = h} ->
    if is_emp_heap h then
      (if is_term mf then true
       else false)
    else false
  | _ -> false

let is_emp_term f =
  Debug.no_1 "is_emp_term" !print_formula string_of_bool is_emp_term f


let elim_prm e =
  let nv v = match v with | CP.SpecVar (t,n,Primed) -> CP.SpecVar(t,n^"PRM",Unprimed) | _ -> v in
  let f_e_f e = None in
  let f_f e = None in
  let f_m e = None in
  let f_a e = None in
  let f_b e = None in
  let f_p_f e = None in
  let f_e e = match e with
    | CP.Null _
    | CP.IConst _
    | CP.AConst _
    | CP.Tsconst _
    | CP.FConst _
    | CP.Func _
    | CP.InfConst _
    | CP.Template _
    | CP.NegInfConst _
    | CP.ArrayAt _ -> Some e
    | CP.Var (v,p)-> Some (CP.Var (nv v, p))
    | CP.Bptriple ((c,t,a),p) -> Some (CP.Bptriple ((nv c,nv t,nv a),p))
    | CP.Tup2 _
    | CP.Add _
    | CP.Subtract _
    | CP.Mult _
    | CP.Div _
    | CP.Max _
    | CP.Min _
    | CP.TypeCast _
    | CP.Bag _
    | CP.BagUnion _
    | CP.BagIntersect _
    | CP.BagDiff _
    | CP.List _
    | CP.ListCons _
    | CP.ListHead _
    | CP.ListTail _
    | CP.ListLength _
    | CP.ListAppend _
    | CP.ListReverse _ -> None
    | CP.Level _ -> report_error no_pos "CF.elim_prm: not handle yet"
  in
  let rec f_h_f e = match e with
    | Star s -> None
    | Conj s -> None
    | Phase s -> None
    | DataNode d -> Some (DataNode {d with h_formula_data_arguments = List.map nv d.h_formula_data_arguments; h_formula_data_node = nv d.h_formula_data_node})
    | ViewNode v -> Some (ViewNode {v with h_formula_view_arguments = List.map nv v.h_formula_view_arguments; h_formula_view_node = nv v.h_formula_view_node}) (*TOCHECK: ho_arguments*)
    | ThreadNode v -> Some (ThreadNode {v with h_formula_thread_node = nv v.h_formula_thread_node}) (*TOCHECK*)
    | HRel (b1,b2,b3) -> Some (HRel (nv b1,(List.map (CP.transform_exp f_e ) b2),b3))
    | StarMinus _ | ConjStar _ | ConjConj _ -> report_error no_pos "CF.f_h_f: not handle yet"
    | Hole _ | FrmHole _
    | HTrue
    | HFalse
    | HEmp | HVar _ -> Some e in
  transform_formula (f_e_f,f_f,f_h_f,(f_m,f_a,f_p_f,f_b,f_e)) e

let convert_hf_to_mut f =
  let h_tr f = match f with
    | DataNode d ->
      Some (
        DataNode
          {d with
           h_formula_data_param_imm =
             List.map (fun _ -> CP.ConstAnn Mutable) d.h_formula_data_param_imm;
           (* h_formula_data_arguments = CP.fresh_spec_vars d.h_formula_data_arguments; *)
          })
    | _ -> None in
  transform_h_formula h_tr f
let convert_hf_to_mut f =
  let pr = !print_h_formula in
  Debug.no_1 "convert_to_mut" pr pr convert_hf_to_mut f

(* this method must convert all the fields to @M annotation *)
let convert_to_mut f =
  let h_tr f = match f with
    | DataNode d ->
      Some (
        DataNode
          {d with
           h_formula_data_param_imm =
             List.map (fun _ -> CP.ConstAnn Mutable) d.h_formula_data_param_imm;
           h_formula_data_arguments = CP.fresh_spec_vars d.h_formula_data_arguments;
          })
    | _ -> None in
  {f with formula_base_heap = transform_h_formula h_tr f.formula_base_heap}

let convert_to_mut f =
  let pr = !print_formula_base in
  Debug.no_1 "convert_to_mut" pr pr convert_to_mut f



let add_struc_unfold_num (f : struc_formula) uf =
  let ff f = Some (add_unfold_num f uf) in
  transform_struc_formula  (*(f_e_f,f_f,f_h_f,(f_memo,f_aset, f_formula, f_b_formula, f_exp))*)
    ((fun _->None),ff,(fun e->Some e),((fun e->Some e),(fun e->Some e),(fun e->Some e),(fun _->None),(fun _->None))) f


let rec pick_view_node h aset = match h with
  | ViewNode v -> if CP.mem v.h_formula_view_node aset then (HEmp,Some v) else (h,None)
  | Star s ->
    let (h,r) = pick_view_node s.h_formula_star_h1 aset in
    (match r with
     | Some _ -> (mkStarH h s.h_formula_star_h2 no_pos, r)
     | None ->
       let (h,r) = pick_view_node s.h_formula_star_h2 aset in
       (mkStarH h s.h_formula_star_h1 no_pos, r))
  | _ -> (h, None)

let f_fst l ( _ :'a) = l

let rec find_nodes e l=
  let f_heap_f l h  = match h with
    | HRel (p,vl, _) ->
      let vl = if (List.exists (CP.eq_spec_var p) l) then [((p,h),CP.filter_vars vl)] else [] in
      Some(h,vl)
    | _ -> None in
  let f_memo = (fun _ a-> Some (a,[])),(fun a _->(a,[])),(fun _ a-> (a,[[]])),(fun a _ -> (a,[])),(fun a _ -> (a,[])) in
  let f_pure = (fun _ a -> Some (a,[])),(fun _ a -> Some (a,[])),(fun _ a -> Some (a,[])) in
  let f = (fun _ -> None), (fun _ _-> None), f_heap_f, f_pure, f_memo in
  let f_arg = l, f_fst, f_fst, (f_fst, f_fst, f_fst), f_fst in
  snd (trans_formula e l f f_arg (fun l1 -> List.concat l1))

let get_heap_inf_args_hp_rel estate vars_hp_rel =
  let node_arg_map = find_nodes estate.es_formula vars_hp_rel in
  let args = List.concat (snd (List.split node_arg_map)) in
  args,node_arg_map

let get_heap_inf_args estate =
  get_heap_inf_args_hp_rel estate estate.es_infer_vars_hp_rel



(****************************************)
(*=========for sa==========*)
(****************************************)
(*TODO: LOC: es_cond_path from estate*)
let get_es_cond_path es = es.es_cond_path

(*TODO: should improve*)
let rec get_ctx_cond_path ctx =
  match ctx with
  | Ctx es -> get_es_cond_path es
  | OCtx (c1,_) ->  get_ctx_cond_path c1

(*TODO: should improve*)
let get_list_ctx_cond_path lc=
  match lc with
  | SuccCtx cl -> begin
      match cl with
      | [] -> []
      | c::_ ->  get_ctx_cond_path c
    end
  | _ -> []

(* WN_2_loc : this should clear all inferred info from context *)
let clear_infer_from_context c1 = c1

(* WN_2_Loc: add p to ts; add new_infer (only those related to pure) from new_ctx into ts *)
let add_pure_and_infer_from_asserted p new_ctx ts = ts

let combine_guard ogs0=
  let rec helper ogs res=
    match ogs with
    | [] -> join_conjunct_opt res
    | og::rest -> begin
        match og with
        | None -> helper rest res
        | Some hf -> helper rest (res@[hf])
      end
  in
  match ogs0 with
  | [] -> None
  | [z] -> z
  | _ -> helper ogs0 []

let convert_guard oh_guard=
  match oh_guard with
  | None -> None
  | Some hf -> Some (formula_of_heap hf no_pos)

let flatten_hp_rel_def hpdef=
  let a1 = hpdef.def_cat in
  let hprel = hpdef.def_lhs in
  let fs,ogs = List.split hpdef.def_rhs in
  let f = disj_of_list fs no_pos in
  let og = combine_guard ogs in
  (a1,hprel,og,f)

let add_proof_traces_ctx ctx0 proof_traces=
  let rec helper ctx=
    match ctx with
    | Ctx es -> Ctx {es with es_proof_traces = es.es_proof_traces@proof_traces}
    | OCtx (ctx1,ctx2) -> OCtx( helper ctx1, helper ctx2)
  in
  helper ctx0

let trans_n_formula (e: formula) (arg: 'a) f f_arg f_comb: (formula * 'b) =
  let f_struc_f, f_f, f_heap_f, f_pure, f_memo = f in
  let f_struc_f_arg, f_f_arg, f_heap_f_arg, f_pure_arg, f_memo_arg = f_arg in
  let trans_heap (e: h_formula) (arg: 'a) : (h_formula * 'b) = trans_h_formula e arg f_heap_f f_heap_f_arg f_comb in
  let trans_mix (e: MCP.mix_formula) (arg: 'a) : (MCP.mix_formula * 'b) =
    MCP.trans_n_mix_formula e arg (f_memo,f_pure) (f_memo_arg,f_pure_arg) f_comb in
  let rec trans_f (e: formula) (arg: 'a) : (formula * 'b) =
    let r = f_f arg e in
    match r with
    | Some e1 -> e1
    | None ->
      let new_arg = f_f_arg arg e in
      match e with
      | Base b ->
        let new_heap, v1 = trans_heap b.formula_base_heap new_arg in
        let new_pure, v2 = trans_mix b.formula_base_pure new_arg in
        let new_base = Base { b with
                              formula_base_heap = new_heap;
                              formula_base_pure = new_pure; }
        in
        (new_base, f_comb [v1; v2])
      | Or o ->
        let nf1, v1 = trans_f o.formula_or_f1 new_arg in
        let nf2, v2 = trans_f o.formula_or_f2 new_arg in
        let new_or = Or { o with
                          formula_or_f1 = nf1;
                          formula_or_f2 = nf2; }
        in
        (new_or, f_comb [v1; v2])
      | Exists e ->
        let new_heap, v1 = trans_heap e.formula_exists_heap new_arg in
        let new_pure, v2 = trans_mix e.formula_exists_pure new_arg in
        let new_exists = Exists { e with
                                  formula_exists_heap = new_heap;
                                  formula_exists_pure = new_pure;}
        in
        (new_exists, f_comb [v1; v2])
  in
  trans_f e arg

(*
type: struc_formula ->
  'a ->
  ('a -> struc_formula -> (struc_formula * 'b) option) *
  ('a -> formula -> (formula * 'b) option) *
  ('a -> h_formula -> (h_formula * 'b) option) *
  (('a -> CP.formula -> (CP.formula * 'b) option) *
   ('a -> Cpure.b_formula -> (Cpure.b_formula * 'b) option) *
   ('a -> CP.exp -> (CP.exp * 'b) option)) *
  (Mcpure_D.memo_pure -> 'a -> (Mcpure_D.memo_pure * 'b) option) ->
  ('a -> struc_formula -> 'a) * ('a -> formula -> 'a) *
  ('a -> h_formula -> 'a) *
  (('a -> CP.formula -> 'a) * ('a -> Cpure.b_formula -> 'a) *
   ('a -> CP.exp -> 'a)) *
  'c -> ('b list -> 'b) -> struc_formula * 'b
*)

let rec trans_n_struc_formula (e: struc_formula) (arg: 'a) f f_arg f_comb : (struc_formula * 'b) =
  let f_struc_f, f_f, f_h_formula, f_pure, f_memo = f in
  let f_struc_f_arg, f_f_arg, f_h_f_arg, f_pure_arg, f_memo_arg = f_arg in
  let trans_pure (e: CP.formula) (arg: 'a) : (CP.formula * 'b)
    = CP.trans_formula e arg f_pure f_pure_arg f_comb in
  let trans_struc (arg: 'a) (e: struc_formula)  : (struc_formula * 'b)
    = trans_n_struc_formula e arg f f_arg f_comb in
  let trans_f (e: formula) (arg: 'a) : (formula * 'b) = trans_n_formula e arg f f_arg f_comb in
  match f_struc_f arg e with
  | Some e1 -> e1
  | None ->
    let new_arg = f_struc_f_arg arg e in
    match e with
    | ECase c ->
      let helper ((e1,e2): CP.formula * struc_formula): (CP.formula * struc_formula) * 'b =
        let ne1, v1 = trans_pure e1 new_arg in
        let ne2, v2 = trans_struc new_arg e2  in
        ((ne1, ne2), f_comb [v1; v2])in
      let new_case_branches, vals = List.split (List.map helper c.formula_case_branches) in
      (ECase {c with formula_case_branches = new_case_branches}, f_comb vals)
    | EBase b ->
      let new_base, v1 = trans_f b.formula_struc_base new_arg in
      let new_cont, l = match b.formula_struc_continuation with
        | None -> (None,[v1])
        | Some b-> let r1,r2 = trans_struc new_arg b in (Some r1, [v1;r2]) in
      (EBase { b with formula_struc_base = new_base; formula_struc_continuation = new_cont; }, f_comb l)
    | EAssume b ->
      let ne, r = trans_f b.formula_assume_simpl new_arg in
      let n_struc, _ = trans_struc new_arg b.formula_assume_struc  in
      let b = {b with formula_assume_simpl=ne; formula_assume_struc = n_struc} in
      (EAssume b, f_comb [r])
    | EInfer b ->
      let new_cont, val3 = trans_struc new_arg b.formula_inf_continuation  in
      (EInfer {b with formula_inf_continuation = new_cont}, f_comb [val3])
    | EList b ->
      let ne,vals = map_l_snd_res (trans_struc new_arg) b in
      (mkEList_no_flatten ne, f_comb vals)


let is_no_heap_struc_formula (e : struc_formula) : bool =
  let f_struc_f _ _ = None in
  let f_f _ _ = None in
  let f_h_formula _ x =  Some (x, is_no_heap_h_formula x) in
  let f1 a e = Some(e,true) in
  let f2 a e = None in
  let f_pure = (f1,f2,f2) in
  let f_memo a e = Some(e,true) in
  let f_arg =
    let f1 e _ = e in
    (f1,f1,f1,(f1,f1,f1),f1) in
  let f_gen = (f_struc_f, f_f, f_h_formula, f_pure, f_memo) in
  let (a,b) = trans_n_struc_formula e false f_gen f_arg (List.for_all (fun x -> x)) in
  b

let is_no_heap_struc_formula (e : struc_formula) : bool =
  let pr = !print_struc_formula in
  Debug.no_1 "is_no_heap_struc_formula" pr string_of_bool is_no_heap_struc_formula e

let residues =  ref (None : (list_context * bool (* * bool * bool * bool *)) option)
(* the second parameter 'bool' is used for printing *)

let set_residue b lc (* ldfa dis_lerr_exc en_lerr_exc *)  =
  residues := Some (lc,b(* ,ldfa,dis_lerr_exc,en_lerr_exc *))

let clear_residue () =
  residues := None

let get_res_residue () =
  match !residues with
  | Some (_, res) -> res
  | None -> false

(*eliminates a fv that is otherwise to be existentially quantified, it does so only if the substitution is not
  a heap var as that would break the linearization..., used in the cast simplifications *)
let elim_e_var to_keep (f0 : formula) : formula =
  let helper2 f = match f with
    | Base b ->
      let h = b.formula_base_heap in
      let p = b.formula_base_pure in
      let a_alias,_ = Mcpure.get_all_vv_eqs_mix p in
      let a_alias = (*filter any directly heap related aliasing *)
        let no_touch = h_fv h in
        List.filter (fun (v1,v2)->
            let f v = not (Gen.BList.mem_eq CP.eq_spec_var v no_touch)  in
            (f v1)&&(f v2)) a_alias in
      let a_alias = (*ensure no substitution of used vars occurs*)
        List.fold_left (fun a (v1,v2)->
            let f v = Gen.BList.mem_eq (=) (CP.name_of_spec_var v) to_keep in
            match (f v1),(f v2) with
            | true,true  -> a
            | true,false -> (v2,v1)::a
            | false,true
            | false,false -> (v1,v2)::a) [] a_alias in
      let () = print_string ("bai-dropped:   "^(pr_list (pr_pair !print_sv !print_sv) a_alias)^"\n") in
      let np = MCP.memo_subst a_alias p in
      let np = MCP.drop_triv_eq np in
      Base{b with formula_base_pure = np;}
    | _ -> f in
  let rec helper f0 = match f0 with
    | Or b -> mkOr (helper b.formula_or_f1) (helper b.formula_or_f2) b.formula_or_pos
    | Base _
    | Exists _ ->
      let qvars,b = split_quantifiers f0 in
      push_exists qvars (helper2 b) in
  helper f0


(*Long: todo here*)
(* Loc: moved to cfout *)
(* let shorten_svl fv  n_tbl = *)
(*   (\* let n_tbl = Hashtbl.create 1 in *\) *)
(*   let reg = Str.regexp "[0-9]*_.*" in  *)
(*   let n_svl = List.map (fun sv -> *)
(*       match sv with *)
(*           CP.SpecVar(t,id,pr) -> *)
(*               let cut_id = Str.global_replace reg "" id in *)
(*               let new_id = *)
(*                 if Hashtbl.mem n_tbl (cut_id,pr) *)
(*                 then *)
(*                   begin *)
(*                     Hashtbl.add n_tbl (cut_id,pr) ((Hashtbl.find n_tbl (cut_id,pr)) + 1); *)
(*                     cut_id ^ string_of_int(Hashtbl.find n_tbl (cut_id,pr)) *)
(*                   end *)
(*                 else *)
(*                   begin *)
(*                     Hashtbl.add n_tbl (cut_id,pr) 0; *)
(*                     cut_id *)
(*                   end *)
(*               in *)
(*               CP.SpecVar(t,(\*(Str.global_replace reg "" id)^ "_" ^Globals.fresh_inf_number()*\) new_id,pr) *)
(*   ) fv in *)
(*   (n_svl,  n_tbl) *)

(* Loc: moved to cfout *)
(* let rearrange_h_formula_x args0 hf0 = *)
(*   let rec helper fv hfl = *)
(*     match fv with *)
(*       | [] -> hfl *)
(*       | v :: fvt ->  *)
(*             (List.filter (fun hf -> contains_spec_var hf v) hfl)@(helper fvt (List.filter (fun hf -> not (contains_spec_var hf v)) hfl)) *)
(*   in *)
(*   match hf0 with *)
(*     | Star hfs -> *)
(*           let fl = split_star_conjunctions hf0 in *)
(*           let re = List.hd args0 in *)
(*           (\* let r = (match re with *\) *)
(*           (\*   | CP.Var(sv, pos) -> sv *\) *)
(*           (\*   | _ -> raise Not_found) in *\) *)
(*           let rf = List.filter (fun hf -> contains_spec_var hf re) fl in *)
(*           let fv = h_fv (List.hd rf) in *)
(*           (\* let () = print_endline (pr_list !print_sv fv) in *\) *)
(*           let fl1 = helper fv fl in *)
(*           (\* let () = print_endline (pr_list !print_h_formula fl1) in *\) *)
(*           let hf1 = List.fold_left (fun f1 f2 -> mkStarH f1 f2 no_pos) (List.hd fl1) (List.tl fl1) in hf1 *)
(*     | _ -> hf0 *)

(* Loc: moved to cfout *)
(* let rearrange_h_formula args0 hf0 = *)
(*   (\* let pr1 = !CP.print_sv in *\) *)
(*   let pr2 = pr_list !CP.print_sv in *)
(*   let pr3 = !print_h_formula in *)
(*   Debug.no_2 "rearrange_h_formula" pr2 pr3 pr3 *)
(*        (fun _ _ -> rearrange_h_formula_x args0 hf0) *)
(*        args0 hf0 *)

(* Loc: moved to cfout *)
(*args0 is root + args of root*)
(* let rearrange_formula_x args0 f0= *)
(*   let rec helper f= *)
(*     match f with *)
(*       | Base fb -> *)
(*             let nh = *)
(*               try rearrange_h_formula args0 fb.formula_base_heap *)
(*               with _ -> fb.formula_base_heap *)
(*             in *)
(*             Base {fb with formula_base_heap = nh; } *)
(*       | Exists _ -> *)
(*             let qvars, base1 = split_quantifiers f in *)
(*             let nf = helper base1 in *)
(*             add_quantifiers qvars ( nf) *)
(*       | Or orf  -> *)
(*             Or { orf with formula_or_f1 = helper orf.formula_or_f1; *)
(*                 formula_or_f2 = helper orf.formula_or_f2 } *)
(*   in *)
(*   helper f0 *)

(* Loc: moved to cfout *)
(* let rearrange_formula args0 f0= *)
(*   let pr1 = pr_list !CP.print_sv in *)
(*   let pr2 = !print_formula in *)
(*   Debug.no_2 "rearrange_formula" pr1 pr2 pr2 *)
(*       (fun _ _ -> rearrange_formula_x args0 f0) *)
(*       args0 f0 *)

(* Loc: moved to cfout *)
(* let rearrange_def def= *)
(*   let new_body1 = *)
(*     match def.hprel_def_body_lib with *)
(*       | Some _ -> def.hprel_def_body *)
(*       | None -> begin *)
(*           try *)
(*             let args = match def.hprel_def_hrel with *)
(*               | HRel (sv, exp_list, pos) -> *)
(*                     List.map (fun exp -> match exp with *)
(*                       | CP.Var(sv, pos) -> sv *)
(*                       | _ -> raise Not_found) exp_list *)
(*               | _ -> raise Not_found *)
(*             in *)
(*             List.map (fun ((p, f_opt) as o) -> *)
(*                 match f_opt with *)
(*                   | Some f -> *)
(*                       (p, Some (rearrange_formula args f)) *)
(*                   | None -> o *)
(*           ) def.hprel_def_body *)
(*           with _ -> def.hprel_def_body *)
(*         end *)
(*   in *)
(*   (\*to shorten variable names here*\) *)
(*   let args = match def.hprel_def_kind with *)
(*     | CP.HPRelDefn (_,r,args) -> r::args *)
(*     | _ -> [] *)
(*   in *)
(*   let svll = List.map (fun (p, f_opt) -> *)
(*                match f_opt with *)
(*                  | Some f -> fv f *)
(*                  | None -> [] *)
(*   ) new_body1 in *)
(*   let svl = List.flatten svll in *)
(*   (\* let () = print_endline ((pr_list !print_sv) (args@svl)) in *\) *)
(*   let svl_rd = List.rev(CP.remove_dups_svl (List.rev args@svl)) in *)
(*   (\*let () = print_endline ((pr_list !print_sv) svl_rd) in*\) *)
(*   (\* let svl_ra = (\\* svl_rd in  *\\)CP.diff_svl svl_rd args in *\) *)
(*   let svl_rp = List.filter (fun sv -> not (CP.is_hprel_typ sv)) svl_rd in *)
(*   (\* let n_tbl = Hashtbl.create 1 in *\) *)
(*   (\* let reg = Str.regexp "_.*" in *\) *)
(*   let n_tbl = Hashtbl.create 1 in *)
(*   let new_svl,_ = shorten_svl svl_rp n_tbl in  *)
(*   let new_body2 = *)
(*     List.map (fun ((p, f_opt) as o) -> *)
(*         match f_opt with *)
(*           | Some f -> (p, Some (subst_avoid_capture svl_rp new_svl f)) *)
(*           | None -> o *)
(*   ) new_body1 *)
(*   in *)
(*   let new_hrel = subst_avoid_capture_h svl_rp new_svl def.hprel_def_hrel in *)
(*   let n_lib = match def.hprel_def_body_lib with *)
(*     | None -> None *)
(*     | Some f -> Some (subst_avoid_capture svl_rp new_svl f) *)
(*   in *)
(*   {def with hprel_def_body = new_body2; *)
(*       hprel_def_body_lib = n_lib; *)
(*       hprel_def_hrel = new_hrel;} *)

(* let rearrange_def def= *)
(*   let pr1 =  *)

(* Loc: moved to cfout *)
(* let rearrange_rel (rel: hprel) = *)
(*   let lfv = List.filter (fun sv -> not (CP.is_hprel_typ sv)) (CP.remove_dups_svl (fv rel.hprel_lhs)) in *)
(*   let gfv = (match rel.hprel_guard with *)
(*     | None -> [] *)
(*     | Some f -> List.filter (fun sv -> not (CP.is_hprel_typ sv)) (CP.remove_dups_svl (fv f))) in *)
(*   let rfv = List.filter (fun sv -> not (CP.is_hprel_typ sv)) (CP.remove_dups_svl (fv rel.hprel_rhs)) in *)
(*   let fv = CP.remove_dups_svl (lfv@gfv@rfv) in *)
(*   (\* let n_tbl = Hashtbl.create 1 in *\) *)
(*   (\* let reg = Str.regexp "_.*" in *\) *)
(*   let n_tbl = Hashtbl.create 1 in *)
(*   let new_svl,_ = shorten_svl fv n_tbl in *)
(*   {rel with hprel_lhs = subst_avoid_capture fv new_svl (rearrange_formula lfv rel.hprel_lhs); *)
(*       hprel_guard = (match rel.hprel_guard with *)
(*          | None -> None *)
(*          | Some f -> Some (subst_avoid_capture fv new_svl (rearrange_formula gfv f))); *)
(*       hprel_rhs = subst_avoid_capture fv new_svl (rearrange_formula rfv rel.hprel_rhs) ; *)
(*   } *)

(* Loc: moved to cfout *)
(* let rearrange_entailment_x lhs rhs= *)
(*   (\*shorten quantifiers of f*\) *)
(*   let shorten_quantifiers f tbl= *)
(*     let quans, bare = split_quantifiers f in *)
(*     let n_quans, tbl1 = shorten_svl quans tbl in *)
(*     let sst0 = List.combine quans n_quans in *)
(*     let new_f = add_quantifiers n_quans (subst sst0 f) in *)
(*     (f, sst0, tbl1) *)
(*   in *)
(*   let tbl0 = Hashtbl.create 1 in *)
(*   (\*rename quantifiers of lhs*\) *)
(*   let lhs1, l_sst, tbl1 = shorten_quantifiers lhs tbl0 in *)
(*   let rhs1 = subst l_sst rhs in *)
(*   (\*rename quantifiers of rhs*\) *)
(*   let rhs2, _, tbl2 = shorten_quantifiers rhs1 tbl1 in *)
(*   let l_svl = (CP.remove_dups_svl (fv lhs1)) in *)
(*   let r_svl = (CP.remove_dups_svl (fv rhs2)) in *)
(*   let all_svl = CP.remove_dups_svl (l_svl@r_svl) in *)
(*   let new_svl,_ = shorten_svl all_svl tbl2 in *)
(*   let n_lhs = subst_avoid_capture all_svl new_svl (rearrange_formula l_svl lhs1) in *)
(*   let n_rhs = subst_avoid_capture all_svl new_svl (rearrange_formula r_svl rhs2) in *)
(*   (n_lhs, n_rhs) *)

(* Loc: moved to cfout *)
(* let rearrange_entailment lhs rhs= *)
(*   let pr1 = !print_formula in *)
(*   let pr2 = pr_pair pr1 pr1 in *)
(*   Debug.no_2 "rearrange_entailment" pr1 pr1 pr2 *)
(*       (fun _ _ -> rearrange_entailment_x lhs rhs) *)
(*       lhs rhs *)

(* Loc: moved to cfout *)
(* let shorten_formula f = *)
(*   let f0 = simplify_pure_f f in *)
(*   let fvars = fv f0 in *)
(*   let qvars,_ = split_quantifiers f0 in *)
(*   (\* let () = print_endline ((pr_list !print_sv) fv) in *\) *)
(*   let vars = CP.remove_dups_svl (fvars@qvars) in *)
(*   let n_tbl = Hashtbl.create 1 in *)
(*   let new_svl,_ = shorten_svl vars n_tbl in *)
(*   (\* let () = print_endline ((pr_list !print_sv) new_svl) in *\) *)
(*   (\* subst_avoid_capture vars new_svl f *\) *)
(*   subst_all (List.combine vars new_svl) f0 *)

(* let rearrange_context bc = *)
(*   let rec helper ctx = *)
(*     match ctx with *)
(*       | Ctx en -> Ctx {en with *)
(*           es_formula = *)
(*                 let fv = CP.remove_dups_svl (fv en.es_formula) in *)
(*                 (\* let () = print_endline ((pr_list !print_sv) fv) in *\) *)
(*                 let new_svl = shorten_svl fv in *)
(*                 (\* let () = print_endline ((pr_list !print_sv) new_svl) in *\) *)
(*                 subst_avoid_capture fv new_svl en.es_formula *)
(*         } *)
(*       | OCtx (ctx1, ctx2) -> OCtx (helper ctx1, helper ctx2) *)
(*   in *)
(*   match bc with *)
(*     | (pt, ctx) -> (pt, helper ctx) *)

(* let rearrange_failesc_context fc = *)
(*   match fc with *)
(*     | (bfl, esc, bcl) -> (bfl, esc, List.map rearrange_context bcl) *)

(* let rearrange_failesc_context_list fcl = *)
(*   List.map rearrange_failesc_context fcl *)

let rec contains_starminus (f:h_formula) : bool =
  (*let _ = print_string ("Checking StarMinus = "^ (string_of_h_formula f) ^ "\n") in *)
  match f with
  | DataNode (h1) -> false
  | ViewNode (h1) -> false
  | Star ({h_formula_star_h1 = h1;
           h_formula_star_h2 = h2;
           h_formula_star_pos = pos})
  | Phase ({h_formula_phase_rd = h1;
            h_formula_phase_rw = h2;
            h_formula_phase_pos = pos})
  | Conj({h_formula_conj_h1 = h1;
          h_formula_conj_h2 = h2;
          h_formula_conj_pos = pos})
  | ConjStar({h_formula_conjstar_h1 = h1;
              h_formula_conjstar_h2 = h2;
              h_formula_conjstar_pos = pos})
  | ConjConj({h_formula_conjconj_h1 = h1;
              h_formula_conjconj_h2 = h2;
              h_formula_conjconj_pos = pos})-> (contains_starminus h1) || (contains_starminus h2)
  | StarMinus _ -> true
  | _ -> false

let rec is_inf_tnt_struc_formula f =
  match f with
  | EList el -> List.exists (fun (_, f) -> is_inf_tnt_struc_formula f) el
  | ECase ec -> List.exists (fun (_, f) -> is_inf_tnt_struc_formula f) ec.formula_case_branches
  | EBase eb -> begin
      match eb.formula_struc_continuation with
      | None -> false
      | Some c -> is_inf_tnt_struc_formula c
    end
  | EAssume _ -> false
  | EInfer ei -> (ei.formula_inf_obj # is_term) || (is_inf_tnt_struc_formula ei.formula_inf_continuation)

let ann_of_h_formula h =
  match h with
  | DataNode dn -> Some dn.h_formula_data_imm
  | ViewNode vn -> Some vn.h_formula_view_imm
  | _ -> None

let restore_hole_formula f hole_matching =
  let f_h_f h = match h with
    | Hole i ->
      (try
         let rep_h = List.assoc i hole_matching in
         let ann = ann_of_h_formula rep_h in
         match ann with
         | Some CP.ConstAnn(Lend) -> Some h
         | _ -> Some rep_h
       with _ -> Some h)
    | _ -> Some h in
  transform_formula (nonef, nonef, f_h_f, (somef, somef, somef, somef, somef)) f

let force_elim_exists_x f quans=
  let ( _,mf,_,_,_,_) = split_components f in
  let eqs = (MCP.ptr_equations_without_null mf) in
  let sst, inter_eqs = if quans = [] then eqs,[] else
      List.fold_left (fun (r1,r2) (sv1,sv2) ->
          let b1 = CP.mem_svl sv1 quans in
          let b2 = CP.mem_svl sv2 quans in
          match b1,b2 with
          | false,true -> (r1@[(sv2,sv1)], r2@[(sv1,sv2)])
          | true, false -> r1@[(sv1,sv2)], r2@[(sv1,sv2)]
          | _ -> r1,r2
        ) ([],[]) eqs in
  (* let ps = List.map  (fun (sv1, sv2) -> CP.mkPtrEqn sv1 sv2 no_pos) inter_eqs in *)
  simplify_pure_f (x_add subst sst f)(* ,  Mcpure.mix_of_pure (CP.conj_of_list ps no_pos ) *)

let force_elim_exists f quans=
  let pr1 = !print_formula in
  let pr2 = !CP.print_svl in
  Debug.no_2 "force_elim_exists" pr1 pr2 pr1
    (fun _ _ -> force_elim_exists_x f quans) f quans

let h_formula_contains_node_name h ident =
  let rec helper h =
    match h with
    | ViewNode   ({ h_formula_view_name = name; })
    | DataNode   ({ h_formula_data_name = name; })
    | ThreadNode ({ h_formula_thread_name = name; }) ->
      if (String.compare ident name == 0) then true else false
    | Star ({h_formula_star_h1 = h1;
             h_formula_star_h2 = h2;})
    | StarMinus ({ h_formula_starminus_h1 = h1;
                   h_formula_starminus_h2 = h2;})
    | Conj ({ h_formula_conj_h1 = h1;
              h_formula_conj_h2 = h2;})
    | ConjStar ({h_formula_conjstar_h1 = h1;
                 h_formula_conjstar_h2 = h2;} )
    | ConjConj ({h_formula_conjconj_h1 = h1;
                 h_formula_conjconj_h2 = h2;} )
    | Phase ({ h_formula_phase_rd = h1;
               h_formula_phase_rw = h2;}) ->
      ((helper h1) || (helper h2))
    | _ -> false
  in helper h

let h_formula_contains_node h aset ident =
  let rec helper h =
    match h with
    | ViewNode   ({ h_formula_view_name = name; h_formula_view_node = sv; })
    | DataNode   ({ h_formula_data_name = name; h_formula_data_node = sv; })
    | ThreadNode ({ h_formula_thread_name = name; h_formula_thread_node = sv; }) ->
      if (String.compare ident name == 0 && CP.EMapSV.mem sv aset) then true else false
    | Star ({h_formula_star_h1 = h1;
             h_formula_star_h2 = h2;})
    | StarMinus ({ h_formula_starminus_h1 = h1;
                   h_formula_starminus_h2 = h2;})
    | Conj ({ h_formula_conj_h1 = h1;
              h_formula_conj_h2 = h2;})
    | ConjStar ({h_formula_conjstar_h1 = h1;
                 h_formula_conjstar_h2 = h2;} )
    | ConjConj ({h_formula_conjconj_h1 = h1;
                 h_formula_conjconj_h2 = h2;} )
    | Phase ({ h_formula_phase_rd = h1;
               h_formula_phase_rw = h2;}) ->
      ((helper h1) || (helper h2))
    | _ -> false
  in helper h

let is_emp_h_formula h =
    match h with
    | HEmp | HTrue -> true
    | _ -> false

let star_elim_useless_emp h =
  let rec helper h =
    match h with
    | HEmp -> None
    | Star ({h_formula_star_h1 = h1;
             h_formula_star_h2 = h2;}) ->
      let h1 = helper h1 in
      let h2 = helper h2 in
      let new_h =
        match h1,h2 with
        | Some h0, None
        | None, Some h0 -> Some h0
        | None, None    -> None
        | _             -> Some h
      in new_h
    | _ -> Some h                          (*incomplete *)
  in
  let new_h_opt = helper h in
  let new_h =
    match new_h_opt with
    | None -> HEmp
    | _    -> h
  in new_h

(** An Hoa : collect important variables in the specification
    Important variables are the ones that appears in the
    post-condition. Those variables are necessary in order
    to prove the final correctness. **)
and collect_important_vars_in_spec deep_flag (spec : struc_formula) : (CP.spec_var list) =
  (** An Hoa : Internal function to collect important variables in the an ext_formula **)
  let rec helper f = match f with
    | ECase b -> List.fold_left (fun x y -> List.append x (helper (* collect_important_vars_in_spec *) (snd y))) [] b.formula_case_branches
    | EBase b ->
      (b.formula_struc_implicit_inst) @ (
        if deep_flag then
          match b.formula_struc_continuation with
          | None -> []
          | Some f -> helper f
        else [])
    | EAssume b -> []
    | EInfer b ->
      if deep_flag then helper b.formula_inf_continuation
      else []
    | EList b -> fold_l_snd helper b
  in
  helper spec

(** An Hoa : end collect_important_vars_in_spec **)
(*Loc: should support mutrec views*)
let project_h_formula_num hf inv svl =
  let rec helper hf =
    match hf with
    | Star sf ->
      let pf1 = helper sf.h_formula_star_h1 in
      let pf2 = helper sf.h_formula_star_h2 in
      let pos = pos_of_h_formula hf in
      CP.mkAnd pf1 pf2 pos
    | ViewNode vn ->
      let args = vn.h_formula_view_arguments in
      let sst = List.combine svl args in
      CP.subst sst inv
    | DataNode dn ->
      let pos = pos_of_h_formula hf in
      CP.mkGtVarInt dn.h_formula_data_node 0 pos
    | _ -> CP.mkTrue no_pos
  in
  try
    helper hf
  with _ -> CP.mkTrue no_pos

let project_h_formula_num hf inv svl =
  let pr1 = !print_h_formula in
  let pr2 = !CP.print_svl in
  let pr3 = !CP.print_formula in
  Debug.no_3 "project_h_formula_num" pr1 pr3 pr2 pr3
    project_h_formula_num hf inv svl

let project_formula_num f inv svl =
  let rec helper f =
    match f with
    | Base b ->
      let hf = project_h_formula_num b.formula_base_heap inv svl in
      let pf = MCP.pure_of_mix b.formula_base_pure in
      let pos = pos_of_formula f in
      CP.mkAnd hf pf pos
    | Or o ->
      let pf1 = helper o.formula_or_f1 in
      let pf2 = helper o.formula_or_f2 in
      let pos = pos_of_formula f in
      CP.mkOr pf1 pf2 None pos
    | Exists e ->
      let hf = project_h_formula_num e.formula_exists_heap inv svl in
      let pf = MCP.pure_of_mix e.formula_exists_pure in
      let vs = e.formula_exists_qvars in
      let pos = pos_of_formula f in
      CP.mkExists vs (CP.mkAnd hf pf pos) None pos
  in
  helper f

let project_body_num body inv svl =
  List.fold_left (fun acc (f,_) ->
      let pf = project_formula_num f inv svl in
      CP.mkOr acc pf None no_pos
    ) (CP.mkFalse no_pos) body

(* type: (formula * 'a) list -> CP.formula -> CP.spec_var list -> CP.formula *)

(*Loc: should support mutrec views*)
let project_body_num body inv svl =
  let pr = !print_pure_f in
  Debug.no_3 "project_body_num" (pr_list (fun (a,_) -> !print_formula a)) pr (!print_spec_var_list) pr project_body_num body inv svl

let subst_hvar_struc f subst =
  let f_f e = Some (subst_hvar e subst) in
  transform_struc_formula
    (nonef, f_f, somef,
     (somef, somef, somef, somef, somef)) f

let subst_hvar_struc f subst =
  let pr = !print_struc_formula in
  Debug.no_1 "subst_hvar_struc" pr pr
    (fun _ -> subst_hvar_struc f subst) f

(* Utils for Vperm reasoning *)

let mkEmp_list_failesc_context pos =
  let ctx = empty_ctx (mkTrueFlow ()) Label_only.Lab2_List.unlabelled pos in
  let ctx = build_context ctx (mkTrue_nf pos) pos in
  let ctx = add_path_id ctx (None, 0) 0 in
  let ctx = set_flow_in_context_override
      { formula_flow_interval = !norm_flow_int; formula_flow_link = None } ctx in
  (* Add initial esc_stack *)
  let init_esc = [((0, ""), [])] in
  let fctx = [mk_failesc_context ctx [] init_esc] in
  fctx

let set_imm_ann_formula ann_list f =
  let f_h_f hf =
    match hf with
    | DataNode ({ h_formula_data_node = sv; } as d) ->
      (try
         let _, imm = List.find (fun (v, _) -> CP.eq_spec_var v sv) ann_list in
         Some (DataNode ({ d with h_formula_data_imm = imm; }))
       with _ -> Some hf)
    | ViewNode ({ h_formula_view_node = sv; } as v) ->
      (try
         let _, imm = List.find (fun (v, _) -> CP.eq_spec_var v sv) ann_list in
         Some (ViewNode ({ v with h_formula_view_imm = imm; }))
       with _ -> Some hf)
    | _ -> None
  in
  transform_formula (nonef, nonef, f_h_f, (somef, somef, somef, somef, somef)) f

let rec remove_heap_formula f =
  match f with
  | Base b -> Base ({ b with formula_base_heap = HEmp; })
  | Exists e -> Exists ({ e with formula_exists_heap = HEmp; })
  | Or o -> Or { o with
                 formula_or_f1 = remove_heap_formula o.formula_or_f1;
                 formula_or_f2 = remove_heap_formula o.formula_or_f2; }

let remove_heap_list_failesc_ctx ctx =
  let remove_heap_es es =
    Ctx { es with es_formula = remove_heap_formula es.es_formula; }
  in transform_list_failesc_context (idf, idf, remove_heap_es) ctx

let remove_lend_ann_formula f =
  let f_h_f _ hf =
    match hf with
    | DataNode ({ h_formula_data_imm = imm; } as d) ->
      if CP.isLend imm then
        Some (DataNode ({ d with h_formula_data_imm = ConstAnn(Mutable)}), [d.h_formula_data_node])
      else Some (hf, [])
    | ViewNode ({ h_formula_view_imm = imm; } as v) ->
      if CP.isLend imm then
        Some (ViewNode ({ v with h_formula_view_imm = ConstAnn(Mutable)}), [v.h_formula_view_node])
      else Some (hf, [])
    | _ -> None
  in
  let somef2 _ f = Some (f, []) in
  let id2 f _ = (f, []) in
  let ida _ f = (f, []) in
  let f_arg = (voidf2, voidf2, voidf2, (voidf2, voidf2, voidf2), voidf2) in
  trans_formula f () (nonef2, nonef2, f_h_f, (somef2, somef2, somef2), (somef2, id2, ida, id2, id2)) f_arg List.concat

let remove_lend_ann_formula f =
  let f_h_f _ hf =
    match hf with
    | DataNode ({ h_formula_data_imm = imm; } as d) ->
      if CP.isLend imm then
        Some (DataNode ({ d with h_formula_data_imm = ConstAnn(Mutable)}), [d.h_formula_data_node])
      else Some (hf, [])
    | ViewNode ({ h_formula_view_imm = imm; } as v) ->
      if CP.isLend imm then
        Some (ViewNode ({ v with h_formula_view_imm = ConstAnn(Mutable)}), [v.h_formula_view_node])
      else Some (hf, [])
    | _ -> None
  in
  let somef2 _ f = Some (f, []) in
  let id2 f _ = (f, []) in
  let ida _ f = (f, []) in
  let f_trans = (nonef2, nonef2, f_h_f, (somef2, somef2, somef2), (somef2, id2, ida, id2, id2)) in
  let f_arg = (voidf2, voidf2, voidf2, (voidf2, voidf2, voidf2), voidf2) in
  trans_formula f () f_trans f_arg List.concat

(* let remove_lend_ann_list_failesc_ctx ctx =                              *)
(*   let remove_lend_ann_es es =                                           *)
(*     Ctx { es with es_formula = remove_lend_ann_formula es.es_formula; } *)
(*   in transform_list_failesc_context (idf, idf, remove_lend_ann_es) ctx  *)

let remove_lend_list_failesc_ctx ctx =
  let remove_lend_es es =
    Ctx { es with es_formula = remove_lend es.es_formula; }
  in transform_list_failesc_context (idf, idf, remove_lend_es) ctx

let isLend_h_formula hf =
  let f_h_f _ hf =
    match hf with
    | DataNode ({ h_formula_data_imm = imm; })
    | ViewNode ({ h_formula_view_imm = imm; }) ->
      if CP.isLend imm then Some (hf, true)
      else Some (hf, false)
    | _ -> None
  in
  snd (trans_h_formula hf () f_h_f voidf2 and_list)

let isLend_formula f =
  match f with
  | Or _ -> false
  | Base ({ formula_base_heap = h })
  | Exists ({ formula_exists_heap = h }) ->
    isLend_h_formula h

(*
  type: (struc_formula -> struc_formula option) * (formula -> formula option) *
  (h_formula -> h_formula option) *

  ((Mcpure_D.memo_pure -> Mcpure_D.memo_pure option) *
   (Mcpure_D.var_aset -> Mcpure_D.var_aset option) *
   (CP.formula -> CP.formula option) *
   (Cpure.b_formula -> Cpure.b_formula option) * (CP.exp -> CP.exp option)) ->
  struc_formula -> struc_formula
*)

let f_change f = match f with
  | Base fe -> Some (Base { fe with formula_base_vperm = CVP.vperm_unprime fe.formula_base_vperm })
  | Exists f2 -> Some (Exists { f2 with formula_exists_vperm = CVP.vperm_unprime f2.formula_exists_vperm})
  | Or _  -> None

let un_norm_fn e =
  let f_none _ = None in
  let f_id x = Some x in
  (* let f_change = f_id in *)
  let f = (f_none, f_change, f_id,(f_id, f_id,f_id,f_id,f_id)) in
  transform_struc_formula f e

let subst_struc_pre sst (f : struc_formula) =
  let wrap_pre f = Wrapper.wrap_one_bool pre_subst_flag true (subst_struc_pre sst) f in
  let un_norm_flag = true in
  (* let un_norm_fn r = r in  *)
  let pr = !print_struc_formula in
  let prlst = pr_list (pr_pair !print_sv !print_sv) in
  Debug.no_2 "subst_struc_pre" prlst pr pr (fun _ _ -> Wrapper.wrap_norm un_norm_flag un_norm_fn wrap_pre f) sst f

(* let map_list_failesc_context f ctx =                           *)
(*   let f_ctx _ ctx = Some (f ctx, ()) in                        *)
(*   let arg = () in                                              *)
(*   let f_comb _ = () in                                         *)
(*   fst (trans_list_failesc_context ctx arg f_ctx voidf2 f_comb) *)

(* let add_vperm_sets_context (vp: CVP.vperm_sets) ctx =                 *)
(*   let add_vperm_sets_es vp es =                                       *)
(*     { es with es_formula = add_vperm_sets_formula vp es.es_formula; } *)
(*   in map_context (add_vperm_sets_es vp) ctx                           *)

(* let add_vperm_sets_list_failesc_ctx (vp: CVP.vperm_sets) ctx =        *)
(*   map_list_failesc_context (add_vperm_sets_context vp) ctx            *)

(* let prepare_ctx_for_par (vp: CVP.vperm_sets) ctx =                     *)
(*   let prepare_es_for_par vp es =                                       *)
(*     es.es_infer_obj # set INF_PAR;                                     *)
(*     { es with es_formula = set_vperm_sets_formula vp es.es_formula; }  *)
(*   in                                                                   *)
(*   map_context (prepare_es_for_par vp) ctx                              *)

(* let prepare_list_failesc_ctx_for_par (vp: CVP.vperm_sets) ctx =        *)
(*   map_list_failesc_context (prepare_ctx_for_par vp) ctx                *)

(* let clear_inf_par_ctx ctx =                      *)
(*   let clear_inf_par_es es =                      *)
(*     es.es_infer_obj # reset INF_PAR; es          *)
(*   in                                             *)
(*   map_context clear_inf_par_es ctx               *)

(* let clear_inf_par_list_failesc_ctx ctx =         *)
(*   map_list_failesc_context clear_inf_par_ctx ctx *)

(* End of Utils for Vperm reasoning *)

let get_vperm_set f =
  let helper f = match f with
    | Base {formula_base_vperm = vp}
    | Exists {formula_exists_vperm = vp}
      -> vp
    | _ -> failwith "get_vperm_set: not expecting OR formula"
  in helper f

let write_vperm_set f vp =
  let helper f = match f with
    | Base b -> Base { b with formula_base_vperm = vp;}
    | Exists b -> Exists { b with formula_exists_vperm = vp;}
    | _ -> failwith "write_vperm_set:not expecting OR formula"
  in helper f


let exist_reachable_states_x (rs:list_partial_context)=
  List.for_all (fun (_,brs) -> not (isFalseBranchCtxL brs)
               ) rs


let exist_reachable_states (rs:list_partial_context)=
  let pr1 = !print_list_partial_context in
  Debug.no_1 "exist_reachable_states" pr1 string_of_bool
    (fun _ -> exist_reachable_states_x rs) rs


let determine_infer_type sp t  = match sp with
  | EInfer b ->
    let inf_o = b.formula_inf_obj in
    inf_o # get t
  | _ -> false

let determine_infer_classic sp  =
  determine_infer_type sp INF_CLASSIC

let determine_arr_as_var sp  =
  determine_infer_type sp INF_ARR_AS_VAR

let form_components (f : formula) hf pf heap_pure =
  if is_False pf || is_False heap_pure then mkFalse mkFalseFlow  no_pos
  else
    let mpf = MCP.mix_of_pure pf in
    match f with
      | Base bf -> Base {bf with formula_base_heap=hf; formula_base_pure=mpf}
      | Exists bf -> Exists {bf with formula_exists_heap=hf; formula_exists_pure=mpf}
      | _ -> report_error no_pos "simplify cannot handle or"

(* Nondeterminism variables *)
let collect_nondet_vars_formula f =
  let f_p_f e = CP.collect_nondet_vars e in
  let f_p_f_opt e = Some (f_p_f e) in
  let f_emp_f _ = [] in
  let f_f = nonef, nonef, (f_p_f_opt, nonef, nonef), (nonef, f_emp_f, f_emp_f, f_p_f, f_emp_f) in
  fold_formula f f_f List.concat

let collect_nondet_vars_list_failesc_context c =
  let f_c _ c = Some (c, fold_context (fun _ es -> collect_nondet_vars_formula es.es_formula) [] c) in
  Gen.BList.remove_dups_eq CP.eq_spec_var
    (snd (trans_list_failesc_context c () f_c voidf2 List.concat))

(* End of Nondeterminism variables *)

let collect_infer_rel_context c =
   (fold_context (fun xs es -> (es.es_infer_rel # get_stk) @ xs) [] c)

let collect_infer_rel_list_context lfc =
  let f_a a _ = a in
  let f_b _ c = Some (c,collect_infer_rel_context c) in
  Gen.Basic.remove_dups (snd(trans_list_context lfc () f_b f_a List.concat))

let collect_infer_rel_list_partial_context lfc =
  let f_a a _ = a in
  let f_b _ c = Some (c,collect_infer_rel_context c) in
  Gen.Basic.remove_dups (snd(trans_list_partial_context lfc () f_b f_a List.concat))

let collect_infer_rel_list_failesc_context lfc =
  let f_a a _ = a in
  let f_b _ c = Some (c,collect_infer_rel_context c) in
  Gen.Basic.remove_dups (snd(trans_list_failesc_context lfc () f_b f_a List.concat))

(* type: list_partial_context -> *)
(*   (entail_state -> entail_state) -> (branch_fail list * branch_ctx list) list *)

(* let map_unsat_partial_context ctx = *)
(*   let f e = e *)
(*   in *)
(*   map_list_partial_context ctx f  *)

let extract_hrel_list (hf:h_formula) pf =
  let lst = new Gen.stack in
  let f hf = match hf with
    |  HRel (hp, eargs, _ ) ->
      let () = lst # push (hp,eargs,pf) in
      Some (HEmp)
    | _ -> None
  in
  let new_f = map_h_formula hf f in
  (lst # get_stk,new_f)

let extract_hrel_list (hf:h_formula) p1 =
  Debug.no_1 "extract_hrel_list" !print_h_formula
    (pr_pair (pr_list (pr_triple !CP.print_sv (pr_list !CP.print_exp) !CP.print_formula)) !print_h_formula)
    (fun _ -> extract_hrel_list hf p1) hf

(* (==infer.ml#3554==) *)
(* extract_hrel_head_list@9@6 *)
(* extract_hrel_head_list inp1 : H(p)&p=null&{FLOW,(20,21)=__norm#E}[] *)
(* extract_hrel_head_list@9 EXIT:Some(([(H,[ p])], emp&p=null&{FLOW,(20,21)=__norm#E}[])) *)
let extract_hrel_head_list (f0:formula) =
  let rec helper f =
    match f with
    | Base ({formula_base_heap = h1; formula_base_pure = p1;} as r) ->
      let p1 = MCP.pure_of_mix p1 in
      let (lst,new_h) = extract_hrel_list h1 p1 in
      if lst==[] then None
      else Some(lst,Base {r with formula_base_heap = new_h})
    | Exists ({ formula_exists_heap = h1; formula_exists_pure = p1;} as r) ->
      let p1 = MCP.pure_of_mix p1 in
      let (lst,new_h) = extract_hrel_list h1 p1 in
      if lst==[] then None
      else Some(lst,Exists {r with formula_exists_heap = new_h})
    | Or ({formula_or_f1 = f1; formula_or_f2 = f2} as r) ->
      let new_1 = helper f1 in
      let new_2 = helper f2 in
      match new_1,new_2 with
      | None,None -> None
      | Some(l1,f1),None -> Some(l1, Or {r with formula_or_f1 = f1})
      | None,Some(l2,f2) -> Some(l2, Or {r with formula_or_f2 = f2})
      | Some(l1,f1),Some(l2,f2) ->
         Some(l1@l2, Or {r with formula_or_f1 = f1; formula_or_f2 = f2})
  in
  helper f0

let extract_hrel_head_list (f0:formula) =
  let pr_hr = pr_list (pr_triple !CP.print_sv (pr_list !CP.print_exp) !CP.print_formula) in
  let pr = pr_option (pr_pair pr_hr !print_formula) in
  Debug.no_1 "extract_hrel_head_list" !print_formula pr extract_hrel_head_list  f0

let trans_args sst args =
  if sst==[] then args
  else
    let new_args = List.combine args sst in
    let new_args = List.sort (fun (_,n1) (_,n2) -> n1-n2) new_args in
    List.map fst new_args

(* TODO:WN need to change other parameters too *)
let get_view_equiv vl sst new_name =
    let args = vl.h_formula_view_arguments in
    let new_args = trans_args sst args in
    {vl with h_formula_view_name = new_name;
             h_formula_view_arguments = new_args;}


let map_formula_heap_only map_h f =
  let rec aux f = match f with
    | Base bf -> Base {bf with formula_base_heap = map_h bf.formula_base_heap}
    | Exists bf -> Exists {bf with formula_exists_heap = map_h bf.formula_exists_heap}
    | Or bf -> Or {bf with formula_or_f1 = aux (bf.formula_or_f1); formula_or_f2 = aux (bf.formula_or_f2)}
  in aux f

let map_struc_formula_heap_only map_h f =
  let rec aux f = match f with
    | EList lst -> EList (List.map (fun (d,s) -> (d,aux s)) lst)
    | ECase cf ->
      let lst = cf.formula_case_branches in
      ECase { cf with
              formula_case_branches = List.map (fun (d,s) -> (d,aux s)) lst;
      }
    | EBase bf ->
      let f1 = map_formula_heap_only map_h bf.formula_struc_base in
      let f2 = map_opt aux bf.formula_struc_continuation in
      EBase { bf with
              formula_struc_base = f1;
              formula_struc_continuation = f2;
            }
    | EInfer bf ->
      let f1 = aux bf.formula_inf_continuation in
      EInfer {bf with
              formula_inf_continuation=f1
             }
    | EAssume bf ->
      let f1 = aux bf.formula_assume_struc in
      let f2 = map_formula_heap_only map_h bf.formula_assume_simpl in
      EAssume {bf with
              formula_assume_struc = f1;
              formula_assume_simpl = f2;
             }
  in aux f

let map_estate_heap_only h_f es =
  let f = es.es_formula in
  let f = map_formula_heap_only h_f f in
  {es with es_formula = f}

let repl_equiv_heap find_f hf =
  let f hf = match hf with
    | HTrue | HFalse | HEmp | DataNode _ | Hole _ | HRel _ | HVar _ -> Some hf
    | ViewNode vl ->
      let name = vl.h_formula_view_name in
      begin
      match find_f name with
      | Some (sst,new_name) ->
        let vl = get_view_equiv vl sst new_name in
        Some (ViewNode vl)
      | _ -> Some hf
      end
    | _ -> None
  in map_h_formula hf f

(* let process_heap_prop_extn p_tab pname vns (\* mutual-rec *\) nnn_sv hf = *)
(*   let f hf = match hf with *)
(*     | HTrue | HFalse | HEmp | DataNode _ | Hole _ | HRel _ | HVar _ -> Some hf *)
(*     | DataNode dl -> *)
(*       failwith x_tbi *)
(*     | ViewNode vl -> *)
(*       let name = vl.h_formula_view_name in *)
(*       if List.exists (fun v -> v=name) vns then *)
(*         begin *)
(*           failwith x_tbi *)
(*         end *)
(*       else Some hf *)
(*     | _ -> None *)
(*   in map_h_formula hf f *)

let repl_equiv_formula find_f f =
  map_formula_heap_only (repl_equiv_heap find_f) f

let repl_equiv_formula find_f f =
  let pr = !print_formula in
  Debug.no_1 "repl_equiv_formula" pr pr (repl_equiv_formula find_f) f

let repl_equiv_struc_formula find_f f =
  map_struc_formula_heap_only (repl_equiv_heap find_f) f

let repl_equiv_struc_formula find_f f =
  let pr = !print_struc_formula in
  Debug.no_1 "repl_equiv_struc_formula" pr pr (repl_equiv_struc_formula find_f) f

let repl_equiv_estate find_f es =
  map_estate_heap_only (repl_equiv_heap find_f) es

let rm_htrue_heap hf =
  let f hf = match hf with
    | HTrue ->
      Some(HEmp)
    | HFalse | HEmp | DataNode _ | Hole _ | HRel _ | HVar _
      -> Some hf
    | _ -> None
  in map_h_formula hf f

let rm_htrue_heap hf =
  let pr = !print_h_formula in
  Debug.no_1 "rm_htrue_heap" pr pr rm_htrue_heap hf

let rm_htrue_struc_formula f =
  map_struc_formula_heap_only (rm_htrue_heap) f

(* TODO: implement and use a map_formula *)
let rm_htrue_formula f =
  map_formula_heap_only rm_htrue_heap f
  (* let rec aux f = match f with *)
  (*   | Base bf -> Base {bf with formula_base_heap = rm_htrue_heap bf.formula_base_heap} *)
  (*   | Exists bf -> Exists {bf with formula_exists_heap = rm_htrue_heap bf.formula_exists_heap} *)
  (*   | Or bf -> Or {bf with formula_or_f1 = aux (bf.formula_or_f1); formula_or_f2 = aux (bf.formula_or_f2)} *)
  (* in aux f *)


let rm_htrue_estate es =
  map_estate_heap_only rm_htrue_heap es
  (* let f = es.es_formula in *)
  (* let f = rm_htrue_formula f in *)
  (* {es with es_formula = f} *)

(* let rm_htrue_context c = *)
(*   let () = x_tinfo_pp "TODO : to be implemented .." no_pos in *)
(*   c *)

let collect_impl_expl_context c =
   (fold_context (fun xs es -> es.es_gen_impl_vars @ (es.es_gen_expl_vars @ xs)) [] c)

let collect_impl_expl_evars_context c =
   (fold_context (fun xs es -> es.es_evars @ (es.es_gen_impl_vars @ (es.es_gen_expl_vars @ xs))) [] c)

let collect_evars_context c =
   (fold_context (fun xs es -> es.es_evars @ xs) [] c)

let remove_inf_cmd_spec new_spec =
  match new_spec with
  | EInfer s -> s.formula_inf_continuation
  | _ -> new_spec

let remove_inf_cmd_spec new_spec =
  let pr = !print_struc_formula in
  Debug.no_1 "remove_inf_cmd_spec" pr pr
    remove_inf_cmd_spec new_spec

(* let un_opt e = match (CP.conv_exp_to_var e) with *)
(*   | Some (sv,_) -> sv *)
(*   | None ->  *)
(*     let () = y_winfo_pp " UNKNOWN spec_var used " in *)
(*     let () = y_tinfo_hp (add_str "exp is var?" !CP.print_exp) e in *)
(*     CP.unknown_spec_var *)


let name_of_h_formula x =
  match x with
  | HRel(v,args,_) -> (CP.name_of_spec_var v, List.map CP.exp_to_sv args)
  | DataNode {h_formula_data_name = n;
              h_formula_data_node = p1;
              h_formula_data_arguments = vs1;
             }
  | ViewNode {h_formula_view_name = n;
              h_formula_view_node = p1;
              h_formula_view_arguments = vs1} -> (n,(p1::vs1))
  | _ ->
        let () = y_ninfo_hp (add_str "problem with name_of_h_formula:" !print_h_formula) x in
        let s = "name_of_h_formula: "^(!print_h_formula x) in
        (s, [])

let name_of_formula x =
  let (h,_,_,_,_,_) = split_components x in
  name_of_h_formula h

let name_of_h_formula x =
  Debug.no_1 "name_of_h_formula" pr_none pr_none name_of_h_formula x

let is_exists_hp_rel v es =
  let vs = es.es_infer_vars_hp_rel in
  CP.is_exists_svl v vs

let get_args_of_node l_node =
  let l_ho_args, l_args, l_node_name, node_kind, r_var, l_perm, l_ann, l_param_ann =
    match l_node with
    | ThreadNode {
        h_formula_thread_name = l_node_name;
        h_formula_thread_node = r_var;
        h_formula_thread_perm = perm; } ->
      ([], [], l_node_name, "thread", r_var, perm, CP.ConstAnn(Mutable), [])
    | DataNode {
        h_formula_data_name = l_node_name;
        h_formula_data_perm = perm;
        h_formula_data_node = r_var;
        h_formula_data_imm = ann;
        h_formula_data_param_imm = param_ann;
        h_formula_data_arguments = l_args } ->
      ([], l_args, l_node_name, "data",r_var, perm, ann, param_ann)
    | ViewNode {
        h_formula_view_name = l_node_name;
        h_formula_view_perm = perm;
        h_formula_view_imm = ann;
        h_formula_view_node = r_var;
        h_formula_view_arguments = l_args;
        h_formula_view_ho_arguments = l_ho_args;
        h_formula_view_annot_arg = l_annot } ->
      (l_ho_args, l_args, l_node_name, "view",r_var, perm, ann, (CP.annot_arg_to_imm_ann_list (List.map fst l_annot)))
    (* TODO:WN:HVar -*)
    | HVar (v,hvar_vs) -> ([], [], CP.name_of_spec_var v, "ho_var",v, None, CP.ConstAnn Mutable, [])
    | HRel (rhp, eargs, _) -> ([], (List.fold_left List.append [] (List.map CP.afv eargs)), "", "hrel",rhp, None, CP.ConstAnn Mutable, [])
    | _ ->
      let h_f = !print_h_formula l_node in
      (* report_error no_pos ("[solver.ml]: do_match cannot handle "^h_f^"\n") *)
      x_fail ("get_args_of_node cannot handle "^ h_f ^ "\n")
  in l_ho_args, l_args, l_node_name, node_kind, r_var, l_perm, l_ann, l_param_ann

let get_args_of_node l_node =
  let pr = !print_h_formula in
  let dummy_pr = fun _ -> "" in
  Debug.no_1 "get_args_of_node" pr dummy_pr
    get_args_of_node l_node


let get_args_of_hrel l_node =
  match l_node with
  | HRel (rhp, eargs, _) -> (List.fold_left List.append [] (List.map CP.afv eargs))
  | _ -> []

let find_node emap hf sv =
  let f_h_f _ hf =
    match hf with
    | DataNode ({ h_formula_data_node = pt; h_formula_data_name = n; h_formula_data_arguments = args;})
    | ViewNode ({ h_formula_view_node = pt; h_formula_view_name = n; h_formula_view_arguments = args;}) ->
      (* TODO : use emap *)
      if CP.eq_spec_var sv pt then Some (hf,[(n,sv,args)])
      else Some (hf,[])
    | _ -> None
  in
  snd (trans_h_formula hf () f_h_f voidf2 (List.concat))

let extr_pred_list f =
  let (hf,_,_,_,_,_) = split_components f in
  let f_h_f _ hf =
    match hf with
    | ViewNode ({ h_formula_view_name = n}) ->
      Some (hf,[n])
    | _ -> None
  in
  snd (trans_h_formula hf () f_h_f voidf2 (List.concat))

(* let find_node emap rhs_h sv = [] *)

let is_comp (l_n,_,l_arg) (r_n,_,r_arg) pure =
  (* DONE : check for satisfiability *)
  if l_n=r_n then
    let lst = List.combine l_arg r_arg in
    let new_pure = List.fold_left (fun z (v1,v2) -> CP.mkAnd z (CP.mkEqn v1 v2 no_pos) no_pos) pure lst in
    let res = !MCP.is_sat_raw (MCP.mix_of_pure new_pure) in
    let () = y_ninfo_hp (add_str "is_comp" string_of_bool) res in
    res (* true *)
  else false

let cross_prod xs ys = List.concat (List.map (fun y -> List.map (fun x -> (x,y)) xs) ys)

let check_compatible ?(inst_rhs=false) emap l_vs r_vs lhs_h lhs_p rhs_h rhs_p =
  let rec collect_unique xs ans =
    match xs with
    | [] -> List.rev ans
    | ((l,r) as p)::xs ->
      if List.exists (fun (v1,v2) -> (CP.eq_spec_var v1 l) || (CP.eq_spec_var v2 r)) ans then collect_unique xs ans
      else collect_unique xs (p::ans) in
  (* let (lhs_h,lhs_p,_,_,_,_) = split_components lhs in *)
  (* let (rhs_h,rhs_p,_,_,_,_) = split_components rhs in *)
  let free_vars = if inst_rhs then (h_fv lhs_h)@(CP.fv lhs_p)@l_vs else [] in
  let r_vs = CP.diff_svl r_vs free_vars in
  let rhs_lst = List.concat (List.map (find_node emap rhs_h) r_vs) in
  (* aliased nodes of r_vs;rhs_eqset? *)
  let lhs_lst = List.concat (List.map (find_node emap lhs_h) l_vs) in
  (* aliased nodes of l_vs;rhs_eqset? *)
  let cross_lst = cross_prod lhs_lst rhs_lst in
  let pure_both = CP.mkAnd lhs_p rhs_p no_pos in
  (* keep only compatible ones *)
  let sel_lst = List.filter (fun (l,r) -> is_comp l r pure_both) cross_lst in
  let sel_lst = List.map (fun ((a,p1,_),(b,p2,_)) -> (p1,p2)) sel_lst in
  (* collect unique instantiation *)
  (* how about instantiation from RHS eq and LHS eq *)
  collect_unique sel_lst []
  (* failwith "TBI" *)

let check_compatible ?(inst_rhs=false) emap l_vs r_vs lhs_h lhs_p rhs_h rhs_p =
  let pr1 = !CP.print_svl in
  let pr2 = !print_h_formula in
  let pr3 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
  Debug.no_4 "check_compatible" (add_str "l_vs" pr1) (add_str "r_vs" pr1)
    (add_str "lhs" pr2) (add_str "rhs" pr2) pr3
    (fun _ _ _ _ -> check_compatible ~inst_rhs:inst_rhs emap l_vs r_vs lhs_h lhs_p rhs_h rhs_p) l_vs r_vs lhs_h rhs_h

let check_compatible_eb ?(inst_rhs=false) emap l_vs r_vs lhs_b (* lhs_p *) rhs_b (* rhs_p *) =
  (* let eqns' = MCP.ptr_equations_without_null lhs_p in *)
  (* let emap = CP.EMapSV.build_eset eqns' in *)
  let lhs_h = lhs_b.formula_base_heap in
  let rhs_h = rhs_b.formula_base_heap in
  let lhs_pure = (MCP.pure_of_mix lhs_b.formula_base_pure) in
  let rhs_pure = (MCP.pure_of_mix rhs_b.formula_base_pure) in
  check_compatible ~inst_rhs:inst_rhs emap l_vs r_vs lhs_h lhs_pure rhs_h rhs_pure

let check_exists_node emap hf sv =
  let r = find_node emap hf sv in
  r!=[]

let fresh_data_arg body_dn =
  let args = body_dn.h_formula_data_arguments in
  let () = y_tinfo_hp (add_str "data args" !CP.print_svl) args in
  { body_dn with  h_formula_data_arguments = List.map CP.fresh_spec_var args }

let extr_exists_hprel ra =
  let lhs = ra.hprel_lhs in
  let guard = ra.hprel_guard in
  let kind = ra.hprel_kind in
  (* let () = y_tinfo_hp (add_str "lhs" !print_formula) lhs in *)
  (* let () = y_tinfo_hp (add_str "guard" (pr_option !print_formula)) guard in *)
  let (lhs_vs,lhs_h_vs) = (fv lhs,fv_heap_of lhs) in
  let (guard_vs,guard_h_vs) = match guard with
    None -> ([],[])
    | Some f -> (fv f,fv_heap_of f) in
  (* let () = y_tinfo_hp (add_str "lhs_vs" !CP.print_svl) lhs_vs in *)
  (* let () = y_tinfo_hp (add_str "guard_vs" !CP.print_svl) guard_vs in *)
  let ex_lhs_vars = CP.diff_svl lhs_vs lhs_h_vs in
  let ex_guard_vars = CP.diff_svl guard_vs (lhs_h_vs@guard_h_vs) in
  (* let () = y_tinfo_hp (add_str "guard" (string_of_rel_cat)) kind in *)
  (ex_lhs_vars,ex_guard_vars)

(* let add_unfold_flag lst =  *)
(*   List.map (fun w -> {w with hprel_fold = false}) lst *)

(* let add_fold_flag lst =  *)
(*   List.map (fun w -> {w with hprel_fold = true}) lst *)

(*
   U(..) # .. --> ..   // unfold
   ....  --> U(..)     // fold
*)

let check_unfold_aux ra =
  let lhs = ra.hprel_lhs in
  let rhs = ra.hprel_rhs in
  (* let (h_l,p_l,_,_,_,_) = split_components lhs in *)
  (* let (h_r,p_r,_,_,_,_) = split_components rhs in *)
  let ans_r =
    match rhs with
    | Or _ -> []
    | _ ->
      let (h_r, p_r, _, _, _, _) = split_components rhs in
      (match h_r with
      | HRel (hp, _, _) ->
        if CP.is_True (MCP.pure_of_mix p_r) then [(false, hp)] (* fold rule *)
        else []
      | _ -> [])
  in
  let ans_l =
    match lhs with
    | Or _ -> []
    | _ ->
      let (h_l, _, _, _, _, _) = split_components lhs in
      (match h_l with
      | HRel (hp, _, _) -> [(true, hp)]
      | _ -> [])
  in ans_r@ans_l

(* let check_unfold_aux ra =                                                 *)
(*   let lhs = ra.hprel_lhs in                                               *)
(*   let rhs = ra.hprel_rhs in                                               *)
(*   let (h_l,p_l,_,_,_,_) = split_components lhs in                         *)
(*   let (h_r,p_r,_,_,_,_) = split_components rhs in                         *)
(*   let ans_r = match h_r with                                              *)
(*   | HRel (hp,_,_) ->                                                      *)
(*     if CP.is_True (MCP.pure_of_mix p_r) then [(false,hp)] (* fold rule *) *)
(*     else []                                                               *)
(*   | _ -> [] in                                                            *)
(*   let ans_l = match h_l with                                              *)
(*   | HRel (hp,_,_) -> [(true,hp)]                                          *)
(*   | _ -> [] in                                                            *)
(*   ans_r@ans_l                                                             *)

let check_unfold ra =
  match check_unfold_aux ra with
  | [] -> (None,[])
  | (b,hp)::_ -> (Some b,[hp])

let modify_hprel (r,(b,hp)) =
  let ut = if b then INFER_UNFOLD else INFER_FOLD in
  { r with hprel_type = ut; hprel_unknown = [hp] }

(* let string_of_hprel_def_short hp = poly_string_of_pr pr_hprel_def_short hp *)

let string_of_infer_type a = match a with
  | INFER_UNKNOWN -> "unknown"
  | INFER_UNFOLD -> "unfold"
  | INFER_FOLD -> "fold"

let add_infer_type_to_hprel ras =
  if not(List.exists (fun r -> r.hprel_type ==INFER_UNKNOWN) ras) then ras
  else
    let pr = pr_list (fun (r,_,_) -> pr_none r) in
    let pr2 = pr_list (fun (r,_,n) -> string_of_int n) in
    let pr_p = pr_pair string_of_infer_type !CP.print_svl in
    let pr3 = pr_list (fun r -> pr_p (r.hprel_type,r.hprel_unknown)) in
    let lst = List.map (fun r -> let a = check_unfold_aux r in (r,a,List.length a)) ras in
    let () = y_tinfo_hp (add_str "add_infer_type" pr2) lst in
    let (emp,lst) = List.partition (fun (_,_,n) -> n==0) lst in
    let (ones,lst) = List.partition (fun (_,_,n) -> n==1) lst in
    let ones_ans = List.map (fun (r,a,_) -> (r,List.hd a)) ones in
    if emp!=[] then y_winfo_hp (add_str "UNCLASSIFIED REL_ASS" pr) emp;
    (* choose a case which occurred before in ones *)
    (* let rec choose ans r = match ans with *)
    (*                        | [] -> r *)
    (*                        | x::xs ->  *)
    (*                          if List.exists (fun (_,t2) -> r=t2) ones_ans then r *)
    (*                          else choose xs x in *)
    let compatible (b1,hp1) = not(List.exists (fun (_,(b2,hp2)) -> hp1=hp2 && not(b1=b2)) ones_ans) in
    (* choose a compatible case *)
    let choose xs =
      let rs = List.filter compatible xs in
      match rs with
      | [] -> List.hd xs (* choose an incompatible *)
      | x::xs -> x in
    let rs2 = List.map (fun (r,a,_) -> modify_hprel (r,(choose a))) lst in
    let emp = List.map (fun (r,_,_) -> r) emp in
    let ones_ans = List.map modify_hprel ones_ans in
    let res = emp@ones_ans@rs2 in
    let () = y_tinfo_hp (add_str "add_infer_type(input)" pr3) ras in
    let () = y_tinfo_hp (add_str "add_infer_type(output)" pr3) res in
    res

let add_infer_type_to_hprel ras =
  let pr = !print_hprel_list_short in
  Debug.no_1 "add_infer_type_to_hprel" pr pr add_infer_type_to_hprel ras

let check_hprel ra =
  let (ex_lhs_vs,ex_guard_vs)= extr_exists_hprel ra in
  let opt = check_unfold ra in
  (* let () = y_tinfo_hp (add_str "XXX:unfold?" (pr_pair (pr_option string_of_bool) !CP.print_svl)) opt in *)
  (* let () = if ex_lhs_vs!=[] then y_winfo_hp (add_str "XXX ex_lhs_vars to eliminate" !CP.print_svl) ex_lhs_vs in *)
  (* let () = if ex_guard_vs!=[] then y_winfo_hp (add_str "XXX ex_guard_vars to eliminate" !CP.print_svl) ex_guard_vs in *)
  ra

let sleek_hprel_assumes =
  object (self)
    val mutable lst = []
    method get = lst
    method set nlst = lst <- nlst
    method add (e:hprel) = lst <- e::lst
  end

(* let sleek_hprel_assumes = ref ([]: CF.hprel list) *)


(* let rev_trans : (Iformula.formula -> formula) ref = ref (fun x -> failwith "TBI") *)

let rev_trans_formula = ref (fun (f:formula) -> Iformula.mkTrue n_flow no_pos )

let rev_trans_formula = ref (fun (f:formula) -> Iformula.mkTrue n_flow no_pos )

(* type: HipUtil.NG.V.label -> h_formula_view -> *)
(*   CP.spec_var list -> formula -> h_formula * CP.spec_var list * Cpure.formula *)
let get_view_unfold_g vd_name vl to_args f =
    let args = vl.h_formula_view_arguments in
    let vv = vl.h_formula_view_name in
    let () = y_tinfo_hp (add_str "unfolding vv" pr_id) vv in
    let () = y_tinfo_hp (add_str "inside" pr_id) vd_name in
    (* let new_args = trans_args sst args in *)
    let sst = List.combine (CP.self_sv::to_args) (vl.h_formula_view_node::args) in
    (* let new_f = x_add subst_all sst f in *)
    let new_f = subst_avoid_capture (CP.self_sv::to_args) (vl.h_formula_view_node::args) f in
    let () = y_tinfo_hp pr_id (HipUtil.view_scc_obj # string_of) in
    let grh = HipUtil.view_scc_obj # unfold_in vv vd_name in
    let () = y_tinfo_hp (add_str "subs" (pr_list (pr_pair !CP.print_sv !CP.print_sv))) sst in
    let (qv,(hf,pure_f,_,_,_,_)) = split_components_exist ~rename_flag:true new_f in
    let pure_f = MCP.pure_of_mix pure_f in
    let () = y_tinfo_hp (add_str "f" !print_formula) f in
    let () = y_tinfo_hp (add_str "new_f" !print_formula) new_f in
    let () = y_tinfo_hp (add_str "hf" !print_h_formula) hf in
    let () = y_tinfo_hp (add_str "pure" !CP.print_formula) pure_f in
    (hf,qv,pure_f)

let get_view_unfold vd_name stk vl to_args f =
  let (hf,qv,pure_f) = get_view_unfold_g vd_name vl to_args f in
  let () = stk # push (qv,pure_f) in
  hf

let add_qv_pure stk res =
  let lst = stk # get_stk in
  (* let () = if not(stk # is_empty)  *)
  (*   then y_winfo_hp (add_str "TODO:add pure & qvars" pr_id) (stk # string_of) in *)
  let res = if lst==[] then res
    else let (qv,pure) = List.fold_left (fun (qv1,p1) (qv2,p2) -> (qv1@qv2,CP.mkAnd p1 p2 no_pos)) ([],CP.mkTrue no_pos) lst in
      (* let () = y_winfo_hp (add_str "TODO:add pure & qvars" pr) (qv,pure) in *)
      let res = add_pure_formula_to_formula pure res in
      let res = push_exists qv res in
      res
  in res

let repl_unfold_heap vd stk u_lst hf =
  let find n =
    try
      Some (List.find (fun (m,_,_) -> string_eq n m) u_lst)
    with _ -> None in
  let f hf = match hf with
    | HTrue | HFalse | HEmp | DataNode _ | Hole _ | HRel _ | HVar _ -> Some hf
    | ViewNode vl ->
      let name = vl.h_formula_view_name in
      begin
      match find name with
      | Some (m,to_args,f) ->
        (* WN : take care of pure by mutable *)
        (* let () = y_tinfo_hp (add_str "Unfolding " (pr_pair pr_id !print_formula)) (name,f) in *)
        let n_hf = get_view_unfold vd stk vl to_args f in
        let pr_hf = !print_h_formula in
        let () = y_tinfo_hp (add_str "Unfolding -> " (pr_pair pr_hf pr_hf)) (hf,n_hf) in
        let () = y_tinfo_hp (add_str "(exist vars,pure)  " (fun s -> s # string_of)) stk in
        Some (n_hf)
        (* failwith (x_loc^"TBI") *)
      | _ -> Some hf
      end
    | _ -> None
  in map_h_formula hf f

(* type: HipUtil.NG.V.label -> *)
(*   (String.t * CP.spec_var list * formula) list -> formula -> formula *)
let repl_unfold_formula vd u_lst f =
  let pr = pr_pair !CP.print_svl !CP.print_formula in
  let stk = new stack_pr "" pr (==) in
  let res = map_formula_heap_only (repl_unfold_heap vd stk u_lst) f in
  add_qv_pure stk res

let repl_unfold_formula vd u_lst f =
  let pr1 = !print_formula in
  let pr2 = pr_triple pr_id !CP.print_svl pr1 in
  Debug.no_3 "repl_unfold_formula" pr_id (pr_list_ln pr2) pr1 pr1
    repl_unfold_formula vd u_lst f

let convert_un_struc_to_formula body =
  match body with
  | [] -> failwith (x_loc^"should not be empty")
  | (f,l)::lst ->
    let f = add_label f l in
    List.fold_left (fun acc (nf,l) -> mkOr acc (add_label nf l) no_pos) f lst

let add_label_to_struc_formula s_f old_sf =
  let () = y_tinfo_hp (add_str "sf" !print_struc_formula) s_f in
  let () = y_tinfo_hp (add_str "old sf" !print_struc_formula) old_sf in
  match s_f,old_sf with
  | EList lst,EList lst2 ->
    begin
      try
        let  nlst = List.combine lst lst2 in
        EList (List.map (fun ((_,f),(l,old_f)) ->
            let lbl = get_label_struc old_f in
            (l,(add_label_opt_struc f lbl))) nlst)
      with _ ->
        let () = y_winfo_pp "struc mismatch with label list" in
        s_f
    end
  | _ -> s_f

let eq_hprel_defn f1 f2 =
  (f1.hprel_lhs = f2.hprel_lhs) && (f1.hprel_rhs = f2.hprel_rhs)  && (f1.hprel_guard = f2.hprel_guard)

(* let trans_heap_formula_new fh (f: formula) =  *)
(*   let f_h_f _ hf = fh hf in  *)
(*   let somef2 _ f = Some (f, []) in *)
(*   let id2 f _ = (f, []) in *)
(*   let ida _ f = (f, []) in *)
(*   let f_arg = (voidf2, voidf2, voidf2, (voidf2, voidf2, voidf2), voidf2) in *)
(*   trans_formula f ()  *)
(*     (nonef2, nonef2, f_h_f, (somef2, somef2, somef2), (somef2, id2, ida, id2, id2))  *)
(*     f_arg List.concat *)

let trans_heap_formula f_h_f (f: formula) =
  let somef2 _ f = Some (f, []) in
  let id2 f _ = (f, []) in
  let ida _ f = (f, []) in
  let f_arg = (voidf2, voidf2, voidf2, (voidf2, voidf2, voidf2), voidf2) in
  trans_formula f ()
    (nonef2, nonef2, f_h_f, (somef2, somef2, somef2), (somef2, id2, ida, id2, id2))
    f_arg List.concat

let trans_heap_formula_new fh (f: formula) =
  let f_h_f _ hf = fh hf in
  trans_heap_formula f_h_f f

let aux_rename_view_h_formula sst hf =
  match hf with
  | ViewNode v ->
    let vn = v.h_formula_view_name in
    (try
      let new_vn = List.assoc vn sst in
      Some (ViewNode { v with h_formula_view_name = new_vn; })
    with _ -> Some hf)
  | _ -> None

let rename_view_formula sst f =
  let f_h_f = (fun hf ->
    match (aux_rename_view_h_formula sst hf) with
    | Some nhf -> Some (nhf, [])
    | None -> None) in
  fst (trans_heap_formula_new f_h_f f)

(* let new_f = build_ctx_with_emp orig_f hf in *)
let build_context_with_emp f hf_ptr =
  let f_h_f = (fun hf ->  if hf==hf_ptr then Some(HEmp,[])
                else Some(hf,[])) in
  fst (trans_heap_formula_new f_h_f f)

let rename_view_struc sst f =
  let f_h_f = (fun hf -> aux_rename_view_h_formula sst hf) in
  let f_f = nonef, nonef, f_h_f, (somef, somef, somef, somef, somef) in
  transform_struc_formula f_f f

let is_sat_raw = Mcpure.is_sat_raw

let is_xpure_unsat = ref (fun (f:formula) -> ((failwith x_loc):bool))

let complex_unfold vn (unfold_set1:(Globals.ident * (CP.spec_var list) * (formula list)) list) orig_f =
  let pure_of_f = get_pure orig_f in
  let () = y_tinfo_hp (add_str "complex_unfold(f)" !print_formula) orig_f in
  let () = y_tinfo_hp (add_str "pure formula of inp2" !CP.print_formula) pure_of_f in

  (* try to replace views if the corresponding list of formulae in unfold_set1
   * has only 1 satisfiable formula *)
  let pr = pr_pair !CP.print_svl !CP.print_formula in
  let stk = new stack_pr "" pr (==) in
  let f_h_f _ hf =
    match hf with
    | ViewNode ({ h_formula_view_node = vsv; h_formula_view_name = vname; } as v)
    (* can only unfold on self *)
    (* when string_eq "self" (CP.name_of_spec_var vsv) *) ->
      begin
        let new_f = build_context_with_emp orig_f hf in
        let vl = v in
        let args = vl.h_formula_view_arguments in
        let vv = vl.h_formula_view_name in
        let () = y_tinfo_hp (add_str "transform .. view node" !CP.print_sv) vsv in
        let () = y_tinfo_hp (add_str "transform .. view name" pr_id) vname in
        (* formulae for view name *)
        try
          let (_,to_args,fl) = List.find (fun (id,_,_) -> string_eq id vname) unfold_set1 in
          let sat_fl = List.filter (fun unf_f ->
              (* let f = unf_f in *)
              let sst = List.combine (CP.self_sv::to_args) (vl.h_formula_view_node::args) in
              let unf_f = x_add subst_all sst unf_f in
              (* let unf_pure_f = get_pure unf_f in *)
              let () = y_tinfo_hp (add_str "complex_unfold(unf_f)" !print_formula) unf_f in
              (* let conj = (CP.mkAnd pure_of_f unf_pure_f no_pos) in *)
              let cf_star = (mkStar_combine new_f unf_f Flow_combine no_pos) in
              (* let flag1 = !is_sat_raw (MCP.mix_of_pure conj) in *)
              let flag = (!is_xpure_unsat cf_star) in
              (* let diff_flag = not(flag=flag1) in *)
              (* let msg = if diff_flag then " DIFFERENT" else "" in *)
              let pr_b = string_of_bool in
              (* let () = if diff_flag then y_tinfo_hp !CP.print_formula unf_pure_f in *)
              let () = y_tinfo_hp (add_str ("check sat"(* ^msg *)) (pr_pair !print_formula pr_b)) (cf_star,flag) in
              not(flag)) fl in
          let () = y_tinfo_hp (add_str "transform .. sat fl" (pr_list !print_formula)) sat_fl in
          (match sat_fl with
           (* if we match with none, we *could* replace with false *)
           | [] -> None
           (* if we have only one satisfiable formula, use that here *)
           | [replace_f] ->
             (* todo: if we need to replace with h_formula, but have
              * replace_f : formula, so how?? *)
             let hf = get_view_unfold vn stk vl to_args replace_f in
             Some(hf,[])
             (* None *)
           | _ -> None)
        with
          Not_found -> None
      end
    | _ -> None
  in
  let somef2 _ f = Some (f, []) in
  let id2 f _ = (f, []) in
  let ida _ f = (f, []) in
  let f_trans = (nonef2, nonef2, f_h_f, (somef2, somef2, somef2), (somef2, id2, ida, id2, id2)) in
  let f_arg = voidf2, voidf2, voidf2, (voidf2, voidf2, voidf2), voidf2 in
  let (nf, _) = trans_formula orig_f () f_trans f_arg List.concat in
  add_qv_pure stk nf

(* type: HipUtil.NG.V.label -> h_formula_view -> *)
(*   CP.spec_var list -> formula -> h_formula * CP.spec_var list * Cpure.formula *)
(* let get_view_unfold_g vd_name vl to_args f = *)

let complex_unfold vn (unfold_set1:(Globals.ident * (CP.spec_var list) * (formula list)) list) f =
  let pr_f = !print_formula in
  let pr1 = pr_list (pr_triple pr_id (pr_list !print_spec_var) (pr_list pr_f)) in
  Debug.no_2 "complex_unfold" pr1 pr_f pr_f (complex_unfold vn) unfold_set1 f

let rec is_struc_false_post sf =
  let recf = is_struc_false_post in
  match sf with
  | ECase b-> List.exists (fun (_, sf1) -> recf sf1) b.formula_case_branches
  | EBase b -> begin
      match b.formula_struc_continuation with
        | Some sf1 -> recf sf1
        | None -> false
    end
  | EAssume b -> isAllConstFalse b.formula_assume_simpl
  | EInfer b-> recf b.formula_inf_continuation
  | EList l-> List.exists (fun (_, sf1) -> recf sf1) l

(* this check if this should be the last component prior to EAssume *)
(* if so, we will allow residue in proving process *)
let rec is_pre_post_cont f =
  match f with
  | None -> false
  | Some e -> (match e with
    | EAssume b ->
      if isAllConstFalse b.formula_assume_simpl then false
      else true
    | EBase b ->
      let f = b.formula_struc_base in
      let (h, p, _, _, _, _) = split_components f in
      if h == HEmp then is_pre_post_cont b.formula_struc_continuation
      else true
    | _ -> true
      )

let is_pre_post_cont f =
  let pr = pr_option !print_struc_formula in
  Debug.no_1 "is_pre_post_cont" pr string_of_bool is_pre_post_cont f

let mk_bind_ptr x =
  let p = CP.Gt(mkVar x no_pos,(CP.mkIConst 1 no_pos),no_pos) in
  let f = CP.mk_bform p in
  f

let rec mk_bind_ptr_f x =
  let pure = mk_bind_ptr x in
  let ef = mkTrue (mkTrueFlow ()) no_pos in
  mkAnd_pure ef (MCP.mix_of_pure pure) no_pos

let rec mk_bind_ptr_struc x =
  let pure = mk_bind_ptr x in
  let ef = mkETrue (mkTrueFlow ()) no_pos in
  mkAnd_pure_pre_struc_formula pure ef

let mk_bind_fields_struc fields =
  let ptrs = List.filter (CP.is_node_typ) fields in
  let ps = List.map mk_bind_ptr ptrs in
  let pure = CP.conj_of_list ps no_pos in
  pure

let get_data_and_views f =
  let stk = new Gen.stack in
  let f_h_f hf =
    match hf with
    | ViewNode ({ h_formula_view_node = vsv; h_formula_view_name = vname; } as v) ->
      let () = stk # push (vsv,(1,hf)) in Some hf
    | DataNode ({ h_formula_data_node = vsv; h_formula_data_name = vname; } as v) ->
      let () = stk # push (vsv,(0,hf)) in Some hf
    | _ -> None in
  let _ = (map_h_formula f f_h_f) in
  let r = stk # get_stk in
  let pr = pr_pair !CP.print_sv (pr_pair string_of_int !print_h_formula) in
  let () = y_tinfo_hp (add_str "get_data_and_views" (pr_list pr)) r in
  r

let no_infer_vars estate = (estate.es_infer_vars == [])

let no_infer_rel estate = (estate.es_infer_vars_rel == [])

let no_infer_templ estate = (estate.es_infer_vars_templ == [])
let no_infer_hp_rel estate = (estate.es_infer_vars_hp_rel == []) || is_error_flow estate.es_formula


(* let no_infer_all estate = (estate.es_infer_vars == [] && estate.es_infer_vars_rel == []) *)

let no_infer_pure estate = (estate.es_infer_vars == []) && (estate.es_infer_vars_rel == [])

let no_infer_all_all estate = no_infer_pure estate && (no_infer_hp_rel estate) && no_infer_templ estate

let extract_nodes stk hf =
  match hf with
  | ViewNode v ->
    let vn = v.h_formula_view_name in
    let ptr = v.h_formula_view_node in
    let args = v.h_formula_view_arguments in
    let () = stk # push (1,vn,ptr,args) in
    Some hf
  | DataNode v ->
    let vn = v.h_formula_data_name in
    let ptr = v.h_formula_data_node in
    let args = v.h_formula_data_arguments in
    let () = stk # push (2,vn,ptr,args) in
    Some hf
  | HRel (n,lst,_) ->
    let vn = CP.name_of_spec_var n in
    let args = List.map (fun e -> match e with Var(v,_) -> v | _ -> failwith "not a Var") lst in
    let (ptr,args) = match args with
      | [] -> failwith "HRel without self?"
      | x::y -> (x,y)
    in
    let () = stk # push (3,vn,ptr,args) in
    Some hf
  | _ -> None

let extract_gen_nodes hf =
  (* 1 - view; 2 -data; 3 - HRel *)
  let stk = new Gen.stack in
  let _ = extract_nodes stk hf in
  let lst = (* List.map (fun (no,_,ptr,_) -> (no,ptr)) *) (stk # get_stk) in
  let (data_lst,other_lst) = List.partition (fun (no,_,_,_) -> no=2) lst in
  let (view_lst,hrel_lst) = List.partition (fun (no,_,_,_) -> no=1) lst in
  (data_lst,view_lst,hrel_lst)

let extract_gen_nodes_ptr hf =
  (* 1 - view; 2 -data; 3 - HRel *)
  let (data_lst,view_lst,hrel_lst) = extract_gen_nodes hf in
  let map_ptr = List.map (fun (_,_,ptr,_)->ptr) in
  (map_ptr data_lst,map_ptr view_lst,map_ptr hrel_lst)

let extract_view_nodes_name hf =
  let (_,vl,_) = extract_gen_nodes hf in
  List.map (fun (_,v,_,_) -> v) vl

(*   self::P<..p>
           == self=p
           or self::node<_,p>
           or self::node<_,q>*q::P<..,p>
*)
let is_segmented vn self_typ (args:CP.spec_var list) (body:formula list) =
  let ty = self_typ in
  let args = List.filter (fun x -> CP.type_of_spec_var x = ty) args in
  let () = y_dinfo_hp (add_str "args" !CP.print_svl) args in
  match args with
  | [x] -> Some x
  | _ -> None

let rec split_or f =
  match f with
  | Or e -> (split_or e.formula_or_f2)@(split_or e.formula_or_f1)
  | _ -> [f]

let mk_or f1 f2 =
  Or {formula_or_f1=f1; formula_or_f2=f2; formula_or_pos=no_pos; }

let join_or f_lst =
  match f_lst with
  | [] -> failwith x_tbi
  | x::lst -> List.fold_left (fun acc x -> mk_or x acc) x lst

let get_root_ptr hf =
  match hf with
  | DataNode {h_formula_data_node = pt}
  | ViewNode { h_formula_view_node = pt}
  | ThreadNode { h_formula_thread_node = pt}
  | HVar(pt,_) -> pt
  | _ -> raise Not_found

let combine_star_pure f1 p =
  let f2 = formula_of_pure_formula p no_pos in
  let f = normalize_combine_star f1 f2 no_pos in
  f

let add_pure_estate es cp =
  let flag = true (* es.es_infer_acc # add_pure cp *) in
  if flag then
    {es with es_formula = combine_star_pure es.es_formula cp;
    }
  else failwith (x_loc^"add_infer_pure_thus_estate")

let same_node_name c rhs_node =
  try
    (get_node_name_x rhs_node)=c
  with _ -> false

let is_non_emp f =
  let flag = ref false in
  let f_h_f hf =
    match hf with
     | DataNode _ -> let () = flag := true in Some hf
     | _ -> None in
  let _ = (map_h_formula f f_h_f) in
  !flag

let struc_formula_of_formula f pos =
  let pr_f = !print_formula in
  let pr_sf = !print_struc_formula in
  Debug.no_1 "struc_formula_of_formula" pr_f pr_sf (fun _ -> struc_formula_of_formula f pos) f

let normalize_struc nb b =
  let pr_f = !print_formula in
  let pr_sf = !print_struc_formula in
  Debug.no_2 "normalize_struc" pr_sf pr_none pr_sf normalize_struc nb b
