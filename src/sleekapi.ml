module C = Cast
module I = Iast
module VG = VarGen
module SC = Sleekcommons
module SE = Sleekengine
module IF = Iformula
module IP = Ipure_D
module NF = Nativefront

type pe = IP.exp
type pf = IP.formula
type hf = IF.h_formula
type mf = SC.meta_formula
type dd = I.data_decl

type typ =
  | Void
  | Bool
  | Float
  | Int
  | Named of string

(* 
   dummy cprog so that solver have access to view and data decls.
   This will mainly be used for using solver through hip functions like check_post.
   It will probably be empty for now. maybe will populate with views (predicates) and data etc in the future
 *)
let cprog : C.prog_decl ref = ref {
    C.prog_data_decls = [];
    C.prog_view_decls = [];
    C.prog_logical_vars = [];
    C.prog_rel_decls =
      (let s = new Gen.stack_pr "prog_rel_decls(CAST)"
         (fun x -> "not yet initialized" ) (=) in s);
    C.prog_templ_decls = [];
    C.prog_ui_decls = [];
    C.prog_ut_decls = [];
    C.prog_hp_decls = [];
    C.prog_view_equiv = [];
    C.prog_axiom_decls = [];
    C.new_proc_decls = Hashtbl.create 1;
    C.prog_barrier_decls = []
}

(* Prelude of api *)
let init () = 
  let () = print_string "Initializing sleek api" in
  (* Prelude file contains some data declarations like int_ptr to support the api
     Declarations in this prelude file will be parsed and stored in a global
     variable, iprog, in sleekengine.ml
  *)
  let slk_prelude_path = (Gen.get_path Sys.executable_name)^"sleekapi_prelude.slk" in
  let () = Sleek.parse_file Nativefront.list_parse slk_prelude_path in
  ()

(* Used as placeholder for pos since no file is parsed *)
let no_pos : VG.loc =
  let no_pos1 = { Lexing.pos_fname = "";
                  Lexing.pos_lnum = 0;
                  Lexing.pos_bol = 0; 
                  Lexing.pos_cnum = 0 } in
  {VG.start_pos = no_pos1; VG.mid_pos = no_pos1; VG.end_pos = no_pos1;}

(* Building pure expressions *)
let null_pure_exp = IP.Null no_pos
let var_pure_exp (ident : string) (primed : bool) = 
  match primed with
  | true ->  IP.Var ((ident, VG.Primed), no_pos) 
  | false -> IP.Var ((ident, VG.Unprimed), no_pos)
let int_pure_exp   int   = IP.IConst (int, no_pos)
let float_pure_exp float = IP.FConst (float, no_pos)

let add_pure_exp lhs rhs = IP.Add (lhs, rhs, no_pos)
let sub_pure_exp lhs rhs = IP.Subtract (lhs, rhs, no_pos)
let mul_pure_exp lhs rhs = IP.Mult (lhs, rhs, no_pos)
let div_pure_exp lhs rhs = IP.Div (lhs, rhs, no_pos)

(* Building pure formula *)
let bool_pure_f bool = IP.BForm ((IP.BConst (bool, no_pos), None), None)
let false_f          = bool_pure_f false
let true_f           = bool_pure_f true

(* terms *)
let gt_pure_f  lhs rhs = IP.BForm ((IP.Gt (lhs, rhs, no_pos), None), None)
let gte_pure_f lhs rhs = IP.BForm ((IP.Gte (lhs, rhs, no_pos), None), None)
let lt_pure_f  lhs rhs = IP.BForm ((IP.Lt (lhs, rhs, no_pos), None), None)
let lte_pure_f lhs rhs = IP.BForm ((IP.Lte (lhs, rhs, no_pos), None), None)
let eq_pure_f  lhs rhs = IP.BForm ((IP.Eq (lhs, rhs, no_pos), None), None)

(* connectives *)
let not_f           f = IP.Not (f, None, no_pos)
let and_f     lhs rhs = IP.And (lhs, rhs, no_pos)
let or_f      lhs rhs = IP.Or (lhs, rhs, None, no_pos)
let implies_f lhs rhs = or_f (not_f lhs) rhs
let iff_f     lhs rhs = and_f (implies_f lhs rhs) (implies_f rhs lhs)

(* Building heap formula *)
let empty_heap_f = IF.HEmp

let data_decl data_name data_fields =
  let df = List.map (function (Void, ident) -> (((Void, ident) : Globals.typed_ident), no_pos, false, [])
                            | (Bool, ident) -> ((Bool, ident), no_pos, false, [])
                            | (Float, ident) -> ((Float, ident), no_pos, false, [])
                            | (Int, ident) -> ((Int, ident), no_pos, false, [])
                            | (Named(name), ident) -> ((Named(name), ident), no_pos, false, [])) data_fields in
  (* Stores data definition into SE.iprog *)
  let () = SE.process_data_def {
    I.data_name = data_name;
    I.data_fields = df;
    I.data_parent_name = "Object";
    I.data_invs = [];
    I.data_pos = no_pos;
    I.data_pure_inv = None;
    I.data_is_template = false;
    I.data_methods = [];
  } in
  let () = I.annotate_field_pure_ext SE.iprog in (* Can be improved to not re-annotatepreviously annotated data decls in SE.iprog *)
  let c_data_decl = Astsimp.trans_data_x SE.iprog (List.hd SE.iprog.I.prog_data_decls) in
  let () = !SE.cprog.Cast.prog_data_decls <- c_data_decl :: !SE.cprog.Cast.prog_data_decls in
  let () = Cf_ext.add_data_tags_to_obj !SE.cprog.Cast.prog_data_decls in (* To mark recursive data declarations *)
  (* print_string ("\n Cprog after data_decl : " ^ (Cprinter.string_of_program !SE.cprog)) *)
  ()

let predicate_decl sleek_str =
  let sleek_cmd = NF.parse_slk sleek_str in
  match sleek_cmd with
  | SC.PredDef pred_def ->
    (* Stores predicate definition into SE.iprog *)
    let () = SE.process_pred_def_4_iast pred_def in
    SE.convert_data_and_pred_to_cast_x ()
  | _ -> ()

let points_to_int_f var_name primed int =
  let p = match primed with
      | true -> VG.Primed
      | false -> VG.Unprimed in
  IF.mkHeapNode_x (var_name, p) "int_ptr" []  0 false Globals.SPLIT0 IP.NoAnn false false
    false None [(int_pure_exp int)] [None] None no_pos

let points_to_f var_name primed node_name (exps : IP.exp list) = 
  let p = match primed with
      | true -> VG.Primed
      | false -> VG.Unprimed in
  let imm_param = List.map (fun _ -> None) exps in
  IF.mkHeapNode_x (var_name, p) node_name [] 0 false Globals.SPLIT0 IP.NoAnn false false false
    None exps imm_param None no_pos
  
(* Functions to build meta_formulae *)

let ante_f heap_f pure_f  =
  let formula_base = {
    IF.formula_base_heap = heap_f;
    IF.formula_base_pure = pure_f;
    IF.formula_base_vperm = IvpermUtils.empty_vperm_sets;
    IF.formula_base_flow = "__norm";
    IF.formula_base_and = [];
    IF.formula_base_pos = no_pos
  } in
  [SC.MetaForm(IF.Base(formula_base))]

let conseq_f heap_f pure_f =
  let formula_base = {
    IF.formula_base_heap = heap_f;
    IF.formula_base_pure = pure_f;
    IF.formula_base_vperm = IvpermUtils.empty_vperm_sets;
    IF.formula_base_flow = "__norm";
    IF.formula_base_and = [];
    IF.formula_base_pos = no_pos
  } in
  let struc_base_formula = {
    IF.formula_struc_explicit_inst = [];
    IF.formula_struc_implicit_inst = [];
    IF.formula_struc_exists = [];
    IF.formula_struc_base = Base(formula_base);
    IF.formula_struc_is_requires = false; (* Not sure what this is *)
    IF.formula_struc_continuation = None;
    IF.formula_struc_pos = no_pos
  } in
  SC.MetaEForm(IF.EBase(struc_base_formula))

(* Antecedent and consequent are IF.formula and IF.struc_formula respectively *)
let entail ante conseq : bool =
  SE.process_entail_check ante conseq (Some false)

let ante_printer xs =
  let rec helper i xs =
    match xs with
    | [] -> ""
    | x::xs' -> "Ante 1 : " ^ (SC.string_of_meta_formula x) ^ "\n" ^ (helper (i+1) xs')
  in
  helper 1 xs

let conseq_printer x =
  "Conseq : " ^ (SC.string_of_meta_formula x)

(* let entail (lhs : CF.list_partial_context) (rhs : CF.list_partial_context) : bool =  *)
 (* let rs_struc, _ = Solver.heap_entail_struc_list_partial_context_init !cprog false false fn_state (snd posts) None None None pos (Some pid) in *)
 (* let res = CF.isSuccessListPartialCtx rs_struc in *)
 (* res *)
  
