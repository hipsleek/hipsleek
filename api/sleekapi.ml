open Hipsleek
open Hipsleek_common

module C = Cast
module I = Iast
module VG = VarGen
module SC = Sleekcommons
module SE = Sleekengine
module CF = Cformula
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

(* Prelude of api *)
let init () = 
  let () = print_string "Initializing sleek api" in
  (* Prelude file contains some data declarations like int_ptr to support the api
     Declarations in this prelude file will be parsed and stored in a global
     variable, iprog, in sleekengine.ml
  *)
  let () = Sleekmain.parse_file Nativefront.list_parse "./sleekapi_prelude.slk" in
  ()

(* Used as placeholder for pos since no file is parsed *)
let no_pos : VG.loc =
  let no_pos1 = { Lexing.pos_fname = "";
                  Lexing.pos_lnum = 0;
                  Lexing.pos_bol = 0; 
                  Lexing.pos_cnum = 0 } in
  {VG.start_pos = no_pos1; VG.mid_pos = no_pos1; VG.end_pos = no_pos1;}

(* Check whether is a variable primed by variable name *)
(* Might need error handling if var has len 0*)
let check_prime var_name =
  let len = String.length var_name in
    let last = String.get var_name (len - 1) in
    match last with 
    | '\'' -> VG.Primed
    | _ -> VG.Unprimed

(* Returns the truncated variable if variable is primed*)
(* Might also need error handling if var has len 0*)
let truncate_var var_name primed = 
  match primed with 
  | VG.Primed -> String.sub var_name 0 ((String.length var_name) - 1)
  | VG.Unprimed -> var_name

(* Building pure expressions *)
let null_pure_exp = IP.Null no_pos

let var_pure_exp (ident : string) = 
  let p = check_prime ident in
  let t_ident = truncate_var ident p in
  IP.Var ((t_ident, p), no_pos)

let int_pure_exp int = IP.IConst (int, no_pos)
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
let false_heap_f = IF.HFalse
let true_heap_f  = IF.HTrue

let sep_conj_f h1 h2 = IF.mkStar h1 h2 no_pos

let points_to_int_f var_name int =
  let p = check_prime var_name in
  let t_var_name = truncate_var var_name p in
  IF.mkHeapNode_x (t_var_name, p) "int_ptr" []  0 false Globals.SPLIT0 IP.NoAnn false false false None [(int_pure_exp int)] [None] None no_pos

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
    SE.convert_data_and_pred_to_cast_x () (* Can be improved to not re-convert previously converted data and predidcates *)
  | _ -> ()                               (* Possible error handling here *)

let lemma_decl sleek_str =
  let sleek_cmd = NF.parse_slk sleek_str in
  match sleek_cmd with
  | SC.LemmaDef lemma_def ->
    if I.is_lemma_decl_ahead lemma_def then
      let () = SE.process_list_lemma lemma_def in
      ()
    else ()
  | _ -> ()                               (* Possible error handling here *)

let points_to_f var_name ident exps = 
  let primed = check_prime var_name in
  let t_var_name = truncate_var var_name primed in
  let imm_param = List.map (fun _ -> None) exps in
  IF.mkHeapNode_x (t_var_name, primed) ident [] 0 false Globals.SPLIT0 IP.NoAnn false false false None exps imm_param None no_pos
  
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
  (* residue can actually be accessed from CF.residues after run_entail_check *)
  (* let validity, (residue: CF.list_context), _ = SE.run_entail_check ante conseq (Some false) in *)
  (* let () = print_string ("\n Residue : " ^ (Cprinter.string_of_list_context residue)) in *)
  (* SE.print_entail_result [] validity residue "\nEntail " false *)

let ante_printer xs =
  let rec helper i xs =
    match xs with
    | [] -> ""
    | x::xs' -> "Ante 1 : " ^ (SC.string_of_meta_formula x) ^ "\n" ^ (helper (i+1) xs')
  in
  helper 1 xs

let conseq_printer x =
  "Conseq : " ^ (SC.string_of_meta_formula x)

(* Converts meta_formulae to cformulae
   This conversion is done by closely following SE.run_infer_one_pass
*)
let mf_to_cform iante iconseq =
  let ivars = [] in
  let _ = CF.residues := None in
  let _ = Infer.rel_ass_stk # reset in
  let _ = CF.rel_def_stk # reset in
  let (n_tl,ante) = SE.meta_to_formula iante false [] [] in
  let xpure_all f =
    let lst = CF.split_components_all f in
    let disj = List.map (fun (h,p,_,_,_,_) ->
        let (mf,_,_) = Cvutil.xpure_heap_symbolic 999 !SE.cprog h p 0 in
        (Mcpure.pure_of_mix mf)) lst in
    Cpure.join_disjunctions disj in
  let f = xpure_all ante in
  let mf = Mcpure.mix_of_pure f in
  let () = SE.last_entail_lhs_xpure := Some mf in
  let ante = Cvutil.prune_preds !SE.cprog true ante in
  let ante = (*important for permissions*)
    if (Perm.allow_perm ()) then
      CF.add_mix_formula_to_formula (Perm.full_perm_constraint ()) ante
    else ante
  in
  let vk = Typeinfer.fresh_proc_var_kind n_tl Float in
  let n_tl = Typeinfer.type_list_add  (Perm.full_perm_name ()) vk n_tl in
  let fvs = CF.fv ante in
  let _ = SC.fv_meta_formula iante in
  let ivars_new = List.map (fun v -> (v,VG.Unprimed)) ivars in
  let fv_idents = (List.map Cpure.name_of_spec_var fvs)@ivars in
  let fv_idents_new = (List.map Cpure.primed_ident_of_spec_var fvs)@ivars_new in
  let _ =
    if !Globals.dis_impl_var then
      let conseq_idents = List.map (fun (v, _) -> v) (SC.fv_meta_formula iconseq) in
      Gen.BList.remove_dups_eq (fun v1 v2 -> String.compare v1 v2 == 0) (fv_idents @ conseq_idents)
    else fv_idents
  in
  let fv_idents_new =
    if !Globals.dis_impl_var then
      let conseq_idents =(SC.fv_meta_formula iconseq) in
      Gen.BList.remove_dups_eq (fun (v1,p1) (v2,p2) -> String.compare v1 v2 == 0 && p1==p2) (fv_idents_new @ conseq_idents)
    else fv_idents_new
  in

  let (n_tl,conseq) = SE.meta_to_struc_formula iconseq false fv_idents_new  n_tl in
  let conseq_fvs = CF.struc_fv ~vartype:Vartypes.var_with_implicit_explicit conseq in
  let vs = Cpure.remove_dups_svl (fvs@conseq_fvs) in
  let () = Global_var.set_stk_vars vs in

  let sst0 = List.map (fun (Cpure.SpecVar (t,i,p) as sv) ->
      let sv2 = (Typeinfer.get_spec_var_type_list_infer ~d_tt:n_tl) (i,p) [] no_pos
      in (sv,sv2)) fvs in
  let sst = List.filter (fun (Cpure.SpecVar (t1,_,_), Cpure.SpecVar (t2,_,_)) -> not(t1=t2) ) sst0 in
  let ante1 = if sst==[] then ante else CF.subst sst ante in
  let ante = Cfutil.transform_bexpr ante1 in
  let conseq = CF.struc_formula_trans_heap_node [] Cfutil.transform_bexpr conseq in
  (ante, conseq)

(* Converts meta_formulae to context and cformula
   Building the context closely follows sleek_entail_check_x and mkEmp_list_failesc_context
 *)
let new_context iante iconseq =
  let cante, cconseq = mf_to_cform iante iconseq in
  let ectx = CF.empty_ctx (CF.mkTrueFlow ()) Label_only.Lab2_List.unlabelled no_pos in
  let ctx = CF.build_context ectx cante no_pos in
  let ctx = CF.add_path_id ctx (None, 0) 0 in
  let ctx = CF.set_flow_in_context_override
      { CF.formula_flow_interval = !Exc.ETABLE_NFLOW.norm_flow_int; CF.formula_flow_link = None} ctx in
  (ctx, cconseq)
(* The following is done in sleek_entail *)
  (* let init_esc = [((0,""),[])] in *)
  (* let lfe = [CF.mk_failesc_context ctx [] init_esc] in *)
  (* let () = print_string ("\n lfe : " ^ (Cprinter.string_of_list_failesc_context lfe)) in *)
  (* (lfe, cconseq) *)

(* let entail iante iconseq = *)
(*   let ante_ctx, conseq = new_context iante iconseq in *)
(*   let rs, pf = Solver.heap_entail_struc_list_failesc_context_init 12 !SE.cprog false true ante_ctx conseq None None None no_pos None in *)
  (* let rs, prf = Sleekcore.sleek_entail !SE.cprog ante_ctx conseq no_pos in *)
(*   let () = print_string ("\n Residue 1 : " ^ (Cprinter.string_of_list_failesc_context rs)) in *)
(*   (\* entail [iante] iconseq *\) *)
  (* let res = CF.isSuccessListFailescCtx rs in *)
  (* let () = print_string ("\n" ^ (string_of_bool res)) in *)
  (* res *)
  
(* Testing API *)
let%expect_test "Entailment checking" =
  
  let () = init () in

  let entail_1 () =
    (* true |- true *)
    let true_f = true_f in
    let empty_heap_f = empty_heap_f in
    let ante_f = ante_f empty_heap_f true_f in
    let conseq_f = conseq_f empty_heap_f true_f in
    (* let () = print_string (ante_printer ante_f) in *)
    (* let () = print_string (conseq_printer conseq_f) in *)
    let _ = entail ante_f conseq_f in
    ()
  in

  let entail_2 () =
    (* x |-> 1 |- x |-> 1 *)
    let ante_f = ante_f (points_to_int_f "x" 1)
        (true_f) in
    let conseq_f = conseq_f (points_to_int_f "x" 1)
        (true_f) in
    let _ = entail ante_f conseq_f in
    ()
  in

  let entail_3 () =
    (* x > 0 /\ x' = x + 1 |- x' > 1 *)
    let ante_f = ante_f empty_heap_f
        (and_f
           (gt_pure_f
              (var_pure_exp "x")
              (int_pure_exp 0))
           (eq_pure_f
              (var_pure_exp "x'")
              (add_pure_exp
                 (var_pure_exp "x")
                 (int_pure_exp 1)))) in
    let conseq_f = conseq_f empty_heap_f
        (gt_pure_f
           (var_pure_exp "x'")
           (int_pure_exp 1)) in
    let _ = entail ante_f conseq_f in
    ()
  in

  let entail_4 () =
    (* x::node<0,null> |- x != null *)
    let () = data_decl "node" [(Int, "val"); (Named("node"), "next")] in
    let ante_f = ante_f 
        (points_to_f "x" "node" [(int_pure_exp 0); (null_pure_exp)]) true_f in
    let conseq_f = conseq_f empty_heap_f
        (not_f (eq_pure_f
                  (var_pure_exp "x")
                  null_pure_exp)) in
    let _ = entail ante_f conseq_f in
    ()
  in
    
  let entail_5 () =  
    (* x=null |- x::ll<0> *)
    let ll = "pred ll<n> == self = null & n = 0
or self::node<next = r> * r::ll<n - 1>
inv n >= 0." in
    let () = predicate_decl ll in
    let ante_f = ante_f empty_heap_f
        (eq_pure_f
           (var_pure_exp "x")
           null_pure_exp) in
    let conseq_f = conseq_f
        (points_to_f "x" "ll" [(int_pure_exp 0)])
        true_f in
    let _ = entail ante_f conseq_f in
    ()
  in

  let entail_6 () =
    (* x::ll<n> |- x::ll<n+1> *)
    let ante_f = ante_f
        (points_to_f "x" "ll" [(var_pure_exp "n")])
        true_f in
    let conseq_f = conseq_f
        (points_to_f "x" "ll" [(add_pure_exp
                                  (var_pure_exp "n")
                                  (int_pure_exp 1)
                               )])
        true_f in
    let _ = entail ante_f conseq_f in
    ()
  in

  let entail_7 () =
    (* x |-> 1 * y |-> 2 |- x -> 1 *) (* maybe need to find a better test case to test the star *)
    let h1 = points_to_int_f "x" 1 in
    let h2 = points_to_int_f "y" 2 in 
    let astar = sep_conj_f h1 h2 in
    let ante_f = ante_f astar true_f in
    let conseq_f = conseq_f (points_to_int_f "x" 1) true_f in
    let _ = entail ante_f conseq_f in
    ()
  in

  let entail_8 () =
    let sort = "pred sortl<n, mi> == self = null & n = 0
or self::node<mi, r> * r::sortl<n - 1, k> & mi <= k
inv n >= 0." in
    let () = predicate_decl sort in
    let lemma = "lemma self::sortl<n, mi> -> self::ll<n>." in
    let () = lemma_decl lemma in
    let ante_f = ante_f
        (points_to_f "x" "sortl" [(var_pure_exp "a");
                                  (var_pure_exp "b")])
        true_f in
    let conseq_f = conseq_f
        (points_to_f "x" "ll" [(var_pure_exp "a")])
        true_f in
    let _ = entail ante_f conseq_f in
    ()
  in

  entail_1 ();
  entail_2 ();
  entail_3 ();
  entail_4 ();
  entail_5 ();
  entail_6 ();
  entail_7 ();
  entail_8 ();
  [%expect]
