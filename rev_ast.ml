#include "xdebug.cppo"
open VarGen
(*translates cformulas to iformulas, with some simplifications*)
open Globals
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

module C = Cast
module I = Iast
module IF = Iformula
module IP = Ipure
module CF = Cformula
module CP = Cpure
module LO = Label_only.LOne

let rev_trans_spec_var v = match v with CP.SpecVar (t,v,p)-> (v,p) 
let sv_n = CP.name_of_spec_var 

let rec rev_trans_exp e = match e with
  | CP.Null p -> IP.Null p 
  (* | CP.Var (v,p) -> IP.Var (rev_trans_spec_var v, p) *)
  | CP.Var (v,p) -> 
    let t =  CP.type_of_spec_var v in
    (* let () = print_endline ((!CP.print_sv v)^ ": " ^ (string_of_typ t)) in *)
    if is_type_var t then IP.Var (rev_trans_spec_var v, p)
    else
      IP.Ann_Exp (IP.Var (rev_trans_spec_var v, p), t, p) (*L2: added annotated sv instead sv here*)
  | CP.Bptriple ((c,t,a),p) ->
    let nc = IP.Var (rev_trans_spec_var c, p) in
    let nt = IP.Var (rev_trans_spec_var t, p) in
    let na = IP.Var (rev_trans_spec_var a, p) in
    IP.Bptriple ((nc,nt,na),p)
  | CP.Tup2 ((e1,e2),p)      -> IP.Tup2 ((rev_trans_exp e1, rev_trans_exp e2), p)
  | CP.IConst b -> IP.IConst b
  | CP.FConst b -> IP.FConst b
  | CP.AConst b -> IP.AConst b
  | CP.Tsconst b -> IP.Tsconst b
  | CP.Add (e1,e2,p)      -> IP.Add (rev_trans_exp e1, rev_trans_exp e2, p)
  | CP.Subtract (e1,e2,p) -> IP.Subtract (rev_trans_exp e1, rev_trans_exp e2, p)
  | CP.Mult (e1,e2,p)     -> IP.Mult (rev_trans_exp e1, rev_trans_exp e2, p)
  | CP.Div (e1,e2,p)      -> IP.Div (rev_trans_exp e1, rev_trans_exp e2, p)
  | CP.Max (e1,e2,p)      -> IP.Max (rev_trans_exp e1, rev_trans_exp e2, p)
  | CP.Min (e1,e2,p)      -> IP.Min (rev_trans_exp e1, rev_trans_exp e2, p)
  | CP.TypeCast (ty,e1,p) -> IP.TypeCast (ty, rev_trans_exp e1, p)
  | CP.Bag (l,p)          -> IP.Bag (List.map rev_trans_exp l, p)
  | CP.BagUnion (l,p)     -> IP.BagUnion (List.map rev_trans_exp l, p)
  | CP.BagIntersect (l,p) -> IP.BagIntersect (List.map rev_trans_exp l, p)
  | CP.BagDiff (e1,e2,p)  -> IP.BagDiff (rev_trans_exp e1, rev_trans_exp e2, p)
  | CP.List (l,p)         -> IP.List (List.map rev_trans_exp l, p)
  | CP.ListCons (e1,e2,p) -> IP.ListCons (rev_trans_exp e1, rev_trans_exp e2, p)
  | CP.ListHead (e1,p) -> IP.ListHead (rev_trans_exp e1, p)
  | CP.ListTail (e,p)     -> IP.ListTail (rev_trans_exp e, p)
  | CP.ListLength (e,p)   -> IP.ListLength (rev_trans_exp e, p)
  | CP.ListAppend (l,p)   -> IP.ListAppend (List.map rev_trans_exp l, p)
  | CP.ListReverse (e,p)  -> IP.ListReverse (rev_trans_exp e, p)
  | CP.ArrayAt (v,el,p)   -> IP.ArrayAt (rev_trans_spec_var v, List.map rev_trans_exp el, p)
  | CP.Func (v,el,p)      -> IP.Func (sv_n v, List.map rev_trans_exp el, p)
  | CP.Level _| CP.InfConst _ | CP.NegInfConst _ -> report_error no_pos "AS.rev_trans_exp: not handle yet"
  | CP.Template t         -> 
    IP.Template {
      IP.templ_id = sv_n t.CP.templ_id;
      IP.templ_args = List.map rev_trans_exp t.CP.templ_args;
      IP.templ_unks = List.map rev_trans_exp t.CP.templ_unks;
      IP.templ_body = map_opt rev_trans_exp t.CP.templ_body;
      IP.templ_pos = t.CP.templ_pos; }

let rec rev_trans_pf f = match f with
  | CP.XPure b -> IP.XPure{  
      IP.xpure_view_node = map_opt sv_n b.CP.xpure_view_node;
      IP.xpure_view_name = b.CP.xpure_view_name;
      IP.xpure_view_arguments = List.map sv_n b.CP.xpure_view_arguments;
      IP.xpure_view_remaining_branches = None;
      IP.xpure_view_pos = b.CP.xpure_view_pos}
  | CP.LexVar _ -> failwith "rev_trans_pure: unexpected lexvar, if you want support for it , implement this case\n"
  | CP.ImmRel _ -> failwith "rev_trans_pf for imm rel not implemented yet"
  | CP.BConst b -> IP.BConst b
  | CP.Frm (v,p) -> IP.Frm ( rev_trans_spec_var v, p)
  | CP.BVar (v,p) -> IP.BVar ( rev_trans_spec_var v, p)
  | CP.Lt (e1,e2,p) -> IP.Lt (rev_trans_exp e1, rev_trans_exp e2, p)
  | CP.Lte (e1,e2,p) -> IP.Lte (rev_trans_exp e1, rev_trans_exp e2, p)
  | CP.Gt (e1,e2,p) -> IP.Gt (rev_trans_exp e1, rev_trans_exp e2, p)
  | CP.Gte (e1,e2,p) -> IP.Gte (rev_trans_exp e1, rev_trans_exp e2, p)
  | CP.SubAnn (e1,e2,p) -> IP.SubAnn (rev_trans_exp e1, rev_trans_exp e2, p)
  | CP.Eq (e1,e2,p) -> IP.Eq (rev_trans_exp e1, rev_trans_exp e2, p)
  | CP.Neq (e1,e2,p) -> IP.Neq (rev_trans_exp e1, rev_trans_exp e2, p)  
  | CP.EqMax (e1,e2,e3,p) -> IP.EqMax (rev_trans_exp e1, rev_trans_exp e2, rev_trans_exp e3, p)
  | CP.EqMin (e1,e2,e3,p) -> IP.EqMin (rev_trans_exp e1, rev_trans_exp e2, rev_trans_exp e3, p)  
  | CP.BagIn (v,e,p) -> IP.BagIn (rev_trans_spec_var v, rev_trans_exp e, p)
  | CP.BagNotIn (v,e,p) -> IP.BagNotIn (rev_trans_spec_var v, rev_trans_exp e, p)
  | CP.BagSub (e1,e2,p) -> IP.BagSub (rev_trans_exp e1, rev_trans_exp e2, p)
  | CP.BagMin (v1,v2,p) -> IP.BagMin (rev_trans_spec_var v1, rev_trans_spec_var v2, p)
  | CP.BagMax  (v1,v2,p) -> IP.BagMax (rev_trans_spec_var v1, rev_trans_spec_var v2, p)
  (* | CP.VarPerm _ -> failwith "rev_trans_pure: unexpected VarPerm, if you want support for it , implement this case\n"  *)
  | CP.RelForm (v,el,p)-> IP.RelForm (sv_n v, List.map rev_trans_exp el, p)
  | CP.ListIn (e1,e2,p) -> IP.ListIn (rev_trans_exp e1, rev_trans_exp e2, p)
  | CP.ListNotIn (e1,e2,p) -> IP.ListNotIn (rev_trans_exp e1, rev_trans_exp e2, p)
  | CP.ListAllN (e1,e2,p) -> IP.ListAllN (rev_trans_exp e1, rev_trans_exp e2, p)
  | CP.ListPerm (e1,e2,p) -> IP.ListPerm (rev_trans_exp e1, rev_trans_exp e2, p)

let rec rev_trans_pure f = match f with
  | CP.BForm ((b1,_),b2)  -> IP.BForm ((rev_trans_pf b1,None), b2)
  | CP.And (b1,b2,b3) -> IP.And (rev_trans_pure b1, rev_trans_pure b2, b3)
  | CP.AndList l -> IP.AndList (map_l_snd rev_trans_pure l)
  | CP.Or (f1,f2,lbl,pos) -> IP.Or (rev_trans_pure f1, rev_trans_pure f2, lbl, pos)
  | CP.Not (f,lbl,pos)-> IP.Not (rev_trans_pure f, lbl, pos)
  | CP.Forall (v,f,lbl,pos)->  IP.Forall (rev_trans_spec_var v,rev_trans_pure f, lbl, pos)
  | CP.Exists (v,f,lbl,pos)->  IP.Exists (rev_trans_spec_var v,rev_trans_pure f, lbl, pos)

let rec rev_trans_mix f = rev_trans_pure(Mcpure.pure_of_mix f)

let rec rev_trans_heap f = match f with 
  | CF.HTrue  -> IF.HTrue
  | CF.HFalse -> IF.HFalse
  | CF.HEmp   -> IF.HEmp
  | CF.HVar (CP.SpecVar(_,v,_),ls)   -> IF.HVar (v,List.map (Cpure.string_of_spec_var) ls)
  | CF.ThreadNode b ->
    IF.mkThreadNode (rev_trans_spec_var b.CF.h_formula_thread_node) 
      b.CF.h_formula_thread_name
      (rev_trans_formula b.CF.h_formula_thread_resource)
      (rev_trans_pure b.CF.h_formula_thread_delayed)
      (Perm.rev_trans_perm b.CF.h_formula_thread_perm)
      None
      b.CF.h_formula_thread_pos
  | CF.DataNode b ->
    IF.mkHeapNode (rev_trans_spec_var b.CF.h_formula_data_node) 
      b.CF.h_formula_data_name [] (* TODO:HO *)
      0
      b.CF.h_formula_data_derv
      b.CF.h_formula_data_split
      (IP.ConstAnn(Mutable))
      true false false
      (Perm.rev_trans_perm b.CF.h_formula_data_perm)
      (List.map (fun c-> IP.Var ((rev_trans_spec_var c),no_pos)) b.CF.h_formula_data_arguments) []
      None b.CF.h_formula_data_pos
  | CF.ViewNode b ->
    IF.mkHeapNode (rev_trans_spec_var b.CF.h_formula_view_node) 
      b.CF.h_formula_view_name  [] (* IMP_TODO:HO *) 
      0
      b.CF.h_formula_view_derv
      b.CF.h_formula_view_split
      (IP.ConstAnn(Mutable))
      true false false
      (Perm.rev_trans_perm b.CF.h_formula_view_perm)
      (List.map (fun c-> IP.Var ((rev_trans_spec_var c),no_pos)) b.CF.h_formula_view_arguments) (List.map (fun _ -> None) b.CF.h_formula_view_arguments)
      None b.CF.h_formula_view_pos
  | CF.Hole _  | CF.FrmHole _ -> failwith "holes should not have been here"
  | CF.HRel  (sv,el,p)  -> IF.HRel (sv_n sv, List.map rev_trans_exp el, p)
  | CF.Phase b  -> IF.mkPhase (rev_trans_heap b.CF.h_formula_phase_rd) (rev_trans_heap b.CF.h_formula_phase_rw) b.CF.h_formula_phase_pos
  | CF.Conj  b  -> IF.mkConj  (rev_trans_heap b.CF.h_formula_conj_h1) (rev_trans_heap b.CF.h_formula_conj_h2) b.CF.h_formula_conj_pos
  | CF.Star  b  -> IF.mkStar  (rev_trans_heap b.CF.h_formula_star_h1) (rev_trans_heap b.CF.h_formula_star_h2) b.CF.h_formula_star_pos
  | CF.StarMinus _| CF.ConjStar _|CF.ConjConj _ -> report_error no_pos "AS.rev_trans_heap: not handle yet"

and rev_trans_formula f =
  let remove_s s=
    let is = String.index s '#' in
    String.sub s 0 is
  in
  match f with 
  | CF.Base b -> IF.Base { 
      IF.formula_base_heap = rev_trans_heap b.CF.formula_base_heap;
      IF.formula_base_pure = rev_trans_mix b.CF.formula_base_pure;
      IF.formula_base_vperm = (* b.CF.formula_base_vperm; *) IvpermUtils.empty_vperm_sets;
      IF.formula_base_flow = remove_s (exlist # get_closest b.CF.formula_base_flow.CF.formula_flow_interval);
      IF.formula_base_and = [];
      IF.formula_base_pos = b.CF.formula_base_pos }
  | CF.Exists b -> IF.Exists {
      IF.formula_exists_qvars = List.map rev_trans_spec_var b.CF.formula_exists_qvars;
      IF.formula_exists_heap = rev_trans_heap b.CF.formula_exists_heap;
      IF.formula_exists_pure = rev_trans_mix b.CF.formula_exists_pure;
      IF.formula_exists_vperm = (* b.CF.formula_exists_vperm; *) IvpermUtils.empty_vperm_sets;
      IF.formula_exists_flow = remove_s (exlist # get_closest b.CF.formula_exists_flow.CF.formula_flow_interval);
      IF.formula_exists_and = [];
      IF.formula_exists_pos =b.CF.formula_exists_pos}
  | CF.Or b-> IF.Or {
      IF.formula_or_f1 =rev_trans_formula b.CF.formula_or_f1; 
      IF.formula_or_f2 =rev_trans_formula b.CF.formula_or_f2; 
      IF.formula_or_pos = b.CF.formula_or_pos;}

let rev_trans_formula f=
  let pr1 = Cprinter.prtt_string_of_formula in
  let pr2 = Iprinter.string_of_formula in
  Debug.no_1 "rev_trans_formula" pr1 pr2
    (fun _ -> rev_trans_formula f) f

let transform_hp_rels_to_iviews (hp_rels:(ident* CF.hp_rel_def) list):(ident*ident*I.view_decl) list = 
  (*CP.rel_cat * h_formula * formula*)

  List.fold_left (fun acc (proc_id,(* (rel_cat, hf,_,f_body) *) def)->
      let f_body = CF.disj_of_list (List.map fst def.CF.def_rhs) no_pos in
      match def.CF.def_cat with
      | CP.HPRelDefn (v,r,paras)->
        let vname = sv_n v in
        let slf, vars, tvars = match def.CF.def_lhs with
          | CF.HRel (v1,el,_)->
            if ((String.compare (sv_n v1) vname)!=0) then failwith "hrel name inconsistency\n"
            else  (
              (*LOC changed here.*)
              (* let tvars = List.map (fun c-> match c with CP.Var (CP.SpecVar (t, v, _),_)-> (t,v) | _ -> failwith "unexpected expr") el in *)
              (* let vars  = List.map (fun c-> *)
              (*     match c with *)
              (*       |  CP.Var (CP.SpecVar (_, v, p),_)-> (v^(match p with Primed -> "PRM"| _ -> "")) *)
              (*       | _ -> failwith "unexpected expr" *)
              (* ) el in *)
              let tvars = List.map (fun (CP.SpecVar (t, v, _))-> (t,v)) (r::paras) in
              let vars  = List.map (fun (CP.SpecVar (_, v, p))-> (v^(match p with Primed -> "PRM"| _ -> ""))
                ) (r::paras) in
              match vars with
              | h::t -> h,t, (List.tl tvars)
              | []   -> failwith "unexpected number of arguments in inferred predicates\n"
            )
          | _ -> failwith "unexpected heap formula instead of hrel node \n"
        in
        let no_prm_body = CF.elim_prm f_body in
        let new_body = CF.set_flow_in_formula_override {CF.formula_flow_interval = !top_flow_int; CF.formula_flow_link =None} no_prm_body in
        let i_body = rev_trans_formula new_body in
        let i_body = IF.subst [((slf,Unprimed),(self,Unprimed))] i_body in
        let struc_body = IF.mkEBase [] [] [] i_body None (* false *) no_pos in
        let n_iview = {  I.view_name = vname;
                         I.view_pos = no_pos;
                         I.view_data_name = "";
                         I.view_type_of_self = None;
                         (* I.view_actual_root = None; *)
                         I.view_vars = vars;
                         I.view_ho_vars = []; (* TODO:HO *)
                         I.view_imm_map = [];
                         I.view_parent_name = None;
                         I.view_derv = false;
                         I.view_derv_from = None;
                         I.view_derv_extns = [];
                         I.view_labels = List.map (fun _ -> LO.unlabelled) vars, false;
                         I.view_modes = List.map (fun _ -> ModeOut) vars ;
                         I.view_typed_vars =  tvars;
                         I.view_kind = View_NORM;
                         I.view_prop_extns = [];
                         I.view_derv_info = [];
                         I.view_pt_by_self  = [];
                         I.view_formula = struc_body;
                         I.view_inv_lock = None;
                         I.view_is_prim = false;
                         I.view_is_hrel = None;
                         I.view_invariant = IP.mkTrue no_pos;
                         I.view_baga_inv = None;
                         I.view_baga_over_inv = None;
                         I.view_baga_under_inv = None;
                         I.view_mem = None;
                         I.view_materialized_vars = [];
                         I.try_case_inference = false; }
        in
        (proc_id,vname, n_iview)::acc
      | _ -> acc) [] hp_rels

let transform_hp_rels_to_iviews hp_rels =
  let pr1 = pr_list (pr_pair pr_id Cprinter.string_of_hp_rel_def) in
  let pr2 = pr_list (pr_triple pr_id pr_id Iprinter.string_of_view_decl) in
  Debug.no_1 "transform_hp_rels_to_iviews" pr1 pr2 transform_hp_rels_to_iviews hp_rels

let rev_trans_hp_decl (hp_decl: C.hp_decl): I.hp_decl = 
  { I.hp_name = hp_decl.C.hp_name;
    I.hp_typed_inst_vars = List.map (fun (sv, k) -> 
        (CP.type_of_spec_var sv, CP.name_of_spec_var sv, k)) hp_decl.C.hp_vars_inst;
    I.hp_part_vars = hp_decl.C.hp_part_vars;
    I.hp_root_pos = hp_decl.C.hp_root_pos;
    I.hp_is_pre = hp_decl.C.hp_is_pre;
    I.hp_formula = rev_trans_formula hp_decl.C.hp_formula; }

let rec rev_trans_ann (a: CP.ann): IP.ann = 
  match a with
  | CP.NoAnn -> IP.NoAnn
  | CP.ConstAnn x -> IP.ConstAnn x
  | CP.PolyAnn sv -> IP.PolyAnn ((CP.name_of_spec_var sv, CP.primed_of_spec_var sv), no_pos)
  | CP.TempAnn t -> rev_trans_ann t
  | CP.TempRes _ -> failwith "rev_trans_ann: Unexpected ann"

let rev_trans_mem_formula (m: CF.mem_perm_formula): IF.mem_formula = 
  { IF.mem_formula_exp = rev_trans_exp m.CF.mem_formula_exp;
    IF.mem_formula_exact = m.CF.mem_formula_exact;
    IF.mem_formula_field_values = List.map (fun (id, el) -> (id, List.map rev_trans_exp el)) m.CF.mem_formula_field_values;
    IF.mem_formula_field_layout = List.map (fun (id, al) -> (id, List.map rev_trans_ann al)) m.CF.mem_formula_field_layout;
    IF.mem_formula_guards = List.map rev_trans_pure m.CF.mem_formula_guards; }

let rec rev_trans_struc_formula (sf: CF.struc_formula): IF.struc_formula = 
  match sf with
  | CF.EList l -> IF.EList (List.map (fun (sld, sf) -> (sld, rev_trans_struc_formula sf)) l)
  | CF.ECase c -> IF.ECase (rev_trans_struc_case_formula c)
  | CF.EBase b -> IF.EBase (rev_trans_struc_base_formula b)
  | CF.EAssume a -> IF.EAssume (rev_trans_struc_assume_formula a) 
  | CF.EInfer i -> IF.EInfer (rev_trans_struc_infer_formula i)

and rev_trans_struc_infer_formula (i: CF.struc_infer_formula): IF.struc_infer_formula =
  { IF.formula_inf_obj = i.CF.formula_inf_obj;
    IF.formula_inf_post = i.CF.formula_inf_post;
    IF.formula_inf_xpost = i.CF.formula_inf_xpost;
    IF.formula_inf_transpec = i.CF.formula_inf_transpec;
    IF.formula_inf_vars = List.map rev_trans_spec_var_primed i.CF.formula_inf_vars;
    IF.formula_inf_continuation = rev_trans_struc_formula i.CF.formula_inf_continuation;
    IF.formula_inf_pos = i.CF.formula_inf_pos; }

and rev_trans_struc_assume_formula (a: CF.assume_formula): IF.assume_formula =
  { IF.formula_assume_simpl = rev_trans_formula a.CF.formula_assume_simpl;
    IF.formula_assume_struc = rev_trans_struc_formula a.CF.formula_assume_struc;
    IF.formula_assume_lbl = a.CF.formula_assume_lbl;
    IF.formula_assume_ensures_type = a.CF.formula_assume_ensures_type; }

and rev_trans_struc_case_formula (c: CF.struc_case_formula): IF.struc_case_formula =
  { IF.formula_case_branches = List.map (fun (e, sf) -> (rev_trans_pure e, rev_trans_struc_formula sf)) c.CF.formula_case_branches;
    IF.formula_case_pos = c.CF.formula_case_pos; }

and rev_trans_struc_base_formula (b: CF.struc_base_formula): IF.struc_base_formula =
  { IF.formula_struc_explicit_inst = List.map rev_trans_spec_var_primed b.CF.formula_struc_explicit_inst;
    IF.formula_struc_implicit_inst = List.map rev_trans_spec_var_primed b.CF.formula_struc_implicit_inst;
    IF.formula_struc_exists = List.map rev_trans_spec_var_primed b.CF.formula_struc_exists;
    IF.formula_struc_base = rev_trans_formula b.CF.formula_struc_base;
    IF.formula_struc_is_requires = b.CF.formula_struc_is_requires;
    IF.formula_struc_continuation = map_opt rev_trans_struc_formula b.CF.formula_struc_continuation;
    IF.formula_struc_pos = b.CF.formula_struc_pos; }

and rev_trans_spec_var_primed (sv: CP.spec_var): (ident * primed) =
  (CP.name_of_spec_var sv, CP.primed_of_spec_var sv)

let rev_sv sv = CP.name_of_spec_var sv

let rev_intv (sv,ssv_opt) = (rev_sv sv,
                             let () = y_binfo_pp x_tbi in
                             None (* map_opt rev_sv ssv_opt *))

let rev_trans_view_decl (v: C.view_decl): I.view_decl = 
  let rev_trans_baga_inv baga_inv =
    map_opt (List.map ((fun (svl, f) -> (
          List.map (fun sv -> rev_intv sv) svl, 
          rev_trans_pure f)))) baga_inv
  in
  { I.view_name = v.C.view_name;
    I.view_vars = List.map CP.name_of_spec_var v.C.view_vars;
    I.view_pos = v.C.view_pos;
    I.view_is_prim = v.C.view_is_prim;
    I.view_is_hrel = v.C.view_is_hrel;
    I.view_data_name = v.C.view_data_name;
    I.view_ho_vars = List.map (fun (fk, sv, sk) -> (fk, CP.name_of_spec_var sv, sk)) v.C.view_ho_vars;
    I.view_imm_map = []; (* TODO *)
    I.view_labels = v.C.view_labels, List.exists (fun c -> not (LO.is_unlabelled c)) v.C.view_labels;
    I.view_modes = v.C.view_modes;
    I.view_typed_vars = List.map (fun sv -> (CP.type_of_spec_var sv, CP.name_of_spec_var sv)) v.C.view_vars;
    I.view_parent_name = v.C.view_parent_name;
    I.view_derv = false; (* TODO *)
    I.view_derv_from = None;
    I.view_derv_extns = [];
    I.view_derv_info = []; (* TODO *)
    I.view_type_of_self = 
      v.C.view_type_of_self;
    I.view_kind = v.C.view_kind;
    I.view_prop_extns = List.map (fun sv -> (CP.type_of_spec_var sv, CP.name_of_spec_var sv)) v.C.view_prop_extns;
    I.view_invariant = 
      (let () = y_binfo_pp "XXX" in
      rev_trans_mix v.C.view_user_inv);
    I.view_baga_inv = rev_trans_baga_inv v.C.view_baga_inv;
    I.view_baga_over_inv = rev_trans_baga_inv v.C.view_baga_over_inv;
    I.view_baga_under_inv = rev_trans_baga_inv v.C.view_baga_under_inv;
    I.view_mem = map_opt rev_trans_mem_formula v.C.view_mem;
    I.view_formula = rev_trans_struc_formula v.C.view_formula;
    I.view_inv_lock = map_opt rev_trans_formula v.C.view_inv_lock;
    I.view_pt_by_self = v.C.view_pt_by_self;
    I.try_case_inference = false; (* TODO *)
    I.view_materialized_vars = List.map (fun mv -> CP.name_of_spec_var mv.C.mater_var) v.C.view_materialized_vars; }

let rev_trans_view_decl (v: C.view_decl): I.view_decl = 
  let pr1 = Cprinter.string_of_view_decl in
  let pr2 = Iprinter.string_of_view_decl in
  Debug.no_1 "rev_trans_view_decl" pr1 pr2 rev_trans_view_decl v

let () = CF.rev_trans_formula := rev_trans_formula

(* let rev_trans_data_decl (d: C.data_decl): I.data_decl =                              *)
(*   let pos = d.C.data_pos in                                                          *)
(*   { I.data_name = d.C.data_name;                                                     *)
(*     I.data_fields = List.map (fun (i, ann) -> (i, pos, false, ann)) d.C.data_fields; *)
(*     I.data_parent_name = d.C.data_parent_name;                                       *)
(*     I.data_invs = List.map rev_trans_formula d.C.data_invs;                          *)
(*     I.data_pos = pos;                                                                *)
(*     I.data_pure_inv = map_opt rev_trans_pure d.C.data_pure_inv;                      *)
(*     I.data_is_template = false;                                                      *)
(*     I.data_methods = []; }                                                           *)
