open Globals
open Wrapper
open Gen
open Others
open Label_only

module AS = Astsimp
module C  = Cast
module IF = Iformula
module IP = Ipure
module CF = Cformula
module CP = Cpure
module H  = Hashtbl
module I  = Iast
module SC = Sleekcore

let generate_ilemma iprog cprog lemma_n coer_type lhs rhs head body=
  (*check entailment*)
  let (res,_,_) =  if coer_type = I.Left then
    SC.sleek_entail_check [] cprog lhs (CF.struc_formula_of_formula rhs no_pos)
  else SC.sleek_entail_check [] cprog rhs (CF.struc_formula_of_formula lhs no_pos)
  in
  if res then
    (*generate ilemma*)
    let ilemma = { I.coercion_type = coer_type;
    I.coercion_exact = false;
    I.coercion_name = (fresh_any_name lemma_n);
    I.coercion_head = (IF.subst_stub_flow IF.top_flow head);
    I.coercion_body = (IF.subst_stub_flow IF.top_flow body);
    I.coercion_proof = I.Return ({ I.exp_return_val = None;
    I.exp_return_path_id = None ;
    I.exp_return_pos = no_pos })}
    in
    (*transfrom ilemma to clemma*)
    let ldef = AS.case_normalize_coerc iprog ilemma in
    let l2r, r2l = AS.trans_one_coercion iprog ldef in
    l2r, r2l
  else
    [],[]

(*if two views are equiv, generate an equiv lemma*)
let check_view_subsume iprog cprog view1 view2=
  let hn_c_trans (sv1, sv2) hf = match hf with
    | CF.ViewNode vn ->
          let nhf = 
            if String.compare sv1 vn.CF.h_formula_view_name = 0 then
              CF.ViewNode {vn with CF.h_formula_view_name = sv2 }
            else hf
          in
          nhf
    | _ -> hf
  in
  let v_f1 = CF.formula_of_disjuncts (List.map fst view1.C.view_un_struc_formula) in
  let v_f2 = CF.formula_of_disjuncts (List.map fst view2.C.view_un_struc_formula) in
  let v_f11 = CF.formula_trans_heap_node (hn_c_trans (view1.C.view_name, view2.C.view_name)) v_f1 in
  let pos1 = (CF.pos_of_formula v_f1) in
  let pos2 = (CF.pos_of_formula v_f2) in
  let hf1 = IF.mkHeapNode (self, Unprimed) (view1.C.view_name)
    0  false  (IF.ConstAnn Mutable) false false false None
    (List.map (fun (CP.SpecVar (_,id,p)) -> IP.Var ((id,p), pos1)) view1.C.view_vars) []  None pos1 in
  let hf2 = IF.mkHeapNode (self, Unprimed) (view2.C.view_name)
    0  false (IF.ConstAnn Mutable) false false false None
    (List.map (fun (CP.SpecVar (_,id,p)) -> IP.Var ((id,p), pos1)) view2.C.view_vars) [] None pos2 in
  let lemma_n = view1.C.view_name ^"_"^ view2.C.view_name in
  let l2r1, r2l1 = generate_ilemma iprog cprog lemma_n I.Left v_f11 v_f2
    (IF.formula_of_heap_1 hf1 pos1) (IF.formula_of_heap_1 hf2 pos2) in
  let l2r2, r2l2 = generate_ilemma iprog cprog lemma_n I.Right v_f11 v_f2
    (IF.formula_of_heap_1 hf1 pos1) (IF.formula_of_heap_1 hf2 pos2) in
  (l2r1@l2r2, r2l1@r2l2)

let generate_lemma_4_views_x iprog cprog=
  let rec helper views l_lem r_lem=
    match views with
      | [] -> (l_lem,r_lem)
      | [v] -> (l_lem,r_lem)
      | v::rest ->
            let l,r = List.fold_left (fun (r1,r2) v1 ->
                let l, r = check_view_subsume iprog cprog v v1 in
                (r1@l,r2@r)
            ) ([],[]) rest
            in
            helper rest (l_lem@l) (r_lem@r)
  in
  let l2r, r2l = helper cprog.C.prog_view_decls [] [] in
  (* let _ = cprog.C.prog_left_coercions <- l2r @ cprog.C.prog_left_coercions in *)
  (* let _ = cprog.C.prog_right_coercions <- r2l @ cprog.C.prog_right_coercions in *)
  (l2r,r2l)

let generate_lemma_4_views iprog cprog=
  let pr1 cp = (pr_list_ln Cprinter.string_of_view_decl_short) cp.C.prog_view_decls in
  let pr2 = pr_list_ln Cprinter.string_of_coerc_short in
  Debug.no_1 "generate_lemma_4_views" pr1 (pr_pair pr2 pr2)
      (fun _ -> generate_lemma_4_views_x iprog cprog)
      cprog
