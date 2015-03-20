#include "xdebug.cppo"
open VarGen
open Globals
open Gen.Basic


module C = Cast
module CP = Cpure
module CF = Cformula
module MCP = Mcpure
module Err = Error

module LO = Label_only.LOne


(* 
 * split maximum chain of a h_formula
 *   - return a list of (possible heap chain * the rest of h_formula)
 *)
(* TRUNG TODO: implement the below function  *)
(* and split_heap_chain (hf: h_formula) *)
(*     : (h_formula * h_formula) list = *)



(* let find_begin_end_point_of_heap_chain (hf: CF.h_formula) (aux_pf: MCP.mix_formula) *)
(*     : (CP.spec_var * CP.spec_var) =                                                 *)
      

(* formula of heap chain, entry point, last point, exit point *) 
type heap_chain = CF.h_formula * CP.spec_var * CP.spec_var * CP.spec_var

(* (*                                                                            *)
(*  * each heap chain is a tuple of (h_formula, begin point, end point of chain) *)
(*  * return a merged heap formula if chain1 and chain2 are consecutive          *)
(*  * otherwise, return None                                                     *)
(*  *)                                                                           *)
(* let merge_heap_chains (chain1: heap_chain) (chain2: heap_chain)               *)
(*     (aux_info: MCP.mix_formula) pos                                           *)
(*     : heap_chain option =                                                     *)
(*   let (hf1, start1, end1) = chain1 in                                         *)
(*   let (hf2, start2, end2) = chain2 in                                         *)
(*   let aux_pf = MCP.pure_of_mix aux_info in                                    *)
(*   let chain1_cond = CP.mkEqExp end1 start2 no_pos in                          *)
(*   let chain2_cond = CP.mkEqExp end2 start1 no_pos in                          *)
(*   (* check if chain2 follows chain1 *)                                        *)
(*   if (TP.imply_raw aux_info chain1_cond) then (                               *)
(*     let new_hf = CF.mkStarH hf1 hf2 pos in                                    *)
(*     Some (new_hf, start1, end2)                                               *)
(*   )                                                                           *)
(*   (* check if chain1 follows chain1 *)                                        *)
(*   else if (TP.imply_raw aux_info chain1_cond) then (                          *)
(*     let new_hf = CF.mkStarH hf2 hf1 pos in                                    *)
(*     Some (new_hf, start2, end1)                                               *)
(*   )                                                                           *)
(*   else None                                                                   *)


(* (* collect all view names from a h_formula *)                                    *)
(* let rec collect_view_from_hformula (hf: CF.h_formula) : ident list =             *)
(*   let eq_id x y = (String.compare x y = 0) in                                    *)
(*   let views = ref [] in                                                          *)
(*   let f_hf hf = match hf with                                                    *)
(*     | ViewNode vn ->                                                             *)
(*         views := Gen.BList.remove_dups_eq eq_id (h_formula_view_name :: !views); *)
(*         (Some hf)                                                                *)
(*     | _ -> None in                                                               *)
(*   let todo_unk = CF.transform_h_formula f_hf hf in                                      *)
(*   !views                                                                         *)

let collect_atomic_heap_chain_x (hf: CF.h_formula) (root_view: C.view_decl) (prog: C.prog_decl)
    : (heap_chain list * CF.h_formula) =
  if ((List.length root_view.C.view_forward_ptrs != 1) 
      || (List.length root_view.C.view_forward_fields != 1)) then
    ([], hf)
  (* consider only the case the root view has 1 forward pointer and 1 forward field *)
  else (
    let fw_ptr = List.hd root_view.C.view_forward_ptrs in
    let fw_field = snd (List.hd root_view.C.view_forward_fields) in
    let root_dname = root_view.C.view_data_name in
    let root_vname = root_view.C.view_name in
    let rec extract_atomic_chain hf = (match hf with
      | CF.DataNode dn ->
          if (String.compare dn.CF.h_formula_data_name root_dname = 0) then (
            try 
              let ddecl = C.look_up_data_def_raw prog.C.prog_data_decls root_dname in
              let entry_sv = dn.CF.h_formula_data_node in
              let last_sv = entry_sv in
              let exit_sv = (
                let svs = List.fold_left2 (fun res arg field ->
                  let ((_,fname),_) = field in
                  if (String.compare fname fw_field = 0) then res @ [arg]
                  else res
                ) [] dn.CF.h_formula_data_arguments ddecl.C.data_fields in
                if (List.length svs != 1) then
                  report_error no_pos "collect_atomic_heap_chain: expect 1 exit sv"
                else List.hd svs
              ) in
              ([(hf, entry_sv, last_sv, exit_sv)], CF.HEmp)
            with _ -> ([], hf)
          )
          else ([], hf)
      | CF.ViewNode vn ->
          if (String.compare vn.CF.h_formula_view_name root_vname = 0) then (
            try 
              let entry_sv = vn.CF.h_formula_view_node in
              let last_sv = entry_sv in
              let exit_sv = (
                let svs = List.fold_left2 (fun res arg var ->
                  if (CP.eq_spec_var var fw_ptr) then res @ [arg]
                  else res
                ) [] vn.CF.h_formula_view_arguments root_view.C.view_vars in
                if (List.length svs != 1) then
                  report_error no_pos "collect_atomic_heap_chain: expect 1 exit sv"
                else List.hd svs
              ) in
              ([(hf, entry_sv, last_sv, exit_sv)], CF.HEmp)
            with _ -> ([], hf)
          )
          else ([], hf)
      | CF.Star s ->
          let h1 = s.CF.h_formula_star_h1 in
          let h2 = s.CF.h_formula_star_h2 in
          let pos = s.CF.h_formula_star_pos in
          let (chains1, h1_rest) = extract_atomic_chain h1 in
          let (chains2, h2_rest) = extract_atomic_chain h2 in
          let heap_chains = chains1 @ chains2 in
          if (h1_rest = CF.HEmp) then (heap_chains, h2_rest)
          else if (h2_rest = CF.HEmp) then (heap_chains, h1_rest)
          else
            let hf_rest = CF.mkStarH h1_rest h2_rest pos in
            (heap_chains, hf_rest)
      | _ -> ([], hf)
    ) in
    let (heap_chains, hf_rest) = extract_atomic_chain hf in
    (heap_chains, hf_rest)
  )

let collect_atomic_heap_chain (hf: CF.h_formula) (root_view: C.view_decl) (prog: C.prog_decl)
    : (heap_chain list * CF.h_formula) =
  let pr_hf = !CF.print_h_formula in
  let pr_vname vd = vd.C.view_name in
  let pr_chain heap_chain = (
    let (hf,entry_sv,last_sv,exit_sv) = heap_chain in
    "(" ^ (!CF.print_h_formula hf) ^ ", " ^ (!CP.print_sv entry_sv)
    ^ ", " ^ (!CP.print_sv last_sv) ^ ", " ^ (!CP.print_sv exit_sv)^ ")"
  ) in
  let pr_out (hc, _) = pr_list pr_chain hc in
  Debug.no_2 "collect_atomic_heap_chain" pr_hf pr_vname pr_out
    (fun _ _ -> collect_atomic_heap_chain_x hf root_view prog) hf root_view


  (* match hf with                                                                                                   *)
  (* | DataNode of h_formula_data                                                                                    *)
  (* | ViewNode of h_formula_view                                                                                    *)
  (* | ThreadNode of h_formula_thread                                                                                *)
  (* | Star star -                                                                                                   *)
  (* | StarMinus of h_formula_starminus                                                                              *)
  (* | Conj of h_formula_conj                                                                                        *)
  (* | ConjStar of h_formula_conjstar                                                                                *)
  (* | ConjConj of h_formula_conjconj                                                                                *)
  (* | Phase of h_formula_phase                                                                                      *)
  (* | Hole of int | FrmHole of int                                                                                  *)
  (* (* | TempHole of int * h_formula *)                                                                             *)
  (* | HRel of (CP.spec_var * ((CP.exp) list) * loc) (*placeh older for heap predicates*)                            *)
  (* (* | HRel of ((CP.spec_var * cond_path_type) * ((CP.exp) list) * loc) (\*placeh older for heap predicates*\) *) *)
  (* | HTrue                                                                                                         *)
  (* | HFalse                                                                                                        *)
  (* | HEmp (* emp for classical logic *)                                                                            *)


(*
 * - Segment a heap formula into heap chains,
 *   each heap chain is as long as possible.
 * - This segmentation is applicable only to conjunction of heap node
 *)
(* let segment_heap_conjunct_into_chains (hf: CF.h_formula) (aux_info: MCP.mix_formula) *)
     (* : (CF.h_formula list) = *)


(*
 * Find a list of heap chain starting from a root node
 * This list is ordered descendingly by the each heap chain length 
 *)
let collect_heap_chains_x (hf: CF.h_formula) (pf: MCP.mix_formula) 
    (root_sv: CP.spec_var) (root_view: C.view_decl) prog
    : (heap_chain * CF.h_formula) list =
  let pos = CF.pos_of_h_formula hf in
  let pf = MCP.pure_of_mix pf in
  Debug.ninfo_hprint (add_str "pf" !CP.print_formula) pf no_pos;
  let emap = CP.EMapSV.build_eset (CP.pure_ptr_equations pf) in
  let rec build_heap_chains built_chains atomic_chains hf_unused = (
    let latest_chain = fst (List.hd built_chains) in
    let (latest_hf,latest_entry,latest_last,latest_exit) = latest_chain in
    Debug.ninfo_hprint (add_str "latest_exit" !CP.print_sv) latest_exit no_pos;
    let aliases = CP.EMapSV.find_equiv_all latest_exit emap in
    Debug.ninfo_hprint (add_str "latest_exit aliases" (pr_list !CP.print_sv)) aliases no_pos;
    try
      let next_chains, rest_chains = List.partition (fun (hf,entry_sv,last_sv,exit_sv) ->
        (CP.eq_spec_var entry_sv latest_exit) || (CP.EMapSV.mem entry_sv aliases)
      ) atomic_chains in
      let next_chain, atomic_chains = (
        match next_chains with
        | [] -> raise Not_found
        | hd::tl -> (hd, tl @ rest_chains)
      ) in
      let (next_hf, next_entry, next_last, next_exit) = next_chain in
      let new_hf = CF.mkStarH latest_hf next_hf pos in
      let new_chain = (new_hf, latest_entry, next_last, next_exit) in
      let hf_rest = List.fold_left (fun hf1 (hf2,_,_,_) ->
        CF.mkStarH hf1 hf2 pos 
      ) hf_unused rest_chains in
      let built_chains = (new_chain, hf_rest) :: built_chains in
      build_heap_chains built_chains atomic_chains hf_unused
    with Not_found -> built_chains
  ) in
  let atomic_chains, hf_unused = collect_atomic_heap_chain hf root_view prog in
  try
    let aliases = CP.EMapSV.find_equiv_all root_sv emap in
    Debug.ninfo_hprint (add_str "root_sv" !CP.print_sv) root_sv no_pos;
    Debug.ninfo_hprint (add_str "root_sv aliases" (pr_list !CP.print_sv)) aliases no_pos;
    let root_chains, rest_chains = List.partition (fun (hf,entry_sv,last_sv,exit_sv) ->
      (CP.eq_spec_var entry_sv root_sv) || (CP.EMapSV.mem entry_sv aliases)
    ) atomic_chains in
    let root_chain, atomic_chains = (
      match root_chains with
      | [] -> raise Not_found
      | hd::tl -> (hd, tl @ rest_chains)
    ) in
    let hf_rest = List.fold_left (fun hf1 (hf2,_,_,_) ->
      CF.mkStarH hf1 hf2 pos 
    ) hf_unused rest_chains in
    build_heap_chains [(root_chain,hf_rest)] rest_chains hf_unused
  with Not_found -> []

let collect_heap_chains (hf: CF.h_formula) (pf: MCP.mix_formula) 
    (root_sv: CP.spec_var) (root_view: C.view_decl) prog
    : (heap_chain * CF.h_formula) list =
  let pr_hf = !CF.print_h_formula in
  let pr_pf = !MCP.print_mix_formula in
  let pr_sv = !CP.print_sv in
  let pr_vname vd = vd.C.view_name in
  let pr_chain ((hc,_,_,_),hf) = (
    "(hc = " ^ (!CF.print_h_formula hc) ^ " , rest = " ^ (!CF.print_h_formula hf) ^ ")"
  ) in
  let pr_out = pr_list pr_chain in
  Debug.no_4 "collect_heap_chains" pr_hf pr_pf pr_sv pr_vname pr_out
      (fun _ _ _ _ -> collect_heap_chains_x hf pf root_sv root_view prog)
      hf pf root_sv root_view

let encode_h_formula_x (hf: CF.h_formula) : ident list =
  let coded_hf = ref [] in
  let f_hf hf = (match hf with
    | CF.DataNode dn ->
        coded_hf := !coded_hf @ [dn.CF.h_formula_data_name];
        Some hf
    | CF.ViewNode vn ->
        coded_hf := !coded_hf @ [vn.CF.h_formula_view_name];
        Some hf
    | CF.Star _ -> None
    | _ -> Some hf
  ) in
  let todo_unk = CF.transform_h_formula f_hf hf in
  !coded_hf

let encode_h_formula (hf: CF.h_formula) : ident list =
  let pr_hf = !CF.print_h_formula in
  let pr_out = pr_list pr_id in
  Debug.no_1 "encode_h_formula" pr_hf pr_out
      (fun _ -> encode_h_formula_x hf) hf

let equal_heap_chain_code_x (code1: ident list) (code2: ident list) : bool = 
  if ((List.length code1) != (List.length code2)) then false
  else (
    List.for_all2 (fun x y ->
      String.compare x y = 0
    ) code1 code2
  )

let equal_heap_chain_code (code1: ident list) (code2: ident list) : bool =
  let pr_c = pr_list pr_id in
  let pr_out = string_of_bool in
  Debug.no_2 "equal_heap_chain_code" pr_c pr_c pr_out
      (fun _ _ -> equal_heap_chain_code_x code1 code2) code1 code2

let try_fold_once_x (f: CF.formula) (root_view: C.view_decl) (fold_f: CF.formula)
    : CF.formula =
  let vname = root_view.C.view_name in
  let extra_pure = ref [] in
  let f_hf hf = (match hf with
    | CF.ViewNode vn ->
        if (String.compare vn.CF.h_formula_view_name vname = 0) then
          let subs = List.map2 (fun sv1 sv2 ->
            (sv1,sv2)
          ) root_view.C.view_vars vn.CF.h_formula_view_arguments in
          let vnode = vn.CF.h_formula_view_node in
          let subs = (
            try
              let self_var = List.find (fun sv ->
                String.compare (CP.name_of_spec_var sv) self = 0
              ) (CF.fv fold_f) in
              subs @ [(self_var, vnode)]
            with Not_found -> subs
          ) in
          let replacing_f = x_add_1 CF.rename_bound_vars fold_f in
          let replacing_f = CF.subst subs replacing_f in
          let (replacing_hf,extra_pf,_,_,_,_) = CF.split_components replacing_f in
          let extra_qvars = CF.get_exists replacing_f in
          extra_pure := !extra_pure @ [(extra_pf, extra_qvars)];
          Some replacing_hf
        else (Some hf)
    | _ -> None) in
  let f_ef _ = None in
  let f_f _ = None in
  let f_m mp = Some mp in
  let f_a a = Some a in
  let f_pf pf = Some pf in
  let f_b bf= Some bf in
  let f_e e = Some e in
  let new_f = CF.transform_formula (f_ef, f_f, f_hf, (f_m, f_a, f_pf, f_b, f_e)) f in
  let pos = CF.pos_of_formula new_f in
  List.fold_left (fun f (mf,qv) ->
    let nf = CF.mkAnd_pure f mf pos in
    CF.push_exists qv nf
  ) new_f !extra_pure

let try_fold_once (f: CF.formula) (root_view: C.view_decl) (fold_f: CF.formula)
    : CF.formula =
  let pr_f = !CF.print_formula in
  let pr_vd vd = vd.C.view_name in
  let pr_out = pr_f in
  Debug.no_3 "try_fold_once_x" pr_f pr_vd pr_f pr_out
      (fun _ _ _ -> try_fold_once_x f root_view fold_f)
      f root_view fold_f

type fold_type =
  | Fold_base_case
  | Fold_inductive_case

let print_fold_type ft =
  match ft with
  | Fold_base_case -> "Fold_base_case"
  | Fold_inductive_case -> "Fold_inductive_case"

let detect_fold_sequence_x (hf: CF.h_formula) (root_sv: CP.spec_var)
    (root_view: C.view_decl) prog
    : fold_type list=
  let vname = root_view.C.view_name in
  Debug.ninfo_hprint (add_str "hf" !CF.print_h_formula) hf no_pos;
  let coded_hf = encode_h_formula hf in
  let coded_hf_len = List.length coded_hf in
  let rec try_fold_view (f: CF.formula) base_f induct_f fold_seq : fold_type list = (
    (* try fold base case *)
    Debug.ninfo_hprint (add_str "f" !CF.print_formula) f no_pos;
    let new_f1 = try_fold_once f root_view base_f in
    Debug.ninfo_hprint (add_str "new_f1" !CF.print_formula) new_f1 no_pos;
    let (hf1,pf1,_,_,_,_) = CF.split_components new_f1 in
    let heap_chains1 = collect_heap_chains hf1 pf1 root_sv root_view prog in
    let is_base_case_ok = (
      if (List.length heap_chains1 = 0) then false
      else (
        let (hf1,_,_,_) = fst (List.hd heap_chains1) in
        let code1 = encode_h_formula hf1 in
        let code1_len = List.length code1 in
        if (code1_len > coded_hf_len) then false
        else if (code1_len < coded_hf_len) then false
        else (equal_heap_chain_code coded_hf code1)
      )
    ) in
    if (is_base_case_ok) then fold_seq @ [Fold_base_case]
    else (
      (* try fold inductive case *)
      let new_f2 = try_fold_once f root_view induct_f in
      Debug.ninfo_hprint (add_str "new_f2" !CF.print_formula) new_f2 no_pos;
      let (hf2,pf2,_,_,_,_) = CF.split_components new_f2 in
      let heap_chains2 = collect_heap_chains hf2 pf2 root_sv root_view prog in
      if (List.length heap_chains2 = 0) then []
      else (
        let (hf2,_,_,_) = fst (List.hd heap_chains2) in
        let code2 = encode_h_formula hf2 in
        let code2_len = List.length code2 in
        let fold_seq = fold_seq @ [Fold_inductive_case] in
        if (code2_len < coded_hf_len) then
          try_fold_view new_f2 base_f induct_f fold_seq
        else if (code2_len = coded_hf_len) then (
          if (equal_heap_chain_code coded_hf code2) then fold_seq
          else try_fold_view new_f2 base_f induct_f fold_seq
        )
        else if (code2_len > coded_hf_len + 1) then []
        else try_fold_view new_f2 base_f induct_f fold_seq
      )
    )
  ) in
  let induct_branches, base_branches = List.partition(fun (f, _) ->
    let hviews = CF.get_views f in
    List.exists (fun hv ->
      String.compare hv.CF.h_formula_view_name vname = 0
    ) hviews
  ) root_view.C.view_un_struc_formula in
  if (List.length base_branches != 1) || (List.length induct_branches != 1) then
    []
  else
    let base_f = fst (List.hd base_branches) in
    let induct_f = fst (List.hd induct_branches) in
    Debug.ninfo_hprint (add_str "base_f" !CF.print_formula) base_f no_pos;
    Debug.ninfo_hprint (add_str "induct_f" !CF.print_formula) induct_f no_pos;
    let view_f = (
      let args = List.map (fun sv ->
        match sv with
        | CP.SpecVar (t,_,_) -> CP.SpecVar (t, fresh_name (), Unprimed)
      ) root_view.C.view_vars in
      let pos = root_view.C.view_pos in
      let hf = CF.mkViewNode root_sv vname args pos in
      CF.formula_of_heap hf pos
    ) in 
    let fold_seq = try_fold_view view_f base_f induct_f [] in
    fold_seq

let detect_fold_sequence (hf: CF.h_formula) (root_sv: CP.spec_var)
    (root_view: C.view_decl) prog
    : fold_type list =
  let pr_hf = !CF.print_h_formula in
  let pr_vd vd = vd.C.view_name in
  let pr_sv = !CP.print_sv in
  let pr_out = pr_list print_fold_type in
  Debug.no_3 "detect_fold_sequence" pr_hf pr_sv pr_vd pr_out
      (fun _ _ _ -> detect_fold_sequence_x hf root_sv root_view prog)
      hf root_sv root_view
