open Globals
open Debug
open Gen.Basic


module C = Cast
module CP = Cpure
module CF = Cformula
module MCP = Mcpure


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
(*   let _ = CF.transform_h_formula f_hf hf in                                      *)
(*   !views                                                                         *)

(* return: (a list of atomic heap chain * the rest of hformula *)
let collect_atomic_heap_chain_x (hf: CF.h_formula) (root_view: C.view_decl) (prog: C.prog_decl)
    : (heap_chain list * CF.h_formula) =
  if ((List.length root_view.C.view_forward_ptrs > 1) || (List.length root_view.C.view_forward_fields > 1)) then
    ([], hf)
  (* consider only the case the root view has at most 1 forward pointer and at most 1 forward field *)
  else (
    let root_dname = root_view.C.view_data_name in
    let root_vname = root_view.C.view_name in
    let rec extract_atomic_chain hf = (match hf with
      | CF.DataNode dn ->
          if (eq_str dn.CF.h_formula_data_name root_dname) then (
            try 
              let fw_field = List.hd root_view.C.view_forward_fields in
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
          let vname = vn.CF.h_formula_view_name in
          let mutrec_vnames = root_view.C.view_mutual_rec_views in
          if ((eq_str vname root_vname) || (mem_str_list vname mutrec_vnames)) then (
            try 
              let fw_ptr = List.hd root_view.C.view_forward_ptrs in
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


(*
 * Find a list of heap chain starting from a root node in rhs.
 * Every nodes in the heap chain except the first node must be the data node
 * This list is ordered descendingly by the each heap chain length 
 *)
let collect_rhs_heap_chains_x (hf: CF.h_formula) (pf: MCP.mix_formula) 
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
    try (
      let next_chains, rest_chains = List.partition (fun (hf,entry_sv,last_sv,exit_sv) ->
        (CP.eq_spec_var entry_sv latest_exit) || (CP.EMapSV.mem entry_sv aliases)
      ) atomic_chains in
      let next_chain, atomic_chains = (
        match next_chains with
        | [] -> raise Not_found
        | hd::tl -> (hd, tl @ rest_chains)
      ) in
      let (next_hf, next_entry, next_last, next_exit) = next_chain in
      match next_hf with
      | CF.DataNode _ -> (
          let new_hf = CF.mkStarH latest_hf next_hf pos in
          let new_chain = (new_hf, latest_entry, next_last, next_exit) in
          let hf_rest = List.fold_left (fun hf1 (hf2,_,_,_) ->
            CF.mkStarH hf1 hf2 pos 
          ) hf_unused rest_chains in
          let built_chains = (new_chain, hf_rest) :: built_chains in
          build_heap_chains built_chains atomic_chains hf_unused
        )
      | _ -> built_chains
    ) with Not_found -> built_chains
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

let collect_rhs_heap_chains (hf: CF.h_formula) (pf: MCP.mix_formula) 
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
      (fun _ _ _ _ -> collect_rhs_heap_chains_x hf pf root_sv root_view prog)
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
  let _ = CF.transform_h_formula f_hf hf in
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
          let replacing_f = CF.rename_bound_vars fold_f in
          let replacing_f = CF.subst subs replacing_f in
          let (replacing_hf,extra_pf,_,_,_) = CF.split_components replacing_f in
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
    let (hf1,pf1,_,_,_) = CF.split_components new_f1 in
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
      let (hf2,pf2,_,_,_) = CF.split_components new_f2 in
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

(* detect the folding sequences of the root_view in order to form the hf formula *)
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

let detect_cts_fold_sequence_x (lhf: CF.h_formula) (rhf: CF.h_formula) 
    (root_sv: CP.spec_var) (root_view: C.view_decl) prog
    : fold_type list=
  let vname = root_view.C.view_name in
  Debug.ninfo_hprint (add_str "lhf" !CF.print_h_formula) lhf no_pos;
  Debug.ninfo_hprint (add_str "rhf" !CF.print_h_formula) rhf no_pos;
  let coded_lhf = encode_h_formula lhf in
  let coded_lhf_len = List.length coded_lhf in
  let rec try_fold_view (f: CF.formula) base_f induct_f fold_seq : fold_type list = (
    (* try fold base case *)
    Debug.ninfo_hprint (add_str "f" !CF.print_formula) f no_pos;
    let new_f1 = try_fold_once f root_view base_f in
    Debug.ninfo_hprint (add_str "new_f1" !CF.print_formula) new_f1 no_pos;
    let (hf1,pf1,_,_,_) = CF.split_components new_f1 in
    let heap_chains1 = collect_heap_chains hf1 pf1 root_sv root_view prog in
    let is_base_case_ok = (
      if (List.length heap_chains1 = 0) then false
      else (
        let (hf1,_,_,_) = fst (List.hd heap_chains1) in
        let code1 = encode_h_formula hf1 in
        let code1_len = List.length code1 in
        if (code1_len > coded_lhf_len) then false
        else if (code1_len < coded_lhf_len) then false
        else (equal_heap_chain_code coded_lhf code1)
      )
    ) in
    if (is_base_case_ok) then fold_seq @ [Fold_base_case]
    else (
      (* try fold inductive case *)
      let new_f2 = try_fold_once f root_view induct_f in
      Debug.ninfo_hprint (add_str "new_f2" !CF.print_formula) new_f2 no_pos;
      let (hf2,pf2,_,_,_) = CF.split_components new_f2 in
      let heap_chains2 = collect_heap_chains hf2 pf2 root_sv root_view prog in
      if (List.length heap_chains2 = 0) then []
      else (
        let (hf2,_,_,_) = fst (List.hd heap_chains2) in
        let code2 = encode_h_formula hf2 in
        let code2_len = List.length code2 in
        let fold_seq = fold_seq @ [Fold_inductive_case] in
        if (code2_len < coded_lhf_len) then
          try_fold_view new_f2 base_f induct_f fold_seq
        else if (code2_len = coded_lhf_len) then (
          if (equal_heap_chain_code coded_lhf code2) then fold_seq
          else try_fold_view new_f2 base_f induct_f fold_seq
        )
        else if (code2_len > coded_lhf_len + 1) then []
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
    let fold_seq = try_fold_view (CF.formula_of_heap rhf no_pos) base_f induct_f [] in
    fold_seq

(* 
 * detect the folding sequences of the root_view in order to form the hf formula
 * in context-sensitive approach:
 *   - RHS, consider a view followed by some nodes
 *)
let detect_cts_fold_sequence (lhf: CF.h_formula) (rhf: CF.h_formula)
    (root_sv: CP.spec_var) (root_view: C.view_decl) prog
    : fold_type list =
  let pr_hf = !CF.print_h_formula in
  let pr_vd vd = vd.C.view_name in
  let pr_sv = !CP.print_sv in
  let pr_out = pr_list print_fold_type in
  Debug.no_4 "detect_cts_fold_sequence" pr_hf pr_hf pr_sv pr_vd pr_out
      (fun _ _ _ _ -> detect_cts_fold_sequence_x lhf rhf root_sv root_view prog)
      lhf rhf root_sv root_view

(* prefix for the name of relation 'size_of_view' *)
let prefix_sizeof = "rs_"

(*
 * Compute the size relation of a view
 *)
let generate_view_size_relation_x (vdecl: C.view_decl) (prog: C.prog_decl) : C.rel_decl =
  let rec size_of_heap_chains root_sv atom_heap_chains emap pos = (
    (* the size of a heap chain contain two part:
       - the first part is number of data nodes
       - the second part is a list of predicate size *)
    try
      let root_aliases = CP.EMapSV.find_equiv_all root_sv emap in
      let next_chains, rest_chains = List.partition (fun (hf,entry_sv,_,exit_sv) ->
        (CP.eq_spec_var entry_sv root_sv) || (CP.EMapSV.mem entry_sv root_aliases)
      ) atom_heap_chains in
      let next_chain, rest_chains = (
        match next_chains with
        | [] -> raise Not_found
        | hd::tl -> (hd, tl @ rest_chains)
      ) in
      let (hf, _, _, exit_sv) = next_chain in
      let (dnode_num, size_rels, rel_vars) = size_of_heap_chains exit_sv atom_heap_chains emap pos in
      match hf with 
      | CF.DataNode _ -> (dnode_num + 1, size_rels, rel_vars)
      | CF.ViewNode vd ->
          let var_size = CP.mk_typed_spec_var Int (fresh_name ()) in
          let size_rel = (
            let rel_sv = CP.mk_typed_spec_var Int (prefix_sizeof ^ vd.CF.h_formula_view_name) in
            let rel_exp = CP.Var (var_size, pos) in
            CP.BForm ((CP.RelForm (rel_sv, [rel_exp], pos), None), None)
          ) in
          (dnode_num, size_rels @ [size_rel], rel_vars @ [var_size])
      | _ -> (dnode_num, size_rels, rel_vars)
    with Not_found -> (0, [], [])
  ) in
  let rsize_name = prefix_sizeof ^ vdecl.C.view_name in
  let rsize_var = CP.SpecVar(Int, "n", Unprimed) in
  let (view_branches, _) = List.split vdecl.C.view_un_struc_formula in
  let size_of_branches = List.map (fun f ->
    let pos = CF.pos_of_formula f in
    let (hf,pf,_,_,_) = CF.split_components f in
    let pf = MCP.pure_of_mix pf in
    let emap = CP.EMapSV.build_eset (CP.pure_ptr_equations pf) in
    let (atom_heap_chains, _) = collect_atomic_heap_chain hf vdecl prog in
    let self_typ = Named (vdecl.C.view_data_name) in
    let self_sv = CP.SpecVar (self_typ, self, Unprimed) in
    let (dnode_num, size_rels, rel_vars) = size_of_heap_chains self_sv atom_heap_chains emap pos in
    let dnode_constraint = (
      let size_sum = List.fold_left (fun e sv ->
        CP.Add (e, CP.Var (sv, pos), pos)
      ) (CP.IConst (dnode_num, pos)) rel_vars in
      CP.mkEqExp (CP.Var (rsize_var, pos)) size_sum pos
    ) in
    let size_formula = List.fold_left (fun f1 f2 ->
      CP.mkAnd f1 f2 pos
    ) dnode_constraint size_rels in
    CP.mkExists rel_vars size_formula None pos 
  ) view_branches in
  let pos = vdecl.C.view_pos in
  let rsize_formula = (
    match size_of_branches with
    | [] -> CP.mkTrue pos
    | hd::tl -> List.fold_left (fun f1 f2 -> CP.mkOr f1 f2 None pos) hd tl
  ) in
  let rel_size = {C.rel_name = rsize_name;
                  C.rel_vars = [rsize_var];
                  C.rel_formula = rsize_formula;} in
  rel_size

let generate_view_size_relation (vdecl: C.view_decl) (prog: C.prog_decl) : C.rel_decl =
  let pr_view = !C.print_view_decl in
  let pr_rel = !C.print_rel_decl in
  Debug.no_1 "generate_view_size_relation" pr_view pr_rel
      (fun _ -> generate_view_size_relation_x vdecl prog) vdecl

let update_view_size_relations (prog: C.prog_decl) : unit =
  List.iter (fun vdecl ->
    let rdecls = prog.C.prog_rel_decls in
    let rname = prefix_sizeof ^ vdecl.C.view_name in
    try let _ = C.look_up_rel_def_raw rdecls rname in ()
    with Not_found -> (
      let rel_size = generate_view_size_relation vdecl prog in
      prog.C.prog_rel_decls <- rdecls @ [rel_size];
    )
  ) prog.C.prog_view_decls


(*
 * colelct reachable pointers in a formula, starting from 'roots' nodes
 *)
let collect_reachable_pointers_in_formula_x (f: CF.formula) (roots: CP.spec_var list)
    : CP.spec_var list =
  let rec collect_helper f roots eset = (
    let (search_f, _, search_mf) = Afutil.create_default_formula_searcher () in
    let search_hf hf = (match hf with
      | CF.ViewNode vn ->
          if not (CP.mem_svl vn.CF.h_formula_view_node roots) then (Some [])
          else (
            let vars = vn.CF.h_formula_view_arguments in
            let pointers = List.filter CP.is_node_typ vars in
            let reachable_ptrs = List.concat (List.map (fun v ->
              CF.compute_equiv_closure_of_sv v eset
            ) pointers) in
            Some (CP.remove_dups_svl reachable_ptrs)
          )
      | CF.DataNode dn ->
          if not (CP.mem_svl dn.CF.h_formula_data_node roots) then (Some [])
          else (
            let vars = dn.CF.h_formula_data_arguments in
            let pointers = List.filter CP.is_node_typ vars in
            let reachable_ptrs = List.concat (List.map (fun v ->
              CF.compute_equiv_closure_of_sv v eset
            ) pointers) in
            Some (CP.remove_dups_svl reachable_ptrs)
          )
      | _ -> None
    ) in
    let searcher = (search_f, search_hf, search_mf) in
    let reachable_ptrs = Afutil.search_in_formula searcher f in
    let reachable_ptrs = CP.remove_dups_svl (roots @ reachable_ptrs) in
    if (List.length reachable_ptrs != List.length roots) then
      collect_helper f reachable_ptrs eset
    else roots
  ) in
  (* return *)
  let eset = CF.build_eset_of_formula f in
  collect_helper f roots eset


let collect_reachable_pointers_in_formula (f: CF.formula) (roots: CP.spec_var list)
    : CP.spec_var list =
  let pr_f = (add_str "f" !CF.print_formula) in
  let pr_roots = (add_str "roots" !CP.print_svl) in
  let pr_res = (add_str "res" !CP.print_svl) in
  Debug.no_2 "collect_reachable_pointers_in_formula" pr_f pr_roots pr_res
      (fun _ _ -> collect_reachable_pointers_in_formula_x f roots) f roots

(*
 * - bound pointers are the pointers of view (or view arguments) which can
 *   be reached from the root node of view
 *)

let compute_bound_pointers_of_view_x (vdecl: C.view_decl) : CP.spec_var list =
  let root = C.get_view_root vdecl in
  let bound_pointers = List.concat (List.map (fun (f,_) ->
    let eset = CF.build_eset_of_formula f in
    let reachable_ptrs = collect_reachable_pointers_in_formula f [root] in
    (* compute list of view vars can be reached from root by this view formula *)
    List.filter (fun vvar ->
      if not (CP.is_node_typ vvar) then false
      else
        let equiv_svl = CF.compute_equiv_closure_of_sv vvar eset in
        CP.EMapSV.overlap reachable_ptrs equiv_svl
    ) vdecl.C.view_vars
  ) vdecl.C.view_un_struc_formula ) in
  CP.remove_dups_svl bound_pointers


let compute_bound_pointers_of_view (vdecl: C.view_decl) : CP.spec_var list =
  let pr_v = (add_str "view" !C.print_view_decl_short) in
  let pr_res = (add_str "res" !CP.print_svl) in
  Debug.no_1 "compute_bound_pointers_of_view" pr_v pr_res
      (fun _ -> compute_bound_pointers_of_view_x vdecl) vdecl

(*
 * Compute head node of main heap chain in a branch formula of a view declaration.
 * Head nodes are the node pointed by "self" (root node)
 *)
let rec compute_head_nodes_of_formula_x  (f: CF.formula) : CF.h_formula list =
  let (search_f, _, search_mf) = Afutil.create_default_formula_searcher () in
  let search_hf hf = (match hf with
    | CF.ViewNode vn ->
        let name = CP.name_of_sv vn.CF.h_formula_view_node in
        if (eq_str name self) then Some [hf]
        else Some []
    | CF.DataNode dn ->
        let name = CP.name_of_sv dn.CF.h_formula_data_node in
        if (eq_str name self) then Some [hf]
        else Some []
    | _ -> None
  ) in
  let search_head = (search_f, search_hf, search_mf) in
  Afutil.search_in_formula search_head f


and compute_head_nodes_of_formula (f: CF.formula) : CF.h_formula list =
  let pr_f = (add_str "f" !CF.print_formula) in
  let pr_res = (add_str "res" (pr_list !CF.print_h_formula)) in
  Debug.no_1 "compute_head_nodes_of_formula" pr_f pr_res
      (fun _ -> compute_head_nodes_of_formula_x f) f


(*
 * Compute body nodes of main heap chain in a branch formula of a view declaration.
 * Body nodes are nodes which can be reached from root, 
 * and also starting from them can reach bound pointers of view
 *)
let rec compute_body_nodes_of_formula_x (f: CF.formula) (vdecl: C.view_decl)
    : CF.h_formula list =
  let root = C.get_view_root vdecl in
  let reachable_ptrs = collect_reachable_pointers_in_formula f [root] in
  let reachable_ptrs = List.filter (fun sv ->
    not (CP.eq_spec_var sv root)
  ) reachable_ptrs in
  (* binfo_hprint (add_str "reachable_ptrs" !CP.print_svl ) reachable_ptrs no_pos; *)
  let (search_f, _, search_mf) = Afutil.create_default_formula_searcher () in
  let search_hf hf = (match hf with
    | CF.ViewNode vn ->
        let vnode = vn.CF.h_formula_view_node in
        if (CP.mem_svl vnode reachable_ptrs) then
          let rch_ptrs = collect_reachable_pointers_in_formula f [vnode] in
          if (CP.is_intersected_svl rch_ptrs vdecl.C.view_bound_pointers) then
            Some [hf]
          else Some []
        else Some []
    | CF.DataNode dn ->
        let dnode = dn.CF.h_formula_data_node in
        if (CP.mem_svl dnode reachable_ptrs) then
          let rch_ptrs = collect_reachable_pointers_in_formula f [dnode] in
          if (CP.is_intersected_svl rch_ptrs vdecl.C.view_bound_pointers) then
            Some [hf]
          else Some []
        else Some []
    | _ -> None
  ) in
  let search_bodies = (search_f, search_hf, search_mf) in
  Afutil.search_in_formula search_bodies f


and compute_body_nodes_of_formula (f: CF.formula) (vdecl: C.view_decl)
    : CF.h_formula list =
  let pr_f = (add_str "f" !CF.print_formula) in
  let pr_v = (add_str "vdecl" C.name_of_view) in
  let pr_res = (add_str "res" (pr_list !CF.print_h_formula)) in
  Debug.no_2 "compute_body_nodes_of_formula" pr_f pr_v pr_res
      (fun _ _ -> compute_body_nodes_of_formula_x f vdecl) f vdecl


(* 
  let compute_direction_info_of_view (vdecl: C.view_decl)  = 
   - base case, inductive case, inductive instantiated case.
*)

type direction_pointer_t = (string * CP.spec_var)
type direction_field_t = (string * ident)


(*
 * Collect forward, backward information from a formula by considering the
 * connection between head and body nodes
 * find forward info: head_nodes --> body_nodes
 * find backward info: body_nodes --> head_nodes
 *)
let compute_direction_info_from_formula_x (f: CF.formula)
    (head_nodes: CF.h_formula list) (body_nodes: CF.h_formula list)
    (data_decls: C.data_decl list) (view_decls: C.view_decl list)
    : direction_pointer_t list * direction_field_t list
      * direction_pointer_t list * direction_field_t list =
  let eset = CF.build_eset_of_formula f in
  let fwps, fwfs, bwps, bwfs = ref [], ref [], ref [], ref [] in
  (* forward fields or pointers: connect directly head nodes to body nodes *)
  let body_ptrs = List.map CF.get_node_var body_nodes in 
  List.iter (fun node -> match node with
    | CF.ViewNode vn ->
        let view_name = vn.CF.h_formula_view_name in
        let view_decl = C.look_up_view_def_raw 0 view_decls view_name in
        List.iter2 (fun vn_arg view_var ->
          let vn_arg_closure = CF.compute_equiv_closure_of_sv vn_arg eset in
          if (CP.is_intersected_svl vn_arg_closure body_ptrs) then (
            let is_existing_fwp = List.exists (fun (x,y) ->
              (eq_str view_name x) && (CP.eq_spec_var y view_var)
            ) !fwps in
            if not is_existing_fwp then
              fwps := !fwps @ [(view_name, view_var)]
          );
        ) vn.CF.h_formula_view_arguments view_decl.C.view_vars
    | CF.DataNode dn ->
        let data_name = dn.CF.h_formula_data_name in
        let data_decl = C.look_up_data_def_raw data_decls data_name in
        List.iter2 (fun dn_arg ((_,field_name),_) ->
          let dn_arg_closure = CF.compute_equiv_closure_of_sv dn_arg eset in
          if (CP.is_intersected_svl dn_arg_closure body_ptrs) then (
            let is_existing_fwf = List.exists (fun (x,y) ->
              (eq_str data_name x) && (eq_str y field_name)
            ) !fwfs in
            if not is_existing_fwf then
              fwfs := !fwfs @ [(data_name, field_name)]
          )
        ) dn.CF.h_formula_data_arguments data_decl.C.data_fields
    | _ -> ()
  ) head_nodes;
  (* backward fields or pointers: connect directly body nodes to head nodes *)
  let head_ptrs = List.map CF.get_node_var head_nodes in 
  List.iter (fun node -> match node with
    | CF.ViewNode vn ->
        let view_name = vn.CF.h_formula_view_name in
        let view_decl = C.look_up_view_def_raw 0 view_decls view_name in
        List.iter2 (fun vn_arg view_var ->
          let vn_arg_closure = CF.compute_equiv_closure_of_sv vn_arg eset in
          if (CP.is_intersected_svl vn_arg_closure head_ptrs) then (
            let is_existing_bwp = List.exists (fun (x,y) ->
              (eq_str view_name x) && (CP.eq_spec_var y view_var)
            ) !bwps in
            if not is_existing_bwp then
              bwps := !bwps @ [(view_name, view_var)]
          );
        ) vn.CF.h_formula_view_arguments view_decl.C.view_vars
    | CF.DataNode dn ->
        let data_name = dn.CF.h_formula_data_name in
        let data_decl = C.look_up_data_def_raw data_decls data_name in
        List.iter2 (fun dn_arg ((_,field_name),_) ->
          let dn_arg_closure = CF.compute_equiv_closure_of_sv dn_arg eset in
          if (CP.is_intersected_svl dn_arg_closure head_ptrs) then (
            let is_existing_bwf = List.exists (fun (x,y) ->
              (eq_str data_name x) && (eq_str y field_name)
            ) !bwfs in
            if not is_existing_bwf then
              bwfs := !bwfs @ [(data_name, field_name)]
          )
        ) dn.CF.h_formula_data_arguments data_decl.C.data_fields
    | _ -> ()
  ) body_nodes;
  (* return *)
  (!fwps, !fwfs, !bwps, !bwfs)


let compute_direction_info_from_formula (f: CF.formula)
    (head_nodes: CF.h_formula list) (body_nodes: CF.h_formula list)
    (data_decls: C.data_decl list) (view_decls: C.view_decl list)
    : direction_pointer_t list * direction_field_t list
      * direction_pointer_t list * direction_field_t list =
  let pr_f = (add_str "f" !CF.print_formula) in
  let pr_head = (add_str "head_nodes" (pr_list !CF.print_h_formula)) in
  let pr_body = (add_str "body_nodes" (pr_list !CF.print_h_formula)) in
  let pr_pointers = pr_list (fun (vn,sv) -> vn^"."^(!CP.print_sv sv)) in
  let pr_fields = pr_list (fun (dn,fn) -> dn^"."^fn) in
  let pr_res = (
    add_str "res"
      (fun (fwps,fwfs,bwps,bwfs) -> 
        "fwps: " ^ (pr_pointers fwps) ^ "; fwfs: " ^ (pr_fields fwfs)
        ^ "; bwps: " ^ (pr_pointers bwps) ^ "; bwfs: " ^ (pr_fields bwfs))
  ) in
  Debug.no_3 "compute_direction_info_from_formula" pr_f pr_head pr_body pr_res
      (fun _ _ _ -> compute_direction_info_from_formula_x f
                      head_nodes body_nodes data_decls view_decls)
      f head_nodes body_nodes


let get_view_base_branches_x (vdecl: C.view_decl) : CF.formula list =
  let rec_view_names = (vdecl.C.view_mutual_rec_views @ [vdecl.C.view_name]) in
  let branches = fst (List.split vdecl.C.view_un_struc_formula) in 
  List.filter (fun f ->
    let used_vnodes = CF.get_view_nodes f in
    let used_vnodes_names = List.map CF.get_node_name used_vnodes in
    not (is_intersected_str_list rec_view_names used_vnodes_names)
  ) branches


let get_view_base_branches (vdecl: C.view_decl) : CF.formula list =
  let pr_v = (add_str "view" C.name_of_view) in
  let pr_res = (add_str "result" (pr_list !CF.print_formula)) in
  Debug.no_1 "get_view_base_branches" pr_v pr_res
      (fun _ -> get_view_base_branches_x vdecl) vdecl


let get_view_all_branches (vdecl: C.view_decl) : CF.formula list =
  let branches = fst (List.split vdecl.C.view_un_struc_formula) in 
  branches


let get_view_inductive_branches_x (vdecl: C.view_decl) : CF.formula list =
  let rec_view_names = (vdecl.C.view_mutual_rec_views @ [vdecl.C.view_name]) in
  let branches = fst (List.split vdecl.C.view_un_struc_formula) in
  List.filter (fun f ->
    let used_vnodes = CF.get_view_nodes f in
    let used_vnodes_names = List.map CF.get_node_name used_vnodes in
    (is_intersected_str_list rec_view_names used_vnodes_names)
  ) branches


let get_view_inductive_branches (vdecl: C.view_decl) : CF.formula list =
  let pr_v = (add_str "view" C.name_of_view) in
  let pr_res = (add_str "result" (pr_list !CF.print_formula)) in
  Debug.no_1 "get_view_inductive_branches" pr_v pr_res
      (fun _ -> get_view_inductive_branches_x vdecl) vdecl


(* unfold the occurences of a view in a formula by its base case *)
let rec do_unfold_view_base_case_x (f: CF.formula) (vd: C.view_decl)
    : CF.formula list =
  let view_name = vd.C.view_name in
  let base_fs = get_view_base_branches vd in
  let (trans_s, trans_f, _, _) = CF.create_default_formula_transformer true in
  let trans_p = CP.create_default_formula_transformer false in
  List.map (fun base_f ->
    let extra_pure = ref [] in
    let trans_h hf = (match hf with
      | CF.ViewNode vn when (eq_str view_name vn.CF.h_formula_view_name) ->
          (* replace this view node by base formula *)
          (* step 1: collect substitution of view root and vars *)
          let subs_view = (
            let view_root = C.get_view_root vd in
            let subs_root = (view_root, vn.CF.h_formula_view_node) in
            List.fold_left2 (fun subs vvar harg ->
              subs @ [(vvar, harg)]
            ) [subs_root] vd.C.view_vars vn.CF.h_formula_view_arguments 
          ) in
          (* step 2: collect substitution of quantified vars in base_f *)
          let subs_quant_vars = match base_f with
            | CF.Exists fe ->
                let quant_vars = fe.CF.formula_exists_qvars in
                List.map (fun sv -> match sv with
                  | CP.SpecVar (t,n,p) -> 
                      let new_sv = CP.SpecVar (t,fresh_any_name n,p) in
                      (sv, new_sv)
                ) quant_vars
            | _ -> []
          in
          (* step 3: build new formula by substitution, replace this view node
             by h_formula and save pure formula to add later *)
          let subs = subs_view @ subs_quant_vars in
          let replacing_f = CF.subst_one_by_one subs base_f in
          let (replacing_hf,extra_pf,_,_,_) = CF.split_components replacing_f in
          let extra_qvars = CF.get_exists replacing_f in
          extra_pure := !extra_pure @ [(extra_pf, extra_qvars)];
          Some replacing_hf                  (* replace the heap part *)
      | _ -> None) in
    let transformer = (trans_s, trans_f, trans_h, trans_p) in
    let new_f = CF.transform_formula transformer f in
    let pos = CF.pos_of_formula new_f in
    let new_f = List.fold_left (fun f (mf,qv) ->
      let nf = CF.mkAnd_pure f mf pos in       (* add the pure part back *)
      CF.push_exists qv nf
    ) new_f !extra_pure in
    new_f
  ) base_fs


and do_unfold_view_base_case (f: CF.formula) (vd: C.view_decl)
    : CF.formula list =
  let pr_f = (add_str "f" !CF.print_formula) in
  let pr_v = (add_str "view" C.name_of_view) in
  let pr_res = (add_str "res" (pr_list !CF.print_formula)) in
  Debug.no_2 "do_unfold_view_base_case" pr_f pr_v pr_res
      (fun _ _ -> do_unfold_view_base_case_x f vd) f vd


let get_view_inductive_branches_unfolded_by_base_case_x (vdecl: C.view_decl)
    (view_decls: C.view_decl list)
    : CF.formula list =
  let rec_view_names = (vdecl.C.view_mutual_rec_views @ [vdecl.C.view_name]) in
  let inductive_branches = get_view_inductive_branches vdecl in
  List.concat (
    List.map (fun inductive_f ->
      let used_vnodes = CF.get_view_nodes inductive_f in
      let used_vnode_names = List.map CF.get_node_name used_vnodes in
      let unfold_vnode_names = intersect_str_list used_vnode_names rec_view_names in
      let unfold_vnode_names = remove_dups_str_list unfold_vnode_names in
      let unfold_vdecls = List.map (fun s ->
        C.look_up_view_def_raw 0 view_decls s
      ) unfold_vnode_names in
      List.fold_left (fun fs vd ->
        List.concat (
          List.map (fun f ->
            do_unfold_view_base_case f vd
          ) fs
        )
      ) [inductive_f] unfold_vdecls
    ) inductive_branches
  )


let get_view_inductive_branches_unfolded_by_base_case (vdecl: C.view_decl)
    (view_decls: C.view_decl list)
    : CF.formula list =
  let pr_v = (add_str "view name" C.name_of_view) in
  let pr_res = (add_str "res" (pr_list !CF.print_formula)) in
  Debug.no_1 "get_view_inductive_branches_unfolded_by_base_case" pr_v pr_res
      (fun _ -> get_view_inductive_branches_unfolded_by_base_case_x vdecl view_decls)
      vdecl


(* check if sv is a direction pointer of a view *)
let is_view_direction_pointer (sv: CP.spec_var) (vdecl: C.view_decl) =
  (CP.mem_svl sv vdecl.C.view_backward_ptrs)
  || (CP.mem_svl sv vdecl.C.view_forward_ptrs)


let is_view_direction_field (field_name: ident) (vdecl: C.view_decl) =
  (mem_str_list field_name vdecl.C.view_backward_fields)
  || (mem_str_list field_name vdecl.C.view_forward_fields)


(*
 * Based on existing direction info in view, do widening to collect more 
 * direction info
 *)
let compute_direction_info_from_view_x (vdecl: C.view_decl)
    (f: CF.formula) (head_and_body_nodes: CF.h_formula list)
    (data_decls: C.data_decl list) (view_decls: C.view_decl list)
    : direction_pointer_t list * direction_field_t list
      * direction_pointer_t list * direction_field_t list =
  let eset = CF.build_eset_of_formula f in
  let fwps, fwfs, bwps, bwfs = ref [], ref [], ref [], ref [] in
  List.iter (fun node -> match node with
    | CF.ViewNode vn ->
        let view_name = vn.CF.h_formula_view_name in
        let vd = C.look_up_view_def_raw 0 view_decls view_name in
        List.iter2 (fun harg vvar ->
          if not (is_view_direction_pointer vvar vd) then (
            let harg_closure = CF.compute_equiv_closure_of_sv harg eset in
            if (CP.is_intersected_svl harg_closure vdecl.C.view_forward_ptrs) then
              fwps := !fwps @ [(view_name, vvar)]
            else if (CP.is_intersected_svl harg_closure vdecl.C.view_backward_ptrs) then
              bwps := !bwps @ [(view_name, vvar)]
          )
        ) vn.CF.h_formula_view_arguments vd.C.view_vars
    | CF.DataNode dn ->
        let data_name = dn.CF.h_formula_data_name in
        let dd = C.look_up_data_def_raw data_decls data_name in
        List.iter2 (fun harg field ->
          let ((_, fname), _) = field in
          if not (is_view_direction_field fname vdecl) then (
            let harg_closure = CF.compute_equiv_closure_of_sv harg eset in
            let harg_closure_names = List.map CP.name_of_sv harg_closure in
            if (is_intersected_str_list harg_closure_names vdecl.C.view_forward_fields) then
              fwfs := !fwfs @ [(data_name, fname)]
            else if (is_intersected_str_list harg_closure_names vdecl.C.view_backward_fields) then
              bwfs := !bwfs @ [(data_name, fname)]
          )
        ) dn.CF.h_formula_data_arguments dd.C.data_fields
    | _ -> ()
  ) head_and_body_nodes;
  (* return *)
  (!fwps, !fwfs, !bwps, !bwfs)


let compute_direction_info_from_view (vdecl: C.view_decl)
    (f: CF.formula) (head_and_body_nodes: CF.h_formula list)
    (data_decls: C.data_decl list) (view_decls: C.view_decl list)
    : direction_pointer_t list * direction_field_t list
      * direction_pointer_t list * direction_field_t list =
  let pr_v = (add_str "view" C.name_of_view) in
  let pr_f = (add_str "f" !CF.print_formula) in
  let pr_pointers = pr_list (fun (vn,sv) -> vn^"."^(!CP.print_sv sv)) in
  let pr_fields = pr_list (fun (dn,fn) -> dn^"."^fn) in
  let pr_res = (
    add_str "res"
      (fun (fwps,fwfs,bwps,bwfs) -> 
        "fwps: " ^ (pr_pointers fwps) ^ "; fwfs: " ^ (pr_fields fwfs)
        ^ "; bwps: " ^ (pr_pointers bwps) ^ "; bwfs: " ^ (pr_fields bwfs))
  ) in
  Debug.no_2 "compute_direction_info_from_view" pr_v pr_f pr_res
      (fun _ _ -> compute_direction_info_from_view_x vdecl f head_and_body_nodes
                      data_decls view_decls)
      vdecl f

let remove_dups_direction_pointers (pointers: direction_pointer_t list)
    : direction_pointer_t list =
  List.fold_left (fun refined_pointers p ->
    let (view_name, view_var) = p in
    let is_added = List.exists (fun (x,y) ->
      (eq_str view_name x) && (CP.eq_spec_var view_var y)
    ) refined_pointers in
    if (is_added) then refined_pointers
    else refined_pointers @ [p]
  ) [] pointers


let remove_dups_direction_fields (fields: direction_field_t list)
    : direction_field_t list =
  List.fold_left (fun refined_fields f ->
    let (data_name, field_name) = f in
    let is_added = List.exists (fun (x,y) ->
      (eq_str data_name x) && (eq_str field_name y)
    ) refined_fields in
    if (is_added) then refined_fields
    else refined_fields @ [f]
  ) [] fields


let string_of_view_direction_info (vdecl: C.view_decl) =
  let dn = vdecl.C.view_data_name in
  "  view name: " ^ vdecl.C.view_name ^ "\n"
      ^ "    forward ptrs: "
      ^ (pr_list !CP.print_sv vdecl.C.view_forward_ptrs) ^ "\n"
      ^ "    forward fields: "
      ^ (pr_list (fun fn -> dn^"."^fn) vdecl.C.view_forward_fields) ^ "\n"
      ^ "    backward ptrs: "
      ^ (pr_list !CP.print_sv vdecl.C.view_backward_ptrs) ^ "\n"
      ^ "    backward fields: "
      ^ (pr_list (fun fn -> dn^"."^fn) vdecl.C.view_backward_fields) ^ "\n"


(* compute direction info of all views *)
let compute_direction_info_of_views_x (view_decls: C.view_decl list)
    (data_decls: C.data_decl list)
    : C.view_decl list =
  (* init information by computing between head and body nodes *)
  let init_view_direction_info vdecls = (
    (* compute direction info by considering connection between head and body nodes *) 
    let (fwps, fwfs, bwps, bwfs) = List.fold_left (fun (a1,b1,c1,d1) vdecl ->
      let branches = get_view_all_branches vdecl in
      let fs = get_view_inductive_branches_unfolded_by_base_case vdecl view_decls in
      let all_fs = branches @ fs in
      let (a2,b2,c2,d2) = List.fold_left (fun (x1,y1,z1,t1) f ->
        let head_nodes = compute_head_nodes_of_formula f in
        let body_nodes = compute_body_nodes_of_formula f vdecl in
        let (x2,y2,z2,t2) = compute_direction_info_from_formula f head_nodes
            body_nodes data_decls view_decls in
        (x1@x2, y1@y2, z1@z2, t1@t2)
      ) ([],[],[],[]) all_fs in
      (a1@a2, b1@b2, c1@c2, d1@d2)
    ) ([], [], [], []) vdecls in
    (* update to view *)
    List.map (fun vd ->
      let fwps = List.filter (fun (vn,_) -> eq_str vn vd.C.view_name) fwps in
      let bwps = List.filter (fun (vn,_) -> eq_str vn vd.C.view_name) bwps in
      let fwfs = List.filter (fun (dn,_) -> eq_str dn vd.C.view_data_name) fwfs in
      let bwfs = List.filter (fun (dn,_) -> eq_str dn vd.C.view_data_name) bwfs in
      let new_fwps = snd (List.split fwps) in
      let new_fwps = CP.remove_dups_svl (new_fwps @ vd.C.view_forward_ptrs) in
      let new_bwps = snd (List.split bwps) in
      let new_bwps = CP.remove_dups_svl (new_bwps @ vd.C.view_backward_ptrs) in
      let new_fwfs = snd (List.split fwfs) in
      let new_fwfs = remove_dups_str_list (new_fwfs @ vd.C.view_forward_fields) in
      let new_bwfs = snd (List.split bwfs) in
      let new_bwfs = remove_dups_str_list (new_bwfs @ vd.C.view_backward_fields) in
      { vd with C.view_forward_ptrs = new_fwps;
                C.view_forward_fields = new_fwfs;
                C.view_backward_ptrs = new_bwps;
                C.view_backward_fields = new_bwfs; }
    ) vdecls
  ) in

  (* aggregating direction info to formula to find all possible direction info *)
  let rec widen_view_direction_info vdecls = (
    let (fwps, fwfs, bwps, bwfs) = List.fold_left (fun (a1,b1,c1,d1) vdecl ->
      (* compute direction info by aggregating info from view to formula *) 
      let branches = get_view_all_branches vdecl in
      let fs = get_view_inductive_branches_unfolded_by_base_case vdecl view_decls in
      let all_fs = branches @ fs in
      let (a2,b2,c2,d2) = List.fold_left (fun (x1,y1,z1,t1) f ->
        let head_and_body_nodes = (compute_head_nodes_of_formula f)
            @ (compute_body_nodes_of_formula f vdecl) in
        let (x2,y2,z2,t2) = compute_direction_info_from_view vdecl f 
            head_and_body_nodes data_decls view_decls in
        (x1@x2, y1@y2, z1@z2, t1@t2)
      ) ([],[],[],[]) all_fs in
      (a1@a2, b1@b2, c1@c2, d1@d2)
    ) ([], [], [], []) vdecls in
    (* update to view *)
    let need_widen_again = ref false in
    let new_vdecls = List.map (fun vd ->
      let fwps = List.filter (fun (vn,_) -> eq_str vn vd.C.view_name) fwps in
      let bwps = List.filter (fun (vn,_) -> eq_str vn vd.C.view_name) bwps in
      let fwfs = List.filter (fun (dn,_) -> eq_str dn vd.C.view_data_name) fwfs in
      let bwfs = List.filter (fun (dn,_) -> eq_str dn vd.C.view_data_name) bwfs in
      let new_fwps = snd (List.split fwps) in
      let new_fwps = CP.remove_dups_svl (new_fwps @ vd.C.view_forward_ptrs) in
      let new_bwps = snd (List.split bwps) in
      let new_bwps = CP.remove_dups_svl (new_bwps @ vd.C.view_backward_ptrs) in
      let new_fwfs = snd (List.split fwfs) in
      let new_fwfs = remove_dups_str_list (new_fwfs @ vd.C.view_forward_fields) in
      let new_bwfs = snd (List.split bwfs) in
      let new_bwfs = remove_dups_str_list (new_bwfs @ vd.C.view_backward_fields) in
      need_widen_again :=
          (List.length new_fwps > List.length vd.C.view_forward_ptrs)
          || (List.length new_fwfs > List.length vd.C.view_forward_fields)
          || (List.length new_bwps > List.length vd.C.view_backward_ptrs)
          || (List.length new_bwfs > List.length vd.C.view_backward_fields);
      { vd with C.view_forward_ptrs = new_fwps;
                C.view_forward_fields = new_fwfs;
                C.view_backward_ptrs = new_bwps;
                C.view_backward_fields = new_bwfs; }
    ) vdecls in
    Debug.ninfo_hprint (add_str "view info 2" 
        (pr_list string_of_view_direction_info)) new_vdecls no_pos;
    if (!need_widen_again) then widen_view_direction_info new_vdecls
    else new_vdecls
  ) in

  (* do fixpoint computation to find direction info in all views *)
  let new_vdecls = init_view_direction_info view_decls in
  Debug.ninfo_hprint (add_str "view info 1"
      (pr_list string_of_view_direction_info)) new_vdecls no_pos;
  widen_view_direction_info new_vdecls 


let compute_direction_info_of_views (view_decls: C.view_decl list)
    (data_decls: C.data_decl list)
    : C.view_decl list =
  let pr_vs = (add_str "views" (pr_list C.name_of_view)) in
  let pr_res = (add_str "res" (pr_list_ln string_of_view_direction_info)) in
  Debug.no_1 "compute_direction_info_of_views" pr_vs pr_res
      (fun _ -> compute_direction_info_of_views_x view_decls data_decls)
      view_decls

(*
 * A formula is well-formed iff all of its heap nodes must
 * be reached from root pointers
 *)
let check_well_formed_formula_x (f: CF.formula) (roots: CP.spec_var list) : bool =
  let rec get_unreached_nodes_x nodes reached_ptrs eset : CF.h_formula list = (
    (* compute reached and unreached nodes *)
    let (reached_nodes, unreached_nodes) = List.partition (fun hf ->
      match hf with
      | CF.ViewNode vn -> 
          let vnode = vn.CF.h_formula_view_node in
          let vnode_equiv_svl = CF.compute_equiv_closure_of_sv vnode eset in
          (CP.EMapSV.overlap vnode_equiv_svl reached_ptrs)
      | CF.DataNode dn -> 
          let dnode = dn.CF.h_formula_data_node in
          let dnode_equiv_svl = CF.compute_equiv_closure_of_sv dnode eset in
          (CP.EMapSV.overlap dnode_equiv_svl reached_ptrs)
      | _ -> report_error no_pos "check_well_formed_formula_x: unexpected node"
    ) nodes in
    (* update reached pointers *)
    let new_reached_ptrs = List.flatten (List.map (fun node ->
      match node with
      | CF.ViewNode vn -> vn.CF.h_formula_view_arguments
      | CF.DataNode dn -> dn.CF.h_formula_data_arguments
      | _ -> report_error no_pos "check_well_formed_formula_x: unexpected node"
    ) reached_nodes) in
    let new_reached_ptrs = CP.remove_dups_svl (reached_ptrs @ new_reached_ptrs) in
    if (List.length new_reached_ptrs != List.length reached_ptrs) then
      get_unreached_nodes unreached_nodes new_reached_ptrs eset
    else unreached_nodes
  )
  and get_unreached_nodes nodes reached_ptrs emap = (
    let pr_nodes = (add_str "nodes" (pr_list !CF.print_h_formula)) in
    let pr_ptrs = (add_str "reached_ptrs" !CP.print_svl) in
    let pr_res = (add_str "res" (pr_list !CF.print_h_formula)) in
    Debug.no_2 "get_unreached_nodes"
        pr_nodes pr_ptrs pr_res
        (fun _ _ -> get_unreached_nodes_x nodes reached_ptrs emap) nodes reached_ptrs
  ) in
  let eset = CF.build_eset_of_formula f in
  let nodes = (CF.get_vnodes f) @ (CF.get_dnodes f) in 
  let unreached_nodes = get_unreached_nodes nodes roots eset in
  (* a formula is well-formed if all nodes are reached from the root *)
  (List.length unreached_nodes == 0)


let check_well_formed_formula (f: CF.formula) (roots: CP.spec_var list) : bool =
  let pr_f = (add_str "f" !CF.print_formula) in
  let pr_roots = (add_str "roots" !CP.print_svl) in
  let pr_res = (add_str "res" string_of_bool) in
  Debug.no_2 "check_well_formed_formula" pr_f pr_roots pr_res
      (fun _ _ -> check_well_formed_formula_x f roots) f roots


let rec check_well_formed_struc_formula_x (sf: CF.struc_formula)
    (roots: CP.spec_var list)
    : bool =
  match sf with
  | CF.EList sf_list ->
      List.for_all (fun (_,sf) -> check_well_formed_struc_formula sf roots) sf_list
  | CF.ECase scf ->
      List.for_all (fun (_,sf) ->
        check_well_formed_struc_formula sf roots
      ) scf.CF.formula_case_branches
  | CF.EBase sbf -> (
      if not (check_well_formed_formula sbf.CF.formula_struc_base roots) then false
      else match sbf.CF.formula_struc_continuation with
        | None -> true
        | Some sf -> (check_well_formed_struc_formula sf roots)
    )
  | CF.EAssume af ->
      check_well_formed_struc_formula af.CF.formula_assume_struc roots
  | CF.EInfer sif ->
      check_well_formed_struc_formula sif.CF.formula_inf_continuation roots


and check_well_formed_struc_formula (sf: CF.struc_formula)
    (roots: CP.spec_var list)
    : bool =
  let pr_sf = (add_str "struc_formula" !CF.print_struc_formula) in
  let pr_roots = (add_str "roots" !CP.print_svl) in
  let pr_res = (add_str "res" string_of_bool) in
  Debug.no_2 "check_well_formed_struc_formula" pr_sf pr_roots pr_res
      (fun _ _ -> check_well_formed_struc_formula_x sf roots) sf roots


(*
 * A view is well-founded iff:
 *   - All of its heap noes must be accessible from the root.
 *   - In each branch of its definition, this view recurs at most 1 node
 *   (including mutually recursive case)
 * 
 * TODO:
 *   - recursive view
 *)
let check_well_founded_view_x (vdecl: C.view_decl) : bool =
  let root = C.get_view_root vdecl in
  if not (check_well_formed_struc_formula vdecl.C.view_formula [root]) then false
  else (
    let rec_names = vdecl.C.view_name::vdecl.C.view_mutual_rec_views in
    let rec_names = remove_dups_str_list rec_names in
    List.for_all (fun (f, _) ->
      let view_nodes = CF.get_views f in
      let rec_nodes = List.filter (fun vn -> 
        List.exists (fun s ->
          (String.compare s vn.CF.h_formula_view_name == 0)
        ) rec_names
      ) view_nodes in
      (List.length rec_nodes <= 1)
    ) vdecl.C.view_un_struc_formula
  )


let check_well_founded_view (vdecl: C.view_decl) : bool =
  let pr_view = !C.print_view_decl in
  let pr_res = string_of_bool in
  Debug.no_1 "check_well_founded_view" pr_view pr_res
    (fun _ -> check_well_founded_view_x vdecl) vdecl


(*
 * Idea:
 *   - find 
 *)


(*
 * Extract main heap chain of a formula
 *)
(* TODO *)
(* let extract_main_heap_chain (f: CF.formula) (root: CP.spec_var) (vdecl: C.view_decl) *)
(*     : CF.formula =                                                                   *)
(*   let fwd_fields = vdecl.C.view_forward_fields in                                    *)
(*   let fwd_ptrs = vdecl.C.view_forward_ptrs in                                        *)


(*
 * related vars: vars which are under some constraints which involve root vars
 * consider only pointer vars
 * note: no need to use emap
 *)
let collect_related_vars_in_formula_x (f: CF.formula) (roots: CP.spec_var list)
    : CP.spec_var list =
  let rec collect_helper f roots = (
    let related_vars = ref roots in
    let trans_ef, trans_f = (fun _ -> None), (fun _ -> None) in
    let trans_hf hf = ( 
      let hf_args = (match hf with
        | CF.ViewNode vn ->
            if not (CP.mem_svl vn.CF.h_formula_view_node !related_vars) then []
            else vn.CF.h_formula_view_arguments
        | CF.DataNode dn ->
            if not (CP.mem_svl dn.CF.h_formula_data_node !related_vars) then []
            else dn.CF.h_formula_data_arguments
        | _ -> []
      ) in
      let pointers = List.filter (fun arg ->
        let typ = CP.type_of_spec_var arg in
        (Globals.is_pointer typ)
      ) hf_args in 
      let _ = (if List.length pointers > 0 then
        (* update related vars *)
        related_vars := CP.remove_dups_svl (!related_vars @ pointers)
      ) in
      None
    ) in
    let trans_m, trans_a = (fun mp -> Some mp), (fun a -> Some a) in
    let trans_pf, trans_e = (fun pf -> Some pf), (fun e -> Some e) in
    let trans_bf bf = (
      let svs = CP.bfv bf in
      let _ = (if (CP.EMapSV.overlap svs !related_vars) then
        (* update related vars *)
        related_vars := CP.remove_dups_svl (!related_vars @ svs)
      ) in
      Some bf
    ) in
    let trans_func = (trans_ef, trans_f, trans_hf,
        (trans_m, trans_a, trans_pf, trans_bf, trans_e)) in
    let _ = CF.transform_formula trans_func f in
    if (List.length !related_vars = List.length roots) then
      roots
    else collect_helper f !related_vars
  ) in
  
  collect_helper f roots


let collect_related_vars_in_formula (f: CF.formula) (roots: CP.spec_var list)
    : CP.spec_var list =
  let pr_f = (add_str "f" !CF.print_formula) in
  let pr_roots = (add_str "roots" !CP.print_svl) in
  let pr_res = (add_str "res" !CP.print_svl) in
  Debug.no_2 "collect_related_vars_in_formula" pr_f pr_roots pr_res
      (fun _ _ -> collect_related_vars_in_formula_x f roots) f roots


(* simplify formulate by removing true, false, HEmp... constants *)
let simplify_formula (f: CF.formula) : CF.formula =
  let rec simplify_helper f = (
    let updated = ref false in
    let trans_ef, trans_f = (fun _ -> None), (fun _ -> None) in
    let trans_m, trans_a = (fun mp -> Some mp), (fun a -> Some a) in
    let trans_bf, trans_e = (fun bf -> Some bf), (fun e -> Some e) in
    let trans_hf hf = (match hf with
      | CF.Star {CF.h_formula_star_h1 = h1; CF.h_formula_star_h2 = h2} -> (
          match (h1, h2) with
          | CF.HEmp, _ -> (updated := true; Some h2)
          | _, CF.HEmp -> (updated := true; Some h1)
          | _, _ -> None
        )
      | _ -> None
    ) in
    let trans_pf pf = (
      match pf with
      | CP.And (pf1, pf2, pos) ->
          if (CP.isConstTrue pf1) then (updated := true; Some pf2)
          else if (CP.isConstFalse pf1) then (updated := true; Some (CP.mkFalse pos)) 
          else if (CP.isConstTrue pf2) then (updated := true; Some pf1)
          else if (CP.isConstFalse pf2) then (updated := true; Some (CP.mkFalse pos))
          else None
      | CP.Or (pf1, pf2, _, pos) ->
          if (CP.isConstTrue pf1) then (updated := true; Some (CP.mkTrue pos))
          else if (CP.isConstFalse pf1) then (updated := true; Some pf2) 
          else if (CP.isConstTrue pf2) then (updated := true; Some (CP.mkTrue pos))
          else if (CP.isConstFalse pf2) then (updated := true; Some pf1)
          else None
      | CP.AndList pfs ->
          let exist_constant_false = List.exists (fun (_,pf) ->
            CP.isConstFalse pf
          ) pfs in
          if (exist_constant_false) then (updated := true; Some (CP.mkFalse no_pos))
          else (
            let non_true_pfs = List.filter (fun (_,pf) ->
              not (CP.isConstTrue pf)
            ) pfs in
            if (List.length non_true_pfs != List.length pfs) then
              (updated := true; Some (CP.AndList non_true_pfs))
            else None
          )
      | _ -> None
    ) in
    let trans_func = (trans_ef, trans_f, trans_hf,
        (trans_m, trans_a, trans_pf, trans_bf, trans_e)) in
    let newf= CF.transform_formula trans_func f in
    if not (!updated) then newf
    else simplify_helper newf 
  ) in
  (* return *)
  simplify_helper f

(*
 * extract sub-formula contains related vars
 * Trung:
 *   - works properly without pure property
 *   - if pure properties exists, how to consider?
 *)
let extract_sub_formula_by_vars (f: CF.formula) (extracted_vars: CP.spec_var list)
    : CF.formula =
  (* TODO: first extract needed elements and keep the original structure *)
  let extract_formula_helper f vars = (
    let trans_ef, trans_f = (fun _ -> None), (fun _ -> None) in
    let trans_hf hf = (
      match hf with
      | CF.ViewNode {CF.h_formula_view_node = node} ->
          if (CP.mem_svl node vars) then Some CF.HEmp 
          else Some hf
      | CF.DataNode {CF.h_formula_data_node = node} ->
          if (CP.mem_svl node vars) then Some CF.HEmp
          else Some hf
      | _ -> None
    ) in
    (* NOTE: this extraction is not correct for disjunction of pure formula *)
    let trans_m, trans_a = (fun mp -> Some mp), (fun a -> Some a) in
    let trans_pf, trans_e = (fun pf -> None), (fun e -> Some e) in
    let trans_bf bf = (
      let svs = CP.bfv bf in
      if (CP.EMapSV.overlap svs vars) then None
      else Some (CP.mkTrue_b no_pos)
    ) in
    let trans_func = (trans_ef, trans_f, trans_hf,
        (trans_m, trans_a, trans_pf, trans_bf, trans_e)) in
    CF.transform_formula trans_func f
  ) in

  let newf = extract_formula_helper f extracted_vars in
  let newf = simplify_formula newf in
  newf


(*
 * Collect only the nodes in main heap chains, starting from root node
 *)
let collect_main_heap_chain_in_formula_x (f: CF.formula) (root: CP.spec_var)
    (vdecl: C.view_decl)
    : CF.formula =
  (* connect pointers of all nodes in main heap chain *)
  let rec collect_main_pointers_x f pointers vdecl fwd_ptr ddecl fwd_field eset = (
    let current_pointers = ref pointers in
    let trans_ef, trans_f = (fun _ -> None), (fun _ -> None) in
    let trans_hf hf = (match hf with
      | CF.ViewNode {CF.h_formula_view_node = vnode;
                     CF.h_formula_view_arguments = arguments} ->
          let vnode_equiv_svl = CF.compute_equiv_closure_of_sv vnode eset in
          if (CP.EMapSV.overlap !current_pointers vnode_equiv_svl) then (
            current_pointers := CP.remove_dups_svl (vnode_equiv_svl @ !current_pointers);
            List.iter2 (fun arg var ->
              if (CP.eq_spec_var fwd_ptr var) then (
                current_pointers := CP.remove_dups_svl (arg::!current_pointers)
              )
            ) arguments vdecl.C.view_vars;
          );
          None
      | CF.DataNode {CF.h_formula_data_node = dnode;
                     CF.h_formula_data_arguments = arguments} ->
          let dnode_equiv_svl = CF.compute_equiv_closure_of_sv dnode eset in
          if (CP.EMapSV.overlap !current_pointers dnode_equiv_svl) then (
            current_pointers := CP.remove_dups_svl (dnode_equiv_svl @ !current_pointers);
            List.iter2 (fun arg ((_,fname),_) ->
              if (eq_str fwd_field fname) then (
                current_pointers := CP.remove_dups_svl (arg::!current_pointers)
              )
            ) arguments ddecl.C.data_fields;
          );
          None
      | _ -> None
    ) in
    let trans_m, trans_a = (fun mp -> Some mp), (fun a -> Some a) in
    let trans_pf, trans_e = (fun pf -> Some pf), (fun e -> Some e) in
    let trans_bf = (fun bf -> Some bf) in
    let trans_func = (trans_ef, trans_f, trans_hf,
        (trans_m, trans_a, trans_pf, trans_bf, trans_e)) in
    let _ = CF.transform_formula trans_func f in
    if (List.length !current_pointers = List.length pointers) then
      !current_pointers
    else collect_main_pointers f !current_pointers vdecl fwd_ptr ddecl fwd_field eset
  )
  and collect_main_pointers f pointers vdecl fwd_ptr ddecl fwd_field eset = (
    let pr_f = (add_str "f" !CF.print_formula) in
    let pr_pointers = (add_str "pointers" !CP.print_svl) in
    let pr_view = (add_str "view" !C.print_view_decl_short) in
    let pr_res = (add_str "res" !CP.print_svl) in
    Debug.no_3 "collect_main_pointers" pr_f pr_pointers pr_view pr_res
        (fun _ _ _ -> collect_main_pointers_x f pointers vdecl fwd_ptr ddecl fwd_field eset)
        f pointers vdecl
  ) in
  
  (* extract main heap chain in raw format *)
  let extract_main_heap_chain f pointers = (
    let trans_ef, trans_f = (fun _ -> None), (fun _ -> None) in
    let trans_hf hf = (match hf with
      | CF.ViewNode {CF.h_formula_view_node = vnode} ->
          if (CP.mem_svl vnode pointers) then Some hf
          else Some CF.HEmp
      | CF.DataNode {CF.h_formula_data_node = dnode} ->
          if (CP.mem_svl dnode pointers) then Some hf
          else Some CF.HEmp
      | _ -> None
    ) in
    let trans_m, trans_a = (fun mp -> Some mp), (fun a -> Some a) in
    let trans_pf, trans_e = (fun pf -> None), (fun e -> Some e) in
    let trans_bf bf = (
      Debug.ninfo_hprint (add_str "bf" !CP.print_b_formula) bf no_pos;
      let svs = CP.bfv bf in
      if (CP.EMapSV.overlap svs pointers) then Some bf
      else Some (CP.mkTrue_b no_pos)
    ) in
    let trans_func = (trans_ef, trans_f, trans_hf,
        (trans_m, trans_a, trans_pf, trans_bf, trans_e)) in
    CF.transform_formula trans_func f
  ) in
  
  let ddecl = (match vdecl.C.view_data_decl with 
    | Some dd -> dd
    | None -> 
        let msg = "collect_main_heap_chain_in_formula: data_decl not found!" in
        report_error no_pos msg
  ) in
  let fwd_field = (match vdecl.C.view_forward_fields with
    | [] ->
        report_warning no_pos "collect_main_heap_chain: forward field not found!";
        "unknown_forward_field"
    | [s] -> s
    | _ ->
        report_warning no_pos "collect_main_heap_chain: expect only 1 forward field!";
        "unknown_forward_field"
  ) in
  let fwd_ptr = (match vdecl.C.view_forward_ptrs with
    | [] ->
        report_warning no_pos "collect_main_heap_chain: foward pointer not found!";
        (CP.mk_spec_var "unknown_forward_pointer")
    | [sv] -> sv
    | _ ->
        report_warning no_pos "collect_main_heap_chain: expect only 1 foward pointer!";
        (CP.mk_spec_var "unknown_forward_pointer")
  ) in
  let eset = CF.build_eset_of_formula f in
  let main_pointers = collect_main_pointers f [root] vdecl fwd_ptr ddecl fwd_field eset in
  let main_heap_chain = extract_main_heap_chain f main_pointers in
  simplify_formula main_heap_chain


let collect_main_heap_chain_in_formula (f: CF.formula) (root: CP.spec_var) (vdecl: C.view_decl)
    : CF.formula =
  let pr_f = (add_str "f" !CF.print_formula) in
  let pr_root = (add_str "root" !CP.print_sv) in
  let pr_view = (add_str "view" (fun vd -> vd.C.view_name)) in
  let pr_res = (add_str "res" !CF.print_formula) in
  Debug.no_3 "collect_main_heap_chain_in_formula" pr_f pr_root pr_view pr_res
      (fun _ _ _ -> collect_main_heap_chain_in_formula_x f root vdecl) f root vdecl


let collect_main_heap_chain_in_view_x (vdecl: C.view_decl) : (CF.formula list) =
  List.map (fun (f,_) ->
    let root = C.self_param vdecl in
    collect_main_heap_chain_in_formula f root vdecl
  ) vdecl.C.view_un_struc_formula


let collect_main_heap_chain_in_view (vdecl: C.view_decl) : (CF.formula list) =
  let pr_view = (add_str "view" !C.print_view_decl_short) in
  let pr_res = (add_str "res" (pr_list !CF.print_formula)) in
  Debug.no_1 "collect_main_heap_chain_in_view_x" pr_view pr_res
      (fun _ -> collect_main_heap_chain_in_view_x vdecl) vdecl

(* TODO *)
(* let collect_heap_around_node *)


(* TODO *)
(* let build_non_inductive_predicate_from_a_formula *)


(*
 * Extract a node & its sub-heap nodes
 *)
(* TODO *)
(* let extract_node (f: CF.formula) (root: CP.spec_var) : CF.formula = *)

(* TODO *)
(* let find_atomic_view *)

(*
 * A view_decl is atomic iff:
 * - Having only 2 branches: 1 base branch and 1 inductive branch
 * - Formula in base branch contains empty heap in the main heap chain
 * - Main heap chain of extension part of formula in inductive branch is irreducible 
 *)
(* let check_atomic_view (vdecl: C.view_decl) : bool =              *)
(*   if (List.length vdecl.C.view_un_struc_formula != 2) then false *)
(*     let base_cases, inductive_cases = List.partition (fun f ->   *)
(*     ) vdecl.C.view_un_struc_formula in                           *)
(*   )                                                              *)

(* let check_atomic_view (vdecl: C.view_decl) : bool =              *)
(*   if (List.length vdecl.C.view_un_struc_formula != 2) then false *)
(*   else (                                                         *)
(*     let base_cases, inductive_cases = List.partition (fun f ->   *)
(*        true                                                      *)
(*     ) vdecl.C.view_un_struc_formula in                           *)
    
(*     (* true *)                                                   *)
(*                                                                  *)
