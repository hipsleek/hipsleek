#include "xdebug.cppo"
(*
this module contains funtions relating to output of cformula
*)

open Globals
open Global_var
open VarGen
open Gen
open Exc.GTable
open VarGen
open Perm
open Label_only
open Label
open Cformula

module CP = Cpure
module MCP = Mcpure

let n_tbl = Hashtbl.create 1
let id_tbl = Hashtbl.create 1

let print_list_failesc_context = ref (fun (c:Cformula.list_failesc_context) -> "list failesc context printer has not been initialized")
let print_formula = ref (fun (c:Cformula.formula) -> "formula printer has not been initialized")
let print_pure_formula = ref (fun (c:Cpure.formula) -> "pure formula printer has not been initialized")
let print_sv = ref (fun (c:Cpure.spec_var) -> "spec_var printer has not been initialized")
let simplify_raw = ref(fun (c:Cpure.formula) -> Cpure.mkTrue no_pos)

let shorten_svl fv =
  (* let n_tbl = Hashtbl.create 1 in *)
  let reg = Str.regexp "[0-9]*_.*" in
  let n_svl = List.map (fun sv ->
      match sv with
        CP.SpecVar(t,id,pr) ->
        let new_id =
          if Hashtbl.mem id_tbl (id,pr)
          then
            Hashtbl.find id_tbl (id,pr)
          else
            let cut_id = Str.global_replace reg "" (id) in
            if Hashtbl.mem n_tbl (cut_id,pr)
            then
              begin
                let off = (Hashtbl.find n_tbl (cut_id,pr)) + 1 in
                let new_id = cut_id ^ string_of_int(off) in
                Hashtbl.add id_tbl (id,pr) new_id;
                Hashtbl.add n_tbl (cut_id,pr) off;
                new_id
              end
            else
              begin
                Hashtbl.add id_tbl (id,pr) cut_id;
                Hashtbl.add n_tbl (cut_id,pr) 0;
                cut_id
              end
        in
        CP.SpecVar(t,(*(Str.global_replace reg "" id)^ "_" ^Globals.fresh_inf_number()*) new_id,pr)
    ) fv in n_svl

let get_all_data_fields prog=
  let fields = List.fold_left (fun r d ->
      let fields = List.fold_left (fun r ((_,id), _) -> r@[id]) [] d.Cast.data_fields in
      r@fields
    ) [] prog.Cast.prog_data_decls in
  fields

let shorten_svl_avoid_field prog fv =
  let fields = get_all_data_fields prog in
  let () = Debug.ninfo_hprint (add_str "fields" (pr_list pr_id)) fields no_pos in
  let pad = "0" in
  (* let n_tbl = Hashtbl.create 1 in *)
  let reg = Str.regexp "[0-9]*_.*" in
  let n_svl = List.map (fun sv ->
      match sv with
        CP.SpecVar(t,id,pr) ->
        let cut_id0 = Str.global_replace reg "" (id ) in
        (* let cut_id = if Gen.BList.mem_eq (fun s1 s2 -> String.compare s1 s2 = 0) cut_id0 fields then *)
        (*   cut_id0 ^ pad *)
        (* else cut_id0 *)
        (* in *)
        let new_id =
          if Hashtbl.mem id_tbl (id,pr)
          then
            Hashtbl.find id_tbl (id,pr)
          else
            let cut_id = Str.global_replace reg "" (id) in
            if Hashtbl.mem n_tbl (cut_id,pr)
            then
              begin
                let off = (Hashtbl.find n_tbl (cut_id,pr)) + 1 in
                let new_id = cut_id ^ string_of_int(off) in
                Hashtbl.add id_tbl (id,pr) new_id;
                Hashtbl.add n_tbl (cut_id,pr) off;
                new_id
              end
            else
              begin
                Hashtbl.add id_tbl (id,pr) cut_id;
                Hashtbl.add n_tbl (cut_id,pr) 0;
                cut_id
              end
        in
        CP.SpecVar(t,(*(Str.global_replace reg "" id)^ "_" ^Globals.fresh_inf_number()*) new_id,pr)
    ) fv in n_svl

let rearrange_h_formula_x args0 hf0 =
  let rec helper fv hfl =
    match fv with
    | [] -> hfl
    | v :: fvt ->
      (List.filter (fun hf -> contains_spec_var hf v) hfl)@(helper fvt (List.filter (fun hf -> not (contains_spec_var hf v)) hfl))
  in
  match hf0 with
  | Star hfs ->
    let fl = split_star_conjunctions hf0 in
    let re = List.hd args0 in
    (* let r = (match re with *)
    (*   | CP.Var(sv, pos) -> sv *)
    (*   | _ -> raise Not_found) in *)
    let rf = List.filter (fun hf -> contains_spec_var hf re) fl in
    let fv = h_fv (List.hd rf) in
    (* let () = print_endline (pr_list !print_sv fv) in *)
    let fl1 = helper fv fl in
    (* let () = print_endline (pr_list !print_h_formula fl1) in *)
    let hf1 = List.fold_left (fun f1 f2 -> mkStarH f1 f2 no_pos) (List.hd fl1) (List.tl fl1) in hf1
  | _ -> hf0

let rearrange_h_formula args0 hf0 =
  (* let pr1 = !CP.print_sv in *)
  let pr2 = pr_list !CP.print_sv in
  let pr3 = !print_h_formula in
  Debug.no_2 "rearrange_h_formula" pr2 pr3 pr3
    (fun _ _ -> rearrange_h_formula_x args0 hf0)
    args0 hf0

(*args0 is root + args of root*)
let rearrange_formula_x args0 f0=
  let rec helper f=
    match f with
    | Base fb ->
      let nh =
        try rearrange_h_formula args0 fb.formula_base_heap
        with _ -> fb.formula_base_heap
      in
      Base {fb with formula_base_heap = nh; }
    | Exists _ ->
      let qvars, base1 = split_quantifiers f in
      let nf = helper base1 in
      add_quantifiers qvars ( nf)
    | Or orf  ->
      Or { orf with formula_or_f1 = helper orf.formula_or_f1;
                    formula_or_f2 = helper orf.formula_or_f2 }
  in
  helper f0

let rearrange_formula args0 f0=
  let pr1 = pr_list !CP.print_sv in
  let pr2 = !print_formula in
  Debug.no_2 "rearrange_formula" pr1 pr2 pr2
    (fun _ _ -> rearrange_formula_x args0 f0)
    args0 f0

let rearrange_def def=
  let new_body1 =
    match def.hprel_def_body_lib with
    | [] -> begin
        try
          let args = match def.hprel_def_hrel with
            | HRel (sv, exp_list, pos) ->
              List.map (fun exp -> match exp with
                  | CP.Var(sv, pos) -> sv
                  | _ -> raise Not_found) exp_list
            | _ -> raise Not_found
          in
          List.map (fun ((p, f_opt,c) as o) ->
              match f_opt with
              | Some f ->
                (p, Some (rearrange_formula args f),c)
              | None -> o
            ) def.hprel_def_body
        with _ -> def.hprel_def_body
      end
    | _ -> def.hprel_def_body
  in
  (*to shorten variable names here*)
  let args = match def.hprel_def_kind with
    | CP.HPRelDefn (_,r,args) -> r::args
    | _ -> []
  in
  let svll = List.map (fun (p, f_opt,_) ->
      match f_opt with
      | Some f -> fv f
      | None -> []
    ) new_body1 in
  let svl = List.flatten svll in
  (* let () = print_endline ((pr_list !print_sv) (args@svl)) in *)
  let svl_rd = List.rev(CP.remove_dups_svl (List.rev args@svl)) in
  (*let () = print_endline ((pr_list !print_sv) svl_rd) in*)
  (* let svl_ra = (\* svl_rd in  *\)CP.diff_svl svl_rd args in *)
  let svl_rp = List.filter (fun sv -> not (CP.is_hprel_typ sv)) svl_rd in
  (* let n_tbl = Hashtbl.create 1 in *)
  (* let reg = Str.regexp "_.*" in *)
  (* let n_tbl = Hashtbl.create 1 in *)
  let new_svl = shorten_svl svl_rp in 
  let new_body2 =
    List.map (fun ((p, f_opt,c) as o) ->
        match f_opt with
        | Some f -> (p, Some (subst_avoid_capture svl_rp new_svl f), c)
        | None -> o
      ) new_body1
  in
  let new_hrel = subst_avoid_capture_h svl_rp new_svl def.hprel_def_hrel in
  let n_lib = match def.hprel_def_body_lib with
    | [] -> []
    | ls -> List.map (fun (f, flow) -> (subst_avoid_capture svl_rp new_svl f, flow)) ls
  in
  {def with hprel_def_body = new_body2;
            hprel_def_body_lib = n_lib;
            hprel_def_hrel = new_hrel;}

let rearrange_hp_def def=
  let new_body1 =
    begin
      try
        let args = match def.def_lhs with
          | HRel (sv, exp_list, pos) ->
            List.map (fun exp -> match exp with
                | CP.Var(sv, pos) -> sv
                | _ -> raise Not_found) exp_list
          | _ -> raise Not_found
        in
        List.map (fun (f, og) ->
            (rearrange_formula args f, og)
          ) def.def_rhs
      with _ -> def.def_rhs
    end
  in
  (*to shorten variable names here*)
  let args = match def.def_cat with
    | CP.HPRelDefn (_,r,args) -> r::args
    | _ -> []
  in
  let svll = List.map (fun (f,_) ->
      fv f
    ) new_body1 in
  let svl = List.flatten svll in
  (* let () = print_endline ((pr_list !print_sv) (args@svl)) in *)
  let svl_rd = List.rev(CP.remove_dups_svl (List.rev args@svl)) in
  (*let () = print_endline ((pr_list !print_sv) svl_rd) in*)
  (* let svl_ra = (\* svl_rd in  *\)CP.diff_svl svl_rd args in *)
  let svl_rp = List.filter (fun sv -> not (CP.is_hprel_typ sv)) svl_rd in
  (* let n_tbl = Hashtbl.create 1 in *)
  (* let reg = Str.regexp "_.*" in *)
  (* let n_tbl = Hashtbl.create 1 in *)
  let new_svl = shorten_svl svl_rp in 
  let new_body2 =
    List.map (fun (f, f_opt) ->
        ((subst_avoid_capture svl_rp new_svl f), f_opt)
      ) new_body1
  in
  let new_hrel = subst_avoid_capture_h svl_rp new_svl def.def_lhs in
  {def with def_rhs = new_body2;
            def_lhs = new_hrel;}

let rearrange_rel (rel: hprel) =
  let lfv = List.filter (fun sv -> not (CP.is_hprel_typ sv)) (CP.remove_dups_svl (fv rel.hprel_lhs)) in
  let gfv = (match rel.hprel_guard with
      | None -> []
      | Some f -> List.filter (fun sv -> not (CP.is_hprel_typ sv)) (CP.remove_dups_svl (fv f))) in
  let rfv = List.filter (fun sv -> not (CP.is_hprel_typ sv)) (CP.remove_dups_svl (fv rel.hprel_rhs)) in
  let fv = CP.remove_dups_svl (lfv@gfv@rfv) in
  (* let n_tbl = Hashtbl.create 1 in *)
  (* let reg = Str.regexp "_.*" in *)
  (* let n_tbl = Hashtbl.create 1 in *)
  let new_svl = shorten_svl fv in
  {rel with hprel_lhs = subst_avoid_capture fv new_svl (rearrange_formula lfv rel.hprel_lhs);
            hprel_guard = (match rel.hprel_guard with
                | None -> None
                | Some f -> Some (subst_avoid_capture fv new_svl (rearrange_formula gfv f)));
            hprel_rhs = subst_avoid_capture fv new_svl (rearrange_formula rfv rel.hprel_rhs) ;
  }

(*
print_tidy for verification condition + entailment
*)
let rearrange_entailment_x prog lhs0 rhs0=
  let lhs = x_add_1 simplify_pure_f_old lhs0 in
  let rhs = x_add_1 simplify_pure_f_old rhs0 in
  let l_quans, l_bare =  split_quantifiers lhs in
  let r_quans, r_bare =  split_quantifiers rhs in
  let l_svl = (CP.remove_dups_svl (fv l_bare)) in
  let r_svl = (CP.remove_dups_svl (fv r_bare)) in
  let all_svl = CP.remove_dups_svl (l_svl@r_svl@l_quans@r_quans) in
  let new_svl = shorten_svl_avoid_field prog all_svl in
  let sst0 = List.combine all_svl new_svl in
  let () = Debug.ninfo_hprint (add_str "sst0" (pr_list (pr_pair !CP.print_sv !CP.print_sv) )) sst0 no_pos in
  let n_lhs = subst_avoid_capture all_svl new_svl (rearrange_formula l_svl l_bare) in
  let n_rhs = subst_avoid_capture all_svl new_svl (rearrange_formula r_svl r_bare) in
  let nl_quans = CP.subst_var_list sst0 l_quans in
  let () = Debug.ninfo_hprint (add_str "l_quans" (!CP.print_svl) ) l_quans no_pos in
  let () = Debug.ninfo_hprint (add_str "nl_quans" (!CP.print_svl) ) nl_quans no_pos in
  (*handle quantifiers*)
  let n_lhs2 = add_quantifiers nl_quans n_lhs in
  let nr_quans = CP.subst_var_list sst0 r_quans in
  let () = Debug.ninfo_hprint (add_str "r_quans" (!CP.print_svl) ) r_quans no_pos in
  let () = Debug.ninfo_hprint (add_str "nr_quans" (!CP.print_svl) ) nr_quans no_pos in
  let n_rhs2 = add_quantifiers nr_quans n_rhs in
  (n_lhs2, n_rhs2)
(* (lhs, rhs) *)

let rearrange_entailment prog lhs rhs=
  let pr1 = !print_formula in
  let pr2 = pr_pair pr1 pr1 in
  Debug.no_2 "rearrange_entailment" pr1 pr1 pr2
    (fun _ _ -> rearrange_entailment_x prog lhs rhs)
    lhs rhs

let elim_imm_vars_pf f =
  match f with
  | Base b -> Base {b with formula_base_pure = MCP.mix_of_pure (CP.elim_idents (MCP.pure_of_mix b.formula_base_pure));}
  | Exists e -> Exists {e with formula_exists_pure = MCP.mix_of_pure (CP.elim_idents (MCP.pure_of_mix e.formula_exists_pure));}
  | _ -> f

let rec elim_imm_vars_f f =
  let get_subs_list pf =
    let fl = CP.split_conjunctions pf in
    let subs_list = List.fold_left (fun acc f ->
        match f with
        | CP.BForm ((p_f, _), _) -> (
            match p_f with
            | CP.Eq (CP.Var (sv1, _), CP.Var (sv2, _), _) -> acc@[(sv1,sv2)]
            | _ -> acc
          )
        | _ -> acc
      ) [] fl in
    subs_list
  in
  match f with
  | Base b ->
    let sst_list = get_subs_list (MCP.pure_of_mix b.formula_base_pure) in
    (* Long: cause problem of string_of_formula *)
    let f = List.fold_left (fun f (sv1,sv2) ->
        subst_avoid_capture [sv1] [sv2] f
      ) f sst_list in
    let f = elim_imm_vars_pf f in
    f
  | Exists e ->
    let sst_list = get_subs_list (MCP.pure_of_mix e.formula_exists_pure) in
    let f = List.fold_left (fun f (sv1,sv2) ->
        subst_avoid_capture [sv1] [sv2] f
      ) f sst_list in
    let f = elim_imm_vars_pf f in
    f
  | Or orf -> Or {orf with formula_or_f1 = elim_imm_vars_f orf.formula_or_f1;
                           formula_or_f2 = elim_imm_vars_f orf.formula_or_f2}

let rec shorten_formula f =
  let helper f =
    let f0 = x_add_1 simplify_pure_f_old f in
    let f0 = elim_imm_vars_f f0 in
    let fvars = fv f0 in
    let qvars,_ = split_quantifiers f0 in
    let vars = CP.remove_dups_svl (fvars@qvars) in
    let vars = List.filter (fun sv ->
        let sv_name = CP.name_of_spec_var sv in
        if (String.length sv_name <= 2) then
          true
        else
          (String.compare (String.sub (sv_name) 0 2) "HP") != 0
      ) vars in
    let new_svl = shorten_svl vars in
    (* subst_avoid_capture vars new_svl f *)
    let new_f = x_add subst_all (List.combine vars new_svl) f0 in
    new_f
  in
  match f with
  | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) ->
    let new_f1 = shorten_formula f1 in
    let new_f2 = shorten_formula f2 in
    let new_f = mkOr new_f1 new_f2 pos in
    new_f
  | _ ->
    let new_f = helper f in
    new_f

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

(* sort specvar with shorter in front *)
let sort_svl vs =
  List.sort (fun sv1 sv2 -> 
      let v1=String.length (CP.ident_of_spec_var sv1) in
      let v2=String.length (CP.ident_of_spec_var sv2) in
      if v1<v2 then -1
      else if v1==v2 then 0
      else 1
    ) vs

(* use program variables; use shorter variables *)
let build_subs lst svl =
  if (List.length lst) <= 1 then []
  else
    let (cv,rest) = List.partition (fun x -> List.exists (CP.eq_ident_var x) svl) lst in
    match (sort_svl cv) with
    | h::_ -> 
      (* let e = CP.Var(h,no_pos) in *)
      List.map (fun v -> (v,h)) rest
    | [] -> 
      begin
        let (const,rest) = List.partition (fun x -> CP.is_const x) lst in
        match const with
        | h::_ -> []
        (* let e = CP.conv_var_to_exp h in *)
        (* List.map (fun v -> (v,e)) rest *)
        | [] -> 
          begin
            match (sort_svl lst) with
            | h::rest -> 
              (* let e = CP.Var(h,no_pos) in *)
              List.map (fun v -> (v,h)) rest
            | [] -> []
          end
      end
 
let simplify_context ?(prog_vs=None) ctx =
  let rec helper ctx =
    match ctx with
    | Ctx en -> Ctx {en with
                     es_formula =
                       let () = x_tinfo_hp (add_str "formula" !print_formula) en.es_formula no_pos in
                       let () = x_tinfo_hp (add_str "renamed_vars" pr_id) (stk_renamed_vars # string_of_no_ln) no_pos in
                       let h,mf,vp,fl,t,a = split_components en.es_formula in
                       let curr_svl = match prog_vs with
                         | None -> stk_vars # get_stk 
                         | Some vs -> vs
                       in
                       let pure_f = MCP.pure_of_mix mf in
                       let eqmap = CP.build_eqmap_at_toplevel pure_f in
                       let eq_part = CP.EMapSV.partition eqmap in
                       let sst = List.concat (List.map (fun lst -> build_subs lst curr_svl) eq_part) in
                       let new_formula = subst sst en.es_formula in
                       let h,mf,vp,fl,t,a = split_components new_formula in
                       let () = x_tinfo_hp (add_str "sst" (pr_list (pr_pair !print_sv !print_sv))) sst no_pos in
                       let () = x_tinfo_hp (add_str "new_formula" !print_formula) new_formula no_pos in
                       let exists_svl = match en.es_formula with
                         | Exists ef -> ef.formula_exists_qvars
                         | _ -> []
                       in
                       let free_svl = fv en.es_formula in
                       let heap_svl = h_fv h in
                       let () = x_tinfo_hp (add_str "exists variables" (pr_list !print_sv)) exists_svl no_pos in
                       let () = x_tinfo_hp (add_str "free variables" (pr_list !print_sv)) free_svl no_pos in
                       let () = x_tinfo_hp (add_str "curr variables" (pr_list !print_sv)) curr_svl no_pos in
                       let () = x_tinfo_hp (add_str "heap variables" (pr_list !print_sv)) heap_svl no_pos in
                       let heap_svl = CP.diff_svl_ident heap_svl curr_svl in
                       let () = x_tinfo_hp (add_str "heap variables(new)" (pr_list !print_sv)) heap_svl no_pos in
                       let () = x_ninfo_hp (add_str "pure formula" !CP.print_formula) pure_f no_pos in
                       let () = x_ninfo_hp (add_str "eqmap" (CP.EMapSV.string_of)) eqmap no_pos in
                       let all_svl = exists_svl@free_svl in
                       let imp_svl = curr_svl@heap_svl in
                       let elim_svl = List.filter (fun sv ->
                           not (Gen.BList.mem_eq Cpure.eq_spec_var_unp sv imp_svl)
                         ) all_svl in
                       let () = x_tinfo_hp (add_str "elim variables" (pr_list !print_sv)) elim_svl no_pos in
                       let elim_svl, bag_exists_svl = List.partition (fun sv ->
                           Cpure.is_int_convertible_var sv
                           (* (Cpure.type_of_spec_var sv = Int) || (Cpure.type_of_spec_var sv = Bool) *)
                         ) elim_svl in
                       let () = x_tinfo_hp (add_str "elim variables" (pr_list !print_sv)) elim_svl no_pos in
                       let () = x_tinfo_hp (add_str "bag exists variables" (pr_list !print_sv)) bag_exists_svl no_pos in
                       if (List.length elim_svl = 0)
                       then
                         en.es_formula
                       else
                         let pf0 = Mcpure.pure_of_mix mf in
                         let pf1 = Cpure.mkExists elim_svl pf0 None no_pos in
                         let pf2 = !simplify_raw pf1 in
                         let pf3 = Cpure.mkExists bag_exists_svl pf2 None no_pos in
                         let pf_simp = Cpure.elim_exists pf3 in
                         let mf_simp = Mcpure.mix_of_pure pf_simp in
                         let new_f0 = mkExists exists_svl h mf_simp vp t fl a no_pos in
                         let () = x_tinfo_hp (add_str "new_f0" !print_formula) new_f0 no_pos in
                         let new_f = elim_exists new_f0 in
                         let () = x_tinfo_hp (add_str "new_f" !print_formula) new_f no_pos in
                         new_f
                    }
    | OCtx (ctx1, ctx2) -> OCtx (helper ctx1, helper ctx2)
  in helper ctx

let simplify_context ?(prog_vs=None) ctx =
  let pr = !print_context in
  Debug.no_1 "simplify_context" pr pr (simplify_context ~prog_vs:prog_vs)  ctx

let simplify_branch_context ?(prog_vs=None) (pt, ctx, fail_type) =
  let ctx = simplify_context ~prog_vs:prog_vs ctx in
  (pt,ctx,fail_type)

let simplify_failesc_context ?(prog_vs=None) fc =
  match fc with
  | (bfl, esc, bcl) -> (bfl, esc, List.map (simplify_branch_context ~prog_vs:prog_vs) bcl)

let simplify_context_list ?(prog_vs=None) ctx =
  List.map (fun x -> simplify_context ~prog_vs:prog_vs x) ctx

let simplify_list_context ?(prog_vs=None) ctx =
  match ctx with
  | FailCtx (ft,c,cex) -> FailCtx (ft,simplify_context ~prog_vs:prog_vs c,cex)
  | SuccCtx lst ->  SuccCtx (simplify_context_list ~prog_vs:prog_vs lst)

let simplify_failesc_context_list ?(prog_vs=None) ctx =
  List.map (fun x -> simplify_failesc_context ~prog_vs:prog_vs x) ctx

let simplify_failesc_context_list ?(prog_vs=None) ctx =
  let pr = !print_list_failesc_context in
  Debug.no_1 "simplify_failesc_context_list" pr pr (simplify_failesc_context_list ~prog_vs:prog_vs)  ctx

let inline_print e =
  if (!Globals.print_en_inline) then elim_imm_vars_f e
  else e

let tidy_print e =
  if (!Globals.print_en_tidy) then inline_print (shorten_formula e)
  else e

(* let tidy_print e = *)
(*   let pr1 = !print_formula in *)
(*   Debug.no_1 "tidy_print" pr1 pr1 *)
(*     (fun _ -> tidy_print e) e *)
