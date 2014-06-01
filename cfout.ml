(*
this module contains funtions relating to output of cformula
*)

open Globals
open Gen
open Exc.GTable
open Perm
open Label_only
open Label
open Cformula

module CP = Cpure
module MCP = Mcpure


let shorten_svl fv  n_tbl =
  (* let n_tbl = Hashtbl.create 1 in *)
  let reg = Str.regexp "[0-9]*_.*" in 
  let n_svl = List.map (fun sv ->
      match sv with
          CP.SpecVar(t,id,pr) ->
              let cut_id = Str.global_replace reg "" id in
              let new_id =
                if Hashtbl.mem n_tbl (cut_id,pr)
                then
                  begin
                    Hashtbl.add n_tbl (cut_id,pr) ((Hashtbl.find n_tbl (cut_id,pr)) + 1);
                    cut_id ^ string_of_int(Hashtbl.find n_tbl (cut_id,pr))
                  end
                else
                  begin
                    Hashtbl.add n_tbl (cut_id,pr) 0;
                    cut_id
                  end
              in
              CP.SpecVar(t,(*(Str.global_replace reg "" id)^ "_" ^Globals.fresh_inf_number()*) new_id,pr)
  ) fv in
  (n_svl,  n_tbl)

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
          (* let _ = print_endline (pr_list !print_sv fv) in *)
          let fl1 = helper fv fl in
          (* let _ = print_endline (pr_list !print_h_formula fl1) in *)
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
      | Some _ -> def.hprel_def_body
      | None -> begin
          try
            let args = match def.hprel_def_hrel with
              | HRel (sv, exp_list, pos) ->
                    List.map (fun exp -> match exp with
                      | CP.Var(sv, pos) -> sv
                      | _ -> raise Not_found) exp_list
              | _ -> raise Not_found
            in
            List.map (fun ((p, f_opt) as o) ->
                match f_opt with
                  | Some f ->
                      (p, Some (rearrange_formula args f))
                  | None -> o
          ) def.hprel_def_body
          with _ -> def.hprel_def_body
        end
  in
  (*to shorten variable names here*)
  let args = match def.hprel_def_kind with
    | CP.HPRelDefn (_,r,args) -> r::args
    | _ -> []
  in
  let svll = List.map (fun (p, f_opt) ->
               match f_opt with
                 | Some f -> fv f
                 | None -> []
  ) new_body1 in
  let svl = List.flatten svll in
  (* let _ = print_endline ((pr_list !print_sv) (args@svl)) in *)
  let svl_rd = List.rev(CP.remove_dups_svl (List.rev args@svl)) in
  (*let _ = print_endline ((pr_list !print_sv) svl_rd) in*)
  (* let svl_ra = (\* svl_rd in  *\)CP.diff_svl svl_rd args in *)
  let svl_rp = List.filter (fun sv -> not (CP.is_hprel_typ sv)) svl_rd in
  (* let n_tbl = Hashtbl.create 1 in *)
  (* let reg = Str.regexp "_.*" in *)
  let n_tbl = Hashtbl.create 1 in
  let new_svl,_ = shorten_svl svl_rp n_tbl in 
  let new_body2 =
    List.map (fun ((p, f_opt) as o) ->
        match f_opt with
          | Some f -> (p, Some (subst_avoid_capture svl_rp new_svl f))
          | None -> o
  ) new_body1
  in
  let new_hrel = subst_avoid_capture_h svl_rp new_svl def.hprel_def_hrel in
  let n_lib = match def.hprel_def_body_lib with
    | None -> None
    | Some f -> Some (subst_avoid_capture svl_rp new_svl f)
  in
  {def with hprel_def_body = new_body2;
      hprel_def_body_lib = n_lib;
      hprel_def_hrel = new_hrel;}

(* let rearrange_def def= *)
(*   let pr1 =  *)

let rearrange_rel (rel: hprel) =
  let lfv = List.filter (fun sv -> not (CP.is_hprel_typ sv)) (CP.remove_dups_svl (fv rel.hprel_lhs)) in
  let gfv = (match rel.hprel_guard with
    | None -> []
    | Some f -> List.filter (fun sv -> not (CP.is_hprel_typ sv)) (CP.remove_dups_svl (fv f))) in
  let rfv = List.filter (fun sv -> not (CP.is_hprel_typ sv)) (CP.remove_dups_svl (fv rel.hprel_rhs)) in
  let fv = CP.remove_dups_svl (lfv@gfv@rfv) in
  (* let n_tbl = Hashtbl.create 1 in *)
  (* let reg = Str.regexp "_.*" in *)
  let n_tbl = Hashtbl.create 1 in
  let new_svl,_ = shorten_svl fv n_tbl in
  {rel with hprel_lhs = subst_avoid_capture fv new_svl (rearrange_formula lfv rel.hprel_lhs);
      hprel_guard = (match rel.hprel_guard with
         | None -> None
         | Some f -> Some (subst_avoid_capture fv new_svl (rearrange_formula gfv f)));
      hprel_rhs = subst_avoid_capture fv new_svl (rearrange_formula rfv rel.hprel_rhs) ;
  }


let rearrange_entailment_x lhs rhs=
  (*shorten quantifiers of f*)
  let shorten_quantifiers f tbl=
    let quans, bare = split_quantifiers f in
    let n_quans, tbl1 = shorten_svl quans tbl in
    let sst0 = List.combine quans n_quans in
    let new_f = add_quantifiers n_quans (subst sst0 f) in
    (new_f, sst0, tbl1)
  in
  let tbl0 = Hashtbl.create 1 in
  (*rename quantifiers of lhs*)
  let lhs1, l_sst, tbl1 = shorten_quantifiers lhs tbl0 in
  let rhs1 = subst l_sst rhs in
  (*rename quantifiers of rhs*)
  let rhs2, _, tbl2 = shorten_quantifiers rhs1 tbl1 in
  let l_svl = (CP.remove_dups_svl (fv lhs1)) in
  let r_svl = (CP.remove_dups_svl (fv rhs2)) in
  let all_svl = CP.remove_dups_svl (l_svl@r_svl) in
  let new_svl,_ = shorten_svl all_svl tbl2 in
  let n_lhs = subst_avoid_capture all_svl new_svl (rearrange_formula l_svl lhs1) in
  let n_rhs = subst_avoid_capture all_svl new_svl (rearrange_formula r_svl rhs2) in
  (n_lhs, n_rhs)

let rearrange_entailment lhs rhs=
  let pr1 = !print_formula in
  let pr2 = pr_pair pr1 pr1 in
  Debug.no_2 "rearrange_entailment" pr1 pr1 pr2
      (fun _ _ -> rearrange_entailment_x lhs rhs)
      lhs rhs

let shorten_formula f =
  let f0 = simplify_pure_f f in
  let fvars = fv f0 in
  let qvars,_ = split_quantifiers f0 in
  (* let _ = print_endline ((pr_list !print_sv) fv) in *)
  let vars = CP.remove_dups_svl (fvars@qvars) in
  let n_tbl = Hashtbl.create 1 in
  let new_svl,_ = shorten_svl vars n_tbl in
  (* let _ = print_endline ((pr_list !print_sv) new_svl) in *)
  (* subst_avoid_capture vars new_svl f *)
  subst_all (List.combine vars new_svl) f0

(* let rearrange_context bc = *)
(*   let rec helper ctx = *)
(*     match ctx with *)
(*       | Ctx en -> Ctx {en with *)
(*           es_formula = *)
(*                 let fv = CP.remove_dups_svl (fv en.es_formula) in *)
(*                 (\* let _ = print_endline ((pr_list !print_sv) fv) in *\) *)
(*                 let new_svl = shorten_svl fv in *)
(*                 (\* let _ = print_endline ((pr_list !print_sv) new_svl) in *\) *)
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
