open Globals
open Gen
open Others

module CP = Cpure
module IF = Iformula
module CF = Cformula
module CFU = Cfutil
module MCP = Mcpure
module CEQ = Checkeq


let size_ext_hpdef_x iprog cprog hpdef=
  (*look up the view size extn*)
  let view_exts = Cast.look_up_view_def_ext_size cprog.Cast.prog_view_decls 1 1 in
  match view_exts with
    | [] -> let hp,args = CF.extract_HRel hpdef.CF.def_lhs in
      (hp, hpdef.CF.def_lhs , [], hpdef)
    | ext_v::_ ->
          let extn_arg = fresh_any_name Globals.size_rel_arg in
          let ext_sv = CP.SpecVar (Int , extn_arg ,Unprimed) in
          let hp,args = CF.extract_HRel hpdef.CF.def_lhs in
          let _ =  Debug.ninfo_hprint (add_str "  args: " !CP.print_svl) args no_pos in
          (* let n_hp = CP.fresh_spec_var hp in *)
          let n_args = args@[ext_sv] in
          let n_lhs, n_hp = x_add (Sautil.add_raw_hp_rel ~caller:x_loc) cprog true false (List.map (fun sv ->
              if CP.is_node_typ sv then (sv,I) else (sv,NI)) n_args) no_pos in
          (*new declaration for cprog*)
          let n_hpcl = Cast.look_up_hp_def_raw cprog.Cast.prog_hp_decls (CP.name_of_spec_var n_hp) in
          (*new declaration for iprog*)
          let _ = Iast.mkhp_decl iprog n_hpcl.Cast.hp_name
            (List.map (fun (CP.SpecVar (t,id,_) ,ins) -> (t,id, ins)) n_hpcl.Cast.hp_vars_inst)
            n_hpcl.Cast.hp_part_vars n_hpcl.Cast.hp_root_pos n_hpcl.Cast.hp_is_pre (IF.mkTrue IF.n_flow no_pos)
          in
          let orig_pred_name = CP.name_of_spec_var hp in
          let extn_view_name = ext_v.Cast.view_name in
          let root_pos = x_add Cast.get_proot_hp_def_raw cprog.Cast.prog_hp_decls orig_pred_name in
          let data_name = Cast.get_root_typ_hprel cprog.Cast.prog_hp_decls orig_pred_name in
          let extn_props = Cast.look_up_extn_info_rec_field cprog.Cast.prog_data_decls data_name in
          (* let extn_props = [("REC")] in *)
          let extn_info = [((orig_pred_name,List.map CP.name_of_spec_var args),(extn_view_name, extn_props , [extn_arg] ), [root_pos])] in
          let n_rhs = Predicate.extend_pred_dervs iprog cprog [hpdef] n_hp n_args extn_info in
          (* let n_lhs = CF.HRel (n_hp, List.map (fun x -> CP.mkVar x no_pos) n_args, no_pos) in *)
          let n_de_cat = match hpdef.CF.def_cat with
            | CP.HPRelDefn _ ->  let r, others = Sautil.find_root cprog [n_hp] n_args (CF.list_of_disjs n_rhs) in
              CP.HPRelDefn (n_hp, r, others)
            | _ -> report_error no_pos "sac.size_ext_hpdef: support HPDEF only"
          in
          let exted_pred = CF.mk_hp_rel_def1 n_de_cat n_lhs [(n_rhs, None)] None in
          let _ =  Debug.info_hprint (add_str "  extend size prop: " pr_id) ((!CP.print_sv hp ) ^ " ===> " ^ (!CP.print_sv n_hp)) no_pos in
          (n_hp,n_lhs, [ext_sv], exted_pred)

let size_ext_hpdef iprog cprog hpdef=
  let pr1 = Cprinter.string_of_hp_rel_def_short in
  let pr2 = pr_quad !CP.print_sv Cprinter.string_of_h_formula !CP.print_svl pr1 in
  Debug.no_1 "size_ext_hpdef" pr1 pr2
      (fun _ -> size_ext_hpdef_x iprog cprog hpdef) hpdef
