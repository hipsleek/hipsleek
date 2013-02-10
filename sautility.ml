(*this file contains all unitilise for shape analysis.
it is used mainly by infer.infer_collect_hp and sa.infer_hp
*)

open Globals
open Gen

module DD = Debug
module CF=Cformula
module CP=Cpure
module MCP=Mcpure
module C = Cast
module CEQ = Checkeq

exception SA_NO_BASE_CASE of (CP.spec_var * (CP.spec_var list) * (CF.formula list)) (*hp without base case*)

(*hp_name * args * unk_args * condition * lhs * rhs *)
type par_def_w_name =  CP.spec_var * CP.spec_var list * CP.spec_var list * CF.formula * (CF.formula option) *
      (CF.formula option)


let is_rec_pardef (hp,_,f,_)=
  let hps = CF.get_hp_rel_name_formula f in
  (CP.mem_svl hp hps)

let string_of_hp_rel_def hp_rel =
 let str_of_hp_rel (r,f1, f2) = ( (CP.print_rel_cat r)^ ": " ^(Cprinter.string_of_h_formula f1) ^ ":: "
 ^(Cprinter.prtt_string_of_formula f2)) in
  (str_of_hp_rel hp_rel)

let string_of_par_def_w_name pd=
  let pr1 = !CP.print_sv in
  let pr4 = !CP.print_svl in
  let pr2 = Cprinter.prtt_string_of_formula in
  let pr3 = fun x -> match x with
    | None -> "None"
    | Some f -> pr2 f
  in
  let pr = pr_hexa pr1 pr4 pr4 pr2 pr3 pr3 in
  pr pd


let string_of_par_def_w_name_short pd=
  let pr1 = !CP.print_sv in
  let pr2 = !CP.print_svl in
  let pr3 = Cprinter.prtt_string_of_formula in
  let pr = pr_quad pr1 pr2 pr3 pr2 in
  pr pd

(**=================================**)

let close_def defs (v1,v2)=
  if (CP.is_null_const v1) || (CP.is_null_const v2) then defs
  else if CP.mem_svl v1 defs then (CP.remove_dups_svl defs@[v2])
  else if CP.mem_svl v2 defs then (CP.remove_dups_svl defs@[v1])
  else (defs)
  (* else *)
  (*   let b1 = CP.mem_svl v1 defs in *)
  (*   let b2 = CP.mem_svl v2 defs in *)
  (*   match b1,b2 with *)
  (*     | false,false *)
  (*     | true,false -> (defs@[v2]) *)

(*close_def is not precise if eqs= x=y & y=z and x=t, svl0=[t], and first examine x=y*)

let find_close svl0 eqs0=
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

(*List.combine but ls2 >= ls1*)
let rec combine_length_neq ls1 ls2 res=
  match ls1,ls2 with
    | [],[] -> res
    | [],sv2::_ -> res
    | sv1::tl1,sv2::tl2 -> combine_length_neq tl1 tl2 (res@[sv1,sv2])
    | _ -> report_error no_pos "sau.combine_first"


 let get_hpdef_name hpdef=
   match hpdef with
     | CP.HPRelDefn hp -> hp
     | _ -> report_error no_pos "sau.get_hp_name"


let is_empty_f f=
   match f with
    | CF.Base fb ->
        (CF.is_empty_heap fb.CF.formula_base_heap) &&
            (CP.isConstTrue (MCP.pure_of_mix fb.CF.formula_base_pure))
    | _ -> report_error no_pos "SAU.is_empty_f: not handle yet"

let is_empty_heap_f f0=
  let rec helper f=
    match f with
      | CF.Base fb ->
          (CF.is_empty_heap fb.CF.formula_base_heap)
      | CF.Exists fe -> (CF.is_empty_heap fe.CF.formula_exists_heap)
      | CF.Or orf -> (helper orf.CF.formula_or_f1) && (helper orf.CF.formula_or_f2)
  in
  helper f0

let is_empty_wop opf=
  match opf with
    | None -> false
    | Some f ->  is_empty_f f

let is_unk_f f=
   match f with
    | CF.Base fb ->
        (CF.is_unkown_heap fb.CF.formula_base_heap) &&
            (CP.isConstTrue (MCP.pure_of_mix fb.CF.formula_base_pure))
    | _ -> report_error no_pos "SAU.is_empty_f: not handle yet"

(*for drop hp args*)
let rec retrieve_args_from_locs_helper args locs index res=
  match args with
    | [] -> res
    | a::ss -> if List.mem index locs then
          retrieve_args_from_locs_helper ss locs (index+1) (res@[a])
        else retrieve_args_from_locs_helper ss locs (index+1) res

let retrieve_args_from_locs args locs=
  retrieve_args_from_locs_helper args locs 0 []

let rec eq_spec_var_order_list l1 l2=
  match l1,l2 with
    |[],[] -> true
    | v1::ls1,v2::ls2 ->
        if CP.eq_spec_var v1 v2 then
          eq_spec_var_order_list ls1 ls2
        else false
    | _ -> false

let check_hp_arg_eq (hp1, args1) (hp2, args2)=
  ((CP.eq_spec_var hp1 hp2) && (eq_spec_var_order_list args1 args2))

let eq_two_int_order_list l10 l20=
  let rec helper l1 l2=
    match l1,l2 with
      |[],[] -> true
    | v1::ls1,v2::ls2 ->
        if v1 = v2 then
          helper ls1 ls2
        else false
    | _ -> false
  in
  helper l10 l20

let check_hp_locs_eq (hp1, locs1) (hp2, locs2)=
  ((CP.eq_spec_var hp1 hp2) && (eq_two_int_order_list locs1 locs2))

let check_simp_hp_eq (hp1, _) (hp2, _)=
   (CP.eq_spec_var hp1 hp2)

let find_close_hpargs_x hpargs eqs0=
  let rec assoc_l ls hp=
    match ls with
      | [] -> []
      | (hp1,args1)::tl -> if CP.eq_spec_var hp hp1 then args1
          else assoc_l tl hp
  in
  let rec helper rem_eqs hpargs0=
    match rem_eqs with
      | [] -> hpargs0
      | (hp1,hp2)::tl -> begin
          let args1 = assoc_l hpargs0 hp1 in
          let args2 = assoc_l hpargs0 hp2 in
          let new_hpargs=
            match args1, args2 with
              | [],[] -> []
              | [],_ -> [(hp1,args2)]
              | _,[] -> [(hp2,args1)]
              | _ -> []
          in
          helper tl (hpargs0@new_hpargs)
      end
  in
  let close_hpargs = helper eqs0 hpargs in
  (Gen.BList.remove_dups_eq check_simp_hp_eq close_hpargs)

let find_close_hpargs hpargs eqs0=
  let pr1 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in
  let pr2 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
  Debug.no_2 "find_close_hpargs" pr1 pr2 pr1
      (fun _ _ -> find_close_hpargs_x hpargs eqs0) hpargs eqs0

let check_hp_args_imply (hp1, args1) (hp2, args2)=
  ((CP.eq_spec_var hp1 hp2) && (CP.diff_svl args1 args2 = []))

let elim_eq_shorter_hpargs_x ls=
  let rec loop_helper cur_ls res=
    match cur_ls with
      | [] -> res
      | hpargs::ss ->
          if List.exists (check_hp_args_imply hpargs) res then
            loop_helper ss res
          else loop_helper ss (res@[hpargs])
  in
  let sort_fn (_,args1) (_,args2)=
    (List.length args2) - (List.length args1)
  in
  let sorted_ls = List.sort sort_fn ls in
  let filterd_ls = loop_helper sorted_ls [] in
  (Gen.BList.remove_dups_eq check_simp_hp_eq filterd_ls)

let elim_eq_shorter_hpargs ls=
  let pr = pr_list_ln (pr_pair !CP.print_sv !CP.print_svl) in
  Debug.no_1 "elim_eq_shorter_hpargs" pr pr
      (fun _ -> elim_eq_shorter_hpargs_x ls) ls

let refine_full_unk partial_hp_locs poss_full_hp_args_locs=
  let rec helper poss_full_ls res=
    match poss_full_ls with
      |[] -> res
      | (hp,args,locs)::lss ->
          try
              let locs1 = List.assoc hp partial_hp_locs in
              if (List.length locs1) = (List.length locs) then
                helper lss (res@[(hp,args,locs)])
              else helper lss res
          with Not_found ->
              report_error no_pos "sau.refine_full_unk"
  in
  helper poss_full_hp_args_locs []

let mkHRel hp args pos=
  let eargs = List.map (fun x -> CP.mkVar x pos) args in
   ( CF.HRel (hp, eargs, pos))

let mkHRel_f hp args pos=
  let hf = mkHRel hp args pos in
  CF.formula_of_heap hf pos

let rec get_hdnodes (f: CF.formula)=
  match f with
    | CF.Base fb ->
        get_hdnodes_hf fb.CF.formula_base_heap
    | _ -> report_error no_pos "SAU.is_empty_f: not handle yet"

and get_hdnodes_hf (hf: CF.h_formula) = match hf with
  | CF.DataNode hd -> [hd]
  | CF.Conj {CF.h_formula_conj_h1 = h1; CF.h_formula_conj_h2 = h2} 
  | CF.Star {CF.h_formula_star_h1 = h1; CF.h_formula_star_h2 = h2} 
  | CF.Phase {CF.h_formula_phase_rd = h1; CF.h_formula_phase_rw = h2} 
      -> (get_hdnodes_hf h1)@(get_hdnodes_hf h2)
  | _ -> []

let rec get_data_view_hrel_vars_formula f=
  let rec helper f0=
    match f0 with
      | CF.Base fb -> get_data_view_hrel_vars_bformula fb
      | CF.Exists fe -> get_data_view_hrel_vars_h_formula fe.CF.formula_exists_heap
      | CF.Or orf  -> (helper orf.CF.formula_or_f1)@ (helper orf.CF.formula_or_f2)
  in
  helper f

and get_data_view_hrel_vars_bformula bf=
  get_data_view_hrel_vars_h_formula bf.CF.formula_base_heap

and get_data_view_hrel_vars_h_formula hf=
  let rec helper h=
 match h with
    | CF.Star { CF.h_formula_star_h1 = hf1;
                CF.h_formula_star_h2 = hf2}
    | CF.Conj { CF.h_formula_conj_h1 = hf1;
                CF.h_formula_conj_h2 = hf2;}
    | CF.Phase { CF.h_formula_phase_rd = hf1;
                 CF.h_formula_phase_rw = hf2;} ->
        let ls1 = helper hf1 in
        let ls2 = helper hf2 in
        (ls1@ls2)
    | CF.DataNode hd -> [hd.CF.h_formula_data_node]
    | CF.ViewNode hv -> [hv.CF.h_formula_view_node]
    | CF.HRel (hp,_,_) -> [hp]
    | CF.Hole _
    | CF.HTrue
    | CF.HFalse
    | CF.HEmp -> []
  in
  helper hf

let rec drop_get_hrel f=
  match f with
    | CF.Base fb ->
        let new_hf, hrels = drop_get_hrel_h_formula fb.CF.formula_base_heap in
        (CF.Base {fb with CF.formula_base_heap= new_hf}, hrels)
    | _ -> report_error no_pos "SAU.drop_get_hrel: not handle yet"

(* and drop_get_hrel_bformula bf= *)
(*   drop_get_hrel_h_formula bf.CF.formula_base_heap *)

and drop_get_hrel_h_formula hf=
  let rec helper hf0=
    match hf0 with
      | CF.Star {CF.h_formula_star_h1 = hf1;
                 CF.h_formula_star_h2 = hf2;
                 CF.h_formula_star_pos = pos} ->
          let n_hf1,hrels1 = helper hf1 in
          let n_hf2,hrels2 = helper hf2 in
          (match n_hf1,n_hf2 with
            | (CF.HEmp,CF.HEmp) -> (CF.HEmp,hrels1@hrels2)
            | (CF.HEmp,_) -> (n_hf2,hrels1@hrels2)
            | (_,CF.HEmp) -> (n_hf1,hrels1@hrels2)
            | _ -> (CF.Star {CF.h_formula_star_h1 = n_hf1;
			                CF.h_formula_star_h2 = n_hf2;
			                CF.h_formula_star_pos = pos},
                    hrels1@hrels2)
          )
      | CF.Conj { CF.h_formula_conj_h1 = hf1;
		          CF.h_formula_conj_h2 = hf2;
		          CF.h_formula_conj_pos = pos} ->
          let n_hf1,hrels1 = helper hf1 in
          let n_hf2,hrels2 = helper hf2 in
          (CF.Conj { CF.h_formula_conj_h1 = n_hf1;
		            CF.h_formula_conj_h2 = n_hf2;
		            CF.h_formula_conj_pos = pos},
           hrels1@hrels2)
      | CF.Phase { CF.h_formula_phase_rd = hf1;
		           CF.h_formula_phase_rw = hf2;
		           CF.h_formula_phase_pos = pos} ->
          let n_hf1,hrels1 = helper hf1 in
          let n_hf2,hrels2 = helper hf2 in
          (CF.Phase { CF.h_formula_phase_rd = n_hf1;
		             CF.h_formula_phase_rw = n_hf2;
		             CF.h_formula_phase_pos = pos},
          hrels1@hrels2)
      | CF.DataNode hd -> (hf0,[])
      | CF.ViewNode hv -> (hf0,[])
      | CF.HRel (sv, eargs, _) -> (CF.HEmp,
                                   [(sv,List.concat (List.map CP.afv eargs))])
      | CF.Hole _
      | CF.HTrue
      | CF.HFalse
      | CF.HEmp -> (hf0,[])
  in
  helper hf


let rec drop_data_hrel_except_x dn_names hpargs f=
  match f with
    | CF.Base fb ->
        let new_hf = drop_data_hrel_except_hf dn_names hpargs fb.CF.formula_base_heap in
        let new_p = CP.filter_var_new (MCP.pure_of_mix fb.CF.formula_base_pure) (dn_names@hpargs) in
        (CF.Base {fb with
            CF.formula_base_heap= new_hf;
            CF.formula_base_pure = MCP.mix_of_pure new_p;
        })
    | _ -> report_error no_pos "SAU.drop_get_hrel: not handle yet"

and drop_data_hrel_except dn_names hpargs f=
  let pr1=Cprinter.prtt_string_of_formula in
  Debug.no_3 "drop_data_hrel_except" !CP.print_svl !CP.print_svl pr1 pr1
      (fun _ _ _ -> drop_data_hrel_except_x dn_names hpargs f) dn_names hpargs f

and drop_data_hrel_except_hf dn_names hpargs hf=
  let rec helper hf0=
    match hf0 with
      | CF.Star {CF.h_formula_star_h1 = hf1;
                 CF.h_formula_star_h2 = hf2;
                 CF.h_formula_star_pos = pos} ->
          let n_hf1 = helper hf1 in
          let n_hf2 = helper hf2 in
          (match n_hf1,n_hf2 with
            | (CF.HEmp,CF.HEmp) -> (CF.HEmp)
            | (CF.HEmp,_) -> (n_hf2)
            | (_,CF.HEmp) -> (n_hf1)
            | _ -> (CF.Star {CF.h_formula_star_h1 = n_hf1;
			                CF.h_formula_star_h2 = n_hf2;
			                CF.h_formula_star_pos = pos})
          )
      | CF.Conj { CF.h_formula_conj_h1 = hf1;
		          CF.h_formula_conj_h2 = hf2;
		          CF.h_formula_conj_pos = pos} ->
          let n_hf1 = helper hf1 in
          let n_hf2 = helper hf2 in
          CF.Conj { CF.h_formula_conj_h1 = n_hf1;
		            CF.h_formula_conj_h2 = n_hf2;
		            CF.h_formula_conj_pos = pos}
      | CF.Phase { CF.h_formula_phase_rd = hf1;
		           CF.h_formula_phase_rw = hf2;
		           CF.h_formula_phase_pos = pos} ->
          let n_hf1 = helper hf1 in
          let n_hf2 = helper hf2 in
          CF.Phase { CF.h_formula_phase_rd = n_hf1;
		             CF.h_formula_phase_rw = n_hf2;
		             CF.h_formula_phase_pos = pos}
      | CF.DataNode hd -> if CP.mem_svl hd.CF.h_formula_data_node dn_names then
            hf0 else CF.HEmp
      | CF.ViewNode hv -> hf0
      | CF.HRel (_, eargs, _) ->
          let args1 = List.concat (List.map CP.afv eargs) in
          if CP.diff_svl args1 hpargs = [] then hf0 else CF.HEmp
      | CF.Hole _
      | CF.HTrue
      | CF.HFalse
      | CF.HEmp -> hf0
  in
  helper hf


let get_ptrs hf0=
  let rec helper hf=
    match hf with
      | CF.Star {CF.h_formula_star_h1 = hf1;
                 CF.h_formula_star_h2 = hf2;}
      | CF.Conj { CF.h_formula_conj_h1 = hf1;
		          CF.h_formula_conj_h2 = hf2;}
      | CF.Phase { CF.h_formula_phase_rd = hf1;
		           CF.h_formula_phase_rw = hf2;} ->
          (helper hf1)@(helper hf2)
      | CF.DataNode hd ->([hd.CF.h_formula_data_node]@
                                 (List.filter (fun (CP.SpecVar (t,_,_)) -> is_pointer t) hd.CF.h_formula_data_arguments))
      | CF.ViewNode hv -> ([hv.CF.h_formula_view_node]@
               (List.filter (fun (CP.SpecVar (t,_,_)) -> is_pointer t) hv.CF.h_formula_view_arguments))
      | CF.HRel (sv, eargs, _) -> List.concat (List.map CP.afv eargs)
      | _ -> []
  in
  helper hf0

let rec drop_hrel_match_args f args=
  match f with
    | CF.Base fb -> let nfb = drop_hrel_match_args_hf fb.CF.formula_base_heap args in
        (CF.Base {fb with CF.formula_base_heap =  nfb;})
    | CF.Or orf -> let nf1 =  drop_hrel_match_args orf.CF.formula_or_f1 args in
                let nf2 =  drop_hrel_match_args orf.CF.formula_or_f2 args in
       ( CF.Or {orf with CF.formula_or_f1 = nf1;
                CF.formula_or_f2 = nf2;})
    | CF.Exists fe -> let nfe = drop_hrel_match_args_hf fe.CF.formula_exists_heap args in
        (CF.Exists {fe with CF.formula_exists_heap = nfe ;})

and drop_hrel_match_args_hf hf0 args=
  let rec helper hf=
    match hf with
      | CF.Star {CF.h_formula_star_h1 = hf1;
              CF.h_formula_star_h2 = hf2;
              CF.h_formula_star_pos = pos} ->
          let n_hf1 = helper hf1 in
          let n_hf2 = helper hf2 in
          let newf =
            (match n_hf1,n_hf2 with
              | (CF.HEmp,CF.HEmp) -> CF.HEmp
              | (CF.HEmp,_) -> n_hf2
              | (_,CF.HEmp) -> n_hf1
              | _ -> (CF.Star {CF.h_formula_star_h1 = n_hf1;
                            CF.h_formula_star_h2 = n_hf2;
                            CF.h_formula_star_pos = pos})
            ) in
          (newf)
      | CF.Conj { CF.h_formula_conj_h1 = hf1;
               CF.h_formula_conj_h2 = hf2;
               CF.h_formula_conj_pos = pos} ->
          let n_hf1 = helper hf1 in
          let n_hf2 = helper hf2 in
          (CF.Conj { CF.h_formula_conj_h1 = n_hf1;
                  CF.h_formula_conj_h2 = n_hf2;
                  CF.h_formula_conj_pos = pos})
      | CF.Phase { CF.h_formula_phase_rd = hf1;
                CF.h_formula_phase_rw = hf2;
                CF.h_formula_phase_pos = pos} ->
          let n_hf1 = helper hf1 in
          let n_hf2 = helper hf2 in
          (CF.Phase { CF.h_formula_phase_rd = n_hf1;
                   CF.h_formula_phase_rw = n_hf2;
                   CF.h_formula_phase_pos = pos})
      | CF.DataNode hd -> (hf)
      | CF.ViewNode hv -> (hf)
      | CF.HRel (_,eargs1,_) ->
          let args1 = List.fold_left List.append [] (List.map CP.afv eargs1) in
          if eq_spec_var_order_list args args1 then (CF.HEmp)
          else (hf)
      | CF.Hole _
      | CF.HTrue
      | CF.HFalse
      | CF.HEmp -> (hf)
  in
  helper hf0

(*==============*)
(*for unk hps*)
(*check whether args of an is in keep_ptrs*)
let get_intersect_hps keep_ptrs (hp, args)=
  (*may need closed*)
  Debug.ninfo_pprint (" keep_ptrs: "^ (!CP.print_svl keep_ptrs)) no_pos;
  Debug.ninfo_pprint (" args: "^ (!CP.print_svl args)) no_pos;
  let interse = CP.intersect_svl args keep_ptrs in
  if interse = [] then [] else [hp]

(*for drop non-selective subformulas*)
(*check a data node does not belong to a set of data node name*)
let check_nbelongsto_dnode dn dn_names=
      List.for_all (fun dn_name -> not(CP.eq_spec_var dn.CF.h_formula_data_node dn_name)) dn_names

(*check a view node does not belong to a set of view node name*)
let check_nbelongsto_vnode vn vn_names=
      List.for_all (fun vn_name -> not(CP.eq_spec_var vn.CF.h_formula_view_node vn_name)) vn_names

let check_neq_hrelnode id ls=
      not (CP.mem_svl id ls)

(*check a data node belongs to a list of data node names*)
let select_dnode dn1 dn_names=
  List.exists (CP.eq_spec_var dn1.CF.h_formula_data_node) dn_names

(*check a view node belongs to a list of view node names*)
let select_vnode vn1 vn_names=
    (*return subst of args and add in lhs*)
  List.exists (CP.eq_spec_var vn1.CF.h_formula_view_node) vn_names

let select_hrel =  CP.mem_svl

let rec look_up_ptr_args_data_node_x hd=
  List.filter CP.is_node_typ hd.CF.h_formula_data_arguments
  (*data nodes*)
  (* let data_def =  C.look_up_data_def no_pos prog.C.prog_data_decls hd.CF.h_formula_data_name in *)
  (* (\*get prototype of a node declaration*\) *)
  (* let args = List.map (fun (t,_) -> t) data_def.C.data_fields in *)
  (* (\*combine with actual areg*\) *)
  (* let targs = List.combine args hd.CF.h_formula_data_arguments in *)
  (* (\*get pointer*\) *)
  (* snd (List.split (List.filter (fun (t, v) -> is_pointer t) targs)) *)

and look_up_ptr_args_data_node hd=
  let pr1 = fun dn -> dn.CF.h_formula_data_name in
Debug.no_1 " look_up_ptr_args_data_node" pr1 !CP.print_svl
    (fun _ ->  look_up_ptr_args_data_node_x hd) hd

(* let loop_up_ptr_args_view_node prog hv= *)
(*   (\*view node*\) *)
(*   let view_def =  Cast.look_up_view_def no_pos prog.Cast.prog_view_decls hv.CF.h_formula_view_name in *)
(*   (\*get prototype of a node declaration*\) *)
(*   let args = List.map (fun (t,_) -> t) view_def.Cast.view_fields in *)
(*   (\*combine with actual areg*\) *)
(*   let targs = List.combine args hd.CF.h_formula_view_arguments in *)
(*   (\*get pointer*\) *)
(*   snd (List.split (List.filter (fun (t, v) -> is_pointer t) targs)) *)

and look_up_ptr_args_one_node prog hd_nodes hv_nodes node_name=
  let rec look_up_data_node ls=
    match ls with
      | [] -> []
      | dn::ds ->
          if CP.eq_spec_var node_name dn.CF.h_formula_data_node then
            (* loop_up_ptr_args_data_node prog dn *)
              List.filter CP.is_node_typ dn.CF.h_formula_data_arguments
          else
              (* let args =  List.filter CP.is_node_typ dn.CF.h_formula_data_arguments in *)
          (*     if (CP.intersect_svl args cur_ptrs) <> [] then *)
          (*       [dn.CF.h_formula_data_node] *)
          (*     else [] *)
          (* in *)
            look_up_data_node ds
  in
  (* let rec look_up_view_node ls= *)
  (*   match ls with *)
  (*     | [] -> [] *)
  (*     | dn::ds -> if CP.eq_spec_var node_name dn.CF.h_formula_view_node then *)
  (*           loop_up_ptr_args_view_node prog hd *)
  (*         else look_up_view_node ds *)
  (* in *)
  let ptrs = look_up_data_node hd_nodes in
  (* if ptrs = [] then look_up_view_node hv_nodes *)
  (* else *) ptrs

(*should improve: should take care hrel also*)
let look_up_closed_ptr_args prog hd_nodes hv_nodes node_names=
  let rec helper old_ptrs inc_ptrs=
    let new_ptrs = List.concat
      (List.map (look_up_ptr_args_one_node prog hd_nodes hv_nodes)
           inc_ptrs) in
    let diff_ptrs = List.filter (fun id -> not (CP.mem_svl id old_ptrs)) new_ptrs in
    let diff_ptrs = Gen.BList.remove_dups_eq CP.eq_spec_var diff_ptrs in
    if diff_ptrs = [] then old_ptrs
    else (helper (old_ptrs@diff_ptrs) diff_ptrs)
  in
  helper node_names node_names

let look_up_backward_closed_ptr_args_x prog hd_nodes hv_nodes node_names=
  let rec find_pt_new cur_hds svl res hd_rest=
    match cur_hds with
      | [] -> res,hd_rest
      | hd::tl -> let ptr_args = List.filter CP.is_node_typ hd.CF.h_formula_data_arguments in
                  if ( CP.intersect_svl ptr_args (svl@res) <> []) then
                    find_pt_new tl svl (res@[hd.CF.h_formula_data_node]@ptr_args) hd_rest
                  else find_pt_new tl svl res (hd_rest@[hd])
  in
  let rec loop_helper hds svl r=
    let r1,rest = find_pt_new hds svl r [] in
    if CP.diff_svl r1 r = [] || rest = [] then (CP.remove_dups_svl r1) else
      loop_helper rest svl r1
  in
  loop_helper hd_nodes node_names []

let look_up_backward_closed_ptr_args prog hd_nodes hv_nodes node_names=
  let pr1 = !CP.print_svl in
  Debug.no_1 "look_up_backward_closed_ptr_args" pr1 pr1
      (fun _ -> look_up_backward_closed_ptr_args_x prog hd_nodes hv_nodes node_names)
      node_names

let rec lookup_undef_args args undef_args def_ptrs=
  match args with
    | [] -> undef_args
    | a::ax -> if CP.mem_svl a def_ptrs then (*defined: omit*)
          lookup_undef_args ax undef_args def_ptrs
        else (*undefined *)
          lookup_undef_args ax (undef_args@[a]) def_ptrs

(*=======utilities for infer_collect_hp_rel=======*)
(*defined pointers list *
  for recursive constraint(HP name *
 parameter name list)*)
(*todo: how about null? is it defined?*)
let rec find_defined_pointers_raw prog f=
  let hds, hvs, hrs = CF.get_hp_rel_formula f in
  let ( _,mix_f,_,_,_) = CF.split_components f in
  let eqs = (MCP.ptr_equations_without_null mix_f) in
  let eqNulls = CP.remove_dups_svl ( MCP.get_null_ptrs mix_f) in
  (*defined vars=  + null + data + view*)
  let def_vs = (* (eqNulls) @ *) (List.map (fun hd -> hd.CF.h_formula_data_node) hds)
   @ (List.map (fun hv -> hv.CF.h_formula_view_node) hvs) in
  (*find closed defined pointers set*)
  (* let def_vs0 = CP.remove_dups_svl def_vs in *)
  let def_vs_wo_args = CP.remove_dups_svl ((List.fold_left close_def def_vs eqs)) in
  (def_vs_wo_args, hds, hvs, hrs, eqs,eqNulls)

and check_node_args_defined prog def_svl hd_nodes hv_nodes dn_name=
  let arg_svl = look_up_ptr_args_one_node prog hd_nodes hv_nodes dn_name in
  (* DD.info_pprint ("  arg_svl" ^ (!CP.print_svl arg_svl)) no_pos; *)
  (* DD.info_pprint ("  def_svl" ^ (!CP.print_svl def_svl)) no_pos; *)
  if arg_svl = [] then false else
    let diff_svl = Gen.BList.difference_eq CP.eq_spec_var arg_svl def_svl in
  (* DD.info_pprint ("  diff_svl" ^ (!CP.print_svl diff_svl)) no_pos; *)
    if diff_svl = [] then true
    else false

and find_defined_pointers_after_preprocess prog def_vs_wo_args hds hvs hrs eqs eqNulls predef_ptrs=
  let tmp = def_vs_wo_args in
  let predef = find_close (def_vs_wo_args@predef_ptrs) eqs in
  (* DD.info_pprint ("   defined raw " ^(!CP.print_svl tmp)) no_pos; *)
  let def_vs = List.filter (check_node_args_defined prog predef hds hvs) tmp in
  (*(HP name * parameter name list)*)
  let hp_paras = List.map
                (fun (id, exps, _) -> (id, List.concat (List.map CP.afv exps)))
                hrs in
  (def_vs@eqNulls, hp_paras, hds, hvs, eqs)

and find_defined_pointers_x prog f predef_ptrs=
  let (def_vs, hds, hvs, hrs, eqs,eqNulls) = find_defined_pointers_raw prog f in
  find_defined_pointers_after_preprocess prog def_vs hds hvs hrs eqs eqNulls predef_ptrs

and find_defined_pointers prog f predef_ptrs=
  let pr1 = !CP.print_svl in
  let pr2 = pr_list_ln (pr_pair !CP.print_sv pr1) in
  (* let pr3 = fun x -> Cprinter.string_of_h_formula (CF.HRel x) in *)
  let pr4 = fun (a1, a2, _, _, _) ->
      let pr = pr_pair pr1 pr2 in pr (a1,a2)
  in
  Debug.no_2 "find_defined_pointers" Cprinter.prtt_string_of_formula pr1 pr4
      (fun _ _ -> find_defined_pointers_x prog f predef_ptrs) f predef_ptrs

let get_raw_defined_w_pure_x prog predef lhs rhs=
  let helper f eqs=
    match f with
      | CF.Base fb ->
          let def_raw,_,_,_,leqs,eqNulls = find_defined_pointers_raw prog f in
          let def_raw1 = CP.remove_dups_svl (def_raw@eqNulls) in
          (def_raw1,leqs)
      | _ -> report_error no_pos "sau.get_raw_defined_w_pure: not handle yet"
  in
  let lsvl,leqs = helper lhs [] in
  let rsvl,reqs = helper rhs leqs in
  let eqs = (leqs@reqs) in
  let svl = lsvl@rsvl@predef in
  let svl1 = if eqs = [] then svl else
                (List.fold_left close_def svl eqs)
  in
  (CP.remove_dups_svl svl1)

let get_raw_defined_w_pure prog predef lhs rhs=
  let pr1 = Cprinter.prtt_string_of_formula in
  let pr2 = !CP.print_svl in
  Debug.no_2 "get_raw_defined_w_pure" pr1 pr1 pr2
      (fun _ _ -> get_raw_defined_w_pure_x prog predef lhs rhs) lhs rhs

let keep_data_view_hrel_nodes prog f hd_nodes hv_nodes keep_rootvars keep_hrels=
  let keep_ptrs = look_up_closed_ptr_args prog hd_nodes hv_nodes keep_rootvars in
  CF.drop_data_view_hrel_nodes f check_nbelongsto_dnode check_nbelongsto_vnode
    check_neq_hrelnode keep_ptrs keep_ptrs keep_hrels

let filter_var prog svl f=
  (* let (def_vs_wo_args, hd_nodes, hv_nodes, hrels, eqs) = find_defined_pointers_raw prog f in *)
  let hd_nodes,hv_nodes,hrels = CF.get_hp_rel_formula f in
  let ls_hpargs = List.map (fun (hp,eargs,_) -> (hp, List.concat (List.map CP.afv eargs))) hrels in
  let keep_ptrs = look_up_closed_ptr_args prog hd_nodes hv_nodes svl in
  let keep_ptrs1 = CP.remove_dups_svl keep_ptrs in
  let keep_hps = List.concat (List.map (get_intersect_hps keep_ptrs1) ls_hpargs) in
  CF.drop_data_view_hrel_nodes f check_nbelongsto_dnode check_nbelongsto_vnode
      check_neq_hrelnode keep_ptrs1 keep_ptrs1 keep_hps

let keep_data_view_hrel_nodes_fb prog fb hd_nodes hv_nodes keep_rootvars keep_hrels=
  let keep_ptrs = look_up_closed_ptr_args prog hd_nodes hv_nodes keep_rootvars in
  CF.drop_data_view_hrel_nodes_fb fb check_nbelongsto_dnode check_nbelongsto_vnode
    check_neq_hrelnode keep_ptrs keep_ptrs keep_hrels keep_ptrs

let keep_data_view_hrel_nodes_two_f prog lhs rhs hd_nodes hv_nodes eqs lhs_hpargs rhs_keep_rootvars rhs_keep_hrels=
  let keep_ptrs = look_up_closed_ptr_args prog hd_nodes hv_nodes rhs_keep_rootvars in
  let closed_keep_ptrs = find_close (keep_ptrs) eqs in
  let lhs_keep_hrels = List.concat (List.map (get_intersect_hps closed_keep_ptrs) lhs_hpargs) in
  let nf1 = CF.drop_data_view_hrel_nodes lhs check_nbelongsto_dnode check_nbelongsto_vnode check_neq_hrelnode keep_ptrs closed_keep_ptrs lhs_keep_hrels in
  let nf2 = CF.drop_data_view_hrel_nodes rhs check_nbelongsto_dnode check_nbelongsto_vnode check_neq_hrelnode keep_ptrs closed_keep_ptrs rhs_keep_hrels in
  (nf1,nf2)

let keep_data_view_hrel_nodes_two_fbs prog f1 f2 hd_nodes hv_nodes hpargs leqs reqs his_ss keep_rootvars lrootvars (* lback_keep_ptrs *) lkeep_hrels rkeep_hrels
      unk_svl prog_vars =
  let filter_eqs keep_svl eqs0=
    let rec helper eqs res=
      match eqs with
        | [] -> res
        | (sv1,sv2)::ss ->
            let b1 = CP.mem_svl sv1 keep_svl in
            let b2 = CP.mem_svl sv2 keep_svl in
            let new_eq=
              match b1,b2 with
                | true,false -> [((* CP.subs_one res *) sv2, (* CP.subs_one res *) sv1)] (*m_apply_par*)
                | true,true -> begin
                    let c1 = CP.mem_svl sv1 prog_vars in
                    let c2 = CP.mem_svl sv2 prog_vars in
                    match c1,c2 with
                      | true,false -> [((* CP.subs_one res *) sv2, (* CP.subs_one res *) sv1)]
                      | _ -> [((* CP.subs_one res *) sv1, (* CP.subs_one res *) sv2)]
                end
                | false,true -> [((* CP.subs_one res *) sv1, (* CP.subs_one res *) sv2)]
                | _ -> []
            in
            helper ss (res@new_eq)
    in
    helper eqs0 []
  in
  let filter_fn null_svl p=
    if CP.is_eq_exp p then
      let p_svl = CP.fv p in
      (CP.diff_svl p_svl null_svl) <> []
    else true
  in
  let filter_eq_in_one_hp_x eqs hpargs=
    let helper l_eqs (_,args)=
      List.filter (fun (sv1,sv2) -> not (CP.mem_svl sv1 args && CP.mem_svl sv2 args) &&
      not (CP.mem_svl sv1 unk_svl || CP.mem_svl sv2 unk_svl)) l_eqs
    in
    List.fold_left helper eqs hpargs
  in
  let filter_eq_in_one_hp eqs hpargs=
    let pr1 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
    let pr2 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in
    Debug.no_2 "filter_eq_in_one_hp" pr1 pr2 pr1
        (fun _ _ -> filter_eq_in_one_hp_x eqs hpargs) eqs hpargs
  in
   let rec keep_prog_vars_helper eqs res=
    match eqs with
      | [] -> res
      | (sv1,sv2)::tl ->
          let new_eq=
            let c1 = CP.mem_svl sv1 prog_vars in
            let c2 = CP.mem_svl sv2 prog_vars in
            match c1,c2 with
              | true,false -> [(sv2, sv1)]
              | _ -> [(sv1, sv2)]
          in
          keep_prog_vars_helper tl (res@new_eq)
  in
  let eqs = (leqs@reqs@his_ss) in
  let _ = Debug.ninfo_pprint ("keep_vars root: " ^ (!CP.print_svl keep_rootvars)) no_pos in
  let keep_closed_rootvars =  (List.fold_left close_def keep_rootvars eqs) in
  let _ = Debug.ninfo_pprint ("keep_vars 1: " ^ (!CP.print_svl keep_closed_rootvars)) no_pos in
  let keep_vars = look_up_closed_ptr_args prog hd_nodes hv_nodes (CP.remove_dups_svl (keep_closed_rootvars)) in
  (*get backward ptrs*)
  (* let lback_keep_ptrs = look_up_backward_closed_ptr_args prog hd_nodes hv_nodes lrootvars in *)
  (* let lback_keep_closed_vars = CP.remove_dups_svl (List.fold_left close_def (lback_keep_ptrs) eqs) in *)
  let lhs_keep_closed_rootvars = CP.remove_dups_svl (List.fold_left close_def (lrootvars) eqs) in
  let _ = Debug.ninfo_pprint ("keep_vars 1: " ^ (!CP.print_svl keep_closed_rootvars)) no_pos in
  let lkeep_vars = look_up_closed_ptr_args prog hd_nodes hv_nodes lhs_keep_closed_rootvars in
  (* let closed_lback_keep_ptrs = (CP.remove_dups_svl (List.fold_left close_def (lback_keep_ptrs) leqs)) in *)
  (*may be alisas between lhs and rhs*)
  let _ = Debug.ninfo_pprint ("keep_vars: " ^ (!CP.print_svl keep_vars)) no_pos in
  let _ = Debug.ninfo_pprint ("lhs keep_vars: " ^ (!CP.print_svl lkeep_vars)) no_pos in
  let nf1 = CF.drop_data_view_hrel_nodes_fb f1 check_nbelongsto_dnode check_nbelongsto_vnode check_neq_hrelnode (keep_vars(* @closed_lback_keep_ptrs *)) (keep_vars(* @closed_lback_keep_ptrs *)) lkeep_hrels (keep_vars@lkeep_vars) in
  let nf2 = CF.drop_data_view_hrel_nodes_fb f2 check_nbelongsto_dnode check_nbelongsto_vnode check_neq_hrelnode keep_vars keep_vars rkeep_hrels keep_vars in
  let _ = Debug.ninfo_pprint ("nf1: " ^ (Cprinter.string_of_formula_base nf1)) no_pos in
  let _ = Debug.ninfo_pprint ("nf2: " ^ (Cprinter.string_of_formula_base nf2)) no_pos in
  (*make explicit null ptrs*)
  let largs= CF.h_fv nf1.CF.formula_base_heap in
  let rargs= CF.h_fv nf2.CF.formula_base_heap in
  let all_args = CP.remove_dups_svl (largs@rargs) in
  (*lhs - nf1*)
  let eqs = (MCP.ptr_equations_without_null nf1.CF.formula_base_pure) in
  (* let _ = DD.info_pprint ("      eqs: " ^ (let pr = pr_list(pr_pair !CP.print_sv !CP.print_sv) in pr eqs)) no_pos in *)
  let eqNulls = CP.remove_dups_svl (MCP.get_null_ptrs nf1.CF.formula_base_pure) in
  let eqNulls1 = find_close eqNulls eqs in
  (* let _ = DD.info_pprint ("      eqNulls1: " ^ (!CP.print_svl eqNulls1)) no_pos in *)
  let eqNulls2 = List.filter (fun sv -> CP.mem_svl sv all_args) eqNulls1 in
  (* let _ = DD.info_pprint ("      eqNulls2: " ^ (!CP.print_svl eqNulls2)) no_pos in *)
  let null_ps = List.map (fun sv -> CP.mkNull sv no_pos) eqNulls2 in
  let new_eqs = filter_eqs all_args eqs in
  let new_eqs1 = List.filter (fun (sv1,sv2) -> not (CP.mem_svl sv1 eqNulls2 && CP.mem_svl sv2 eqNulls2)) new_eqs in
  let new_eqs1 = filter_eq_in_one_hp new_eqs1 hpargs in
  let nf1a = CF.subst_b new_eqs1 nf1 in
  let _ = Debug.ninfo_pprint ("nf1a: " ^ (Cprinter.string_of_formula_base nf1a)) no_pos in
  let ps10 = CP.list_of_conjs (MCP.pure_of_mix nf1a.CF.formula_base_pure) in
  let new_ps10 = (* List.map (CP.subst new_eqs) *) ps10 in
  let new_ps11 = List.filter (filter_fn eqNulls2) new_ps10 in
  let new_ps12 = new_ps11@null_ps  in
  let new_ps13 = CP.remove_redundant_helper new_ps12 [] in
  let new_p13 = CP.conj_of_list new_ps13 no_pos in
  let nf11 = {nf1a with CF.formula_base_pure = MCP.mix_of_pure new_p13} in
  (*rhs - nf2: not handle yet*)
  let new_nf2 = CF.subst_b (new_eqs1@reqs) nf2 in
  (*subst again*)
  let nleqs = (MCP.ptr_equations_without_null nf11.CF.formula_base_pure) in
  let nreqs = (MCP.ptr_equations_without_null new_nf2.CF.formula_base_pure) in
  let nleqs1 = List.filter (fun (sv1,sv2) -> not (CP.mem_svl sv1 eqNulls2 && CP.mem_svl sv2 eqNulls2)) nleqs in
  let nleqs2 = filter_eq_in_one_hp nleqs1 hpargs in
  let nreqs1 = List.filter (fun (sv1,sv2) -> not (CP.mem_svl sv1 eqNulls2 && CP.mem_svl sv2 eqNulls2)) nreqs in
  let nreqs2 = filter_eq_in_one_hp nreqs1 hpargs in
  let nleqs3 =  keep_prog_vars_helper nleqs2 [] in
  let lhs_b2 = CF.subst_b (nleqs3) nf11 in (*m_apply_par*)
  let rhs_b2 = CF.subst_b (nleqs3@nreqs2) new_nf2 in
  (lhs_b2,rhs_b2)

let rec drop_data_view_hrel_nodes_from_root prog f hd_nodes hv_nodes eqs drop_rootvars well_defined_svl=
  match f with
    | CF.Base fb ->
        let hd_names = List.fold_left (fun ls hd -> ls@[hd.CF.h_formula_data_node]) [] hd_nodes in
        let keep_hds = CP.diff_svl hd_names drop_rootvars in
        let closed_keep_svl = look_up_closed_ptr_args prog hd_nodes hv_nodes keep_hds in
        let well_defined_svl1 = CP.diff_svl well_defined_svl closed_keep_svl in
        let new_p=
          if well_defined_svl1 = [] then fb.CF.formula_base_pure else
            let pure_keep_svl = CP.diff_svl (CF.fv f) well_defined_svl1 in
            MCP.mix_of_pure (CP.filter_var_new
                  (MCP.pure_of_mix fb.CF.formula_base_pure) pure_keep_svl)
        in
        CF.Base { fb with
            CF.formula_base_heap = drop_data_view_hrel_nodes_hf_from_root
                prog fb.CF.formula_base_heap
                hd_nodes hv_nodes eqs (drop_rootvars@well_defined_svl1);
            CF.formula_base_pure = new_p
    }
      | _ -> report_error no_pos "sau.drop_data_view_hrel_nodes"


and drop_data_view_hrel_nodes_hf_from_root prog hf hd_nodes hv_nodes eqs drop_rootvars=
  let _ = Debug.ninfo_pprint ("drop_vars root: " ^ (!CP.print_svl drop_rootvars)) no_pos in
  (* let drop_closed_rootvars = CP.remove_dups_svl (List.fold_left close_def drop_rootvars eqs) in *)
  let _ = Debug.ninfo_pprint ("close drop_rootvars: " ^ (!CP.print_svl drop_rootvars)) no_pos in
  let drop_vars = look_up_closed_ptr_args prog hd_nodes hv_nodes drop_rootvars in
  (*may be alisas between lhs and rhs*)
  let _ = Debug.ninfo_pprint ("drop_vars: " ^ (!CP.print_svl drop_vars)) no_pos in
  let nhf = CF.drop_data_view_hrel_nodes_hf hf select_dnode select_vnode select_hrel drop_vars drop_vars drop_vars in
  let _ = Debug.ninfo_pprint ("nhf: " ^ (Cprinter.string_of_h_formula nhf)) no_pos in
  nhf

(*END for drop non-selective subformulas*)
(************************************************************)
 (****************(*for infer_collect_hp*)*****************)
(************************************************************)
let update_hp_args hf renamed_hps=
  let rec look_up_helper hp0 args0 ls_hp_args=
    match ls_hp_args with
      | [] -> false,[]
      | (hp1,old_args1,new_args1)::hs ->
          if CP.eq_spec_var hp0 hp1 && (eq_spec_var_order_list args0 old_args1)  then (true, new_args1)
          else look_up_helper hp0 args0 hs
  in
  let rec helper hf0=
    match hf0 with
      | CF.HRel (hp, eargs, p ) ->
          let args0 = (List.fold_left List.append [] (List.map CP.afv eargs)) in
          let r,args1= look_up_helper hp args0 renamed_hps in
          if r then (CF.HRel (hp,List.map (fun sv -> CP.mkVar sv p) args1, p))
          else hf0
      | CF.Conj hfc ->
          CF.Conj {hfc with CF.h_formula_conj_h1=helper hfc.CF.h_formula_conj_h1;
              CF.h_formula_conj_h2=helper hfc.CF.h_formula_conj_h2;}
      | CF.Star hfs ->
          CF.Star {hfs with CF.h_formula_star_h1=helper hfs.CF.h_formula_star_h1;
              CF.h_formula_star_h2=helper hfs.CF.h_formula_star_h2;}
      | CF.Phase hfp->
           CF.Phase{hfp with CF.h_formula_phase_rd=helper hfp.CF.h_formula_phase_rd;
              CF.h_formula_phase_rw=helper hfp.CF.h_formula_phase_rw;}
      | _ -> hf0
  in
  helper hf

let test_and_update fb renamed_hps ls_new_p pos=
  if ls_new_p = [] then fb
    else
    begin
        {fb with CF.formula_base_heap =
                update_hp_args fb.CF.formula_base_heap renamed_hps;
            CF.formula_base_pure = MCP.mix_of_pure (List.fold_left
               (fun p1 p2-> CP.mkAnd p1 p2 pos)(List.hd ls_new_p)
               (List.tl ls_new_p))}
    end

let rename_hp_args_x lfb rfb=
  let lp = MCP.pure_of_mix lfb.CF.formula_base_pure in
  let lpos = (CP.pos_of_formula lp) in
  let lhf = lfb.CF.formula_base_heap in
  let lls_hp_args = CF.get_HRels lhf in
  (*rhs*)
  let rp = MCP.pure_of_mix rfb.CF.formula_base_pure in
  let rpos = (CP.pos_of_formula rp) in
  let rhf = rfb.CF.formula_base_heap in
  let rls_hp_args = CF.get_HRels rhf in
  let rec lhelper args1 args2 p r=
    match args2 with
      | [] -> r,p,args1
      | a1::ass -> if CP.mem_svl a1 args1 then
            let new_v = CP.SpecVar (CP.type_of_spec_var a1,
                  "v_" ^ (string_of_int (Globals.fresh_int())),Unprimed)  in
            let p1 =
              (* if CP.isConstTrue p then *)
                CP.mkPtrEqn a1 new_v lpos
              (* else *)
              (*   let ss = List.combine [a1] [new_v] in *)
              (*   let p0 = CP.filter_var_new p [a1] in *)
              (*   CP.subst ss p0 *)
            in
            let p2 = CP.mkAnd p p1 lpos in
            lhelper (args1@[new_v]) ass p2 true
          else lhelper (args1@[a1]) ass p r
  in
  let rec rhelper args1 args2 lp rp r=
    match args2 with
      | [] -> r,lp,rp,args1
      | a1::ass -> if CP.mem_svl a1 args1 then
            let new_v = CP.SpecVar (CP.type_of_spec_var a1,
                  "v_" ^ (string_of_int (Globals.fresh_int())),Unprimed)  in
            let rp1 =
              (* if CP.isConstTrue rp then *)
                CP.mkPtrEqn a1 new_v rpos
              (* else *)
              (*   let rp0 = CP.filter_var_new rp [a1] in *)
              (*   CP.subst ss rp0 *)
            in
            let rp2 = CP.mkAnd rp rp1 rpos in
            rhelper (args1@[new_v]) ass lp rp2 true
          else rhelper (args1@[a1]) ass lp rp r
  in
  let rename_one_lhp (hp,args)=
    let r,np,new_args= lhelper [] args lp false in
    if r then [((hp,args,new_args),np)] else []
  in
  let rename_one_rhp (hp,args)=
    let r,nlp,nrp,new_args= rhelper [] args lp rp false in
    if r then [((hp,args,new_args),(nlp,nrp))] else []
  in
  let lpair = List.concat (List.map rename_one_lhp lls_hp_args) in
  let rpair = List.concat (List.map rename_one_rhp rls_hp_args) in
  let lrenamed_hps,lls_p= List.split lpair in
  let rrenamed_hps,rls_p= List.split rpair in
  let lrls_p,rrls_p = List.split rls_p in
  let l_new_hps = lrenamed_hps@rrenamed_hps in
  let l_new_p = lls_p@lrls_p in
  let new_lb= test_and_update lfb l_new_hps l_new_p lpos in
  let new_rb = test_and_update rfb rrenamed_hps rrls_p rpos in
  (new_lb,new_rb)

let rename_hp_args lfb rfb=
  let pr=Cprinter.prtt_string_of_formula_base in
  Debug.no_2 "rename_hp_args" pr pr (pr_pair pr pr)
      (fun _ _ -> rename_hp_args_x lfb rfb) lfb rfb

(************************************************************)
      (*******************END**************************)
(************************************************************)

let rec subst_view_hp_formula view_name hp (f: CF.formula) =
  match f with
    | CF.Base fb -> CF.Base {fb with CF.formula_base_heap = subst_view_hp_h_formula view_name hp fb.CF.formula_base_heap }
    | CF.Exists fe -> CF.Exists {fe with CF.formula_exists_heap = subst_view_hp_h_formula view_name hp fe.CF.formula_exists_heap }
    | CF.Or orf  -> CF.Or { orf with
      CF.formula_or_f1 = subst_view_hp_formula view_name hp orf.CF.formula_or_f1;
      CF.formula_or_f2= subst_view_hp_formula view_name hp orf.CF.formula_or_f2;
    }

and subst_view_hp_h_formula view_name (hp_name, _, p) hf =
  let rec helper hf0=
    match hf0 with
      | CF.Star hfs -> CF.Star {hfs with
          CF.h_formula_star_h1 = helper hfs.CF.h_formula_star_h1;
          CF.h_formula_star_h2 = helper hfs.CF.h_formula_star_h2;}
      | CF.Conj hfc -> CF.Conj {hfc with
          CF.h_formula_conj_h1 = helper hfc.CF.h_formula_conj_h1;
          CF.h_formula_conj_h2 = helper hfc.CF.h_formula_conj_h2;}
      | CF.Phase hfp -> CF.Phase {hfp with
          CF.h_formula_phase_rd = helper hfp.CF.h_formula_phase_rd;
          CF.h_formula_phase_rw = helper hfp.CF.h_formula_phase_rw;}
      | CF.ViewNode hv -> if hv.CF.h_formula_view_name = view_name then
            let n_args = [hv.CF.h_formula_view_node]@hv.CF.h_formula_view_arguments in
            (CF.HRel (hp_name,  List.map (fun x -> CP.mkVar x p) n_args,p))
          else hf0
      | _ -> hf0
  in
  helper hf

(************************************************************)
      (******************CHECKEQ************************)
(************************************************************)
(*==========check_relaxeq=============*)
(*currently we do not submit exists*)
let check_stricteq_hnodes_x stricted_eq hns1 hns2=
  (*allow dangl ptrs have diff names*)
  let all_ptrs =
    if stricted_eq then [] else
    let ptrs1 = List.map (fun hd -> hd.CF.h_formula_data_node) hns1 in
    let ptrs2 = List.map (fun hd -> hd.CF.h_formula_data_node) hns2 in
    CP.remove_dups_svl (ptrs1@ptrs2)
  in
  let check_stricteq_hnode hn1 hn2=
    let arg_ptrs1 = List.filter CP.is_node_typ hn1.CF.h_formula_data_arguments in
    let arg_ptrs2 = List.filter CP.is_node_typ  hn2.CF.h_formula_data_arguments in
    if (hn1.CF.h_formula_data_name = hn2.CF.h_formula_data_name) &&
        (CP.eq_spec_var hn1.CF.h_formula_data_node hn2.CF.h_formula_data_node) then
      let b = eq_spec_var_order_list arg_ptrs1 arg_ptrs2 in
      (*bt-left2: may false if we check set eq as below*)
      let diff1 = (Gen.BList.difference_eq CP.eq_spec_var arg_ptrs1 arg_ptrs2) in
      (* (\*for debugging*\) *)
      (* let _ = Debug.info_pprint ("     arg_ptrs1: " ^ (!CP.print_svl arg_ptrs1)) no_pos in *)
      (* let _ = Debug.info_pprint ("     arg_ptrs2: " ^ (!CP.print_svl arg_ptrs2)) no_pos in *)
      (* let _ = Debug.info_pprint ("     diff1: " ^ (!CP.print_svl diff1)) no_pos in *)
      (*END for debugging*)
      if stricted_eq then (* (diff1=[]) *)b else
          (*allow dangl ptrs have diff names*)
        let diff2 = CP.intersect_svl diff1 all_ptrs in
        (diff2 = [])
    else
      false
  in
  let rec helper hn hns2 rest2=
    match hns2 with
      | [] -> (false,rest2)
      | hn1::hss ->
          if check_stricteq_hnode hn hn1 then
            (true,rest2@hss)
          else helper hn hss (rest2@[hn1])
  in
  let rec helper2 hns1 hns2=
    match hns1 with
      | [] -> if hns2 = [] then true else (not stricted_eq)
      | hn1::rest1 ->
          let r,rest2 = helper hn1 hns2 [] in
          if r then
            helper2 rest1 rest2
          else false
  in
  if (List.length hns1) <= (List.length hns2) then
    helper2 hns1 hns2
  else false

let check_stricteq_hnodes stricted_eq hns1 hns2=
  let pr1 hd = Cprinter.prtt_string_of_h_formula (CF.DataNode hd) in
  let pr2 = pr_list_ln pr1 in
  Debug.no_3 "check_stricteq_hnodes" string_of_bool pr2 pr2 string_of_bool
      (fun _ _ _ -> check_stricteq_hnodes_x stricted_eq hns1 hns2)  stricted_eq hns1 hns2


let check_stricteq_hrels hrels1 hrels2=
   let check_stricteq_hr (hp1, eargs1, _) (hp2, eargs2, _)=
     let r = (CP.eq_spec_var hp1 hp2) in
     (* ((Gen.BList.difference_eq CP.eq_exp_no_aset *)
        (*     eargs1 eargs2)=[]) *)
     if r then
       let ls1 = List.concat (List.map CP.afv eargs1) in
       let ls2 = List.concat (List.map CP.afv eargs2) in
       (true, List.combine ls1 ls2)
     else (false,[])
  in
  let rec helper hr hrs2 rest2=
    match hrs2 with
      | [] -> (false,[],rest2)
      | hr1::hss ->
          let r,ss1= check_stricteq_hr hr hr1 in
          if r then
            (true,ss1,rest2@hss)
          else helper hr hss (rest2@[hr1])
  in
  let rec helper2 hrs1 hrs2 ss0=
    match hrs1 with
      | [] -> true,ss0
      | hr1::rest1 ->
          let r,ss, rest2 = helper hr1 hrs2 [] in
          if r then
            helper2 rest1 rest2 (ss0@ss)
          else (false,ss0)
  in
  if (List.length hrels1) = (List.length hrels2) then
    helper2 hrels1 hrels2 []
  else (false,[])

let check_stricteq_h_fomula_x stricted_eq hf1 hf2=
  let hnodes1, _, hrels1 = CF.get_hp_rel_h_formula hf1 in
  let hnodes2, _, hrels2 = CF.get_hp_rel_h_formula hf2 in
  let r,ss = check_stricteq_hrels hrels1 hrels2 in
  let helper hn=
    let n_hn = CF.h_subst ss (CF.DataNode hn) in
    match n_hn with
      | CF.DataNode hn -> hn
      | _ -> report_error no_pos "sau.check_stricteq_h_fomula"
  in
  if r then begin
      let n_hnodes1 = List.map helper hnodes1 in
      let n_hnodes2 = List.map helper hnodes2 in
      if (List.length n_hnodes1) <= (List.length n_hnodes2) then
        check_stricteq_hnodes stricted_eq n_hnodes1 n_hnodes2
      else
        check_stricteq_hnodes stricted_eq n_hnodes2 n_hnodes1
    end
  else false

let check_stricteq_h_fomula stricted_eq hf1 hf2=
  let pr1 = Cprinter.string_of_h_formula in
  Debug.no_3 " check_stricteq_h_fomula" string_of_bool pr1 pr1 string_of_bool
      (fun _ _ _ ->  check_stricteq_h_fomula_x stricted_eq hf1 hf2) stricted_eq hf1 hf2

let check_relaxeq_formula_x f1 f2=
  let hf1,mf1,_,_,_ = CF.split_components f1 in
  let hf2,mf2,_,_,_ = CF.split_components f2 in
  DD.ninfo_pprint ("   mf1: " ^(Cprinter.string_of_mix_formula mf1)) no_pos;
  DD.ninfo_pprint ("   mf2: " ^ (Cprinter.string_of_mix_formula mf2)) no_pos;
  (* let r1,mts = CEQ.checkeq_h_formulas [] hf1 hf2 [] in *)
  let r1 = check_stricteq_h_fomula true hf1 hf2 in
  if r1 then
    (* let new_mf1 = xpure_for_hnodes hf1 in *)
    (* let cmb_mf1 = MCP.merge_mems mf1 new_mf1 true in *)
    (* let new_mf2 = xpure_for_hnodes hf2 in *)
    (* let cmb_mf2 = MCP.merge_mems mf2 new_mf2 true in *)
    (* (\*remove dups*\) *)
    (* let np1 = CP.remove_redundant (MCP.pure_of_mix cmb_mf1) in *)
    (* let np2 = CP.remove_redundant (MCP.pure_of_mix cmb_mf2) in *)
    let np1 = CF.remove_neqNull_redundant_hnodes_hf hf1 (MCP.pure_of_mix mf1) in
    let np2 = CF.remove_neqNull_redundant_hnodes_hf hf2 (MCP.pure_of_mix mf2) in
    (* DD.info_pprint ("   f1: " ^(!CP.print_formula np1)) no_pos; *)
    (* DD.info_pprint ("   f2: " ^ (!CP.print_formula np2)) no_pos; *)
    (* let r2,_ = CEQ.checkeq_p_formula [] np1 np2 mts in *)
    let r2 = CP.equalFormula np1 np2 in
    let _ = DD.ninfo_pprint ("   eq: " ^ (string_of_bool r2)) no_pos in
    r2
  else
    false

let check_relaxeq_formula f1 f2=
  let pr1 = Cprinter.string_of_formula in
  Debug.no_2 "check_relaxeq_formula" pr1 pr1 string_of_bool
      (fun _ _ -> check_relaxeq_formula_x f1 f2) f1 f2

(*exactly eq*)
let checkeq_pair_formula (f11,f12) (f21,f22)=
  (check_relaxeq_formula f11 f21)&&(check_relaxeq_formula f12 f22)

let rec checkeq_formula_list_x fs1 fs2=
  let rec look_up_f f fs fs1=
    match fs with
      | [] -> (false, fs1)
      | f1::fss -> if (check_relaxeq_formula f f1) then
            (true,fs1@fss)
          else look_up_f f fss (fs1@[f1])
  in
  if List.length fs1 = List.length fs2 then
    match fs1 with
      | [] -> true
      | f1::fss1 ->
          begin
              let r,fss2 = look_up_f f1 fs2 [] in
              if r then
                checkeq_formula_list fss1 fss2
              else false
          end
  else false

and checkeq_formula_list fs1 fs2=
  let pr1 = pr_list_ln Cprinter.prtt_string_of_formula in
  Debug.no_2 "checkeq_formula_list" pr1 pr1 string_of_bool
      (fun _ _ -> checkeq_formula_list_x fs1 fs2) fs1 fs2

let remove_subsumed_pure_formula_x ps=
  (*check ps01 <<= ps02*)
  let check_subsume (ps01,null_svl1) (ps02,null_svl2)=
    (* Gen.BList.difference_eq CP.equalFormula ps01 ps02 = [] *)
    (List.length null_svl1>0) && (CP.diff_svl null_svl1 null_svl2 = [])
  in
  let sort_fn (ps01,null_svl1) (ps02,null_svl2)=
    (* (List.length ps01) - (List.length ps02) *)
    (List.length null_svl1) - (List.length null_svl2)
  in
  (* let ls_ps = List.map CP.list_of_conjs ps in *)
  let ls_ps1 = List.sort sort_fn ps in
  let ls_ps2 = Gen.BList.remove_dups_eq check_subsume ls_ps1 in
  (* List.map (fun (ps,_) -> CP.join_conjunctions ps) ls_ps2 *)
  List.map fst ls_ps2

let remove_subsumed_pure_formula ps=
  let pr1=pr_list_ln (pr_pair !CP.print_formula !CP.print_svl) in
  let pr2= pr_list_ln (!CP.print_formula) in
  Debug.no_1 "remove_subsumed_pure_formula" pr1 pr2
      (fun _ -> remove_subsumed_pure_formula_x ps) ps

let remove_subsumed_pure_formula fs=
  let helper f pos p=
    CF.mkAnd_pure f (MCP.mix_of_pure p) pos
  in
  if fs = [] then [] else
    let ps = List.map
      (fun f ->
          let p = CF.get_pure f in
          let mf = MCP.mix_of_pure p in
          let eqs = (MCP.ptr_equations_without_null mf) in
          let null_svl = MCP.get_null_ptrs (mf) in
          (p,find_close null_svl eqs)
      ) fs
    in
    let ps1= remove_subsumed_pure_formula ps in
    let emp_f = CF.mkTrue_nf no_pos in
    List.map (helper emp_f no_pos) ps1

(*=============common prefix equal=========*)
let check_com_pre_eq_formula_x f1 f2=
  let hf1,mf1,_,_,_ = CF.split_components f1 in
  let hf2,mf2,_,_,_ = CF.split_components f2 in
  DD.ninfo_pprint ("   mf1: " ^(Cprinter.string_of_mix_formula mf1)) no_pos;
  DD.ninfo_pprint ("   mf2: " ^ (Cprinter.string_of_mix_formula mf2)) no_pos;
  (* let r1,mts = CEQ.checkeq_h_formulas [] hf1 hf2 [] in *)
  let r1 = check_stricteq_h_fomula false hf1 hf2 in
  if r1 then
    (*remove dups*)
    let np1 = CP.remove_redundant (MCP.pure_of_mix mf1) in
    let np2 = CP.remove_redundant (MCP.pure_of_mix mf2) in
    DD.ninfo_pprint ("   p1: " ^(!CP.print_formula np1)) no_pos;
    DD.ninfo_pprint ("   p2: " ^ (!CP.print_formula np2)) no_pos;
    (* let r2,_ = CEQ.checkeq_p_formula [] np1 np2 mts in *)
    let r2 = CP.equalFormula np1 np2 in
    let _ = DD.ninfo_pprint ("   eq: " ^ (string_of_bool r2)) no_pos in
    r2
  else
    false

let check_com_pre_eq_formula f1 f2=
  let pr1 = Cprinter.string_of_formula in
  Debug.no_2 "check_com_pre_eq_formula" pr1 pr1 string_of_bool
      (fun _ _ -> check_com_pre_eq_formula_x f1 f2) f1 f2

(************************************************************)
      (******************END CHECKEQ**********************)
(************************************************************)


(******************************************************************)
   (****************SIMPL HP PARDEF/CF.formula*****************)
(******************************************************************)
(*
  x::node<_,p> ===> p can not be a root
*)
let find_root_x args fs=
  let rec examine_one_arg fs a=
    match fs with
      | [] -> true
      | f::fs_tl ->
          (*get ptos of all nodes*)
          let hds = get_hdnodes f in
          let ptos = List.concat (List.map (fun hd -> hd.CF.h_formula_data_arguments) hds) in
          if CP.mem_svl a ptos then false
          else examine_one_arg fs_tl a
  in
  (*trciky here. should have another better*)
  match args with
    | [a] -> (a,[])
    | _ -> begin
        let root_cands = List.filter (examine_one_arg fs) args in
        match root_cands with
          | [] -> report_error no_pos "sau.find_root_x: dont have a root. what next?"
          | r::_ -> (r,List.filter (fun sv -> not (CP.eq_spec_var r sv)) args)
    end

let find_root args fs=
  let pr1 = pr_list_ln Cprinter.prtt_string_of_formula in
  let pr2 = pr_pair !CP.print_sv !CP.print_svl in
  Debug.no_2 "find_root" !CP.print_svl pr1 pr2
      (fun _ _ -> find_root_x args fs) args fs

(*root = p && p:: node<_,_> ==> root = p& root::node<_,_> & *)
let mk_expl_root r f0=
  let rec find_r_subst ss res=
    match ss with
      | [] -> res
      | (sv1,sv2)::tl->
          if CP.eq_spec_var r sv1 then
            find_r_subst tl (res@[(sv2,sv1)])
          else if CP.eq_spec_var r sv2 then
            find_r_subst tl (res@[(sv1,sv2)])
          else find_r_subst tl (res)
  in
  let helper f=
    match f with
    | CF.Base fb ->
        let eqs = (MCP.ptr_equations_without_null fb.CF.formula_base_pure) in
        let r_ss = find_r_subst eqs [] in
        let new_h1 =
          if r_ss= [] then fb.CF.formula_base_heap else
            CF.h_subst r_ss fb.CF.formula_base_heap
        in
        CF.Base {fb with CF.formula_base_heap = new_h1}
    | _ -> report_error no_pos "cformula.mk_expl_root: not handle yet"
  in
  helper f0

let filter_fn h_svl p=
  if CP.is_eq_exp p then
    let p_svl = CP.fv p in
    (CP.diff_svl p_svl h_svl) = []
  else true

(*fix subst*)
let filter_unconnected_hf args hf=
  let hds =  get_hdnodes_hf hf in
  let ptrs = List.map (fun hd -> hd.CF.h_formula_data_node) hds in
  let tail_ptrs = List.concat (List.map (fun hd ->
      List.filter CP.is_node_typ hd.CF.h_formula_data_arguments) hds) in
  let unconnected_ptr = CP.diff_svl ptrs (tail_ptrs@args) in
  CF.drop_hnodes_hf hf unconnected_ptr

let remove_irr_eqs_x keep_svl p=
  let rec rearrang_eq ls res=
    match ls with
      | [] -> res
      | (sv1,sv2)::ss -> begin
          let b1= CP.mem_svl sv1 keep_svl in
          let b2 = CP.mem_svl sv2 keep_svl in
          match b1,b2 with
            | true,true -> rearrang_eq ss res
            | true,false -> rearrang_eq ss (res@[(sv2,sv1)])
            | false,true -> rearrang_eq ss (res@[(sv1,sv2)])
            | _ -> rearrang_eq ss res
      end
  in
  let eqs = (MCP.ptr_equations_without_null (MCP.mix_of_pure p)) in
  let eqs1 = rearrang_eq eqs [] in
  let eqs2 = Gen.BList.remove_dups_eq
    (fun (sv11,_) (sv21,_) -> CP.eq_spec_var sv11 sv21) eqs1
  in
  let p1 = CP.subst eqs2 p in
  let cons = CP.list_of_conjs p1 in
  let cons1 = CP.remove_redundant_helper cons [] in
  let cons2 = List.filter (filter_fn keep_svl) cons1 in
  let new_p = (CP.conj_of_list cons2 no_pos) in
  new_p,eqs2

let remove_irr_eqs keep_svl p=
  let pr1 = !CP.print_formula in
  let pr2 = fun (a,_) -> pr1 a in
  Debug.no_2 "remove_irr_eqs" !CP.print_svl pr1 pr2
      (fun _ _ -> remove_irr_eqs_x keep_svl p)  keep_svl p

let elim_irr_eq_exps prog args f=
  match f with
    | CF.Base fb ->
        (* let h_svl = CP.remove_dups_svl (args@(CF.h_fv fb.CF.formula_base_heap)) in *)
        (* let cons = CP.list_of_conjs (MCP.pure_of_mix fb.CF.formula_base_pure) in *)
        (* let cons1 = CP.remove_redundant_helper (cons) [] in *)
        (* let cons2 = List.filter (filter_fn h_svl) cons1 in *)
        (* let new_p = MCP.mix_of_pure (CP.conj_of_list cons2 no_pos) in *)
        let hd_nodes,hv_nodes,hrels = CF.get_hp_rel_formula f in
  (* let ls_hpargs = List.map (fun (hp,eargs,_) -> (hp, List.concat (List.map CP.afv eargs))) hrels in *)
        let keep_ptrs = look_up_closed_ptr_args prog hd_nodes hv_nodes args in
        let keep_ptrs1 = CP.remove_dups_svl keep_ptrs in
        let new_p,ss = remove_irr_eqs keep_ptrs1 (MCP.pure_of_mix fb.CF.formula_base_pure) in
        let new_h1 = CF.h_subst ss fb.CF.formula_base_heap in
        let new_h2 = filter_unconnected_hf args new_h1 in
        CF.Base {fb with CF.formula_base_pure = MCP.mix_of_pure new_p;
            CF.formula_base_heap = new_h2}
    | _ -> report_error no_pos "cformula. elim_irr_eq_exps: not handle yet"


let remove_dups_pardefs_x grp=
  let eq_pardefs (_,args1,f1,_) (_,args2,f2,_)=
    let ss = List.combine args1 args2 in
    let nf1 = CF.subst ss f1 in
    check_relaxeq_formula nf1 f2
  in
  Gen.BList.remove_dups_eq eq_pardefs grp

let remove_dups_pardefs grp=
  let pr1 = (pr_list_ln string_of_par_def_w_name_short) in
  Debug.no_1 "remove_dups_pardefs" pr1 pr1
      (fun _ -> remove_dups_pardefs_x grp) grp

let remove_dups_pardefs_w_neqNull_x grp=
  let norm args0 (a1,args1,f1,a4)=
    let ss = List.combine args1 args0 in
    let nf1 = CF.subst ss f1 in
    (a1,args1,f1,a4,nf1)
  in
  let get_expl_svl f=
    let hds = get_hdnodes f in
    List.map (fun hd -> hd.CF.h_formula_data_node) hds
  in
  let process_one args0 expl_svl (a11,args1,a13,a14,f1) rem=
    let neqNull_svl1 = CF.get_neqNull f1 in
    let rec helper l_rem=
    match l_rem with
      | [] ->
          let ss = List.combine args0 args1 in
          let neqNull_svl12 = List.map (CP.subs_one ss) neqNull_svl1 in
          let expl_svl1 = List.map (CP.subs_one ss) expl_svl in
          let hpargs = List.concat (snd (List.split (CF.get_HRels_f a13))) in
          (* let _ = Debug.info_pprint ("    hpargs:" ^ (!CP.print_svl hpargs)) no_pos in *)
          (* let _ = Debug.info_pprint ("    neqNull_svl12:" ^ (!CP.print_svl neqNull_svl12)) no_pos in *)
          let neq_svl = CP.intersect_svl neqNull_svl12 (expl_svl1@a14@hpargs) in
          let newf = CF.remove_neqNull_svl neq_svl a13 in
          if is_empty_f newf then [] else
            [(a11,args1,newf,a14,f1)]
      | (a21,args2,a23,a24,f2)::tl ->
          let neqNull_svl2 = CF.get_neqNull f2 in
          let _ = Debug.ninfo_pprint ("    neqNull_svl1:" ^ (!CP.print_svl neqNull_svl1)) no_pos in
          let _ = Debug.ninfo_pprint ("    neqNull_svl2:" ^ (!CP.print_svl neqNull_svl2)) no_pos in
          let neqNull_svl11 = CP.diff_svl neqNull_svl1 neqNull_svl2 in
          if neqNull_svl11 = [] then
            let b = check_relaxeq_formula f1 f2 in
            if b then [] else helper tl
          else
            if CP.diff_svl neqNull_svl11 expl_svl = [] then
              let new_f1 = CF.remove_neqNull_svl neqNull_svl11 f1 in
              let new_f2 = CF.drop_hnodes_f f2 neqNull_svl11 in
              let b = check_relaxeq_formula new_f1 new_f2 in
              if b then [] else helper tl
            else helper tl
    in
    helper rem
  in
  let rec loop_helper args0 expl_svl ls res=
    match ls with
      | [] -> res
      | pdef_ex::tl ->
          let new_pdef = process_one args0 expl_svl pdef_ex (res@tl) in
          loop_helper args0 expl_svl tl (res@new_pdef)
  in
  (*to add the normalized f*)
  let args0,new_grp=
    match grp with
      | [] -> [],[]
      | (a1,args0,f0,a4)::tl ->
          let new_tl = List.map (norm args0) tl in
          (args0,(a1,args0,f0,a4,f0)::new_tl)
  in
  let expl_svl = CP.remove_dups_svl (List.concat (List.map (fun (_,_,_,_,f0) -> get_expl_svl f0) new_grp)) in
  let res_ex = loop_helper args0 expl_svl new_grp [] in
  (*to remove the normalized f*)
  List.map (fun (a1,a2,a3,a4,a5) -> (a1,a2,a3,a4)) res_ex

let remove_dups_pardefs_w_neqNull grp=
  let pr1 = (pr_list_ln string_of_par_def_w_name_short) in
  Debug.no_1 "remove_dups_pardefs_w_neqNull" pr1 pr1
      (fun _ -> remove_dups_pardefs_w_neqNull_x grp) grp

let remove_longer_common_prefix fs=
  let sort_fn (s1,_) (s2,_)=
    s1-s2
  in
  let sort_formula fs1=
    let fs_w_size = List.map (fun f -> (CF.get_h_size_f f, f)) fs1 in
    let sorted_fs_w_size = List.sort sort_fn fs_w_size in
    let fs2 = List.map snd sorted_fs_w_size in
    (* let pr = pr_list_ln Cprinter.prtt_string_of_formula in *)
    (*  let _ = DD.info_pprint ( "sorted-increasing size: " ^ (pr fs2)) no_pos in *)
    fs2
  in
  let rec helper cur res=
    match cur with
      | [] -> res
      | f::ss ->
          if List.exists
            (fun f2 ->
                check_com_pre_eq_formula f2 f)
            res then
            helper ss res
          else helper ss (res@[f])
  in
  let fs1 = sort_formula fs in
  helper fs1 []

let remove_longer_common_prefix_w_unk unk_hps fs=
  let rec helper cur res=
    match cur with
      | [] -> res
      | f::ss ->
          let f1 = CF.subst_unk_hps_f f unk_hps in
          if List.exists
            (fun f2 ->
                let f21 = CF.subst_unk_hps_f f2 unk_hps in
                check_com_pre_eq_formula f1 f21)
            res then
            helper ss res
          else helper ss (res@[f])
  in
  helper fs []

let remove_equiv_wo_unkhps_x hp unk_hps fs=
  let rec partition_helper cur res_unkhp_fs res_elim_unkhp_fs rems=
    match cur with
      | [] -> res_unkhp_fs,res_elim_unkhp_fs,rems
      | f::ss ->
          let newf,args = CF.drop_hrel_f f unk_hps in
          if args = [] then
            partition_helper ss res_unkhp_fs res_elim_unkhp_fs (rems@[f])
          else
            begin
                let newf2,_ = CF.drop_hrel_f newf [hp] in
                if is_empty_f newf2 then
                  partition_helper ss res_unkhp_fs res_elim_unkhp_fs rems
                else
                  partition_helper ss (res_unkhp_fs@[f]) (res_elim_unkhp_fs@[newf]) rems
            end
  in
  let check_dups elim_unkhp_fs non_unkhp_fs=
    let rec helper1 fs r=
      match fs with
        | [] -> r
        | f::fss ->
            (*check duplicate or not ll-append5*)
            if List.exists (fun f1 -> check_relaxeq_formula f f1) elim_unkhp_fs then
              helper1 fss r
            else helper1 fss (r@[f])
    in
    helper1 non_unkhp_fs []
  in
  let unkhp_fs,elim_unkhp_fs,rems= partition_helper fs [] [] [] in
  let rems1 = check_dups elim_unkhp_fs rems in
  (unkhp_fs@rems1)

let remove_equiv_wo_unkhps hp unk_hps fs=
  let pr = pr_list_ln Cprinter.prtt_string_of_formula in
  Debug.no_2 "remove_equiv_wo_unkhps" !CP.print_svl pr pr
      (fun _ _ -> remove_equiv_wo_unkhps_x hp unk_hps fs) unk_hps fs

(************************************)
(*check hf2 is subset of hf1*)
let check_subset_h_fomula_x hf1 hf2=
  let helper1 hn=
    (hn.CF.h_formula_data_node, hn.CF.h_formula_data_arguments)
  in
  let helper2 (hp, eargs,_)=
    (hp, List.concat (List.map CP.afv eargs))
  in
  let hnodes1, _, hrels1 = CF.get_hp_rel_h_formula hf1 in
  let hnodes2, _, hrels2 = CF.get_hp_rel_h_formula hf2 in
  (*quick check first*)
  if (List.length hnodes2) < (List.length hnodes1) &&
    (List.length hrels2) < (List.length hrels1) then
    let hnargs1 = List.map helper1 hnodes1 in
    let hnargs2 = List.map helper1 hnodes2 in
    let hpargs1 = List.map helper2 hrels1 in
    let hpargs2 = List.map helper2 hrels2 in
    if (Gen.BList.difference_eq check_hp_arg_eq hnargs2 hnargs1) = [] then
      ((Gen.BList.difference_eq check_hp_arg_eq hpargs2 hpargs1) = [])
    else
      false
  else
    false

let check_subset_h_fomula hf1 hf2=
  let pr1 = Cprinter.string_of_h_formula in
  Debug.no_2 " check_subset_h_fomula"  pr1 pr1 string_of_bool
      (fun _ _ ->  check_subset_h_fomula_x hf1 hf2) hf1 hf2

let remove_subset fs0=
  let size_compare f1 f2=
    let s1 = get_data_view_hrel_vars_formula f1 in
    let s2 = get_data_view_hrel_vars_formula f2 in
    (List.length s2) - (List.length s1)
  in
  let check_subset f1 f2=
    let (hf1,mf1,_,_,_) = CF.split_components f1 in
    let (hf2,mf2,_,_,_) = CF.split_components f2 in
    let np1 = CF.remove_neqNull_redundant_hnodes_hf hf1 (MCP.pure_of_mix mf1) in
    let np2 = CF.remove_neqNull_redundant_hnodes_hf hf2 (MCP.pure_of_mix mf2) in
    (* DD.info_pprint ("   p1: " ^(!CP.print_formula np1)) no_pos; *)
    (* DD.info_pprint ("   p2: " ^ (!CP.print_formula np2)) no_pos; *)
    let r2 = CP.equalFormula np1 np2 in
    if r2 then
      check_subset_h_fomula hf1 hf2
    else false
  in
  let rec helper fs res=
    match fs with
      | [] -> res
      | f::fss ->
          if List.exists
            (fun f2 -> check_subset f2 f) res then
            helper fss res
          else helper fss (res@[f])
  in
  let fs1 = List.sort size_compare fs0 in
  helper fs1 []
(************************************)

let is_trivial f (hp,args)=
  let hpargs = CF.get_HRels_f f in
  let b1 = List.exists (fun hpargs1 -> check_hp_arg_eq (hp,args) hpargs1) hpargs in
  b1||(is_empty_f f)

let simplify_one_formula prog args f=
  let f1 = elim_irr_eq_exps prog args f in
  (* let f1 = filter_var prog args f in *)
  f1

(************************************************************)
    (****************END SIMPL HP PARDEF/CF.formula************)
(************************************************************)

let norm_hnodes_x args fs=
  let rec get_subst_svl matcheds svl1 svl2 ss=
    match svl1,svl2 with
	 | [],[] -> ss
	 | v1::sl1,v2::sl2 ->
         if CP.eq_spec_var v1 v2 || CP.mem_svl v2 matcheds ||
           CP.mem_svl v2 args || CP.mem_svl v1 args
         then
		   get_subst_svl matcheds sl1 sl2 ss
	     else get_subst_svl matcheds sl1 sl2 (ss@[(v2,v1)])
	 | _ -> report_error no_pos "sau.norm_hnodes_x 1"
  in
  let rec look_up_one_hd hn1 lnds matched2 rest2=
    match lnds with
      | [] ->  ([],matched2, rest2)
      | hn2::ls ->
          if hn1.CF.h_formula_data_name = hn2.CF.h_formula_data_name &&
            CP.eq_spec_var hn1.CF.h_formula_data_node hn2.CF.h_formula_data_node
          then
		    (*return last args and remain*)
            (* let _ = DD.info_pprint ("  svl1: " ^ (!CP.print_svl hn1.CF.h_formula_data_arguments)) no_pos in *)
            (* let _ = DD.info_pprint ("  svl2: " ^ (!CP.print_svl hn.CF.h_formula_data_arguments)) no_pos in *)
            (get_subst_svl matched2 hn1.CF.h_formula_data_arguments
                 hn2.CF.h_formula_data_arguments [],
             matched2@[hn2.CF.h_formula_data_node],rest2@ls)
		  else look_up_one_hd hn1 ls matched2 (rest2@[hn2])
  in
  let helper hn lnds matched2 rest2=
    let last_ss,matched,rest= look_up_one_hd hn lnds matched2 rest2 in
    let fresh_rest = List.map (fun hd -> CF.h_subst last_ss (CF.DataNode hd)) rest in
    let fresh_rest1 = List.concat (List.map get_hdnodes_hf fresh_rest) in
    (last_ss,matched,fresh_rest1)
  in
  let rec norm_hnodes_two_hns sh_dns matched2 rest_dns2 ss=
    match sh_dns with
      | [] -> (matched2, rest_dns2, ss)
      |  hn::sh_ls ->
          let new_ss, n_matcheds2,n_rest2 = helper hn rest_dns2 matched2 [] in
             norm_hnodes_two_hns sh_ls n_matcheds2 n_rest2 (ss@new_ss)
  in
  let norm_one_f base_ldns f=
    let hnds = get_hdnodes f in
    let _,_, ss = norm_hnodes_two_hns base_ldns [] hnds [] in
    let cur_svl = CF.fv f in
    let to_subst = List.map snd ss in
    let inter= CP.intersect_svl (CP.remove_dups_svl cur_svl)
      (CP.remove_dups_svl to_subst) in
    let f1=
      if inter = [] then f else
        let fr_inter = CP.fresh_spec_vars inter in
        let ss1 = List.combine inter fr_inter in
        CF.subst ss1 f
    in
    CF.subst ss f1
  in
  let move_root ldns=
    let rec move_root_to_top arg lldns rest=
      match lldns with
        | [] -> (false,rest)
        | hd::hds ->
            if CP.eq_spec_var arg hd.CF.h_formula_data_node then
              (true,lldns@rest)
            else move_root_to_top arg hds (rest@[hd])
    in
    let rec sel_root largs=
      match largs with
        | [] -> ldns
        | a::ass ->
            let b,res= move_root_to_top a ldns [] in
            if b then res
            else sel_root ass
    in
    sel_root args
  in
  let base_f = List.hd fs in
  let base_ldns = get_hdnodes base_f in
  if base_ldns = [] then fs else
    let base_ldns1 = move_root base_ldns in
    let tl_fs = List.map (norm_one_f base_ldns1) (List.tl fs) in
    (base_f::tl_fs)

let norm_hnodes args fs=
  let pr1 = pr_list_ln Cprinter.prtt_string_of_formula in
  Debug.no_2 "norm_hnodes" !CP.print_svl pr1 pr1
      (fun _ _ -> norm_hnodes_x args fs) args fs


let generate_equiv_pdefs_x unk_hps pdef_grps=
  let get_succ_hps_pardef (_,_,f,_)=
    (CF.get_HRels_f f)
  in
  let rec lookup_succ_hps_grp rem_grps hp done_grps=
    match rem_grps with
      | [] -> (false,[],done_grps,[])
      | grp::tl -> begin
          match grp with
            | [] -> lookup_succ_hps_grp tl hp done_grps
            | (hp1,_,_,_)::_ ->
                if CP.eq_spec_var hp1 hp then
                  let succ_hpargs = List.concat (List.map get_succ_hps_pardef grp) in
                  let hps = CP.remove_dups_svl (List.map fst succ_hpargs) in
                   (true,hps, done_grps@tl,grp)
                else
                  lookup_succ_hps_grp tl hp (done_grps@[grp])
      end
  in
  let subst_equiv_hp_one_pdef from_hp to_hp (hp,args,f,unk_svl)=
    let new_f = CF.subst_hprel f [from_hp] to_hp in
    if is_trivial new_f (hp,args) then [] else
      [(hp,args,new_f,unk_svl)]
  in
  let subst_equiv_hp_one_grp from_hp to_hp grp=
    match grp with
      | [] -> []
      | (hp,_,_,_)::tl ->
          if CP.eq_spec_var from_hp hp then grp
          else
            List.concat (List.map (subst_equiv_hp_one_pdef from_hp to_hp) grp)
  in
  (*hp0 --> hp_equiv*)
  let gen_equiv_hps_one_hp equiv_hps pdef_grps0 (hp0,args0,p0)=
    let size0 =  List.length args0 in
    (*remove invalid equivs*)
    let equivs_hps = List.concat (List.map (fun (hp1,args1,_) ->
        if CP.eq_spec_var hp0 hp1 || List.length args1 <> size0 then []
        else [hp1])  equiv_hps)
    in
    if equivs_hps = [] then pdef_grps0 else
      let is_pdefined,succ_hps,other_grps,cur_grp = lookup_succ_hps_grp pdef_grps0 hp0 [] in
      let not_process = succ_hps@unk_hps in
      let real_equivs_hps = List.filter (fun hp1 -> not (CP.mem_svl hp1 not_process)) equivs_hps in
      let new_pdef_grps0=
        (* if real_equivs_hps = [] then pdef_grps0 else *)
        if is_pdefined  then pdef_grps0 else
      (*build new pdefs*)
          (* let new_pdefs = List.map (fun hp2 -> (hp0,args0, mkHRel_f hp2 args0 p0)) real_equivs_hps in *)
          (* other_grps@[(cur_grp@new_pdefs)] *)
          match real_equivs_hps with
            | [hp2] -> List.map (subst_equiv_hp_one_grp hp0 hp2) pdef_grps0
            | _ -> pdef_grps0
      in
      new_pdef_grps0
  in
  let gen_equiv_hps_one pdef_grps1 grp=
    let equiv_hps = List.concat (List.map (fun (_,_,f,_) ->
        CF.check_and_get_one_hpargs f) grp) in
    List.fold_left (gen_equiv_hps_one_hp equiv_hps) pdef_grps1 equiv_hps
  in
  let rec loop_helper pdef_grps2 done_hps=
    let rec helper ls=
      match ls with
        | [] -> pdef_grps2
        | grp::tl -> begin
            match grp with
              | (hp1,_,_,_)::_ ->
                  if CP.mem_svl hp1 done_hps then
                    helper tl
                  else
                    let new_grps = gen_equiv_hps_one pdef_grps2 grp in
                    loop_helper new_grps (done_hps@[hp1])
              | [] -> helper tl
        end
    in
    helper pdef_grps2
  in
  loop_helper pdef_grps []

let generate_equiv_pdefs unk_hps pdef_grps=
  let pr1 =  Cprinter.prtt_string_of_formula in
  let pr2 = pr_list_ln (pr_list_ln (pr_quad !CP.print_sv !CP.print_svl pr1 !CP.print_svl)) in
  Debug.no_2 "generate_equiv_pdefs" !CP.print_svl pr2 pr2
      (fun _ _ -> generate_equiv_pdefs_x unk_hps pdef_grps) unk_hps pdef_grps


(************************************************************)
      (******************FORM HP DEF*********************)
(************************************************************)

(*check which parameters of a hp can be dropped*)
(*fs is a set of formulae of hp's definition*)
let drop_hp_arguments_x prog hp args0 fs=
  let rec helper raw_defined_svl args res index=
    match args with
      | [] -> res
      | a::ass -> if (CP.mem_svl a raw_defined_svl) then
            helper raw_defined_svl ass (res) (index+1)
          else helper raw_defined_svl ass (res@[index]) (index+1)
  in
  let intersect_cand cands=
    let _ = Debug.ninfo_pprint ("     cands: " ^ (let pr = pr_list Cprinter.string_of_list_int in pr cands)) no_pos in
    if cands = [] then [] else
      let locs = List.fold_left (fun ls1 ls2 -> Gen.BList.intersect_eq (=) ls1 ls2) (List.hd cands) (List.tl cands) in
      locs
  in
  let rename_drop_args args1 locs0=
    let rec loop_helper args index res=
      match args with
        | [] -> res
        | a::ass ->
            if List.mem index locs0 then
              let new_a = CP.fresh_spec_var a in
              loop_helper ass (index+1) (res@[new_a])
            else loop_helper ass (index+1) (res@[a])
    in
    loop_helper args1 0 []
  in
  let process_one_f f=
    let def_vs_wo_args, hd_nodes, hv_nodes, hrs, eqs,eqNulls = find_defined_pointers_raw prog f in
    let used_svl = look_up_closed_ptr_args prog hd_nodes hv_nodes (def_vs_wo_args@eqNulls@args0) in
    let hpargs = (List.map (fun (hp1,eargs,_)-> hp1,(List.concat (List.map CP.afv eargs))) hrs) in
    let rec_hpargs, rem_hpargs = List.partition (fun (hp1, _) -> CP.eq_spec_var hp1 hp) hpargs in
    let rec_args = CP.remove_dups_svl (List.concat (List.map snd rec_hpargs)) in
     (*  match rec_hpargs with *)
    (*     | [] -> [] *)
    (*     | [(_,args)] -> args *)
    (*     | _ -> report_error no_pos "sau.drop_hp_arguments" *)
    (* in *)
    if rec_args = [] then [] else
      let res = helper (CP.remove_dups_svl
                            ((List.concat (List.map snd rem_hpargs))@
                                    used_svl@args0)) rec_args [] 0 in
      res
  in
  let cands = List.map process_one_f fs in
  let cands1 = (List.filter (fun x -> x<>[]) cands) in
  let drops = intersect_cand cands1 in
  (*rename dropped args*)
  let new_args,new_fs=
    if drops = [] then args0,fs
    else
      (*simplify-remove irr things from fs*)
      let n_args = rename_drop_args args0 drops in
      let simplify_helper args2 f=
        let f1 = elim_irr_eq_exps prog args2 f in
        if (is_empty_f f1) then []
        else [f1]
      in
      let fs1 = List.concat (List.map (simplify_helper n_args) fs) in
      (n_args,fs1)
  in
  (new_args,new_fs)

let drop_hp_arguments prog hp args0 fs=
  let pr1 = pr_list_ln (Cprinter.prtt_string_of_formula) in
  let pr2 = !CP.print_svl in
  let pr3 = pr_pair pr2 pr1 in
  Debug.no_3 "drop_hp_arguments" !CP.print_sv pr2 pr1 pr3
      (fun _ _ _ -> drop_hp_arguments_x prog hp args0 fs) hp args0 fs


let get_longest_common_hnodes_two args shortes_ldns ldns2 eqs=
  let rec get_subst_svl svl1 svl2 ss=
    match svl1,svl2 with
	 | [],[] -> ss
	 | v1::sl1,v2::sl2 -> if CP.eq_spec_var v1 v2 then
		get_subst_svl sl1 sl2 ss
	    else get_subst_svl sl1 sl2 (ss@[(v1,v2)])
	 | _ -> report_error no_pos "sau.get_longest_common_hnodes_two 1"
  in
  let rec look_up_one_hd hn lnds matched2 rest2=
    match lnds with
      | [] ->  ([],[],matched2, rest2)
      | hn1::ls ->
          (* let eq_svl = find_close [hn1.CF.h_formula_data_node] eqs in *)
          if hn.CF.h_formula_data_name = hn1.CF.h_formula_data_name &&
            CP.eq_spec_var hn.CF.h_formula_data_node hn1.CF.h_formula_data_node
            (* CP.mem_svl hn.CF.h_formula_data_node eq_svl *)
          then
		    (*return last args and remain*)
            (* let _ = DD.info_pprint ("  svl1: " ^ (!CP.print_svl hn1.CF.h_formula_data_arguments)) no_pos in *)
            (* let _ = DD.info_pprint ("  svl2: " ^ (!CP.print_svl hn.CF.h_formula_data_arguments)) no_pos in *)
            (hn1.CF.h_formula_data_arguments,get_subst_svl hn1.CF.h_formula_data_arguments hn.CF.h_formula_data_arguments [],
             matched2@[hn1.CF.h_formula_data_node],rest2@ls)
		  else look_up_one_hd hn ls matched2 (rest2@[hn1])
  in
  let helper hn lnds matched2 rest2=
    let last_svl,last_ss,matched,rest= look_up_one_hd hn lnds matched2 rest2 in
    (* let fresh_rest = List.map (fun hd -> CF.h_subst last_ss (CF.DataNode hd)) rest in *)
    (* let fresh_rest1 = List.concat (List.map get_hdnodes_hf fresh_rest) in *)
    (last_svl,[],last_ss,matched,rest)
  in
  let rec look_up_min_hds sh_dns matched2 rest_dns2 ss last_ss last_svl=
    match sh_dns with
      | [] -> (matched2, rest_dns2, ss, last_ss,last_svl)
          (* report_error no_pos "sau.get_longest_common_hnodes_two" *)
          (* if length rest_dns2: mk pure equality all ss*)
      (*| [hn] ->
          let last_ss, n_matcheds2,n_rest2 =  helper hn rest_dns2 matched2 [] in
          (n_matcheds2, n_rest2, ss, last_ss)*)
      |  hn::sh_ls ->
          let new_last_svl,new_ss, new_last_ss, n_matcheds2,n_rest2 =  helper hn rest_dns2 matched2 [] in
            look_up_min_hds sh_ls n_matcheds2 n_rest2 (ss@new_ss) (new_last_ss@last_ss) new_last_svl
  in
  (*remove all dnodes in tail of args*)
  
  (* let _ =  DD.info_pprint ("       args: " ^ (!CP.print_svl args)) no_pos in *)
  look_up_min_hds shortes_ldns [] ldns2 [] [] []

let process_one_f_x prog org_args args next_roots hp_subst sh_ldns com_eqNulls com_eqPures com_hps (ldns, f)=
  (* let _ =  DD.info_pprint ("       new args: " ^ (!CP.print_svl args)) no_pos in *)
  (* let pr2 = pr_list Cprinter.string_of_h_formula in *)
  (* let _ = DD.info_pprint ("      sh_ldns:" ^ (pr2 (List.map (fun hd -> CF.DataNode hd) sh_ldns))) no_pos in *)
  let ( _,mix_f,_,_,_) = CF.split_components f in
  let eqs = (MCP.ptr_equations_without_null mix_f) in
  let (matcheds2, rest2, ss, last_ss0,_) = get_longest_common_hnodes_two org_args sh_ldns ldns eqs in
  (*drop all matcheds*)
  let _ =  DD.ninfo_pprint ("       matched 1: " ^ (!CP.print_svl matcheds2)) no_pos in
  (* let _ =  DD.info_pprint ("       eqNulls: " ^ (!CP.print_svl com_eqNulls)) no_pos in *)
  (* let _ =  DD.info_pprint ("       f: " ^ (Cprinter.prtt_string_of_formula f)) no_pos in *)
  let nf1 = CF.drop_hnodes_f f matcheds2 in
  let _ =  DD.ninfo_pprint ("       nf1: " ^ (Cprinter.prtt_string_of_formula nf1)) no_pos in
  (* let _ =  DD.info_pprint ("       args: " ^ (!CP.print_svl args)) no_pos in *)
  (* let _ =  DD.info_pprint ("       last_ss0: " ^ (let pr = pr_list (pr_pair Cprinter.string_of_spec_var Cprinter.string_of_spec_var) in pr last_ss0)) no_pos in *)
  (*apply susbt ss*)
  let nf2 = CF.remove_com_pures nf1 com_eqNulls com_eqPures in
  (* let _ =  DD.info_pprint ("       nf2: " ^ (Cprinter.prtt_string_of_formula nf2)) no_pos in *)
  let nf3 = CF.subst ss nf2 in
  (*if rest = [] then add pure equality all last_ss*)
  let nf5,last_ss=
    (*partition last_ss into two groups: one for subst another not*)
    let last_ss1,last_ss2 = List.partition
      (fun (v1,v2) -> Gen.BList.difference_eq CP.eq_spec_var [v1;v2] args = [])
      last_ss0
    in
    (*mk eq for last_ss1*)
    let ps = List.concat (List.map (fun ((CP.SpecVar (t,v,p)) ,v2) ->
        if (is_pointer t)
        then [CP.mkPtrEqn v2 (CP.SpecVar (t,v,p)) no_pos]
        else []) last_ss1) in
    let p = CP.conj_of_list ps no_pos in
   (*apply subst last_ss2*)
    let nf4 = CF.subst last_ss2 nf3 in
    (*should remove x!=null if x is in matched2s*)
    (*combine them*)
    CF.mkAnd_pure nf4 (MCP.mix_of_pure p) no_pos,last_ss2
  in
  let _ =  DD.ninfo_pprint ("       nf5: " ^ (Cprinter.prtt_string_of_formula nf5)) no_pos in
  (*subst hp rel by its new definition if applicable*)
  let hprel,hf = hp_subst in
  let hp2,args2= CF.extract_HRel hprel in
  let hpargs = CF. get_HRels_f nf5 in
  let nf6 =
    try
        let args3 = List.assoc hp2 hpargs in
         (* let _ =  DD.info_pprint ("       hf: " ^ (Cprinter.prtt_string_of_h_formula hf)) no_pos in*)
        let slv_root = get_ptrs hprel in
        (* let _ = DD.info_pprint ("       svl_roots: " ^ (Cprinter.string_of_spec_var_list slv_root)) no_pos in *)
        let old_svl = get_ptrs hf in
        (*rename everything except root*)
        let old_svl1 = Gen.BList.difference_eq CP.eq_spec_var old_svl slv_root in
        let fresh_svl = CP.fresh_spec_vars old_svl1 in
        let ss = List.combine old_svl1 fresh_svl in
        let n_hf = CF.h_subst (ss) hf in
        let nf5a,n_hf2=
          (*base case has at least one node?*)
          let hds= get_hdnodes_hf n_hf in
          if hds=[] then (nf5,n_hf) else
            let _ = DD.ninfo_pprint ("       next_roots: " ^ (Cprinter.string_of_spec_var_list next_roots)) no_pos in
            let hds1= get_hdnodes nf5 in
            let last_svl = look_up_closed_ptr_args prog hds1 [] next_roots in
            (*is recursive?*)
            let inter = CP.intersect_svl last_svl args3 in
             let _ = DD.ninfo_pprint ("       inter: " ^ (Cprinter.string_of_spec_var_list inter)) no_pos in
            if  inter <> [] then
              let ss1 = List.combine inter next_roots in
              (*find commond pattern: even/odd. testcase: sll-del*)
              (*todo: should have better refinement*)
              let hds2 = get_hdnodes_hf n_hf in
              let n1 = List.length hds1 in
              if (n1 = 0) || ((List.length hds2) mod 2 = n1 mod 2) then
                let nf5b = CF.drop_hnodes_f nf5 last_svl in
                let nf5b0 = CF.subst ss1 nf5b in
                (nf5b0,n_hf)
              else
                (* let nf5b0 = CF.subst ss1 nf5 in *)
                let n_hf1 =  CF.drop_hnodes_hf n_hf (List.map (fun hn -> hn.CF.h_formula_data_node) hds) in
                let hp_args = CF.get_HRels n_hf1 in
                let fst_args = match hp_args with
                  | [(_,args0)] -> args0
                  | _ -> report_error no_pos "sau.process_one_f: sth wrong"
                in
                let ss2 = List.combine fst_args inter in
                (nf5, CF.h_subst ss2 n_hf1)
            else (nf5,n_hf)
        in
        let _ =  DD.ninfo_pprint ("       n_hf2: " ^ (Cprinter.prtt_string_of_h_formula n_hf2)) no_pos in
        let _ =  DD.ninfo_pprint ("       nf5a: " ^ (Cprinter.prtt_string_of_formula nf5a)) no_pos in
        let nf6 = CF.subst_hrel_f nf5a [(hprel, n_hf2)] in
        nf6
    with Not_found -> nf5
  in
  let nf7 = CF.drop_exact_hrel_f nf6 com_hps in
  let _ =  DD.ninfo_pprint ("       nf6: " ^ (Cprinter.prtt_string_of_formula nf6)) no_pos in
  let _ =  DD.ninfo_pprint ("       nf7: " ^ (Cprinter.prtt_string_of_formula nf7)) no_pos in
  nf7

let process_one_f prog org_args args next_roots hp_subst sh_ldns com_eqNulls com_eqPures com_hps (ldns, f)=
  let pr1 = !CP.print_svl in
  let pr2 = Cprinter.prtt_string_of_formula in
  Debug.no_3 "process_one_f" pr1 pr1 pr2 pr2
      (fun _ _ _ -> process_one_f_x prog org_args args next_roots hp_subst sh_ldns com_eqNulls com_eqPures com_hps (ldns, f))
      org_args args f


let get_shortest_lnds ll_ldns min=
  let rec helper ll=
  match ll with
    | [] -> report_error no_pos "sau.get_shortest_lnds"
    | (ldns,f)::lls -> if List.length ldns = min then
          (ldns,f)
        else helper lls
  in
  helper ll_ldns

(*(hds,f) list*)
let get_min_number ll_ldns=
  let rec helper ll min=
  match ll with
    | [] -> min
    | (lnds,f)::lls ->
        let ns = List.length lnds in
        if ns < min then
          helper lls ns
        else helper lls min
  in
  (*start with length of the first one*)
  let fmin = List.length (fst (List.hd ll_ldns)) in
  helper (List.tl ll_ldns) fmin

let get_min_number_new prog args ll_ldns=
  let helper1 dns=
    let closed_args = (look_up_closed_ptr_args prog dns [] args) in
    let dns1 = List.filter (fun dn -> CP.mem_svl dn.CF.h_formula_data_node closed_args) dns in
    (List.length dns1, dns1)
  in
  (*todo: should check eqFormula*)
  let helper_pure_hprels f =
    let ( hf,mix_f,_,_,_) = CF.split_components f in
    let eqNulls = CP.remove_dups_svl ( MCP.get_null_ptrs mix_f) in
    let ps = CP.list_of_conjs (MCP.pure_of_mix mix_f) in
    let hprels = CF.get_hprel_h_formula hf in
	eqNulls,ps,hprels
  in
  let rec helper ll r_min r_hns r_eqNulls r_ps r_hprels=
  match ll with
    | [] -> r_min,r_hns,r_eqNulls,r_ps,r_hprels
    | (lnds,f)::lls ->
        let ns,nhds = helper1 lnds in
		let eqNulls,ps,hprels = helper_pure_hprels f in
		let new_eqNulls = CP.intersect_svl r_eqNulls eqNulls in
        let new_ps = Gen.BList.intersect_eq CP.equalFormula ps r_ps in
        let new_hprels = Gen.BList.intersect_eq CF.eq_hprel r_hprels hprels in
        if ns < r_min then
          helper lls ns nhds new_eqNulls new_ps new_hprels
        else helper lls r_min r_hns new_eqNulls new_ps new_hprels
  in
  (*start with length of the first one*)
  let fmin, fdns = helper1 (fst (List.hd ll_ldns)) in
  let eqNull,eqPures, hprels = helper_pure_hprels (snd (List.hd ll_ldns)) in
  helper (List.tl ll_ldns) fmin fdns eqNull eqPures hprels

let add_raw_hp_rel_x prog unknown_ptrs pos=
  if (List.length unknown_ptrs > 0) then
    let hp_decl =
      { Cast.hp_name = Globals.hp_default_prefix_name ^ (string_of_int (Globals.fresh_int()));
        Cast.hp_vars =  CP.remove_dups_svl unknown_ptrs;
        Cast.hp_formula = CF.mkBase CF.HEmp (MCP.mkMTrue pos) CF.TypeTrue (CF.mkTrueFlow()) [] pos;}
    in
    prog.Cast.prog_hp_decls <- (hp_decl :: prog.Cast.prog_hp_decls);
    Smtsolver.add_hp_relation hp_decl.Cast.hp_name hp_decl.Cast.hp_vars hp_decl.Cast.hp_formula;
    let hf =
      CF.HRel (CP.SpecVar (HpT,hp_decl.Cast.hp_name, Unprimed), 
               List.map (fun sv -> CP.mkVar sv pos) hp_decl.Cast.hp_vars,
      pos)
    in
    DD.ninfo_pprint ("       gen hp_rel: " ^ (Cprinter.string_of_h_formula hf)) pos;
    (hf, CP.SpecVar (HpT,hp_decl.Cast.hp_name, Unprimed))
  else report_error pos "sau.add_raw_hp_rel: args should be not empty"

let add_raw_hp_rel prog unknown_args pos=
  let pr1 = !CP.print_svl in
  let pr2 = Cprinter.string_of_h_formula in
  let pr4 (hf,_) = pr2 hf in
  Debug.no_1 "add_raw_hp_rel" pr1 pr4
      (fun _ -> add_raw_hp_rel_x prog unknown_args pos) unknown_args


(**********************)
(*check root: is_dangling (root=), is_null,is_not_null*)
let check_root_accept_dang_x root0 f0=
  let check_root_accept_dang_helper root hf p=
    if CF.is_empty_heap hf then
      let cons = CP.list_of_conjs p in
      let is_dang,is_null = List.fold_left
        (fun (b1,b2) p -> let b11,b21= CP.check_dang_or_null_exp root p in
                          b1||b11,b2||b21) (false,false) cons in
      (is_dang,is_null,false)
    else
      let ptrs = CF.get_ptrs hf in
      let is_not_null = CP.mem_svl root ptrs in
    (false,false,is_not_null)
  in
  let helper f=
    match f with
    | CF.Base fb ->
        check_root_accept_dang_helper root0 fb.CF.formula_base_heap
            (MCP.pure_of_mix fb.CF.formula_base_pure)
    | _ -> report_error no_pos "SAU.is_empty_f: not handle yet"
  in
  helper f0

let check_root_accept_dang root0 f0=
  let pr1 = Cprinter.prtt_string_of_formula in
  let pr2 = string_of_bool in
  Debug.no_2 "check_root_accept_dang" !CP.print_sv pr1 (pr_triple pr2 pr2 pr2)
      (fun _ _ -> check_root_accept_dang_x root0 f0) root0 f0

let check_root_accept_dang_fs root0 fs=
  let rec helper cur_fs cur_is_dang cur_is_null cur_is_not_null=
    match cur_fs with
      | [] -> (cur_is_dang) || (cur_is_null&&cur_is_not_null)
      | f::tl ->
          let is_dang,is_null,is_not_null = check_root_accept_dang root0 f in
          let n_is_dang = is_dang || cur_is_dang in
          if n_is_dang then true else
            let n_is_null = is_null || cur_is_null in
            let n_is_not_null = is_not_null || cur_is_not_null in
            if n_is_null && n_is_not_null then true
            else helper tl n_is_dang n_is_null n_is_not_null
  in
  helper fs false false false

let remove_dups_recursive_x hp args unk_hps unk_svl defs=
  let is_rec_f f=
    let hps = CF.get_hp_rel_name_formula f in
    (CP.mem_svl hp hps)
  in
  let is_independ_f f =
    let hps = CF.get_hp_rel_name_formula f in
    let hps1 = CP.remove_dups_svl hps in
    (* DD.ninfo_pprint ("       hp: " ^ (!CP.print_sv hp)) no_pos; *)
    let rems = List.filter (fun hp1 -> not(CP.eq_spec_var hp hp1)
    && not (CP.mem_svl hp1 unk_hps) ) hps1 in
    (* DD.ninfo_pprint ("       rems: " ^ (!CP.print_svl rems)) no_pos; *)
    (rems = [])
  in
  (*r_ss for recover las_svl after match*)
  let recover_subst r_ss n_matcheds2=
    let rec loop_helper key_sv ss res_ss=
      match ss with
        | [] -> key_sv,res_ss (*can not find*)
        | (sv1,sv2)::ls ->
            if CP.eq_spec_var key_sv sv2 then sv1,(res_ss@ls)
            else loop_helper key_sv ls (res_ss@[(sv1,sv2)])
    in
    let rec out_loop r_ss ls done_ls=
      match ls  with
        | [] -> done_ls,r_ss
        | sv::tl -> let new_sv,new_r_ss = loop_helper sv r_ss [] in
                    out_loop new_r_ss tl (done_ls@[new_sv])
    in
    out_loop r_ss n_matcheds2 []
  in
  let rec match_hds all_rec_dns rec_dns matched2 rest_dns2 last_svl r_ss r=
    match rec_dns with
      | [] -> (r, matched2,last_svl)
      |  hns::rec_ls ->
          (* let pr = pr_list_ln (fun hd -> Cprinter.prtt_string_of_h_formula (CF.DataNode hd)) in *)
          (* let _ = DD.info_pprint ("       hns: " ^ (pr hns)) no_pos in *)
           let (n_matcheds2, rest2, ss, last_ss,new_last_svl) = get_longest_common_hnodes_two args hns rest_dns2 [] in
           (* let _ = DD.info_pprint ("       n_matcheds2: " ^ (!CP.print_svl n_matcheds2)) no_pos in *)
           (* let _ = DD.info_pprint ("       new_last_svl: " ^ (!CP.print_svl new_last_svl)) no_pos in *)
           if (List.length n_matcheds2) = (List.length hns) then
             let last_svl1 = List.filter CP.is_node_typ new_last_svl in
             (* let last_svl2 = CP.diff_svl last_svl1 unk_svl in *)
             let _ = DD.ninfo_pprint ("       last_svl1: " ^ (!CP.print_svl last_svl1)) no_pos in
             let _ = DD.ninfo_pprint ("       args: " ^ (!CP.print_svl args)) no_pos in
             let ss = combine_length_neq last_svl1 args [] in
             let n_rest2 = List.map (CF.dn_subst (ss)) rest2 in
             let n_matcheds21,r_ss1 = recover_subst r_ss n_matcheds2 in
             (* let _ = DD.info_pprint ("       n_matcheds21: " ^ (!CP.print_svl n_matcheds21)) no_pos in *)
             if rest2 = [] then (true,matched2@n_matcheds21,last_svl1) else
               (*continue, if applicable*)
               match_hds all_rec_dns all_rec_dns (matched2@n_matcheds21) n_rest2 last_svl1 (r_ss1@ss) true
           else match_hds all_rec_dns rec_ls matched2 rest_dns2 last_svl r_ss r
  in
  let match_with_rec rec_ls_dns f=
    (* let _ = DD.info_pprint ("       f:" ^ *)
    (*                  (Cprinter.prtt_string_of_formula f)) no_pos in *)
    let hds = get_hdnodes f in
    let rec_ls_dns1 = List.filter (fun hds -> hds <> []) rec_ls_dns in
    let b,matched,last_svl = match_hds rec_ls_dns1 rec_ls_dns1 [] hds [] [] false in
    if not b then ([],[f])
    else
      let last_svl1 = List.filter CP.is_node_typ last_svl in
      (* let _ = DD.info_pprint ("       last_svl1: " ^ *)
      (*                (!CP.print_svl last_svl1)) no_pos in *)
      let residue = CF.drop_hnodes_f f matched in
      (* let _ = DD.info_pprint ("       residue:" ^ *)
      (*                (Cprinter.prtt_string_of_formula residue)) no_pos in *)
      let ss = combine_length_neq last_svl1 args [] in
      let new_residue = CF.subst ss residue in
      (* let _ = DD.info_pprint ("       new_residue:" ^ *)
      (*                (Cprinter.prtt_string_of_formula new_residue)) no_pos in *)
      ([(f,new_residue)],[])
  in
  let match_with_base_x is_acc_dang poss_base_fs base_fs=
    (*remove unk hps and neqNull*)
    (* let pr1 = pr_list_ln Cprinter.prtt_string_of_formula in *)
    (* let _ = DD.info_pprint ("       base_fs:" ^ (pr1 base_fs)) no_pos in *)
    let base_fs1 = List.map (fun f -> let new_f,_ = CF.drop_hrel_f f unk_hps in new_f) base_fs in
    (* let _ = DD.info_pprint ("       base_fs1:" ^ (pr1 base_fs1)) no_pos in *)
    let process_helper (f,residue) =
      (* let _ = DD.info_pprint ("       residue:" ^ (Cprinter.prtt_string_of_formula residue)) no_pos in *)
      let residue1,_ = CF.drop_hrel_f residue unk_hps in
      let residue2 = CF.remove_neqNulls_f residue1 in
      (* let _ = DD.info_pprint ("       residue2:" ^ (Cprinter.prtt_string_of_formula residue2)) no_pos in *)
      let drop = if is_empty_f residue2 then
            is_acc_dang
          else
            List.exists
                (fun base_f ->
                    check_relaxeq_formula base_f residue2
                )
                base_fs1
      in
      if drop then [] else [f]
    in
    let new_base_fs = List.concat (List.map process_helper poss_base_fs) in
    new_base_fs
  in
  (*for debugging*)
  let match_with_base is_acc_dang poss_base_fs base_fs=
    let pr1 = pr_list_ln Cprinter.prtt_string_of_formula in
    let pr2 = pr_list_ln (pr_pair Cprinter.prtt_string_of_formula Cprinter.prtt_string_of_formula) in
    Debug.no_3 "match_with_base" string_of_bool pr2 pr1 pr1
        (fun _ _ _ -> match_with_base_x is_acc_dang poss_base_fs base_fs) is_acc_dang poss_base_fs base_fs
  in
  (*END for debugging*)
  (*partition into 4 groups: rec, base, depend - not process,
    others-match with rec to find residue*)
  let rec_fs,rem_fs= List.partition is_rec_f defs in
  let indep_fs, dep_fs = List.partition is_independ_f rem_fs in
  if (List.length indep_fs >= 1) then
    let root,(* non_r_args *) _ = find_root args defs in
    (* let _ = DD.info_pprint (" root: " ^ (!CP.print_sv root) ) no_pos in *)
    (* let root = *)
    (*   if args = [] then report_error no_pos "sau.remove_dups_recursive: hp should have at least one argument" *)
    (*   else (List.hd args) *)
    (* in *)
    let rec_fs1 = remove_longer_common_prefix rec_fs in
    let rec_ls_hds = List.map get_hdnodes rec_fs1 in
    let parts = List.map (match_with_rec rec_ls_hds) indep_fs in
    let ls_poss_base_fs,ls_base_fs = List.split parts in
    let base_fs = List.concat ls_base_fs in
    let poss_base_fs = List.concat ls_poss_base_fs in
    let dep_fs1 = remove_longer_common_prefix dep_fs in
    if base_fs = [] then
      (*residue list*)
      let poss_base_fs1 = List.map snd poss_base_fs in
      let poss_base_fs2 = List.filter (fun f -> not(is_empty_f f)) poss_base_fs1 in
      (* Gen.BList.remove_dups_eq (fun f1 f2 -> check_relaxeq_formula f1 f2) defs *)
      (false,(rec_fs1@dep_fs1@poss_base_fs2))
    else
      let accept_dang = check_root_accept_dang_fs root defs in
      let new_base_fs = match_with_base accept_dang poss_base_fs base_fs in
      (true,(rec_fs1@dep_fs1@base_fs@new_base_fs))
  else
    (true,defs)

(*return: (base_case_exist,defs)*)
let remove_dups_recursive hp args unk_hps unk_svl defs=
  let pr1 = pr_list_ln Cprinter.prtt_string_of_formula in
  let pr2 = pr_pair string_of_bool pr1 in
  Debug.no_3 "remove_dups_recursive" !CP.print_sv !CP.print_svl pr1 pr2
      (fun _ _ _ -> remove_dups_recursive_x hp args unk_hps unk_svl defs) hp args defs

let simplify_set_of_formulas_x prog hp args unk_hps unk_svl defs=
  let is_self_rec f=
    let hpargs = CF.check_and_get_one_hpargs f in
    match hpargs with
      | [(hp1,_,_)] -> if CP.eq_spec_var hp hp1 then true else false
      | _ -> false
  in
  let helper f=
    let f1 = filter_var prog args f in
    let f2 =  elim_irr_eq_exps prog (CP.remove_dups_svl (args@unk_svl)) f1 in
    if is_empty_f f2 || (is_trivial f2 (hp,args)) || is_self_rec f2 then [] else [f2]
  in
  let base_case_exist,defs1 = remove_dups_recursive hp args unk_hps unk_svl defs in
  let defs2 = List.concat (List.map helper defs1) in
  let b_defs3,r_defs3=List.partition is_empty_heap_f defs2 in
  (*remove duplicate for base cases*)
  let b_defs4 = remove_subsumed_pure_formula b_defs3 in
  (*remove duplicate for recursive cases*)
  let r_defs4 = Gen.BList.remove_dups_eq check_relaxeq_formula r_defs3 in
    (*  if base_case_exist then *)
  (*      List.concat (List.map helper defs1) *)
  (*    else defs1 *)
  (* in *)
  (base_case_exist,b_defs4@r_defs4)

let simplify_set_of_formulas prog hp args unk_hps unk_svl defs=
   let pr1 = pr_list_ln Cprinter.prtt_string_of_formula in
   let pr2 = pr_pair string_of_bool pr1 in
   Debug.no_3 "simplify_set_of_formulas" !CP.print_sv !CP.print_svl pr1 pr2
       (fun _ _ _ -> simplify_set_of_formulas_x prog hp args unk_hps unk_svl defs) hp args defs

(**********************)
let mk_hprel_def prog unk_hps unk_svl hp args defs pos=
  if defs = [] then [] else begin
    let _ = DD.ninfo_pprint ((!CP.print_sv hp)^"(" ^(!CP.print_svl args) ^ ")") pos in
    let new_args,defs1 =
      if CP.mem_svl hp unk_hps then (args,defs) else (* (args,defs) *)
        drop_hp_arguments prog hp args defs
    in
    let base_case_exist,defs2 = simplify_set_of_formulas prog hp new_args unk_hps unk_svl defs1 in
    if defs2 = [] (* || not base_case_exist *) then [] else
    (* let defs1 = List.map CF.remove_neqNull_redundant_hnodes_f defs in *)
      (*make disjunction*)
      let def = List.fold_left (fun f1 f2 -> CF.mkOr f1 f2 (CF.pos_of_formula f1))
        (List.hd defs2) (List.tl defs2) in
      DD.ninfo_pprint (" =: " ^ (Cprinter.prtt_string_of_formula def) ) pos;
      let def = (hp, (CP.HPRelDefn hp, (CF.HRel (hp, List.map (fun x -> CP.mkVar x no_pos) new_args, pos)), def)) in
      [def]
 end

let mk_unk_hprel_def hp args defs pos=
  let def = List.fold_left (fun f1 f2 -> CF.mkOr f1 f2 (CF.pos_of_formula f1))
    (List.hd defs) (List.tl defs) in
  DD.ninfo_pprint (" ==: " ^ (Cprinter.prtt_string_of_formula def) ) pos;
  let def = (hp, (CP.HPRelDefn hp, (CF.HRel (hp, List.map (fun x -> CP.mkVar x no_pos) args, pos)), def)) in
  [def]

(*because root is moved to top*)
let mk_orig_hprel_def_x prog unk_hps hp r other_args args sh_ldns eqNulls eqPures hprels unk_svl=
  (* let other_args = List.tl args in *)
  let get_connected_helper ((CP.SpecVar (t,v,p)) as r)=
    if CP.mem_svl r other_args then
      let new_v = (* CP.SpecVar (t, *)
                  (* (v) ^ "_" ^ (string_of_int (Globals.fresh_int())),Unprimed) *)
        CP.fresh_spec_var r
      in
	  [(r,new_v)]
	else []
  in
  let rec look_up_next_ptrs hds r res=
      match hds with
        | [] -> ([],res,[],[])
        | hd::hss -> if CP.eq_spec_var r hd.CF.h_formula_data_node then
              let r_nexts,ssl = List.split (List.concat (List.map ((fun (CP.SpecVar (t,v,p)) ->
                  if (is_pointer t)
                  then
				    let ss = get_connected_helper (CP.SpecVar (t,v,p)) in
					let new_v = CP.subs_one ss (CP.SpecVar (t,v,p)) in
					([new_v,ss])
                  else [])) hd.CF.h_formula_data_arguments)) in
			  let ss = List.concat ssl in
			  let matched_hn =
				if ss <> [] then 
				  let r =(CF.h_subst ss (CF.DataNode hd)) in
					  match r with
					   | CF.DataNode hd -> hd
					   | _ -> report_error no_pos "sau.look_up_next_ptrs"
				else hd
			  in
              (r_nexts, res@hss,[matched_hn],ss)
            else look_up_next_ptrs hss r (res@[hd])
  in
  let rec helper hds roots r_nexts r_done r_ss=
    match roots with
      | [] -> (r_nexts,hds,r_done,r_ss)
      | r::rs -> let nptrs,nhds,hn_done,ss = look_up_next_ptrs hds r [] in
                 helper nhds rs (r_nexts@nptrs) (r_done@hn_done) (r_ss@ss)
  in
  let rec get_last_ptrs_new ls_lnds roots root_nexts r_done r_ss=
    match root_nexts with
      | [] -> roots,r_done,r_ss,ls_lnds
      | _ -> let nptrs,nhds,hn_done,ss = helper ls_lnds root_nexts [] [] [] in
             get_last_ptrs_new nhds root_nexts nptrs (r_done@hn_done) (r_ss@ss)
  in
  let next_roots,new_sh_dns,ss,rem_dns = get_last_ptrs_new sh_ldns [r] [r] [] [] in
  let dnss = (new_sh_dns@rem_dns) in
  let hdss = List.map (fun hd -> (CF.DataNode hd)) dnss in
  (*subst*)
  (*let hdss = List.map (CF.h_subst ss) hdss in *)
   (*currently we just support one next root. should improve when support tree*)
  let _ = DD.ninfo_pprint ("      next_roots:" ^ (!CP.print_svl next_roots)) no_pos in
  (* let _ = DD.info_pprint ("      unk_svl:" ^ (!CP.print_svl unk_svl)) no_pos in *)
  (* let next_roots1 = CP.diff_svl next_roots unk_svl in *)
  (* let next_roots1 = CP.diff_svl next_roots unk_svl in *)
  (* let _ = DD.info_pprint ("      next_roots1:" ^ (!CP.print_svl next_roots1)) no_pos in *)
  match next_roots with
     | [] -> report_error no_pos "sau.generalize_one_hp: sth wrong"
     | _ ->  let _ = DD.ninfo_pprint ("      last root:" ^ (Cprinter.string_of_spec_var_list  next_roots)) no_pos in
         (*generate new hp*)
             let n_args = (next_roots@other_args) in
         let n_hprel,n_hp =  add_raw_hp_rel prog n_args no_pos in
         (*first rel def for the orig*)
         let rest =  (hdss@[n_hprel]@(List.map (fun hprel -> CF.HRel hprel) hprels)) in
         let orig_defs_h = List.fold_left (fun hf1 hf2 -> CF.mkStarH hf1 hf2 no_pos) (List.hd rest) (List.tl rest) in
         let orig_def = CF.formula_of_heap orig_defs_h no_pos in
         (*common null process*)
		 let orig_def1 =
		   match eqNulls with
		   | [] -> orig_def
		   | _ ->
			  (*let eqNulls1 = List.map (CP.subs_one ss) eqNulls in*)
			  let ps = List.map (fun v -> CP.mkNull v no_pos) eqNulls in
		      let p = CP.conj_of_list ps no_pos in
			  CF.mkAnd_pure orig_def (MCP.mix_of_pure p) no_pos
		 in
         (*common pure process*)
         let common_pures = CP.conj_of_list eqPures no_pos in
         let orig_def2 = CF.mkAnd_pure orig_def1 (MCP.mix_of_pure common_pures) no_pos in
         let defs = mk_hprel_def prog unk_hps unk_svl hp args [orig_def2] no_pos in
         (*subst*)
         let hprel = CF.HRel (hp, List.map (fun x -> CP.mkVar x no_pos) args, no_pos) in
		 (*elim all except root*)
		 let n_orig_defs_h = CF.drop_hnodes_hf orig_defs_h other_args in
         (defs, (hprel, n_orig_defs_h), n_hp, n_args, dnss,
          CP.diff_svl next_roots unk_svl)
     (* | _ -> report_error no_pos "sau.generalize_one_hp: now we does not handle more than two ptr fields" *)

let mk_orig_hprel_def prog unk_hps hp r other_args args sh_ldns eqNulls eqPures hprels unk_svl=
  let pr1 = !CP.print_sv in
  let pr2 = !CP.print_svl in
  let pr3 = fun hd -> Cprinter.prtt_string_of_h_formula (CF.DataNode hd) in
  let pr4 =  pr_list !CP.print_formula in
  let pr5 = pr_list (pr_pair pr1 string_of_hp_rel_def) in
  let pr6 (d,_,hp,args,dns,_) = let pr = pr_quad pr5 pr1 pr2 (pr_list pr3) in
                              pr (d,hp,args,dns)
  in
  let pr7a hrel = Cprinter.string_of_hrel_formula (CF.HRel hrel) in
  let pr7 = pr_list pr7a in
  Debug.no_7 "mk_orig_hprel_def" pr2 pr1 pr2 (pr_list pr3) pr2 pr4 pr7 pr6
      (fun _ _ _ _ _ _ _ -> mk_orig_hprel_def_x prog unk_hps hp r other_args args sh_ldns eqNulls eqPures hprels unk_svl)
      unk_hps hp args sh_ldns eqNulls eqPures hprels

let elim_not_in_used_args (a,b,orig_fs) fs hp args=
  let helper svl f=
    let new_f,_ = CF.drop_hrel_f f [hp] in
    svl@(CF.fv new_f)
  in
  let svl = List.fold_left helper [] fs in
  let new_args = CP.intersect_svl args svl in
  let n_orig_hpdef,new_fs=
    if List.length args = List.length new_args then (a,b,orig_fs),fs
    else
      let old_hrel = mkHRel hp args no_pos in
      let new_hrel = mkHRel hp new_args no_pos in
      let subst = [(old_hrel,new_hrel)] in
      let new_fs = List.map (fun f -> CF.subst_hrel_f f subst) fs in
      ((a,b,CF.subst_hrel_f orig_fs subst), new_fs)
  in
  n_orig_hpdef,new_args,new_fs

let get_longest_common_hnodes_list_x prog unk_hps unk_svl hp r non_r_args args fs=
 if List.length fs <= 1 then
   let hpdef = mk_hprel_def prog unk_hps unk_svl hp args fs no_pos in
   hpdef
 else begin
   let lldns = List.map (fun f -> (get_hdnodes f, f)) fs in
   let min,sh_ldns,eqNulls,eqPures,hprels = get_min_number_new prog args lldns in
   (*remove hp itself*)
   let hprels1 = List.filter (fun (hp1,_,_) -> not(CP.eq_spec_var hp hp1)) hprels in
   if min = 0 && eqNulls = [] then
     (*mk_hprel_def*)
     let hpdef = mk_hprel_def prog unk_hps unk_svl hp args fs no_pos in
     hpdef
   else
     (*get shortest list of hnodes*)
     (* let sh_ldns, _ = get_shortest_lnds lldns min in *)
     (*assume root is the first arg*)
     (* let root = List.hd args in *)
     (*let sh_ldns1 = move_root_to_top root sh_ldns in*)
     let orig_hpdefs, hp_subst, new_hp, n_args,sh_ldns2,next_roots = mk_orig_hprel_def prog unk_hps hp r non_r_args args sh_ldns eqNulls eqPures hprels1 unk_svl in
     match orig_hpdefs with
       | [] -> []
       | [(hp01,orig_hpdef)] ->
       (* let com_hps = List.map (fun (hp,eargs,_)-> (hp,eargs)) hprels1 in *)
       let n_fs = List.map (process_one_f prog args n_args next_roots hp_subst sh_ldns2 eqNulls eqPures hprels1) lldns in
       let n_fs1 = List.filter (fun f -> not ((is_empty_f f) || (CF.is_only_neqNull n_args [] f))) n_fs in
       (*for debugging*)
       (* let pr1 = pr_list_ln Cprinter.prtt_string_of_formula in *)
       (* let _ = Debug.info_pprint ("  n_fs: "^ (pr1 n_fs)) no_pos in *)
       (* let _ = Debug.info_pprint ("  n_fs1: "^ (pr1 n_fs1)) no_pos in *)
       (*END for debugging*)
       let n_fs2 = Gen.BList.remove_dups_eq (fun f1 f2 -> check_relaxeq_formula f1 f2) n_fs1 in
       let n_orig_hpdef,n_args1,n_fs3 =
         if !Globals.sa_elim_useless then
           elim_not_in_used_args orig_hpdef n_fs2 new_hp n_args
         else (orig_hpdef, n_args, n_fs2)
       in
       let new_hpdef = mk_hprel_def prog unk_hps unk_svl new_hp n_args1 n_fs3 no_pos in
       if new_hpdef = [] then
         let hpdef = mk_hprel_def prog unk_hps unk_svl hp args fs no_pos in
         hpdef
       else
         ((hp01,n_orig_hpdef)::new_hpdef)
       | _ -> report_error no_pos "sau.get_longest_common_hnodes_list"
 end

let get_longest_common_hnodes_list prog unk_hps unk_svl hp r non_r_args args fs=
  let pr1 = pr_list_ln Cprinter.prtt_string_of_formula in
  let pr2 = fun (_, def) -> Cprinter.string_of_hp_rel_def def in
  let pr3 = !CP.print_sv in
  let pr4 = !CP.print_svl in
  Debug.no_5 "get_longest_common_hnodes_list" pr3 pr4 pr4 pr4 pr1 (pr_list_ln pr2)
      (fun _ _ _ _ _-> get_longest_common_hnodes_list_x prog unk_hps unk_svl hp r non_r_args args fs)
      hp args unk_hps unk_svl fs

(************************************************************)
      (******************END FORM HP DEF*********************)
(************************************************************)

(************************************************************)
    (****************SUBST HP PARDEF*****************)
(************************************************************)
let rec look_up_subst_group hp args nrec_grps=
  (*refresh all ptrs except ones in args2 which substed by args*)
  let rec refresh_ptrs args2 ptrs r_ss=
    match ptrs with
      | [] -> r_ss
      | sv::svl ->
          if CP.mem_svl sv args2 then
             refresh_ptrs args2 svl r_ss
          else
            let f_sv = CP.fresh_spec_var sv in
            refresh_ptrs args2 svl r_ss@[(sv,f_sv)]
  in
  let rec susbt_group fs pardefs=
    match pardefs with
      | [] -> fs
      | (_, args2, f,_)::pss->
          (*should refresh f*)
          let ptrs = CF.get_ptrs_w_args_f f in
          let ss1 = refresh_ptrs args2 (CP.remove_dups_svl ptrs) [] in
          let ss = List.combine args2 args in
          let nf1 = CF.subst (ss1) f in
          let nf2 = CF.subst (ss) nf1 in
          susbt_group (fs@[nf2]) pss
  in
  match nrec_grps with
    | [] -> [](* report_error no_pos "sau.look_up_groups" *)
    | grp::gs -> begin
        let hp1,_,_,_ = (List.hd grp) in
        if CP.eq_spec_var hp hp1 then
           [(hp1,susbt_group [] grp)]
        else
          look_up_subst_group hp args gs
    end


(*this function is used two times: succ subts with
 - first for nrec_grp and
 - at the end for rec_indp_grp
*)
let succ_susbt_x prog nrec_grps unk_hps allow_rec_subst (hp,args,f,unk_svl)=
  DD.ninfo_pprint ("       succ_susbt hp: " ^ (!CP.print_sv hp)) no_pos;
  let pos = no_pos in
  let simplify_and_empty_test args f=
    let f1 = simplify_one_formula prog args f in
    let r =
      if is_empty_f f1 then []
      else [(hp,args,f1,unk_svl)]
    in
    r
  in
  (*l1 x l2*)
  let helper ls1 ls2=
    (* let pr = (Cprinter.prtt_string_of_formula) in *)
    (* let pr1 = pr_list_ln pr in *)
    let res = List.concat (List.map (fun f1 ->
        List.map (fun f2 ->
            (* let _ = DD.info_pprint ("       f1:" ^ (pr f1)) no_pos in *)
            (* let _ = DD.info_pprint ("       f2:" ^ (pr f2)) no_pos in *)
            let ptrs = get_data_view_hrel_vars_formula f1 in
            let new_f2 = CF.drop_hnodes_f f2 ptrs in
            let ls_hpargs1 = CF.get_HRels_f f1 in
            let ls_hpargs2 = CF.get_HRels_f new_f2 in
            let ls_inter = Gen.BList.intersect_eq check_hp_arg_eq ls_hpargs2 ls_hpargs1 in
            let dups_hps = List.map fst ls_inter in
            let new_f21,_ = CF.drop_hrel_f new_f2 dups_hps in
         (* let _ = DD.info_pprint ("       new_f21:" ^ (pr new_f21)) no_pos in *)
         CF.mkStar f1 new_f21 CF.Flow_combine pos
    ) ls2) ls1)
    in
    (* let _ = DD.info_pprint ("       res:" ^ (pr1 res)) no_pos in *)
    res
  in
  let succ_hp_args = CF.get_HRels_f f in
  (*filter hp out if not allow subst by itself*)
  let succ_hp_args =
    if allow_rec_subst then succ_hp_args else
      List.filter (fun (hp1,_) -> not (CP.eq_spec_var hp hp1)) succ_hp_args
  in
  (* DD.info_pprint ("       succ_hp_args:" ^ (let pr = pr_list_ln (pr_pair !CP.print_sv !CP.print_svl) *)
  (*                                           in pr succ_hp_args)) no_pos; *)
  match succ_hp_args with
    | [] -> (false, simplify_and_empty_test args f)
    | _ -> begin
        let r = List.concat (List.map (fun (hp0,arg0) -> look_up_subst_group hp0 arg0 nrec_grps)  succ_hp_args) in
        if List.length r = 0 then
          (false, simplify_and_empty_test args f)
        else
          let matched_hps, fs_list = List.split r in
        (*create template from f*)
          let nf,_ = CF.drop_hrel_f f matched_hps in
        (*combine fs_list*)
          let lsf_cmb = List.fold_left helper [nf]
            (List.filter (fun ls -> ls <>[]) fs_list) in
          DD.ninfo_pprint ("       succ_susbt lsf_cmb:" ^ (let pr = pr_list_ln (Cprinter.prtt_string_of_formula)
                                                          in pr lsf_cmb)) no_pos;
          let lsf_cmb1 = List.map (simplify_one_formula prog args) lsf_cmb in
          let lsf_cmb2 = List.filter (fun f ->  not (is_trivial f (hp,args)) ) lsf_cmb1 in
        (*remove f which has common prefix*)
          let lsf_cmb3 = remove_longer_common_prefix lsf_cmb2 in
          DD.ninfo_pprint ("       succ_susbt lsf_cmb 1:" ^ (let pr = pr_list_ln (Cprinter.prtt_string_of_formula)
               in pr lsf_cmb1)) no_pos;
          (* DD.info_pprint ("       succ_susbt lsf_cmb 2:" ^ (let pr = pr_list_ln (Cprinter.prtt_string_of_formula) *)
          (*      in pr lsf_cmb2)) no_pos; *)
          let fss = List.map (fun f1 -> (hp,args,f1,unk_svl)) lsf_cmb3 in
          (true, fss)
    end

let succ_susbt prog nrec_grps unk_hps allow_rec_subst (hp,args,f,unk_svl)=
   let pr1 = pr_list_ln (pr_list_ln string_of_par_def_w_name_short) in
   let pr2 = pr_quad !CP.print_sv !CP.print_svl Cprinter.prtt_string_of_formula !CP.print_svl in
   let pr3 = pr_pair string_of_bool (pr_list_ln pr2) in
   Debug.no_3 "succ_susbt" pr1 string_of_bool pr2 pr3
       (fun _ _  _ -> succ_susbt_x prog nrec_grps unk_hps allow_rec_subst (hp,args,f,unk_svl)) nrec_grps allow_rec_subst (hp,args,f,unk_svl)

let succ_subst_with_mutrec_x prog deps unk_hps=
  let find_succ_one_dep_grp dep_grp=
    let (hp,_,_,_) = List.hd dep_grp in
    let succ_hps = List.concat (List.map (fun (_,_,f,_) -> CF.get_hp_rel_name_formula f) dep_grp) in
    (*remove dups*)
    let succ_hps1 = Gen.BList.remove_dups_eq CP.eq_spec_var succ_hps in
    (* DD.ninfo_pprint ("       succ_hps: " ^ (!CP.print_svl succ_hps)) no_pos; *)
      (*remove unk_hps*)
      (* let succ_hps2 = List.filter (fun hp1 -> not (CP.mem_svl hp1 unk_hps)) succ_hps1
      in *)
    (hp,succ_hps1)
  in
  let update_helper hp0 succ0 (hp1,succ1)=
    if CP.mem_svl hp0 succ1 then (hp1,CP.remove_dups_svl (succ0@succ1))
    else (hp1,succ1)
  in
  let check_mutrec ls_hp_succ=
    let rec subst_helper ls res=
      match ls with
        | [] -> res
        | (hp,succ_hps)::tl ->
            let indir_succ_hps = List.concat (List.map (fun (hp,succ1) -> if CP.mem_svl hp succ_hps
                then succ1 else []) (tl@res)) in
            let new_succ = CP.remove_dups_svl (succ_hps@indir_succ_hps) in
            let new_res = List.map (update_helper hp new_succ) res in
            let new_tl = List.map (update_helper hp new_succ) tl in
            subst_helper new_tl (new_res@[(hp,new_succ)])
    in
    let closed_ls_hp_succ = subst_helper ls_hp_succ [] in
    List.concat (List.map (fun (hp,succ) -> if CP.mem_svl hp succ then [hp] else []) closed_ls_hp_succ)
  in
  let check_subst_diverge ls_mut_rec_hp_succ=
    let rec rec_check_diverge hp last history=
      (*START debugging*)
      (* let _ = DD.info_pprint ("       hp: " ^ (!CP.print_sv hp)) no_pos in *)
      (* let _ = DD.info_pprint ("       last: " ^ (!CP.print_svl last)) no_pos in *)
      (* let _ = DD.info_pprint ("       history: " ^ (let pr = pr_list !CP.print_svl in pr history)) no_pos in *)
      (*END debugging*)
      let last1 = List.filter (fun hp0 -> not (CP.eq_spec_var hp0 hp)) last in
      if last1 = [] then false else
        if List.exists
          (fun prev_succ -> CP.diff_svl prev_succ last1 = []) history then true
        else
          let new_succ = List.concat (List.map (fun (hp0,succ0) -> if CP.mem_svl hp0 last1 then succ0 else []) ls_mut_rec_hp_succ) in
          let new_last = CP.remove_dups_svl (new_succ) in
          rec_check_diverge hp new_last (history@[last1])
    in
    let rec_diverge,rec_terminating = List.partition
      (fun (hp0,succ0) -> rec_check_diverge hp0 succ0 []) ls_mut_rec_hp_succ in
    (List.map fst rec_terminating, List.map fst rec_diverge)
  in
  let subst_one_mutrec_grp all_orig_mut_rec_grps terminating_mutrec_grp=
    let rec susbt_helper grp=
      let bs, ls_new_grp = List.split (List.map (succ_susbt prog all_orig_mut_rec_grps unk_hps false) grp) in
      let b = List.fold_left (fun b1 b2 -> b1 || b2) false bs in
      let new_grp = List.concat ls_new_grp in
      if b then susbt_helper new_grp else new_grp
    in
    susbt_helper terminating_mutrec_grp
  in
  let ls_hp_succ = List.map find_succ_one_dep_grp deps in
  let mut_rec_hps = check_mutrec ls_hp_succ in
  (*START debugging*)
  (* let pr1 = pr_list_ln (pr_pair !CP.print_sv !CP.print_svl) in *)
  (* let _ = DD.info_pprint ("       ls_hp_succ: " ^ (pr1 ls_hp_succ)) no_pos in *)
  (* let _ = DD.info_pprint ("       mut_rec_hps: " ^ (!CP.print_svl mut_rec_hps)) no_pos in *)
  (*END debugging*)
  if mut_rec_hps = [] then ([],[],deps,[]) else
  (*partition*)
    let mut_rec_deps,nmut_rec_deps= List.partition
      (fun grp -> let (hp,_,_,_) = List.hd grp in
                  CP.mem_svl hp mut_rec_hps
      )
      deps
    in
    (*check safe subst*)
    let ls_mut_rec_hp_succ = List.filter (fun (hp,_) -> CP.mem_svl hp mut_rec_hps) ls_hp_succ in
    let to_be_subst,to_be_not_subst = check_subst_diverge ls_mut_rec_hp_succ in
    (*START debugging*)
    (* let _ = DD.info_pprint ("       to_be_subst: " ^ (!CP.print_svl to_be_subst)) no_pos in *)
    (* let _ = DD.info_pprint ("       to_be_not_subst: " ^ (!CP.print_svl to_be_not_subst)) no_pos in *)
    (*END debugging*)
    let rem,to_be_subst_grps = List.partition
      (fun grp -> let (hp0,_,_,_) = List.hd grp in
                  CP.mem_svl hp0 to_be_not_subst
      ) mut_rec_deps
    in
    (*subst*)
    let substed_mit_rec_indp = List.map (subst_one_mutrec_grp mut_rec_deps) to_be_subst_grps in
  (substed_mit_rec_indp,rem,nmut_rec_deps,to_be_subst)

(*out: rec_indp,rec_dep,nrec_deps*)
let succ_subst_with_mutrec prog deps unk_hps=
  let pr1 = pr_list_ln (pr_list_ln string_of_par_def_w_name_short) in
  Debug.no_1 " succ_subst_with_mutrec" pr1 (pr_quad pr1 pr1 pr1 !CP.print_svl)
      (fun _ -> succ_subst_with_mutrec_x prog deps unk_hps) deps

let succ_subst_with_rec_indp_x prog rec_indp_grps unk_hps depend_grps=
  let is_independ_pardef (hp,_,f,_) =
    let hps = CF.get_hp_rel_name_formula f in
    let hps = CP.remove_dups_svl hps in
    (* DD.ninfo_pprint ("       rec hp: " ^ (!CP.print_sv hp)) no_pos; *)
    let _,rems = List.partition (fun hp1 -> CP.eq_spec_var hp hp1) hps in
    (* DD.ninfo_pprint ("       rec rems: " ^ (!CP.print_svl rems)) no_pos; *)
    (rems = [])
  in
  let is_independ_group grp =
    List.for_all is_independ_pardef grp
  in
  let get_hp_name_from_grp grp=
    match grp with
      | [] -> report_error no_pos "sau.succ_susbt_with_rec_indp: should not empty"
      | (hp,_,_,_)::_ -> hp
  in
  let refine_grp_helper_x hp0 args0 fss=
    let fss1 = remove_longer_common_prefix fss in
    (* let fss1 = Gen.BList.remove_dups_eq (fun f1 f2 -> check_relaxeq_formula f1 f2) fss in *)
    let fss2= List.filter (fun f ->  not (is_trivial f (hp0,args0)) ) fss1 in
    (*remove neqNull if fss>1 formula*)
    let fss3 =
      if List.length fss2 > 1 then
        (* List.filter (fun f -> not(CF.is_only_neqNull args0 [] f)) fss2 *)
        let helper f=
          let f1 = CF.remove_neqNulls_f f in
          if is_empty_f f1 then [] else [f1]
        in
        List.concat (List.map helper fss2)
      else fss2
    in
    fss3
  in
  let refine_grp_helper hp0 args0 fss=
    let pr1= pr_list_ln Cprinter.prtt_string_of_formula in
    Debug.no_3 "refine_grp_helper" !CP.print_sv !CP.print_svl pr1 pr1
        (fun _ _ _ -> refine_grp_helper_x hp0 args0 fss)
        hp0 args0 fss
  in
  (********************)
  (* preprocess rec_indps:
     subst rec branch by all base branches
  *)
(*
  let preprocess_rec_indp_x grp=
    let rec_branches,base_branches = List.partition is_rec_pardef grp in
    if rec_branches = [] || base_branches = [] then grp else
      begin
          (*each rec_branch, substed by base*)
          let new_rec_bracnhes = List.concat (snd (List.split (
              List.map (succ_susbt prog [base_branches] unk_hps true) rec_branches))) in
          match new_rec_bracnhes with
            | [] -> base_branches
            | (hp1,args1,_,unk_svl)::_ ->
                let new_rec_fss = refine_grp_helper hp1 args1 (List.map (fun (_,_,f,_)-> f) new_rec_bracnhes) in
                let new_rec_bracnhes1 =  List.map (fun f -> (hp1,args1,f,unk_svl)) new_rec_fss in
                (base_branches@new_rec_bracnhes1)
      end
  in
  (*for debugging**)
  let preprocess_rec_indp grp=
    let pr1 = (pr_list_ln string_of_par_def_w_name_short) in
    Debug.no_1 "preprocess_rec_indp" pr1 pr1
        (fun _ -> preprocess_rec_indp_x grp) grp
  in
*)
  (*END for debugging**)
  (* let rec_indp_grps1 = List.map preprocess_rec_indp rec_indp_grps in *)
  (*********************************)
        (*******END***************)
  (********************************)
  let rec get_last_ptr_x args0 hds=
    match hds with
      | [] -> args0
      | hd ::tl ->
          let args1 = List.filter (fun a -> not (CP.eq_spec_var hd.CF.h_formula_data_node a)) args0 in
          if List.length args1 < List.length args0 then
            let new_ptrs = List.filter CP.is_node_typ hd.CF.h_formula_data_arguments in
            get_last_ptr_x (CP.remove_dups_svl (args1@new_ptrs)) tl
          else
            get_last_ptr_x args0 tl
  in
  let rec get_last_ptr args0 hds=
    let pr1 = !CP.print_svl in
    let pr2 = !CP.print_svl in
    Debug.no_1 "get_last_ptr" pr1 pr2
        (fun _ -> get_last_ptr_x args0 hds) args0
  in
   let succ_subst_one_pardef rec_indp_hps (hp,args,f,unk_svl)=
    let _ = DD.ninfo_pprint ("       hp: " ^ (!CP.print_sv hp)) no_pos in
    let _ = DD.ninfo_pprint ("       rec_indp_hps: " ^ (!CP.print_svl rec_indp_hps)) no_pos in
    let succ_hprels = CF.get_hprel f in
    let succ_hps = (List.map (fun (hp,_,_) -> hp) succ_hprels) in
    let succ_hps1 = List.filter (fun hp1 -> not (CP.eq_spec_var hp1 hp)) succ_hps in
    (* let _ = DD.info_pprint ("       succ_hps1: " ^ (!CP.print_svl succ_hps1)) no_pos in *)
    let new_pardefs=
      if (succ_hps1 = []) || (CP.diff_svl succ_hps1 rec_indp_hps <> []) (* || *)
      (* not (CF.is_HRel_f f) *)
      (*currently we just support f without hnodes hns, should enhance:
        recursive branches: matching with hns first
      *)
      then
        [(hp,args,f,unk_svl)]
      else
        let _, fss = succ_susbt prog rec_indp_grps unk_hps false (hp,args,f,unk_svl) in
        (* let pr1= Cprinter.prtt_string_of_formula in *)
        (* let pr2 (_,_,a,_)= pr1 a in *)
        (* let pr3 = pr_list_ln pr2 in *)
        (* let _ = DD.info_pprint ("       fss: " ^ (pr3 fss)) no_pos in *)
        (* let hprel = mkHRel hp args no_pos in *)
        (* let ss = List.map (fun hprel1 -> ((CF.HRel hprel1), hprel)) succ_hprels in *)
        (* let fss1 = List.map (fun (_,_,f,_) -> (CF.subst_hrel_f f ss)) fss in *)
        (*pair args*)
        let hds = get_hdnodes f in
        let pr_args = List.map (fun a -> let last_args=get_last_ptr [a] hds in (a,last_args)) args in
        let pr1 = pr_list (pr_pair !CP.print_sv !CP.print_svl) in
        let _ = DD.ninfo_pprint ("       pr_args: " ^ (pr1 pr_args)) no_pos in
        let subst_helper pr_args0 (hp1,eargs1,p)=
          let args1 = List.concat (List.map CP.afv eargs1) in
          let rec get_new_arg ls r=
            match ls with
              | [] -> r
              | (a,last_args)::tl ->
                  let inter= CP.intersect_svl last_args args1 in
                  let new_a=
                    match inter with
                      | [] -> a
                      | [na] -> na
                      | _ -> report_error no_pos "sau.subst_helper"
                  in
                  get_new_arg tl (r@[new_a])
          in
          let rec add_anon_args ls l_args1 r=
            match ls with
              | [] -> r
              | a::tl -> if CP.mem_svl a l_args1 then
                    add_anon_args tl l_args1 (r@[a])
                  else
                    let fr_a = CP.fresh_spec_var a in
                    add_anon_args tl l_args1 (r@[fr_a])
          in
          let new_args0 = if List.length args = List.length args1 then
            get_new_arg pr_args0 []
              else add_anon_args args args1 []
          in
          let hprel = mkHRel hp new_args0 no_pos in
          ((CF.HRel (hp1,eargs1,p)), hprel)
        in
        let ss = List.map (subst_helper pr_args) succ_hprels in
        let fss1 = List.map (fun (_,_,f,_) -> (CF.subst_hrel_f f ss)) fss in
        (* let fss1 = List.map (fun (_,_,f,_) -> (CF.subst_hprel f succ_hps1 hp)) fss in *)
        let fss2 = refine_grp_helper hp args (fss1) in
        let fss3 = List.map (fun f1 -> (hp,args,f1,unk_svl)) fss2 in
        fss3
    in
    new_pardefs
  in
  let succ_subst_one_grp rec_indp_hps grp=
    let pardefs =
      if List.length grp > 1 then
        List.concat (List.map (succ_subst_one_pardef rec_indp_hps) grp)
      else grp
    in
    pardefs
  in
  let rec susbt_fix rec_indp_grps0 depend_grps0 r=
  (*get all rec_indp hp names*)
    let rec_indp_hps = List.map get_hp_name_from_grp rec_indp_grps0 in
    let new_dep_grps = List.map (succ_subst_one_grp rec_indp_hps) depend_grps0 in
    let new_indp_grps,deps = List.partition is_independ_group new_dep_grps in
    if new_indp_grps = [] || deps = [] then
      (r@new_dep_grps)
    else susbt_fix (rec_indp_grps0@new_indp_grps) deps (r@new_indp_grps)
  in
  susbt_fix rec_indp_grps depend_grps []

let succ_subst_with_rec_indp prog rec_indp_grps unk_hps depend_grps=
  let pr1 = pr_list_ln (pr_list_ln string_of_par_def_w_name_short) in
  Debug.no_3 "succ_subst_with_rec_indp" pr1 !CP.print_svl pr1 pr1
      (fun _ _ _ -> succ_subst_with_rec_indp_x prog rec_indp_grps unk_hps depend_grps)
      rec_indp_grps unk_hps depend_grps

(************************************************************)
    (****************END SUBST HP PARDEF*****************)
(************************************************************)

(************************************************************)
    (****************SUBST HP DEF*****************)
(************************************************************)

let rec look_up_subst_hpdef hp args nrec_hpdefs=
  match nrec_hpdefs with
    | [] -> [](* report_error no_pos "sau.look_up_groups" *)
    | (a1,hprel1,f1)::gs -> begin
        let hp1 = get_hpdef_name a1 in
        (* DD.info_pprint ("       hp: " ^ (!CP.print_sv hp)) no_pos; *)
        (* DD.info_pprint ("       succ_susbt_def hp1: " ^ (!CP.print_sv hp1)) no_pos; *)
        if CP.eq_spec_var hp hp1 then
           let args1 = get_ptrs hprel1 in
           let ss = List.combine args1 args in
           let nf1 = CF.subst ss f1 in
           (CF.list_of_disjs nf1)
        else
          look_up_subst_hpdef hp args gs
    end

let compose_subs f1 f2 pos=
  let ptrs1 = get_data_view_hrel_vars_formula f1 in
  let ptrs2 = get_data_view_hrel_vars_formula f2 in
  let svl1 = CF.fv f1 in
  let irre_svl = CP.diff_svl ptrs2 svl1 in
  let new_f2 = CF.drop_hnodes_f f2 (ptrs1@irre_svl) in
  let new_f21,_ = CF.drop_hrel_f new_f2 ptrs1 in
  CF.mkStar f1 new_f21 CF.Flow_combine pos

let succ_susbt_hpdef_x prog nrec_hpdefs all_succ_hp (hp,args,f)=
  DD.ninfo_pprint ("       succ_susbt_def hp: " ^ (!CP.print_sv hp)) no_pos;
  DD.ninfo_pprint ("       all_succ_hp: " ^ (!CP.print_svl all_succ_hp)) no_pos;
  let pos = no_pos in
  (*l1 x l2*)
  let helper ls1 ls2=
    List.concat (List.map (fun f1 ->
        List.map (fun f2 ->
            compose_subs f1 f2 pos
    ) ls2) ls1)
  in
  let simplify_and_empty_test args f=
    let f1 = simplify_one_formula prog args f in
    (* let _ = DD.info_pprint ("       f:" ^ (Cprinter.prtt_string_of_formula f)) no_pos in *)
    (* let _ = DD.info_pprint ("       f1:" ^ (Cprinter.prtt_string_of_formula f1)) no_pos in *)
    let r =
      if is_empty_f f1 then []
      else [f1]
    in
    r
  in
  let succ_hp_args = CF.get_HRels_f f in
  (*filter hp out*)
  let succ_hp_args = List.filter (fun (hp1,_) -> not (CP.eq_spec_var hp hp1) &&
      (CP.mem_svl hp1 all_succ_hp)) succ_hp_args in
  (* DD.info_pprint ("       succ_hp_args:" ^ (let pr = pr_list_ln (pr_pair !CP.print_sv !CP.print_svl) *)
  (*                                           in pr succ_hp_args)) no_pos; *)
  match succ_hp_args with
    | [] ->
        (false, simplify_and_empty_test args f)
    | _ -> begin
        let fs_list =  (List.map (fun (hp0,arg0) -> look_up_subst_hpdef hp0 arg0 nrec_hpdefs) succ_hp_args) in
        let r = (List.concat fs_list) in
        if List.length r = 0 then
          (false, simplify_and_empty_test args f)
        else
        (*create template from f*)
          let nf,_ = CF.drop_hrel_f f (fst (List.split succ_hp_args)) in
        (*combine fs_list*)
          let lsf_cmb = List.fold_left helper [nf] fs_list in
          (* DD.info_pprint ("       succ_susbt lsf_cmb:" ^ (let pr = pr_list_ln (Cprinter.prtt_string_of_formula) *)
          (*                                                 in pr lsf_cmb)) no_pos; *)
          (*remove trivial def*)
          let lsf_cmb1 = List.filter (fun f -> not (is_trivial f (hp,args))) lsf_cmb in
          (*simpl pure*)
          let lsf_cmb2 = List.concat
            (List.map (simplify_and_empty_test args) lsf_cmb1)
          in
        (*remove f which has common prefix*)
          let lsf_cmb3 = (remove_longer_common_prefix lsf_cmb2) in
          ((lsf_cmb3 <> []),lsf_cmb3)
    end

let succ_susbt_hpdef prog nrec_hpdefs all_succ_hp (hp,args,f)=
  let pr1 = pr_list_ln (string_of_hp_rel_def) in
  let pr2 = !CP.print_svl in
  let pr3 = pr_triple !CP.print_sv !CP.print_svl Cprinter.prtt_string_of_formula in
  let pr4 = pr_pair string_of_bool (pr_list_ln Cprinter.prtt_string_of_formula) in
  Debug.no_3 " succ_susbt_hpdef" pr1 pr2 pr3 pr4
      (fun _ _ _ -> succ_susbt_hpdef_x prog nrec_hpdefs all_succ_hp (hp,args,f))
      nrec_hpdefs all_succ_hp (hp,args,f)

let combine_hpdefs_x hpdefs=
  (*partition the set by hp_name*)
  let rec partition_hpdefs_by_hp_name defs parts=
    match defs with
      | [] -> parts
      | (a1,a2,a3)::xs ->
          let part,remains= List.partition (fun (a2,_,_) ->
              let hp1 = get_hpdef_name a1 in
              let hp2 = get_hpdef_name a2 in
              CP.eq_spec_var hp1 hp2) xs
          in
          partition_hpdefs_by_hp_name remains (parts@[[(a1,a2,a3)]@part])
  in
  let extract_def args0 (_, hprel, f)=
    let _,args = CF.extract_HRel hprel in
    let ss = List.combine args args0 in
    CF.list_of_disjs (CF.subst ss f)
  in
  let combine_one_hpdef grp=
    match grp with
      | [] -> report_error no_pos "sau.combine_one_hpdef"
      | [def] -> def
      | (hp0, hprel0, f0)::tl ->
          let _,args0 = CF.extract_HRel hprel0 in
          let fs = (CF.list_of_disjs f0)@(List.concat (List.map (extract_def args0) tl)) in
          let fs1 = (remove_longer_common_prefix fs) in
          let fs2 = remove_subset fs1 in
          let p = (CF.pos_of_formula f0) in
          let def = List.fold_left (fun f1 f2 -> CF.mkOr f1 f2 p)
                      (List.hd fs2) (List.tl fs2)
          in
          (hp0,hprel0, def)
  in
  let hp_groups = partition_hpdefs_by_hp_name hpdefs [] in
  (List.map combine_one_hpdef hp_groups)

let combine_hpdefs hpdefs=
  let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def in
  Debug.no_1 "combine_hpdefs" pr1 pr1
      (fun _ -> combine_hpdefs_x hpdefs) hpdefs

(************************************************************)
    (****************END SUBST HP DEF*****************)
(************************************************************)

let recover_dropped_args_x drop_hp_args hp_defs=
  let helper hrel=
    match hrel with
      | CF.HRel (hp, eargs, p ) -> (hp, eargs, p )
      | _ -> report_error no_pos "SAU.recover_droped_args_x 1"
  in
  let recover_def drops def=
    let hpdef,hprel,hp_body = def in
    let hp1, eargs1, p = helper hprel in
    let rec helper2 ldrops r_drop=
      match ldrops with
        | [] -> r_drop,def
        | (hp, eargs, dropped_eargs)::ds ->
          if CP.eq_spec_var hp hp1 then
            let args = List.concat (List.map CP.afv dropped_eargs) in
            let args1 = List.concat (List.map CP.afv eargs1) in
            let ss = List.combine args args1 in
            let new_eargs = CP.e_apply_subs_list ss eargs in
            (r_drop@ds, (hpdef, (CF.HRel (hp1,new_eargs,p)),hp_body))
          else helper2 ds (r_drop@[(hp, eargs, dropped_eargs)])
    in
    helper2 drops []
  in
  let rec helper1 drops hpdefs res=
    match hpdefs with
      | [] -> res
      | def::ls ->
          let drops1,def1 = recover_def drops def in
          helper1 drops1 ls (res@[def1])
  in
  helper1 drop_hp_args hp_defs []

let recover_dropped_args drop_hp_args hp_defs=
  let pr0 = pr_list !CP.print_exp in
  let pr1 = pr_list (pr_triple !CP.print_sv pr0 pr0) in
  let pr2 = pr_list_ln Cprinter.string_of_hp_rel_def in
  Debug.no_2 "recover_dropped_args" pr1 pr2 pr2
      (fun _ _ -> recover_dropped_args_x drop_hp_args hp_defs) drop_hp_args hp_defs

(************************************************************)
    (****************(*UNK HPS*)*****************)
(************************************************************)
let drop_non_node_unk_hps_x hp_defs ls_non_node_unk_hpargs =
  let drop_one_hpdef lnon_node_hp_names (rc, hf, f)=
    let f1,_ = CF.drop_hrel_f f lnon_node_hp_names in
    (rc, hf, f1)
  in
  let non_node_hp_names = List.map fst ls_non_node_unk_hpargs in
  List.map (drop_one_hpdef non_node_hp_names) hp_defs

let drop_non_node_unk_hps hp_defs non_node_unk_hps =
  let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr2 = pr_list_ln (pr_pair !CP.print_sv !CP.print_svl) in
  Debug.no_2 "drop_non_node_unk_hps" pr1 pr2 pr1
      (fun _ _ -> drop_non_node_unk_hps_x hp_defs non_node_unk_hps) hp_defs non_node_unk_hps

let transform_unk_hps_to_pure_x hp_defs unk_hp_frargs =
  (* let transform_hp_unk (hp,args)= *)
  (*   let hp_name = CP.name_of_spec_var hp in *)
  (*   let fr_args = List.map (fun sv -> CP.fresh_spec_var_prefix hp_name sv) args in *)
  (*   (hp,fr_args) *)
  (* in *)
  let rec lookup_hpdefs rem_hpdefs (hp0,args0)=
    match rem_hpdefs with
      | [] -> report_error no_pos "sau.lookup_hpdefs"
      | (_,hrel,f)::tl->
          let hp,args = CF.extract_HRel hrel in
          if CP.eq_spec_var hp hp0 then
            let ss = List.combine args args0 in
            CP.subst ss (CF.extract_pure f)
          else lookup_hpdefs tl (hp0,args0)
  in
  let subst_xpure lhpdefs f0=
    let process_p_helper p=
      let ps = CP.list_of_conjs p in
      let xp_ps,rem_ps = List.partition CP.is_xpure ps in
      let xp_hpargs = List.map CP.extract_xpure xp_ps in
      let xp_ps = (List.map (lookup_hpdefs lhpdefs) xp_hpargs) in
      let new_p =  CP.conj_of_list (rem_ps@xp_ps) no_pos in
      new_p
    in
    let rec helper f=
      match f with
        | CF.Base fb ->
            let new_p =  process_p_helper (MCP.pure_of_mix fb.CF.formula_base_pure) in
            CF.Base{fb with CF.formula_base_pure = (MCP.mix_of_pure new_p)}
        | CF.Exists fe ->
            let new_p =  process_p_helper (MCP.pure_of_mix fe.CF.formula_exists_pure) in
            CF.Exists{fe with CF.formula_exists_pure = (MCP.mix_of_pure new_p)}
        | CF.Or orf -> CF.Or {orf with
            CF.formula_or_f1 = helper orf.CF.formula_or_f1;
            CF.formula_or_f2 = helper orf.CF.formula_or_f2;
        }
    in
    helper f0
  in
  (*returns eqs/ss: mkEqexp/subst ss*)
  let look_up_get_eqs_ss args0 ls_unk_hpargs_fr (used_hp,used_args)=
    try
        let _,fr_args = List.find (fun (hp,_) -> CP.eq_spec_var hp used_hp) ls_unk_hpargs_fr in
        let ss = List.combine used_args fr_args in
        let rs1,rs2 = List.partition (fun (sv1,_) -> CP.mem_svl sv1 args0) ss in
        ([used_hp],rs1,rs2)
    with
      | Not_found -> ([],[],[])
  in
  let subst_pure_hp_unk args0 ls_unk_hpargs_fr f=
    let ls_used_hp_args = CF.get_HRels_f f in
    (*look up*)
    let r = List.map (look_up_get_eqs_ss args0 ls_unk_hpargs_fr) ls_used_hp_args in
    let ls_used_unk_hps,ls_eqs, ls_ss = split3 r in
    let used_unk_hps = List.concat ls_used_unk_hps in
    let eqs = List.concat ls_eqs in
    let ss = List.concat ls_ss in
    (*remove unkhps*)
    let f1,_ = CF.drop_hrel_f f used_unk_hps in
    (*subst*)
    let f2 = CF.subst ss f1 in
    (*add pure eqs*)
    let pos = CF.pos_of_formula f2 in
    let p_eqs = List.map (fun (sv1,sv2) -> CP.mkPtrEqn sv1 sv2 pos) eqs in
    let p = CP.conj_of_list p_eqs pos in
    let f3 = CF.mkAnd_pure f2 (MCP.mix_of_pure p) pos in
    f3
  in
  let subst_pure_hp_unk_hpdef ls_unk_hpargs_fr (rc, hf, def)=
    let _,args0 = CF.extract_HRel hf in
    let fs = CF.list_of_disjs def in
    let fs1 = List.map (subst_pure_hp_unk args0 ls_unk_hpargs_fr) fs in
    let def1 = CF.disj_of_list fs1 (CF.pos_of_formula def) in
    (rc, hf, def1)
  in
  let ls_unk_hpargs_fr = unk_hp_frargs in
  (* let ls_unk_hpargs_fr = List.map transform_hp_unk unk_hpargs in *)
  let new_hpdefs = List.map (subst_pure_hp_unk_hpdef ls_unk_hpargs_fr) hp_defs in
  (*subst XPURE*)
  List.map (fun (a,b,f) -> (a,b, subst_xpure new_hpdefs f)) new_hpdefs

let transform_unk_hps_to_pure hp_defs unk_hpargs =
  let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def in
  let pr2 = pr_list_ln (pr_pair !CP.print_sv !CP.print_svl) in
  Debug.no_2 "transform_unk_hps_to_pure" pr1 pr2 pr1
      (fun _ _ -> transform_unk_hps_to_pure_x hp_defs unk_hpargs) hp_defs unk_hpargs

(************************************************************)
    (****************(*END UNK HPS*)*****************)
(************************************************************)

let split_rhs_x prog cs=
  let simpily_lhs_rhs cs rhs_grp_hpargs hd_nodes hv_nodes eqs lhs_hpargs lhs rhs=
    let rhs_hps,rhs_keep_svl = List.split rhs_grp_hpargs in
    let n_lhs,n_rhs= keep_data_view_hrel_nodes_two_f prog lhs rhs hd_nodes hv_nodes eqs lhs_hpargs (List.concat rhs_keep_svl) rhs_hps in
    {cs with CF.hprel_lhs = n_lhs;
        CF.hprel_rhs = n_rhs
    }
  in
  let belong_one_node lsargs args0 args1=
    let args1 = CP.remove_dups_svl (args0@args1) in
    List.exists (fun args -> CP.diff_svl args1 args = []) lsargs
  in
  let rec partition_intersect_hpargs ls_node_args hpargs parts=
    match hpargs with
      | [] -> parts
      | (hp,args0)::tl->
           let part,remains= List.partition (fun (_,args1) ->
               CP.intersect_svl args0 args1 <> [] ||
           belong_one_node ls_node_args args0 args1) tl in
          partition_intersect_hpargs ls_node_args remains (parts@[[(hp,args0)]@part])
  in
  if List.length cs.CF.unk_hps > 0 then [cs]
  else
    let rhs_hpargs = CF.get_HRels_f cs.CF.hprel_rhs in
    match rhs_hpargs with
      | [] -> [cs]
      | [a] -> [cs]
      | _ ->
           let lhs = cs.CF.hprel_lhs in
           let rhs = cs.CF.hprel_rhs in
           let ldns,lvns,lhrels = CF.get_hp_rel_formula lhs in
           let rdns,rvns,_ = CF.get_hp_rel_formula rhs in
           let hns = ldns@rdns in
           let hvs = lvns@rvns in
          let grps = partition_intersect_hpargs (List.map (fun hd -> hd.CF.h_formula_data_arguments) hns) rhs_hpargs [] in
          if List.length grps <= 1 then [cs] else
            let lhs_hpargs = List.map (fun (hp, eargs,_) -> (hp,(List.fold_left List.append [] (List.map CP.afv eargs)))) lhrels in
            let ( _,mix_lf,_,_,_) = CF.split_components cs.CF.hprel_lhs in
            let (_,mix_rf,_,_,_) = CF.split_components cs.CF.hprel_rhs in
            let leqs = MCP.ptr_equations_without_null mix_lf in
            let reqs = MCP.ptr_equations_without_null mix_rf  in
            let eqs = leqs@reqs in
            List.map (fun rhs_hpargs -> simpily_lhs_rhs cs rhs_hpargs hns hvs eqs lhs_hpargs lhs rhs) grps

let split_rhs prog cs=
  let pr1 = Cprinter.string_of_hprel in
  Debug.no_1 "split_rhs" pr1 (pr_list_ln pr1)
      (fun _ -> split_rhs_x prog cs) cs

(*like tree recursion PLDI07*)
let simp_tree_one_hp_x unk_hps hp args fs=
  let is_rec_f f=
    let hps = CF.get_hp_rel_name_formula f in
    (CP.mem_svl hp hps)
  in
  let is_independ_f f =
    let hps = CF.get_hp_rel_name_formula f in
    let hps1 = CP.remove_dups_svl hps in
    (* DD.ninfo_pprint ("       hp: " ^ (!CP.print_sv hp)) no_pos; *)
    let rems = List.filter (fun hp1 -> not(CP.eq_spec_var hp hp1)
    && not (CP.mem_svl hp1 unk_hps) ) hps1 in
    (* DD.ninfo_pprint ("       rems: " ^ (!CP.print_svl rems)) no_pos; *)
    (rems = [])
  in
  let sort_fn (_,hds1) (_,hds2)=
    (List.length hds1)-(List.length hds2)
  in
  let rec check_exist f ls_f=
    match ls_f with
      | [] -> false
      | f1::tl_fs ->
           let r,_ (*map*) = CEQ.checkeq_formulas [] f f1 in
          if (* check_relaxeq_formula f f1 *) r then true else
            check_exist f tl_fs
  in
  let rec find_prec_point r (f,hds) rec_args done_fs done_hds=
    match hds with
      | [] -> f
      | hd::tl -> if CP.eq_spec_var hd.CF.h_formula_data_node r then
            let nf = CF.drop_hnodes_f f [r] in
            let n_roots = List.filter CP.is_node_typ hd.CF.h_formula_data_arguments in
            let rec_nrs,non_rec_nrs = List.partition (fun arg ->
                CP.mem_svl arg rec_args ) n_roots in
            if non_rec_nrs = [] then f else
              let nf1 = List.fold_left
                (fun f0 a -> drop_hrel_match_args f0 [a]) nf rec_nrs
              in
              let _ = DD.ninfo_pprint ("non_rec_nrs: " ^ (!CP.print_svl non_rec_nrs) ) no_pos in
              let nf2,a =
                match non_rec_nrs with
                  | [a] -> (find_prec_point a (nf1,done_hds@tl) rec_args done_fs
                      [],a)
                  | _ -> report_error no_pos "sau.find_prec_point"
              in
              let _ = DD.ninfo_pprint (" nf2: " ^ (Cprinter.prtt_string_of_formula nf2) ) no_pos in
              let ss2 = List.combine [a] args in
              let nf2a = CF.subst ss2 nf2 in
              if check_exist nf2a done_fs then
                let hf4 = mkHRel hp [a] no_pos in
                let nf3 = drop_data_hrel_except [r] rec_nrs f in
                CF.mkAnd_f_hf nf3 hf4 no_pos
              else f
          else
            find_prec_point r (f,tl) rec_args done_fs (done_hds@[hd])
  in
  let process_one_rec_f args (f,hsa) done_fs=
    let _ = DD.ninfo_pprint (" f: " ^ (Cprinter.prtt_string_of_formula f) ) no_pos in
    if check_exist f done_fs then [] else
      let hpargs = CF.get_HRels_f f in
      let rec_args = List.fold_left
        (fun args0 (hp1,args) -> if CP.eq_spec_var hp1 hp then (args0@args) else args0) [] hpargs in
      let newf=
        match args with
          | [a] -> find_prec_point a (f, hsa) rec_args done_fs []
          | _ -> report_error no_pos "sau. process_one_rec_f"
      in
      let _ = DD.ninfo_pprint (" newf: " ^ (Cprinter.prtt_string_of_formula newf) ) no_pos in
      if check_exist newf done_fs then done_fs else (done_fs@[newf])
  in
  (*find base case*)
   let _, dep_fs = List.partition is_independ_f fs in
  if (List.length dep_fs >= 1) || (List.length args > 1) then fs else
    let rec_fs,base_fs= List.partition is_rec_f fs in
    (*sort all based on length of heaps*)
    let rec_ls_hds = List.map (fun f -> (f,get_hdnodes f)) rec_fs in
    let rec_ls_hds1 = List.sort sort_fn rec_ls_hds in
  (*for each of remain: find the next root, if it exists in base case, subst to become recursive one*)
    let fs1 = List.fold_left (fun done_fs (f,hds) -> process_one_rec_f args (f,hds) done_fs) base_fs rec_ls_hds1 in
    (* let fs2 = norm_hnodes args fs1 in *) fs1
    (* Gen.BList.remove_dups_eq check_relaxeq_formula fs2 *)

let simp_tree_one_hp unk_hps hp args fs=
  let pr1 = pr_list_ln Cprinter.prtt_string_of_formula in
  Debug.no_3 "simp_tree_one_hp" !CP.print_sv !CP.print_svl pr1 pr1
      (fun _ _ _ -> simp_tree_one_hp_x unk_hps hp args fs) hp args fs

let simp_tree_x unk_hps hpdefs=
  let process_one_hp (a,hprel,f)=
    let hp,args = CF.extract_HRel hprel in
    let fs = CF.list_of_disjs f in
    let nfs = simp_tree_one_hp unk_hps hp args fs in
    let nf = List.fold_left (fun f1 f2 -> CF.mkOr f1 f2 (CF.pos_of_formula f))
      (List.hd nfs) (List.tl nfs) in
    (a,hprel, nf)
  in
  List.map process_one_hp hpdefs

let simp_tree unk_hps hpdefs=
  let pr1 = pr_list_ln Cprinter.string_of_hp_rel_def_short in
  Debug.no_1 "simp_tree" pr1 pr1
      (fun _ -> simp_tree_x unk_hps hpdefs) hpdefs

(************************************************************)
    (****************(*currently we dont use*)*****************)
(************************************************************)
(*currently we dont use*)
let ann_unk_svl prog par_defs=
  (*partition the set by hp_name*)
  let rec partition_pdefs_by_hp_name pdefs parts=
    match pdefs with
      | [] -> parts
      | (a1,a2,a3,a4,a5,a6)::xs ->
          let part,remains= List.partition (fun (hp_name,_,_,_,_,_) -> CP.eq_spec_var a1 hp_name) xs in
          partition_pdefs_by_hp_name remains (parts@[[(a1,a2,a3,a4,a5,a6)]@part])
  in
  let add_unk_hp_f unk_hf opdef=
    match opdef with
      | None -> None
      | Some f ->
          let p = CF.pos_of_formula f in
          Some (CF.mkAnd_f_hf f unk_hf p)
  in
  let add_unk_hp_pdef unk_hf0 unk_args0 (hp,args,unk_args,cond,olhs,orhs)=
    let ss = List.combine unk_args0 unk_args in
    let unk_hf = CF.h_subst ss unk_hf0 in
    (hp,args,unk_args,cond,add_unk_hp_f unk_hf olhs, add_unk_hp_f unk_hf orhs)
  in
  let process_one_group par_defs=
    let (hp,args0,unk_args0,cond0,olhs0,orhs0) = List.hd par_defs in
    let _ = Debug.ninfo_pprint ("     partial unk hp: " ^ (!CP.print_sv hp)) no_pos in
    let unk_hf, unk_hps = add_raw_hp_rel_x prog unk_args0 no_pos in
    let new_par_def0= (hp,args0,unk_args0,cond0,add_unk_hp_f unk_hf olhs0, add_unk_hp_f unk_hf orhs0) in
    let tl_par_defs = List.map (add_unk_hp_pdef unk_hf unk_args0) (List.tl par_defs) in
    ((unk_hps,unk_args0), new_par_def0::tl_par_defs)
  in
  let par_unk_defs,rems = List.partition (fun (_,_,unk_slv,_,_,_) -> unk_slv <> []) par_defs in
  let parunk_groups = partition_pdefs_by_hp_name par_unk_defs [] in
  let r = List.map process_one_group parunk_groups in
  let new_hpargs,new_unk_pardefs = List.split r in
  (new_hpargs, (List.concat new_unk_pardefs)@rems)

(*END currently we dont use*)
(************************************************************)
    (****************(*ENDcurrently we dont use*)*****************)
(************************************************************)
