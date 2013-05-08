open Globals
open Gen.Basic

module CF = Cformula
module CP = Cpure
module MCP = Mcpure
module S = Solver
module TP = Tpdispatcher

let print_list_formula ps = String.concat "\n"
  (List.map !CP.print_formula ps)

let rec spec_var_is_mem sv l=
    match l with
      | [] -> false
      | sv2::vs -> if (CP.name_of_spec_var sv) = (CP.name_of_spec_var sv2) then
            true
          else spec_var_is_mem sv vs

let rec list_spec_var_intersect l1 l2=
  match l1 with
    | [] -> false
    | v::vs -> if spec_var_is_mem v l2 then true
        else list_spec_var_intersect vs l2

let rec list_spec_var_subset_x l1 l2=
  match l1 with
    | [] -> true
    | v::vs -> if spec_var_is_mem v l2 then list_spec_var_subset_x vs l2
        else false

and list_spec_var_subset l1 l2 =
  let pr1 = !CP. print_svl in
  Debug.no_2 "list_spec_var_subset" pr1 pr1 string_of_bool
      (fun _ _ -> list_spec_var_subset_x l1 l2) l1 l2

let is_eq_pointers p svs=
  match p with
    | CP.BForm ((pf,_), _,_)->
        (
            match pf with
              | CP.Eq (CP.Var (sv1,_), CP.Var (sv2,_),_) ->
                  if list_spec_var_intersect [sv1;sv2] svs then
                    Gen.BList.remove_dups_eq CP.eq_spec_var (svs@[sv1;sv2])
                  else svs
              | _ -> svs
        )
    | _ -> svs

let rec select_eq_vars ps vs=
  let rec select_eq_vars_helper one_vs ps remains=
    match ps with
      | [] -> (remains, one_vs)
      | p::pss ->
          (* for each p in ps. *)
          (*if (var p) in one_vs then*)
          let new_one_vs = is_eq_pointers p one_vs in
          if (List.length new_one_vs) = (List.length one_vs) then
            (*add p into remains*)
            select_eq_vars_helper one_vs pss (p::remains)
          else
            (* add (var p) into one_vs*)
            select_eq_vars_helper new_one_vs pss remains
  in
  let rm,new_vs = select_eq_vars_helper vs ps [] in
  if (List.length new_vs) = (List.length vs) then
    rm,new_vs
  else
    select_eq_vars rm new_vs

(*
call slice_p with  remain_ps=[] and c_slice=[]
*)
let rec slice_p ps vs remain_ps c_slice=
 match ps with
   | [] -> (remain_ps, c_slice)
   | p::ss ->
       (*
         check var(p) in vs then
            add p into slices
           recursive call
         else add p into remain, recursive call
       *)
       let svs = CP.fv p in
        (* let _ = print_endline ("vars of p:" ^ (!CP. print_svl svs)) in *)
       if (list_spec_var_subset svs vs) then
         slice_p ss vs remain_ps (c_slice@[p])
       else slice_p ss vs (remain_ps@[p]) c_slice

let h_ptos (h: CF.h_formula)=  S.h_ptos h
(*
  v is pointer: add v!=null
  v1,v2 point-to: v1!=v2
*)
let check_sat_base_f prog fb= S.check_sat_base_f prog fb
  
  (* let ptos =  h_ptos h in *)
  (* (\*null*\) *)
  (* let null_p= CP.join_conjunctions (List.map (fun v -> CP.mkNeqNull v no_pos) ptos) in *)
  (* let dis_ps = *)
  (*   match (CP.mklsPtrNeqEqn ptos no_pos) with *)
  (*     | None -> [] *)
  (*     | Some p -> [p] *)
  (* in *)
  (* let r = ref (-9999) in *)
  (* let p = CP.join_conjunctions ([p] @ [null_p] @ dis_ps) in *)
  (* let _ = print_endline ("pure: " ^ (!CP.print_formula p)) in *)
  (* TP.is_sat_sub_no p r *)

(*to do:
- check sat, elim dis, dangling pointers
- cluster: constraints among multiple nodes
*)
let rec neg_formula prog f=
  let tmp,ll = norm_disj_formula prog f [] in
  if (List.length ll) = 0 then
     let _ = print_endline "closed tree" in
     CF.Base {tmp with  CF.formula_base_heap = CF.HEmp;
     CF.formula_base_pure = MCP.mkMTrue no_pos}
  else
     let branches = combine_branches tmp ll in
     combine_disj_neg branches

and norm_disj_formula prog f branches=
  match f with
    | CF.Base fb ->
        let h = fb.CF.formula_base_heap in
        let p = MCP.pure_of_mix fb.CF.formula_base_pure in
        (*check sat*)
        if (check_sat_base_f prog fb = 1) then
        (*rm_p: residue constraints after localization*)
          let (rm_p, hns) = norm_conj h (CP.list_of_conjs p) in
        (************************)
        (*pure neg*)
          let np_hnodes = List.flatten (List.map neg_p_hnode hns) in
          (*pure neg global constraints*)
          let pf =
            if (List.length rm_p) = 0 then []
            else
              let nglobal = neg_pure rm_p in
              [(CF.HEmp, nglobal)]
          in
        (************************)
          (*get neg * first*)
          (*get equivalent sets*)
          let equ_svs = List.map (fun (_,(svs,_)) -> svs ) hns in
          let eq_star_pointers = CP.mklsPtrEqEqn equ_svs no_pos in
          let eq_star_f = List.map (fun p -> (CF.HEmp, p)) eq_star_pointers in
          (*heap neg needs dangling node support*)
          let nh_hnodes = List.flatten (List.map neg_h_hnode hns) in
          (*disjunct of three above*)
          (fb,branches @ [(np_hnodes @ pf @ nh_hnodes @ eq_star_f)])
        else
          (fb,[])
    | CF.Or { CF.formula_or_f1 = f1;
              CF.formula_or_f2 =f2;
              CF.formula_or_pos =p } ->
        let tmp1, branches1 = norm_disj_formula prog f1 branches in
        let _ , branches2 = norm_disj_formula prog f2 branches1 in
        (tmp1, branches2)
    | CF.Exists e -> let f = CF.normalize_combine_heap 
                       (CF.formula_of_mix_formula e.CF.formula_exists_pure no_pos) e.CF.formula_exists_heap
                     in  norm_disj_formula prog f branches
(* failwith ("neg.neg_formula: not handle exist formula") *)

and construct_branch branches cur_chain res=
  let pr1 = pr_pair Cprinter.string_of_h_formula !CP.print_formula in
  let pr_br = pr_list pr1 in
  let pr2 = pr_list pr_br in
 Debug.no_1 "construct_branch" pr2 pr2
      (fun _ -> construct_branch_x branches cur_chain res) branches

and construct_branch_x branches cur_chain res=
  (* let helper1 c ll= *)
  (*   List.map (fun l -> l@[c]) ll *)
  (* in *)
  (* let helper2 br ll= *)
  (*  List.concat (List.map (fun c -> helper1 c ll) br) *)
  (* in *)
  (* match branches with *)
  (*   | [] -> [] *)
  (*   | [br] -> [br] *)
  (*   | br::brs -> *)
  (*       let ll0 = List.map (fun c -> [c]) br in *)
  (*       List.fold_right helper2 brs ll0 *)
  (*both code are OK*)
  match branches with
    | [] -> (res @[cur_chain])
    | b::bs ->
        ( match b with
          | [] -> res
          | c::cs -> let cur_res = construct_branch bs (cur_chain@[c]) res in
                     construct_branch (cs::bs) cur_chain cur_res
        )

and combine_branches tmp ll= (*list of negation on branches: (neg_p, neg) *)
  (* let neg_p_branches, neg_h_branches = List.split ll in *)
  (*********neg_p**********)
  let disj_neg_p_combined = construct_branch ll [] [] in
  (*construct hnode*)
  let ll1 = List.map List.split disj_neg_p_combined in
  let p_disjs = List.concat (List.map (combine_branch tmp) ll1) in
  (********neg_h***************)
   (* let disj_neg_h_combined = construct_branch neg_h_branches [] [] in *)
   (* (\*construct hnode*\) *)
   (* let ll2 = List.map List.split disj_neg_h_combined in *)
   (* let h_disjs = List.concat (List.map (combine_branch tmp) ll2) in *)
   (* (p_disjs @ h_disjs) *)
  p_disjs

(*
each alias has one node : (CF.h_formula_view list)
*)
and neg_p_hnode (vn,(eq_svs,slice_p))=
  let npure = neg_pure slice_p in
  let mk_hnode sv=
    (CF.DataNode {vn with CF.h_formula_data_node = sv}, npure)
  in
  List.map mk_hnode eq_svs

and neg_h_hnode (vn,(eq_svs,_))=
  (*dangling pointers*)
  let mk_dangNode sv=
    (CF.DangNode {CF.h_formula_dang_node = sv;
                  CF.h_formula_dang_name = vn.CF.h_formula_data_name;
                 CF.h_formula_dang_pos = vn.CF.h_formula_data_pos},
    CP.mkTrue no_pos)
  in
  (*or null pointers*)
  let mk_nullNode sv=
    (CF.HEmp, CP.mkNull sv no_pos)
  in
  (List.map mk_dangNode eq_svs)@(List.map mk_nullNode eq_svs)

and neg_pure (ps:CP.formula list)=
  let neg_p_conjs = List.map CP.mkNot_s ps in
  CP.join_disjunctions neg_p_conjs

(*
slicing p into node: (n1 /\ p1)*(n2/\p2).../\pm : (CF.Base list)
*)
and norm_conj (h: CF.h_formula) (conjs:CP.formula list)=
  match h with
    | CF.DataNode vn ->
        let rm_p, hnode= norm_one_hnode vn conjs in
        (rm_p, [(vn,hnode)])
    | CF.Star { CF.h_formula_star_h1 = h1;
                CF.h_formula_star_h2 = h2
              } ->
        let rm_p1, hnodes1 = norm_conj h1 conjs in
        let rm_p, hnodes2 = norm_conj h2 rm_p1 in
        (rm_p, hnodes1@hnodes2)
    | CF.HEmp ->  (conjs,[])
    | _ -> failwith ("neg.norm_conj: not handled yet")

and norm_one_hnode_x (vn: CF.h_formula_data) (conjs: CP.formula list)=
  let vs = vn.CF.h_formula_data_arguments in
  (* let _ = print_endline ("args" ^ (!CP. print_svl vs)) in *)
  (* let _ = print_endline ("data node" ^ *)
  (*                               (!CP. print_svl [vn.CF.h_formula_data_node])) in *)
         (*slice p into vn*)
         (*equiv class*)
  let rm_p,eq_svs = select_eq_vars conjs [vn.CF.h_formula_data_node] in
  (* let _ = print_endline ("eq vars" ^ (!CP. print_svl eq_svs)) in *)
  let rm_p, slice_p = slice_p rm_p vs [] [] in
  (* let _ = print_endline ("slice: " ^ (print_list_formula slice_p)) in *)
  (* let _ = print_endline ("rm: " ^ (print_list_formula rm_p)) in *)
  (rm_p,(eq_svs,slice_p))


and norm_one_hnode (vn: CF.h_formula_data) (conjs: CP.formula list)=
  let pr1 = fun x -> !CP. print_svl [x.CF.h_formula_data_node] in
  let pr2 = fun (rm, (esvs, slice)) ->
      ("rm: " ^ (print_list_formula rm)) ^
      ("\neq vars" ^ (!CP. print_svl esvs))^
      ("\nslice: " ^ (print_list_formula slice)) in
  Debug.no_1 "norm_one_hnode" pr1 pr2
      (fun _  -> norm_one_hnode_x vn conjs) vn

and combine_branch tmp (p_hnodes,p_pures)=
  let h=
    match p_hnodes with
      | [] -> CF.HEmp
      | [p] -> p
      | p::ps -> combine_spatial_conj ps p
  in
  (*todo: megre two node if same var*)
  (*todo: sub corresponding pure constraints*)
  let p= CP.join_conjunctions p_pures  in
  let r = ref (-9999) in
  if (TP.is_sat_sub_no p r) then
    [ CF.Base {tmp with CF.formula_base_heap = h;
     CF.formula_base_pure = (MCP.mix_of_pure p)}]
  else []

and combine_spatial_conj hnodes h=
   match hnodes with
    | [] -> h
    | h0::hs ->
        ( match h0 with
          | CF.HEmp -> combine_spatial_conj hs h
          | _ -> let h1 = CF.Star { CF.h_formula_star_h1 = h;
                                    CF.h_formula_star_h2  = h0;
                                    CF.h_formula_star_pos = no_pos } in
                 combine_spatial_conj hs h1
        )

and combine_disj_neg bfs=
  let mkOr_no_pos f1 f2 = CF.mkOr f1 f2 no_pos in
  List.fold_left mkOr_no_pos (List.hd bfs) (List.tl bfs)



(********************)
let rec check_sat_x prog (f:CF.formula): int=
  S.check_sat prog f

let check_sat prog (f:CF.formula): int=
  let pr =  Cprinter.string_of_formula in
  Debug.no_1 "check_sat" pr string_of_int (fun f -> check_sat_x prog f ) f


let rec check_sat_failesc_ctx proc ctx=
 ""

let check_sat_list_failesc_ctx proc ctx=
 ""
