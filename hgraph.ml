#include "xdebug.cppo"
open VarGen
(*this module supports graph on physical heap*)

open Globals
open Gen
open Exc.GTable
 (* open Perm *)
open Label_only
open Label

module C = Cast
module Err = Error
module CP = Cpure
module MCP = Mcpure
module CF = Cformula

let loc_number = ref (0:int)
let heap_size = ref (50:int)

let hgraph_grp_min_size_unsat = 3

let hgraph_grp_min_size_entail = 2

let reset_fress_addr () =
  loc_number :=0

let set_heap_size n =
  heap_size := n+1

let fresh_addr () =
  loc_number := !loc_number + 1;
  !loc_number


let matrix ls1 ls2=
  List.fold_left (fun ls id2 -> ls@(List.map (fun id1 -> (id1,id2)) ls1)) [] ls2

let remove_dups_int l= Gen.BList.remove_dups_eq (=) l
let intersect_int l1 l2= Gen.BList.intersect_eq (=) l1 l2
let diff_int l1 l2= Gen.BList.difference_eq (=) l1 l2
let mem_int id ls= List.mem id ls
(***************************************************************)
(***************************************************************)
(*vertex*)
type heap_vertex = {
  hv_id: int; (*0 is null*)
  hv_kind: bool; (*true: singleton; false: any*)
  hv_lbl: CP.spec_var list;
}

type heap_edge = {
    he_kind : bool; (*true: point-to, false: other*)
    he_b_id: int;
    he_e_id: int;
}

type adj = {
    a_root: int;
    a_nexts: int list;
}

type heap_graph = {
    hg_sccs : (int*((int * (int list) * (int list)) list)) list;
    hg_vertexs: heap_vertex list;
    hg_edges: heap_edge list;
    hg_adjg2: adj list;
    hg_adj1: adj list;
    hg_adj0: adj list;
    hg_non_tough_edges: (int * int) list;
}

let mk_hgraph sccs hvs hes adjg2 adj1 adj0 nt_edges= {
    hg_sccs = sccs;
    hg_vertexs = hvs;
    hg_edges = hes;
    hg_adjg2 = adjg2;
    hg_adj1 = adj1;
    hg_adj0 = adj0;
    hg_non_tough_edges = nt_edges;
}

let mk_empty_hgraph () =  mk_hgraph [] [] [] [] [] [] []

(******************printer********************************)
let print_hv hv=
  (string_of_int hv.hv_id) ^ ": " ^ (!CP.print_svl hv.hv_lbl)

let print_he he=
  (if he.he_kind then "(r) " else "b") ^ (string_of_int he.he_b_id) ^ "-->"^(string_of_int he.he_e_id)

let print_adj a=
  let pr1 = pr_list string_of_int in
  (string_of_int a.a_root) ^ "-->"^(pr1 a.a_nexts)

let print_hgraph g=
  let pr0 = pr_list string_of_int in
  let pr1 = pr_list_ln (pr_pair string_of_int (pr_list (pr_triple string_of_int pr0 pr0) )) in
  let pr2 = pr_list print_adj in
  let pr3 = pr_list print_hv in
  let pr4 = pr_list (pr_pair string_of_int string_of_int) in
  let string_sscs = "sscs:" ^ (pr1 g.hg_sccs) in
  let string_hvs = "\nvertexs:" ^ (pr3 g.hg_vertexs) in
  let string_hes = "\nedges:" ^ ((pr_list print_he) g.hg_edges) in
  let string_adjg2 = "\nadj >= 2:" ^ (pr2 g.hg_adjg2) in
  let string_adj1 = "\nadj = 1:" ^ (pr2 g.hg_adj1) in
  let string_adj0 = "\nadj >= 0:" ^ (pr2 g.hg_adj0) in
  let string_non_tough_edges = "\nnt-edges:" ^ (pr4 g.hg_non_tough_edges) in
  string_sscs ^ string_hvs ^ string_hes ^ string_adjg2 ^ string_adj1 ^ string_adj0 ^ string_non_tough_edges

(*****************end*printer********************************)
 let cmp_edge e1 e2 = e1.he_b_id - e2.he_b_id

let rec look_up_vertex sv ls_vertexes=
  match ls_vertexes with
    | v::rest -> if CP.mem_svl sv v.hv_lbl then v.hv_id else
        look_up_vertex sv rest
    | [] -> raise Not_found

 let rec look_up_edge edges b_id e_id=
   match edges with
     | e::rest -> if e.he_b_id = b_id && e.he_e_id = e_id then e
       else look_up_edge rest b_id e_id
     | [] -> raise Not_found

 let rec look_up_next_edges edges b_id=
   List.filter (fun e-> e.he_b_id = b_id) edges

let rec look_up_coming_edges edges e_id=
   List.filter (fun e-> e.he_e_id = e_id) edges

let rec look_up_adj root_id ls_adj=
  match ls_adj with
    | [] -> []
    | a::rest -> if a.a_root = root_id then a.a_nexts else
        look_up_adj root_id rest

let look_up_children v hg_adjg2 hg_adj1 adj0=
  if List.exists (fun a -> a.a_root = v) adj0 then [] else
    begin
      try
        let children = List.find (fun a -> a.a_root = v) (hg_adj1@hg_adjg2) in
        children.a_nexts
      with _ -> []
    end

let look_up_end_of_edges_x edges v=
  List.filter (fun e -> e.he_e_id = v)  edges

let look_up_end_of_edges edges v=
  let pr1 = pr_list print_he in
  Debug.no_2 "look_up_end_of_edges" pr1 string_of_int pr1
      (fun _ _ -> look_up_end_of_edges_x edges v)
      edges v

let set_pto_edges_x vertexs eds diff_pair=
  let cmp_pair (id1, _) (id2,_) = id1 -id2 in
  let rec var2add vs sv=
    match vs with
      | []-> raise Not_found
      | v::rest -> if CP.mem_svl sv v.hv_lbl then v.hv_id
        else var2add rest sv
  in
  let rec look_up ptos id1 id2 rest_ptos=
    match ptos with
      | [] -> false,rest_ptos
      | (id3,id4)::rest ->
            if id1= id3 && id2 = id4 then (true, rest_ptos@rest) else
              look_up rest id1 id2 (rest_ptos@[(id3,id4)])
  in
  let ptos = List.map (fun (sv1,sv2) -> (var2add vertexs sv1, var2add vertexs sv2)) diff_pair in
  let () = Debug.ninfo_hprint (add_str "ptos" (pr_list (pr_pair string_of_int string_of_int))) ptos no_pos in
  let sort_eds = List.sort cmp_edge eds in
  let sort_ptos = List.sort cmp_pair ptos in
  let sort_eds2,_ = List.fold_left (fun (r,ptos) e ->
      let b, rest_ptos = look_up ptos e.he_b_id e.he_e_id [] in
      let () = Debug.ninfo_hprint (add_str "e" print_he) e no_pos in
      let () = Debug.ninfo_hprint (add_str "b" string_of_bool) b no_pos in
      let ne = if b then {e with he_kind = true} else e in
      (r@[ne],rest_ptos)
  ) ([],sort_ptos) sort_eds in
  sort_eds2,sort_ptos

let set_pto_edges vertexs eds diff_pair=
  let pr1 = pr_list print_hv in
  let pr2 = pr_list print_he in
  let pr3 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
  let pr4 = pr_list (pr_pair string_of_int string_of_int) in
  Debug.no_3 "set_pto_edges" pr1 pr2 pr3 (pr_pair pr2 pr4)
      (fun _ _ _ -> set_pto_edges_x vertexs eds diff_pair)
      vertexs eds diff_pair

(*******************************************************)
(*AUX methods - non graph*)
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

let subst_one_id subst id=
  let rec helper rem_subs cur_id=
    match rem_subs with
      | [] -> cur_id
      | (id1,id2)::rest -> if id2=cur_id then helper rest id1 else helper rest cur_id
  in
  helper subst id

let subst_rnext subst (r,nexts)=
  let n_r = subst_one_id subst r in
  let new_nexts = List.map (subst_one_id subst) nexts in
  let new_nexts1 =List.filter (fun id1 -> not(n_r = id1)) new_nexts in
  (*remove (id1,id2) (id2,id3) (id3,id1)*)
  let new_rnexts = if new_nexts1 = [] then [] else [(n_r, new_nexts1)] in
  (new_rnexts, subst@(List.map (fun id1 -> (n_r,id1)) new_nexts1))

let find_close_chains_x ls_rnexts=
  let rec comb_dups ls1 done_ls=
    match ls1 with
      | [] -> done_ls
      | (r,nexts)::rest -> let same,rem = List.partition (fun (r1,_) -> r1=r) rest in
        let comb_nexts = remove_dups_int (List.fold_left (fun ls (_,nexts1) -> ls@nexts1) nexts same) in
        comb_dups rem (done_ls@[(r,comb_nexts)])
  in
  let rec loop_helper ls subst done_res=
    match ls with
      | [] -> done_res
      | (r,nexts)::rest ->
            let new_rnexts,new_subst = subst_rnext subst (r,nexts) in
            loop_helper rest new_subst (done_res@new_rnexts)
  in
  (*head of ls_nexts is unique: ((1,[2;5]); (1,[3;4;5])) ==> (1,[2;3;4;5])*)
  let ls_rnexts1 = comb_dups ls_rnexts [] in
  loop_helper ls_rnexts1 [] []

let find_close_chains ls_rnexts=
  let pr1 = string_of_int in
  let pr2 = pr_list pr1 in
  let pr3 = pr_list (pr_pair pr1 pr2) in
  Debug.no_1 "find_close_chains" pr3 pr3
      (fun _ -> find_close_chains_x ls_rnexts) ls_rnexts

let classify_merge_throw_chains_x ls_rnexts=
  let collect (res_roots, res_nexts) (r,nexts)= (res_roots@[r], res_nexts@nexts) in
  (*[(4,[6,1]),(2,[6,1,4])] --> [(2,[6,1,4])]*)
  let rec find_close rem_rnexts parts=
    match rem_rnexts with
      | [] -> parts
      | (r,nexts)::rest ->
            let same,rems = List.partition (fun (r1,_) -> List.mem r1 nexts) (parts@rest) in
            if same = [] then find_close rest (parts@[(r,nexts)]) else
            let _,rnexts= List.fold_left collect ([],nexts) same in
            find_close (rems@[(r,remove_dups_int (List.filter (fun id -> not (id = r)) rnexts))]) []
  in
  let rec find_close_merge ls_merge_throw parts=
    match ls_merge_throw with
      | [] -> parts
      | (ls_merge, ls_throw)::rest ->
            let same_merges,rems = List.partition (fun (ls_merge1,_) -> intersect_int ls_merge ls_merge1 <> []) rest in
            let ls_total_merge,ls_total_throw = List.fold_left (
                fun (ls1,ls2) (ls_merge1, ls_throw1) ->
                    (ls1@ls_merge1),ls2@ls_throw1
            ) (ls_merge, ls_throw) same_merges in
            find_close_merge rems (parts@[(remove_dups_int ls_total_merge,ls_total_throw)])
  in
  let rec fix_close rem_rnexts=
    let new_rem_rnexts = find_close rem_rnexts [] in
    if List.length new_rem_rnexts = List.length rem_rnexts then new_rem_rnexts else
      fix_close new_rem_rnexts
  in
  let rec classify_helper rem_rnexts parts=
    match rem_rnexts with
      | [] -> parts
      | (r,nexts)::rest ->
            let same,rems = List.partition (fun (_,nexts1) -> intersect_int nexts nexts1 <> []) rest in
            let roots,rnexts= List.fold_left collect ([r],nexts) same in
            classify_helper rems (parts@[(remove_dups_int roots, remove_dups_int rnexts)])
  in
  let ls_rnexts1 = fix_close ls_rnexts in
  let merge_throw, normal = List.fold_left (fun (ls1,ls2) (roots,rnexts) ->
     if List.length roots > 1 then (ls1@[(roots,rnexts)],ls2) else
       (ls1,ls2@[(List.hd roots,rnexts)])
  ) ([],[]) (classify_helper ls_rnexts1 []) in
  (find_close_merge merge_throw [], normal)

let classify_merge_throw_chains ls_rnexts=
  let pr1 = string_of_int in
  let pr2 = pr_list pr1 in
  let pr3 = pr_list (pr_pair pr1 pr2) in
  let pr4 = pr_list (pr_pair pr2 pr2) in
  Debug.no_1 "classify_merge_throw_chains" pr3 (pr_pair pr4 pr3)
      (fun _ -> classify_merge_throw_chains_x ls_rnexts) ls_rnexts
(***************************************************)
let add_hv hv_kind hv_lbl=
  {
      hv_id = fresh_addr ();
      hv_kind = hv_kind;
      hv_lbl = hv_lbl;
  }

let get_hv_lbl hv= hv.hv_lbl

let add_hv_lbs hv svl = {hv with hv_lbl = hv.hv_lbl@svl}

(*combine hv2 lbl into hv1 lbl*)
let combine_hv_lbl hv1 hv2 = {hv1 with hv_lbl = hv1.hv_lbl@hv2.hv_lbl}

let remove_hv vertexs id=
  let rec helper rems done_vertexs=
    match rems with
      | hv::rest -> if hv.hv_id = id then (hv, done_vertexs@rest) else
          helper rest (done_vertexs@[hv])
      | [] -> report_error no_pos "hgraph.remove_hv"
  in
  helper vertexs []

let batch_remove_hvs vertexs ids=
  let rm_vs,rems = List.partition (fun v -> List.mem v.hv_id ids) vertexs in
  rm_vs,rems

let update_hv_lbl_x vertexs id new_lbl=
  let rec helper rems done_vertexs=
    match rems with
      | hv::rest -> if hv.hv_id = id then
          let new_hv = add_hv_lbs hv new_lbl in
          (done_vertexs@(new_hv::rest))
        else
          helper rest (done_vertexs@[hv])
      | [] -> report_error no_pos "hgraph.update_hv_lbl"
  in
  helper vertexs []

let update_hv_lbl vertexs id new_lbl=
  let pr1 = pr_list print_hv in
  Debug.no_3 "update_hv_lbl" pr1 string_of_int !CP.print_svl pr1
      (fun _ _ _ -> update_hv_lbl_x vertexs id new_lbl)
      vertexs id new_lbl

let rename_hv_id hv new_id = {hv with hv_id = new_id}

(*edge*)
let add_he he_kind id1 id2=
  {
      he_kind = he_kind;
      he_b_id = id1;
      he_e_id = id2;
  }

let from_var_to_hv_x vertexs sv=
  let rec helper rems=
    match rems with
      | hv::rest -> if CP.mem_svl sv hv.hv_lbl then hv.hv_id else
          helper rest
      | [] -> report_error no_pos "HGRAPH.from_var_to_hv"
  in
  helper vertexs

let from_var_to_hv vertexs sv=
  let pr1 = pr_list print_hv in
  Debug.no_2 "from_var_to_hv" pr1 !CP.print_sv string_of_int
      (fun _ _ -> from_var_to_hv_x vertexs sv) vertexs sv

let split_adj adjs r_id=
  (* let () = Debug.info_pprint (" r_id: "^ (string_of_int r_id)) no_pos in *)
  let rec helper ls done_adjs=
    match ls with
      | a::rest -> if a.a_root = r_id then
          a,(done_adjs@rest)
        else helper rest (done_adjs@[a])
      | [] -> report_error no_pos "hgraph.split_adj"
  in
  helper adjs []

let batch_split_adjs adjs r_ids=
  List.partition (fun adj -> List.mem adj.a_root r_ids) adjs

let drop_get_nexts_adj adjs r_id=
  let rec helper ls done_adjs=
    match ls with
      | a::rest -> if a.a_root = r_id then
          a.a_nexts,(done_adjs@rest)
        else helper rest (done_adjs@[a])
      | [] -> [],done_adjs
  in
  helper adjs []

let drop_get_nexts_adjs adjs r_ids=
  let rec process_one_helper rem_roots res_adjs res_nexts=
    match rem_roots with
      | [] -> (res_nexts,res_adjs)
      | r::rest -> let adj2_nexts, rem_adjs =  drop_get_nexts_adj res_adjs r in
        process_one_helper rest rem_adjs (res_nexts@adj2_nexts)
  in
  process_one_helper r_ids adjs []

let drop_adjs adjs r_ids=
  let rems = List.filter (fun a -> not(List.mem a.a_root r_ids)) adjs in
  rems

(*END*)
(************************************************************************)
            (*******************NORMALIZE******************)
(************************************************************************)
(************************************************************************)
            (*******************INIT GRAPH******************)
(************************************************************************)
let add_vertex_x sv must_eqs=
  let svl1 = find_close [sv] must_eqs in
  let new_hv = add_hv false svl1 in
  (new_hv, List.map (fun sv -> (sv, new_hv.hv_id)) svl1)

let add_vertex sv ls_must_eqs=
  let pr1 =pr_list (pr_pair !CP.print_sv !CP.print_sv) in
  let pr2 = pr_list (pr_pair !CP.print_sv string_of_int) in
  Debug.no_2 "add_vertex" !CP.print_sv pr1 (pr_pair print_hv pr2)
      (fun _ _ -> add_vertex_x sv ls_must_eqs) sv ls_must_eqs

let build_init_ls_vertex_x edges must_eqs=
  let svl1,svl2 = List.split edges in
  (*for debugging*)
  (* let sort_fn (CP.SpecVar (_,sv1,_)) (CP.SpecVar (_,sv2,_)) = String.compare sv1 sv2 in *)
  let sorted_ls = (* List.sort sort_fn *) (CP.remove_dups_svl (svl1@svl2)) in
  (*end*)
  List.fold_left (fun (ls1,ls2) sv ->
      let new_hv,new_maps = add_vertex sv must_eqs in
      (ls1@[new_hv], ls2@new_maps)
  )
      ([],[]) sorted_ls

let build_init_ls_vertex edges must_eqs=
  let pr1 =pr_list (pr_pair !CP.print_sv !CP.print_sv) in
  let pr2 = pr_list (pr_pair !CP.print_sv string_of_int) in
  Debug.no_2 " build_init_ls_vertex" pr1 pr1 (pr_pair (pr_list print_hv) pr2)
      (fun _ _ -> build_init_ls_vertex_x edges must_eqs) edges must_eqs

(*each may_eq is an edge*)
let build_init_edges_x ls_may_eqs ini_maps=
  let process_one_edge (sv1,sv2)=
    try
      let id1 = List.assoc sv1 ini_maps in
      let id2 = List.assoc sv2 ini_maps in
      add_he false id1 id2
    with Not_found ->
        report_error no_pos "HGRAPH.build_init_graph: all vars should belong to one address "
  in
  List.map process_one_edge ls_may_eqs

let build_init_edges ls_may_eqs ini_maps=
  let pr1 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
  let pr2 = pr_list (pr_pair !CP.print_sv string_of_int) in
  let pr3 = pr_list print_he in
  Debug.no_2 "build_init_edges" pr1 pr2 pr3
      (fun _ _ -> build_init_edges_x ls_may_eqs ini_maps) ls_may_eqs ini_maps

let build_ls_adj_x edges =
  let rec part_edge rem_edges res_g1 res1 res0=
    match rem_edges with
      | [] -> (res_g1,res1, res0)
      | he1::rest -> begin
            let part,rem = List.partition (fun he -> he.he_b_id=he1.he_b_id ) rest in
            let ls_nexts = he1.he_e_id::(List.map (fun he -> he.he_e_id) part) in
            let new_adj = {a_root = he1.he_b_id; a_nexts = ls_nexts} in
            let l = List.length ls_nexts in
            let n_res_g1,n_res1, n_res0= match l with
              | 0 -> (res_g1, res1, res0@[new_adj])
              | 1 -> (res_g1, res1@[new_adj], res0)
              | _ -> (res_g1@[new_adj], res1, res0)
            in
            part_edge rem n_res_g1 n_res1 n_res0
        end
  in
  part_edge edges [] [] []

let build_ls_adj edges=
  let pr1 =pr_list print_he in
  let pr2 = pr_list print_adj in
  let pr3 = pr_triple pr2 pr2 pr2 in
  Debug.no_1 "build_ls_adj" pr1 pr3
      (fun _ -> build_ls_adj_x edges) edges

let transform ls_must_eq ini_maps=
  let helper (sv1,sv2)=
    let id1 = List.assoc sv1 ini_maps in
    let id2 = List.assoc sv2 ini_maps in
    (id1,id2)
  in
  List.map helper ls_must_eq

(************************************************************************)
          (*******************END INIT GRAPH******************)
(************************************************************************)

(************************************************************************)
            (*******************TRANS GRAPH******************)
(************************************************************************)
(************************************************************************)
            (*******************SCC******************)
(************************************************************************)
(*
temp methods
*)
let list_to_arr_x ls_adjs =
  let arr = Array.create !heap_size [] in
  let rec helper ls arr=
    match ls with
      | [] -> arr
      | adj::rest -> let () = Array.set arr adj.a_root adj.a_nexts in
        helper rest arr
  in
  helper ls_adjs arr

let list_to_arr ls_adjs =
  let pr1 = pr_arr_ln (pr_list string_of_int) in
  Debug.no_1 "list_to_ar" (pr_list print_adj) pr1
      (fun _ -> list_to_arr_x ls_adjs) ls_adjs

let rec check_overlapping_scc arr_adj scc=
  let rec update ls_in_out r_id nexts res=
    match ls_in_out with
      | [] -> res
      | (id,out_num,in_num)::rest ->
            if id = r_id then
              let n_out_num = (List.length nexts) + out_num in
              update rest r_id nexts (res@[(id,n_out_num,in_num)])
            else if List.mem id nexts then
              update rest r_id nexts (res@[(id,out_num,in_num+1)])
            else update rest r_id nexts (res@[(id,out_num,in_num)])
  in
  let process_adj (ls_ex_scc,r_id) nexts =
    (*filter out irr adjs*)
    if List.mem r_id scc then
      if nexts = [] then (ls_ex_scc,r_id+1) else
        let n_ls_ex_scc = update ls_ex_scc r_id (intersect_int nexts scc) [] in
        (n_ls_ex_scc, r_id+1)
    else
      (ls_ex_scc,r_id+1)
  in
  let ex_scc = List.map (fun id -> (id,0,0)) scc in
  let ex_scc1,_ = Array.fold_left (fun (cur_int_out,i) nexts ->
      process_adj (cur_int_out,i) nexts
  ) (ex_scc,0) arr_adj
  in
  let mul_out,mul_in(* ,eqs *) = List.fold_left (fun (ls1,ls2) (id,n1,n2) ->
       (* let () = Debug.info_pprint (" id: "^ (string_of_int id) ^ " n1= " ^ *)
       (*    (string_of_int n1) ^ " n2= " ^ (string_of_int n2) ) no_pos in *)
      match n1>1, n2>1 with
        | false,true -> (ls1,ls2@[id])
        | true,false -> (ls1@[id], ls2)
        (* | true,true -> (ls1, ls2,ls3@[id]) *)
        | _ -> (ls1,ls2)
  ) ([],[]) ex_scc1 in
  (* let ls1 = List.filter (fun (id1,id2) -> not (id1=id2)) (matrix mul_out mul_in) in *)
  (* let eqs = List.fold_left (fun (ls) (id,n1,n2) -> *)
  (*     match n1>1, n2>1 with *)
  (*         | true,true -> (ls@[id]) *)
  (*         | _ -> (ls) *)
  (* ) ([]) ex_scc1 in *)
  (* let ls2 = if eqs = [] then [] else *)
  (*   let first = List.hd eqs in *)
  (*   List.map (fun id -> (first,id)) (List.tl eqs) *)
  (* in *)
  (* (ls1) *) (mul_out, mul_in)

and check_overlapping_sccs_nested arr_adjs scc=
  let (mul_outs, mul_ins) = check_overlapping_scc arr_adjs scc in
  (*remove one-out vertexs and check nested loops, if any*)
  let ls_ones,_ = Array.fold_left (fun (ls,n) nexts ->
      let nls = if List.mem n scc && List.length nexts = 1 then ls@[n] else ls in
      (nls,n+1)
  ) ([],0) arr_adjs in
  if ls_ones = [] || mul_outs = [] ||  mul_ins = [] then
    let eqs = List.filter (fun (id1,id2) -> not (id1=id2)) (matrix mul_outs mul_ins) in
    eqs
  else
    (* let pr1 = pr_list string_of_int in *)
    (* let () = Debug.info_pprint (" ls_ones: " ^ (pr1 ls_ones)) no_pos in *)
    let ls_ones1 = List.filter (fun id -> not (List.mem id mul_ins)) ls_ones in
    (* let () = Debug.info_pprint (" ls_ones1: " ^ (pr1 ls_ones1)) no_pos in *)
    let (todo_unk:int list) = List.map (fun i -> let () =  arr_adjs.(i) <- [] in i) ls_ones1 in
    (* let () = Debug.info_pprint (" scc: down 1 ") no_pos in *)
    let nested_eqs,_,_= build_scc_arr arr_adjs in
    let used_mul_outs,used_mul_ins = List.split nested_eqs in
    let new_mul_outs = diff_int mul_outs used_mul_outs in
    let new_mul_ins = diff_int mul_ins used_mul_ins in
    let new_eqs =  List.filter (fun (id1,id2) -> not (id1=id2)) (matrix new_mul_outs new_mul_ins) in
    (new_eqs@nested_eqs)

and check_overlapping_sccs_x arr_adjs sccs=
  (* List.fold_left (fun ls scc -> ls@(check_overlapping_scc arr_adjs scc)) [] sccs *)
  List.fold_left (fun ls scc -> ls@(check_overlapping_sccs_nested arr_adjs scc)) [] sccs

and check_overlapping_sccs arr_adjs sccs=
  let pr1 = pr_list string_of_int in
  let pr2 = pr_list (pr_pair string_of_int string_of_int) in
  Debug.no_1 "check_overlapping_sccs" (pr_list pr1) pr2
      (fun _ -> check_overlapping_sccs_x arr_adjs sccs) sccs

and partition_until ls p=
  let rec helper ls rem_ls=
    match ls with
      | [] -> raise Not_found
      | id::rest -> if id = p then (rem_ls, ls)
        else helper rest (rem_ls@[id])
  in
  helper ls []

and visit dfsnum low arr_adj x n l t=
  (* let pr1 = pr_list string_of_int in *)
  (* let pr2 = pr_arr string_of_int in *)
  (* let () = Debug.info_pprint (" visit: " ^ (string_of_int x)) no_pos in *)
  (* let () = Debug.info_pprint (" l: " ^ (pr1 l)) no_pos in *)
  let vist_next dfsnum2 low2 x2 y n2 l2 t2=
    (* let () = Debug.info_pprint (" visit_next: " ^ (string_of_int q)) no_pos in *)
    if not(List.mem y l2) then
      let t21= t2@[y] in
      let dfsnum22,low22,n22,l22,t22,sccs = visit dfsnum2 low2 arr_adj y n2 l2 t21 in
      let () = Array.set low22 x2 (min (Array.get low22 x2) (Array.get low22 y)) in
      (* let () = Debug.info_pprint (" 1 out visit_next: "^ (string_of_int y) ^ ", l22: " ^ (pr1 l22)) no_pos in *)
      (dfsnum22,low22, n22, l22, t22,sccs)
    else
      (* let () = Debug.info_pprint (" low2: " ^ (pr2 low2)) no_pos in *)
      (* let () = Debug.info_pprint (" dfsnum2: " ^ (pr2 dfsnum2)) no_pos in *)
      let () = Array.set low2 x2 (min (Array.get low2 x2) (Array.get dfsnum2 y)) in
      (* let () = Debug.info_pprint (" 2 out visit_next: "^ (string_of_int y) ^ ", l2: " ^ (pr1 l2)) no_pos in *)
      (dfsnum2,low2, n2, l2, t2,[])
  in
  let l = l@[x] in
  let () = Array.set dfsnum x n in
  let n = n+ 1 in
  let () = Array.set low x (Array.get dfsnum x) in
  let dfsnum1,low1,n1,l1,t1,sccs1 = List.fold_left (fun (l_dfsnum,l_low, l_n, l_l, l_t,l_scc) q ->
      let r_dfsnum,r_low, r_n, r_l, r_t, r_sccs = vist_next l_dfsnum l_low x q l_n l_l l_t in
      (r_dfsnum,r_low, r_n, r_l, r_t, l_scc@r_sccs)
  ) (dfsnum,low, n, l, t,[]) (arr_adj.(x))
  in
  (* let () = Debug.info_pprint (" after nexts x: " ^ (string_of_int x)) no_pos in *)
  (* let () = Debug.info_pprint (" l1: " ^ (pr1 l1)) no_pos in *)
  (* let () = Debug.info_pprint (" low1: " ^ (pr2 low1)) no_pos in *)
  (* let () = Debug.info_pprint (" dfsnum1: " ^ (pr2 dfsnum1)) no_pos in *)
  let l2,sccs2 = if low1.(x) = dfsnum1.(x) then
    let rems,scc = partition_until l1 x in
    (* let () = Debug.info_pprint (" scc: " ^ (pr1 scc)) no_pos in *)
    (* let () = Debug.info_pprint (" rems: " ^ (pr1 rems)) no_pos in *)
    (rems,[scc])
  else
    (* let () = Debug.info_pprint (" NONE: " ) no_pos in *)
    (l1,[])
  in
  (dfsnum1,low1,n1,l2,t1,sccs1@sccs2)

and eq_list_int ls1 ls2 = (List.length ls1 = List.length ls2) &&
  (Gen.BList.difference_eq (=) ls1 ls2 = [])

(*Tarjan algo*)
and build_scc_x arr_adj=
  let dfs (ls_scc,topo_order,done_vs,r) nexts=
    if not(List.mem r done_vs) && nexts <> [] then
      (* let () = Debug.info_pprint (" dfs: " ^ (string_of_int r)) no_pos in *)
      let dfsnum = Array.create !heap_size (-1) in
      let low = Array.create !heap_size (-1) in
      let _,_,_,_,_,sccs=visit dfsnum low arr_adj r 0 [] [r] in
      let sccs1 = Gen.BList.remove_dups_eq eq_list_int sccs in
      let sccs2 = Gen.BList.difference_eq eq_list_int sccs1 ls_scc in
      let new_done_vs = List.concat sccs2 in
      (ls_scc@(List.filter (fun ls -> List.length ls > 1) sccs2),topo_order@sccs2,
      done_vs@new_done_vs,r+1)
    else (ls_scc,topo_order,done_vs,r+1)
  in
  let sccs,topo_order,_,_ = (Array.fold_left dfs ([],[],[],0) arr_adj) in
  (* let new_eqs0 = check_overlapping_sccs arr_adj sccs in *) let new_eqs0 = [] in
  (new_eqs0,sccs,topo_order)

and build_scc_arr arr_adjs= build_scc_x arr_adjs

let build_scc ls_adj=
  let pr1 = pr_list print_adj in
  let pr2 = (pr_list string_of_int) in
  let pr3 = pr_list pr2 in
  let pr4 = pr_list (pr_pair string_of_int string_of_int) in
  Debug.no_1 "build_scc" pr1 (pr_triple pr4 pr3 pr3)
      (fun _ ->  build_scc_arr (list_to_arr (ls_adj))) ls_adj

(************************************************************************)
            (*******************END SCC******************)
(************************************************************************)
let rec collect comps res_svl res_els=
  match comps with
    | [] -> (res_svl,res_els)
    | (r, chains,_,_)::rest ->
          let new_svl,new_els = List.fold_left (
              fun (ls1,ls2) (_,svl,els,_) ->
                  (ls1@svl,ls2@els)) (res_svl,res_els) chains in
          collect rest new_svl new_els

let rec collect_except_scc comps scc res_svl res_els=
  match comps with
    | [] -> (res_svl,res_els)
    | (r, chains,_,_)::rest ->
          let new_svl,new_els = List.fold_left (
              fun (ls1,ls2) (r_n,svl,els,_) ->
                  if List.mem r_n scc then (ls1,ls2) else
                  (ls1@svl,ls2@els)
          ) (res_svl,res_els) chains
          in
          collect_except_scc rest scc new_svl new_els

let recover_mutrec_x comps ls_need_recover=
  let process_one_mem_scc l_comps r (r_n,scc,el)=
    let cur, rems = List.partition (fun (r1,_,_,_) -> (r=r1)) l_comps in
    (*get all relevant comps*)
    let rele_comps,rems1 = List.partition (fun (r,_,_,_) -> List.mem r scc) rems in
    let new_svl,new_els = collect_except_scc rele_comps scc [] [] in
    let new_cur=
      match cur with
        | [] -> (r, [(r_n, remove_dups_int (new_svl@scc), el::new_els,[])], [], (-1))
        | [(_,chains,c,d)] -> (r, chains@[(r_n,remove_dups_int (new_svl@scc), el::new_els, [])],c,d)
        | _ -> report_error no_pos "hgraph.recover_mutrec"
    in
    rems@[new_cur]
  in
  let rec classify rem_comps res=
    match rem_comps with
      | [] -> res
      | (r,chains, deps, n)::rest ->
            let same,rems = List.partition (fun (r1,_,_,_) -> r1 = r) rest in
            let new_chains, new_deps =  List.fold_left (fun (ls1,ls2) (_,chains1, deps1,_) -> (ls1@chains1,ls2@deps1)) (chains,deps) same in
            classify rems (res@[(r,new_chains, new_deps,n)])
  in
  let rec process_one l_comps (r, ls_rn_scc_el)=
    (* let pr1 = pr_list string_of_int in *)
    (* let () = Debug.info_pprint (" scc: " ^ (pr1 scc)) no_pos in *)
    (*colect svl, els except itsefl*)
    (* let ls_r_rn = generate_mutrec scc in *)
    let comps1 = List.fold_left (fun comps trip -> process_one_mem_scc comps r trip) l_comps ls_rn_scc_el in
    comps1
  in
  let comps1 = List.fold_left (process_one) comps ls_need_recover in
  classify comps1 []

let recover_mutrec comps ls_need_recover=
  let pr0 = (pr_list string_of_int) in
  let pr1 = pr_list (pr_quad string_of_int (pr_list (pr_quad string_of_int pr0 pr0 pr0)) pr0 string_of_int) in
  let pr2 = pr_list (pr_pair string_of_int (pr_list (pr_triple string_of_int pr0 string_of_int))) in
  Debug.no_2 "recover_mutrec" pr1 pr2 pr1
      (fun _ _ -> recover_mutrec_x comps ls_need_recover) comps ls_need_recover

let combine_loop depden_on_loops scc_svl comps=
  let process_chain (r_n, svl, els, deps)=
    let inter = intersect_int deps scc_svl in
    if inter  <> [] then
      let loop_comps = List.filter (fun (r,_,_,_) -> List.mem r inter) comps in
      let new_svl,new_els = collect loop_comps [] [] in
      (r_n, remove_dups_int svl@new_svl, remove_dups_int els@new_els, deps)
    else (r_n, svl, els, deps)
  in
  let process_one (r,chains,deps,n)=
    (r,List.map process_chain chains,deps,n)
  in
  List.map process_one depden_on_loops

let combine_dependent_components_x comps sccs topo_order=
  let classify_helper (l_indep_comps, l_depen_comps) (r,chains)=
    let dep_rs = List.fold_left (fun ls (_,_,_, ls1) -> ls@ls1) [] chains in
    (*remove self recursive for loop scenarios*)
    let dep_rs1 = remove_dups_int (List.filter (fun sv -> not (sv=r)) dep_rs) in
    if dep_rs1 = [] then
      (*indepen_coms, remove empty depent list of chains*)
      (*c is endlink, now support multiple endlinks wit [c]*)
      let n_chains = List.map (fun (a,b,c,d) -> (a,b,[c],d)) chains in
      (l_indep_comps@[(r, n_chains,[],0)], l_depen_comps)
    else
      let n_chains = List.map (fun (a,b,c,d) -> (a,b,[c],d)) chains in
      (l_indep_comps, l_depen_comps@[(r, n_chains, dep_rs1,  0)])
  in
  (*sort order of nrec_grps to subst*)
  (* let topo_sort_x comps= *)
  (*   let update_order_from_comps updated_roots incr (r,chains, dep_rs1, old_n)= *)
  (*     if List.mem r updated_roots then *)
  (*       (r,chains, dep_rs1,old_n+incr) *)
  (*     else (r,chains, dep_rs1,old_n) *)
  (*   in *)
  (*   let process_one_dep_comps topo (r, chains, dep_rs,  n)= *)
  (*     List.map (update_order_from_comps dep_rs 1) topo *)
  (*   in *)
  (*   let topo1 = List.fold_left process_one_dep_comps comps comps in *)
  (*   (\*sort decreasing and return the topo list*\) *)
  (*   let topo2 = List.sort (fun (_,_,_,n1) (_,_,_,n2) -> n2-n1) topo1 in *)
  (*   topo2 *)
  (* in *)
  let topo_sort_x comps=
    let rec look_up_comp_order rem_orders r n=
      match rem_orders with
        | ls::rest -> if List.mem r ls then n
          else look_up_comp_order rest r (n+1)
        | [] -> report_error no_pos "hgraph.combine_dependent_components: 1"
    in
    let process_one_dep_comps (r, chains, dep_rs,  _)=
      let n = look_up_comp_order topo_order r 0 in
      (r, chains, dep_rs,  n)
    in
    let topo1 = List.map process_one_dep_comps comps in
    (*sort decreasing and return the topo list*)
    let topo2 = List.sort (fun (_,_,_,n1) (_,_,_,n2) -> n1-n2) topo1 in
    topo2
  in
  (*for debugging*)
  let topo_sort comps=
    let pr0 = pr_list string_of_int in
    let pr1 = pr_quad string_of_int (pr_list (pr_quad string_of_int pr0 pr0 pr0))
      pr0 string_of_int in
    let pr2 = pr_list_ln pr1 in
    Debug.no_1 "topo_sort" pr2 pr2
        (fun _ -> topo_sort_x comps) comps
  in
  let rec look_up_indep comps deps=
    match comps with
      | [] -> []
      | (r,chains,_,_)::rest ->
            if List.mem r deps then
              List.map (fun (_,svl,els,_) -> (svl,els)) chains
            else look_up_indep rest deps
  in
  let rec look_up_dep comps deps=
    match comps with
      | [] -> []
      | (r,chains,_,_)::rest ->
            if List.mem r deps then
              List.map(fun (_,svl,el,_) -> (svl,el)) chains
            else look_up_dep rest deps
  in
  let rec combine chains indep_comps comps res=
    match chains with
      | [] -> res
      | (r_n, svl, els, deps)::rest ->
            let svl1 = look_up_indep indep_comps deps in
            let svl2 = look_up_dep comps deps in
            let n_svl,endlinks =  if List.length svl1 > 0 || List.length svl2 > 0 then
              let ls1,ls2 = List.fold_left (fun (svl,endlinks) (n_svl, n_ends) -> svl@n_svl,endlinks@n_ends) (svl,[]) (svl1@svl2) in
              (Gen.BList.remove_dups_eq (=) ls1,ls2)
            (* let new_chains = *)
            (*   List.map (fun (svl1,el1) ->  (r_n, CP.remove_dups_svl (svl@svl1), el1, deps)) (svl1@svl2) *)
            else
              (svl, els)
            in
            (*make use of endlinks when support multiple endlinks*)
            let new_chains = [(r_n, n_svl, endlinks, deps)] in
            combine rest indep_comps comps (res@new_chains)
  in
  let rec combine_comps l_comps indep_comps res=
    match l_comps with
      | [] -> res
      | (r, chains, dep_rs1,  n)::rest ->
            (*if dep_rs1 = [] then chains else*)
            let n_chains = combine chains indep_comps (res@rest) [] in
            combine_comps rest indep_comps (res@[(r, n_chains, dep_rs1,  n)])
  in
  let indep_comps, dep_coms = List.fold_left classify_helper ([],[]) comps in
  (* let indep_comps = [] in *)
  (* let dep_coms = List.map pre_process comps in *)
  (*build topo - dependent graph among components*)
  let sorted_dep_coms = topo_sort dep_coms in
  (*combine: bottom-up*)
  let combined_dep_comps = combine_comps sorted_dep_coms indep_comps [] in
  (* (\*post process*\) *)
  (* (\*should recombine for mutex dependence*\) *)
  (* let combined_dep_comps1 = recover_mutrec combined_dep_comps sccs in *)
  (* let indep_comps1 = recover_mutrec indep_comps sccs in *)
  (* (\*redundant do combine for ones relate to loops*\) *)
  (* let scc_svl = List.concat sccs in *)
  (* let depden_on_loops,rems = List.partition (fun (_,_,deps,_) -> intersect_int deps scc_svl <> []) combined_dep_comps in *)
  (* let depden_on_loops1 = combine_loop depden_on_loops scc_svl combined_dep_comps1 in *)
  (* let combined_dep_comps1 = depden_on_loops1@rems in *)
  (* let combined_dep_comps2 = List.map (fun (r,chains,_,_) -> *)
  (*     let n_chains = List.map (fun (a,b,c,_) -> (a,b,c)) chains in *)
  (*     (r,n_chains) *)
  (* ) (indep_comps1@combined_dep_comps1) in *)
  (indep_comps@combined_dep_comps)

let combine_dependent_components comps sccs topo_order=
  let pr1 = pr_list string_of_int in
  let pr2 = pr_pair string_of_int (pr_list (pr_quad string_of_int pr1 string_of_int pr1)) in
  let pr3 = pr_quad string_of_int (pr_list (pr_quad string_of_int pr1 pr1 pr1))
  pr1 string_of_int in
  Debug.no_2 "combine_dependent_components" (pr_list_ln pr2) (pr_list pr1) (pr_list_ln pr3)
      (fun _ _ -> combine_dependent_components_x comps sccs topo_order) comps topo_order

let recover_from_loop comps sccs ls_need_recover=
  (*should recombine for mutex dependence*)
  (*loop until reach fixpoint*)
  let comps1 = recover_mutrec comps ls_need_recover in
  (*end loop*)
  (*redundant do combine for ones relate to loops*)
  let scc_svl = List.concat sccs in
  let depden_on_loops,rems = List.partition (fun (_,_,deps,_) -> intersect_int deps scc_svl <> []) comps1 in
  let depden_on_loops1 = combine_loop depden_on_loops scc_svl comps1 in
  let comps2 = depden_on_loops1@rems in
  let comps3 = List.map (fun (r,chains,_,_) ->
      let n_chains = List.map (fun (a,b,c,_) -> (a,b,c)) chains in
      (r,n_chains)
  ) (comps2) in
  (comps3)

let rec find_chain adjg2_roots cur res ls_adj1=
  (* let () = Debug.info_pprint (" XXXXXXXXXX 3: " ^ (!CP.print_sv cur)) no_pos in *)
  if List.mem cur adjg2_roots then
    (*this chain points to anothe2r root*)
    (cur,res,[cur])
  else
    let nexts = look_up_adj cur ls_adj1 in
    (* let () = Debug.info_pprint (" XXXXXXXXXX 4: " ^ (!CP.print_sv n)) no_pos in *)
    match nexts with
      | [] -> (cur,res,[])
      | [n] -> if List.mem n res then (n,res,[]) (*loop*) else
            find_chain adjg2_roots n (res@[n]) ls_adj1
      | _ -> report_error no_pos "hgraph.find_chain: <=1 nexts"

let get_mutrec_adj adjs=
  let get_deps ls a= ls@(List.map (fun id -> (a.a_root, id)) a.a_nexts) in
  let rec check_mut deps res=
    match deps with
      | [] -> res
      | (id1,id2)::rest -> begin
          let invs, rems = List.partition (fun (id3,id4) -> id3 = id2 && id4=id1) rest in
          let new_res=
            if invs = [] then [] else [(id1,id2);(id2,id1)]
          in
          check_mut rems (res@new_res)
        end
  in
  check_mut (List.fold_left get_deps [] adjs) []

let build_raw_chains sccs adjg1_roots ls_adj1 all_adjs adj=
  (*list of (maybe emp-next ptr,ptrs in the chain, last ptrs)*)
  (*now only work with view -- should support data node also - a chain has a dn --> non emp*)
  let process_one_chain (r,r_n) =
    (* let () = Debug.info_pprint (" XXXXXXXXXX 5 - root: " ^ (!CP.print_sv r)) no_pos in *)
    let end_link, chains, deps = find_chain adjg1_roots r_n [r;r_n] ls_adj1 in
    (r_n, chains,end_link,deps)
  in
  (*list of (root next, scc, end link)*)
  let find_scc sccs r_n=
    let rec look_up ls=
      match ls with
        | [] -> (r_n,[],r_n)
        | scc::rest -> if List.mem r_n scc then (r_n,scc,r_n) else
            look_up rest
    in
    look_up sccs
  in
  let rec look_up_scc r sccs=
    match sccs with
      | [scc] -> scc
      | scc::rest -> if List.mem r scc then scc else look_up_scc r rest
      | [] -> report_error no_pos "hgraph.look_up_scc"
  in
  let check_in_scc r nexts sccs=
    let rec look_up ls_scc done_sccs=
      match ls_scc with
        | [] -> (nexts,[])
        | scc::rest -> if List.mem r scc then
            let loop,non_loop = List.fold_left (fun (ls1,ls2) id ->
                if (List.mem id scc) then
                  (*r may be the intersection of multiple loops,
                    id is in a loop, to prevent 8-shape loop*)
                  let other_next_loops = List.filter (fun rn -> not (rn=id)) nexts in
                  let cur_loop_scc = if other_next_loops = [] then scc else
                    (* let scc_except_other_nexts = diff_int scc other_next_loops in *)
                    let scc_adjs = List.filter (fun adj -> (List.mem adj.a_root scc) ) all_adjs in
                    let r_adj,rems = split_adj scc_adjs r in
                    let new_r_adj = {r_adj with a_nexts = [id]} in
                    let _,cur_sccs,_ = build_scc (* scc_adjs *) (new_r_adj::rems) in
                    look_up_scc id cur_sccs
                  in
                  (ls1@[(id,cur_loop_scc,r)],ls2)
                else (ls1,ls2@[id])
            ) ([],[]) nexts
            in
            let other_sccs = done_sccs@rest in
            let other_loops = List.map (find_scc other_sccs) non_loop in
            let non_loop,loop1 = List.fold_left (fun (ls1,ls2) (r_n,scc,el) ->
                if scc = [] then (ls1@[r_n],ls2) else (ls1,ls2@[(r_n,scc,el)])
            ) ([],[]) other_loops in
            let loop = loop@loop1 in
            let need_recover = if loop = [] then [] else
              [(r, loop)]
            in
            (non_loop, need_recover)
          else look_up rest (done_sccs@[scc])
    in
    look_up sccs []
  in
  let non_loop, need_recover = check_in_scc adj.a_root adj.a_nexts sccs in
  let pr_reach = List.map (fun n -> (adj.a_root, n)) non_loop in
  (*remove mutrec*)
  (* let pr_reach1 = List.filter (fun (id1,id2) -> *)
  (*     not(List.exists (fun scc -> check_in_scc id1 id2 (List.hd scc) scc) sccs)) pr_reach in *)
  ((adj.a_root,List.map process_one_chain pr_reach),need_recover)

let build_comps_x sccs topo_order ls_adjg1 ls_adj1=
  (*collect mutrec*)
  let adjs = ls_adjg1@ls_adj1 in
  (* let ls_mutrec = get_mutrec_adj (ls_adjg1@ls_adj1) in *)
  let adjg1_roots = List.map (fun adj -> adj.a_root) ls_adjg1 in
  let raw_comps,ls_need_recover = List.fold_left ( fun (comps, loops) adj ->
      let (r,chains), new_loops =  build_raw_chains sccs adjg1_roots ls_adj1 adjs adj in
      let comps1 = if chains = [] then comps else comps@[(r,chains)] in
      (comps1,loops@new_loops)
  ) ([],[]) ls_adjg1 in
  let comps = combine_dependent_components raw_comps sccs topo_order in
  (*recover here*)
  let comps1 = recover_from_loop comps sccs ls_need_recover in
  comps1

let build_comps sccs topo_order ls_adjg1 ls_adj1=
  let pr1 = pr_list print_adj in
  let pr2 = (pr_list string_of_int) in
  let pr3 = pr_list (pr_pair string_of_int (pr_list (pr_triple string_of_int pr2 pr2)) ) in
  Debug.no_3 "build_comps" (pr_list pr2) pr1 pr1 pr3
      (fun _ _ _ -> build_comps_x sccs topo_order ls_adjg1 ls_adj1) topo_order ls_adjg1 ls_adj1

let do_merge_hv vertexs eqs=
  let process_one vs (id1, id2)=
    let hv2,n_vertexs = remove_hv vs id2 in
    let n_vertexs1 = update_hv_lbl n_vertexs id1 hv2.hv_lbl in
     n_vertexs1
  in
  List.fold_left (fun vs pr -> process_one vs pr) vertexs eqs

let do_chain_merge_hv_x vertexs chain_emps=
  let process_one vs (id1, ids2)=
    let hvs2,n_vertexs = batch_remove_hvs vs ids2 in
    let total_lbl = List.fold_left (fun ls hv -> ls@hv.hv_lbl) [] hvs2 in
    let n_vertexs1 = update_hv_lbl n_vertexs id1 total_lbl in
     n_vertexs1
  in
  List.fold_left (fun vs pr -> process_one vs pr) vertexs chain_emps

let do_chain_merge_hv vertexs chain_emps=
  let pr1 = pr_list print_hv in
  let pr2 = string_of_int in
  let pr3 = pr_list (pr_pair pr2 (pr_list pr2)) in
  Debug.no_2 "do_chain_merge_hv" pr1 pr3 pr1
      (fun _ _ -> do_chain_merge_hv_x vertexs chain_emps)
      vertexs chain_emps

let do_merge_throw_hv_x vertexs merge_throws=
  let process_one vs (merge_ids, throw_ids)=
    let throw_hvs,n_vertexs = batch_remove_hvs vs throw_ids in
    let first_merge_hv,n_vertexs1 = remove_hv n_vertexs (List.hd merge_ids) in
    let tail_merges,n_vertexs2 = batch_remove_hvs n_vertexs1 (List.tl merge_ids) in
    let total_lbl = List.fold_left (fun ls hv -> ls@hv.hv_lbl) [] (throw_hvs@tail_merges) in
    let first_merge_hv1 = {first_merge_hv with hv_lbl = (first_merge_hv.hv_lbl@total_lbl)} in
    (* let n_vertexs3 = update_hv_lbl n_vertexs2 id1 total_lbl in *)
     n_vertexs2@[first_merge_hv1]
  in
  List.fold_left (fun vs pr -> process_one vs pr) vertexs merge_throws

let do_merge_throw_hv vertexs merge_throws=
  let pr1 = pr_list print_hv in
  let pr2 = pr_list string_of_int in
  let pr3 = pr_list (pr_pair pr2 pr2) in
  Debug.no_2 "do_merge_throw_hv" pr1 pr3 pr1
      (fun _ _ -> do_merge_throw_hv_x vertexs merge_throws)
      vertexs merge_throws

let subst (id1,id2) a=
  let rec helper l_ids res=
    match l_ids with
      | [] -> res
      | id::rest -> let new_id = if id=id2 then id1 else id in
        helper rest (res@[new_id])
  in
  let new_nexts = helper a.a_nexts [] in
  {a with a_nexts = new_nexts}

let subst_chain (r_id, emp_chain_mems) a=
  let rec helper l_ids res=
    match l_ids with
      | [] -> res
      | id::rest -> let new_res = if List.mem id  emp_chain_mems then (res@[r_id]) else (res@[id]) in
        helper rest new_res
  in
  let new_nexts = helper a.a_nexts [] in
  {a with a_nexts = new_nexts}

let detect_simple_dups_chains r nexts=
  let rec classify_helper rem_nexts parts eqs=
    match rem_nexts with
      | [] -> (parts,eqs)
      | n::rest -> let same,rems = List.partition (fun id -> id=n) rest in
                   if same = [] then classify_helper rems (parts@[n]) eqs
                   else classify_helper rems (parts@[n]) (eqs@[(r, n)])
  in
  classify_helper nexts [] []

let update_comb_adjs ls_adj eqs=
  let process_helper adjs (id1,ids2)=
    let adj1,rems1 = split_adj adjs id1 in
    let adj2_nexts,rems2 = drop_get_nexts_adjs rems1 ids2 in
    let nexts1 = List.filter (fun id -> not (List.mem id ids2)) adj1.a_nexts in
    let nexts2 = nexts1@adj2_nexts in
    (*update remain*)
    let rems3 = List.map (subst_chain (id1,ids2)) rems2 in
    (rems3@[{adj1 with a_nexts = nexts2}])
  in
  let adjs1 = List.fold_left (fun adjs eq -> process_helper adjs eq) ls_adj eqs in
  let adjs2,eqs = List.fold_left (fun (ls1,ls2) adj ->
      let nexts1 =  List.filter (fun id-> not(id=adj.a_root)) adj.a_nexts in
      let new_nexts,eqs = detect_simple_dups_chains adj.a_root nexts1 in
      let new_adj = {adj with a_nexts = new_nexts} in
      (ls1@[new_adj],ls2@eqs)
  ) ([],[]) adjs1 in
  (* let pr1 = pr_list print_adj in *)
  (* let () = Debug.info_pprint (" adjs1: "^ (pr1 adjs1)) no_pos in *)
  (* let () = Debug.info_pprint (" adjs2: "^ (pr1 adjs2)) no_pos in *)
  adjs2,eqs

let update_chain_adjs_x ls_adj chain_emps=
  let process_helper adjs (id1,ids2)=
    let adj1,rems1 = split_adj adjs id1 in
    let rems2 = drop_adjs rems1 ids2 in
    let nexts1 = List.filter (fun id -> not (List.mem id ids2)) adj1.a_nexts in
    (*update remain*)
    let rems3 = List.map (subst_chain (id1,ids2)) rems2 in
    (rems3@[{adj1 with a_nexts = nexts1}])
  in
  let adjs1 = List.fold_left (fun adjs eq -> process_helper adjs eq) ls_adj chain_emps in
  let adjs2,eqs = List.fold_left (fun (ls1,ls2) adj ->
      let nexts1 =  List.filter (fun id-> not(id=adj.a_root)) adj.a_nexts in
      let new_nexts,eqs = detect_simple_dups_chains adj.a_root nexts1 in
      let new_adj = {adj with a_nexts = new_nexts} in
      (ls1@[new_adj],ls2@eqs)
  ) ([],[]) adjs1 in
  (* let pr1 = pr_list print_adj in *)
  (* let () = Debug.info_pprint (" adjs1: "^ (pr1 adjs1)) no_pos in *)
  (* let () = Debug.info_pprint (" adjs2: "^ (pr1 adjs2)) no_pos in *)
  adjs2,eqs

let update_chain_adjs ls_adj chain_emps=
  let pr1 = pr_list print_adj in
  let pr2 = pr_list string_of_int in
  let pr2a = pr_list (pr_pair string_of_int string_of_int) in
  let pr3 = pr_list (pr_pair string_of_int pr2) in
  Debug.no_2 "update_chain_adjs" pr1 pr3 (pr_pair pr1 pr2a )
      (fun _ _ -> update_chain_adjs_x ls_adj chain_emps)
      ls_adj chain_emps


let update_merge_throw_chain_adjs_x ls_adj ls_merge_throw=
  let throw_helper throw_ids adj= {adj with a_nexts =
          List.filter (fun id -> not (List.mem id throw_ids)) adj.a_nexts} in
  let process_helper adjs (merge_ids,throw_ids)=
    let merge_adjs,rems1 = batch_split_adjs adjs merge_ids in
    let rems2 = drop_adjs rems1 throw_ids in
    let throw_ids = throw_ids@merge_ids in
    let merge_adjs1 = List.map (throw_helper throw_ids) merge_adjs in
    let first_merge,tail_merges = split_adj merge_adjs1 (List.hd merge_ids) in
    let total_lbl = List.fold_left (fun ls adj -> ls@adj.a_nexts) [] (tail_merges) in
    (*update remain*)
    let rems3 = List.map (subst_chain (first_merge.a_root,throw_ids)) rems2 in
    (rems3@[{first_merge with a_nexts = first_merge.a_nexts@total_lbl}])
  in
  let adjs1 = List.fold_left (fun adjs eq -> process_helper adjs eq) ls_adj ls_merge_throw in
  let adjs2,eqs = List.fold_left (fun (ls1,ls2) adj ->
      let nexts1 =  List.filter (fun id-> not(id=adj.a_root)) adj.a_nexts in
      let new_nexts,eqs = detect_simple_dups_chains adj.a_root nexts1 in
      let new_adj = {adj with a_nexts = new_nexts} in
      (ls1@[new_adj],ls2@eqs)
  ) ([],[]) adjs1 in
  (* let pr1 = pr_list print_adj in *)
  (* let () = Debug.info_pprint (" adjs1: "^ (pr1 adjs1)) no_pos in *)
  (* let () = Debug.info_pprint (" adjs2: "^ (pr1 adjs2)) no_pos in *)
  adjs2,eqs

let update_merge_throw_chain_adjs ls_adj ls_merge_throw=
  let pr1 = pr_list print_adj in
  let pr2 = pr_list string_of_int in
  let pr2a = pr_list (pr_pair string_of_int string_of_int) in
  let pr3 = pr_list (pr_pair pr2 pr2) in
  Debug.no_2 "update_merge_throw_chain_adjs" pr1 pr3 (pr_pair pr1 pr2a)
      (fun _ _ -> update_merge_throw_chain_adjs_x ls_adj ls_merge_throw)
      ls_adj ls_merge_throw

let rec merge_alias_hv_x vertexs ls_adjg1 ls_adj1 ls_eq=
  let ls_eq1 = List.map (fun (id1,id2) -> (id1,[id2])) ls_eq in
  let ls_eq2 = find_close_chains ls_eq1 in
  let n_vertexts = do_chain_merge_hv vertexs ls_eq2 in
  let new_adjs, eqs = update_comb_adjs (ls_adjg1@ls_adj1) ls_eq2 in
  let new_adjg1, rems = List.partition (fun a -> List.length a.a_nexts > 1) new_adjs in
  let new_adj1, _ = List.partition (fun a -> List.length a.a_nexts > 0) rems in
  if eqs = [] then
    (n_vertexts, new_adjg1, new_adj1)
  else merge_alias_hv n_vertexts new_adjg1 new_adj1 eqs

and merge_alias_hv vertexs ls_adjg1 ls_adj1 ls_eq=
  (* let pr0 = pr_list string_of_int in *)
  let pr1 = pr_list print_hv in
  let pr2 = pr_list print_adj in
  let pr3= pr_list (pr_pair string_of_int string_of_int) in
  Debug.no_4 "merge_alias_hv" pr1 pr2 pr2 pr3 (pr_triple pr1 pr2 pr2)
      (fun _ _ _ _ -> merge_alias_hv_x vertexs ls_adjg1 ls_adj1 ls_eq)
      vertexs ls_adjg1 ls_adj1 ls_eq

let rec merge_emp_chains_x vertexs ls_adjg1 ls_adj1 ls_chain_emps=
  (*find_close of ls_chain_emps*)
  (* let ls_chain_emps0 = find_close_chains ls_chain_emps in *)
  let ls_merge_throw, ls_chain_emps0 = classify_merge_throw_chains ls_chain_emps in
  (*do merge_thwo: thow and merge*)
  let n_vertexts = do_chain_merge_hv vertexs ls_chain_emps0 in
  let n_vertexts1 = do_merge_throw_hv n_vertexts ls_merge_throw in
  let new_adjs, eqs1 = update_chain_adjs (ls_adjg1@ls_adj1) ls_chain_emps0 in
  let new_adjs1, eqs2 = update_merge_throw_chain_adjs new_adjs ls_merge_throw in
  let new_adjg1, rems = List.partition (fun a -> List.length a.a_nexts > 1) new_adjs1 in
  let new_adj1, _ = List.partition (fun a -> List.length a.a_nexts > 0) rems in
  let eqs = eqs1@eqs2 in
  if eqs = [] then
    (n_vertexts1, new_adjg1, new_adj1)
  else
    merge_emp_chains n_vertexts1 new_adjg1 new_adj1 (List.map (fun (id1,id2) -> (id1,[id2])) eqs)

and merge_emp_chains vertexs ls_adjg1 ls_adj1 ls_chain_emps=
  let pr0 = pr_list string_of_int in
  let pr1 = pr_list print_hv in
  let pr2 = pr_list print_adj in
  let pr3 = pr_list (pr_pair string_of_int pr0) in
  Debug.no_4 "merge_emp_chains" pr1 pr2 pr2 pr3 (pr_triple pr1 pr2 pr2)
      (fun _ _ _ _ -> merge_emp_chains_x vertexs ls_adjg1 ls_adj1 ls_chain_emps)
      vertexs ls_adjg1 ls_adj1 ls_chain_emps

(************************************************************************)
            (*******************END TRANS GRAPH******************)
(************************************************************************)
(************************************************************************)
            (******************RULE FOCRE******************)
(************************************************************************)
let eq_end_pair (id1,id2) (id3, id4)= (id2=id4)
let eq_pair (id1,id2) (id3, id4)= (id1=id3)&&(id2=id4)

let rec intersect_fast ls ls1=
  match ls with
    | [] -> true
    | sv::rest ->
          if List.mem sv ls1 then intersect_fast rest ls1
          else false

let rec find_non_empty_one_chain l_non_emps ptrs=
  match l_non_emps with
    | [] -> false
    | (id1,id2)::rest -> if intersect_fast [id1;id2] ptrs then true
      else
        find_non_empty_one_chain rest ptrs

(*all sv1, sv2 \in svl: emp (sv1,sv2) *)
let build_emp svl maybe_emps=
  let inter_emp = List.filter (fun (sv1,sv2) -> (List.mem sv1 svl) && (List.mem sv2 svl)) maybe_emps in
  inter_emp

(*rule 2*)
(*root r: a chain has a node or a non-base case between two nodes of the chain
==> other chains of root r must be base cases
r --> w1
r ---> w2

if not emp(r,w1) then emp(r,w2)
*)
let force_spatial_no_dups_x non_emps (r,chains)=
  let rec find_non_emp cur_ls done_ls=
    match cur_ls with
      | [] -> []
      | (r_n,ptrs,end_ptrs)::rest ->
            if find_non_empty_one_chain non_emps ptrs then
              (* List.map (fun (r_n,_,_) -> (r,r_n)) (done_ls@rest) *)
              let prune_brs, ptr_other_chains = List.fold_left (fun (ls1,ls2) (r_n,svl,_) -> (ls1@[r_n],ls2@svl)) ([],[]) (done_ls@rest) in
              (* build_emp (Gen.BList.remove_dups_eq (=) ptr_other_chains) maybe_emps *)
              if prune_brs = [] then [] else
                [(r, List.filter (fun id -> not(id=r)) (remove_dups_int ptr_other_chains),prune_brs)]
            else
              find_non_emp rest (done_ls@[(r_n,ptrs,end_ptrs)])
  in
  let emps = find_non_emp chains [] in
  emps

let force_spatial_no_dups non_emps (r,chains)=
  let pr0 = string_of_int in
  let pr0a = pr_list pr0 in
  let pr1 = pr_list (pr_triple pr0 pr0a pr0a) in
  let pr2 = pr_pair pr0 (pr_list (pr_triple pr0 pr0a pr0a)) in
  Debug.no_2 "force_spatial_no_dups" (pr_list (pr_pair pr0 pr0)) pr2 pr1
      (fun _ _-> force_spatial_no_dups_x non_emps (r,chains)) non_emps (r,chains)

(*rule 3*)
(*
r --> w
r --> w'
r---> w''
and if not emp(w, w') then emp(r, w'')
*)
let force_spatial_transitive_x non_emps (r,chains)=
  let rec find_non_emp_from_2_chains ptrs rem_chains done_chains=
    match rem_chains with
      | [] -> []
      | (r_n,ptrs1,end_links)::rest ->
            (*todo: maybe wrong. should check: non_emp(sv1,sv2) and sv1 in ptrs and sv2 in ptrs1*)
             if find_non_empty_one_chain non_emps (ptrs@ptrs1) then
               (rest@done_chains)
             else find_non_emp_from_2_chains ptrs rest (done_chains@[(r_n,ptrs1,end_links)])
  in
  let rec find_non_emp_trans cur_ls done_ls=
    match cur_ls with
      | [] -> []
      | (r_n,ptrs,end_ptrs)::rest ->
            let emp_chains = find_non_emp_from_2_chains ptrs rest [] in
            if emp_chains = [] then
               find_non_emp_trans rest (done_ls@[(r_n,ptrs,end_ptrs)])
            else
              (* List.map (fun (r_n,_,_) -> (r,r_n)) (done_ls@emp_chains) *)
              let prune_brs, ptr_other_chains = List.fold_left (fun (ls1,ls2) (r_n,svl,_) -> (ls1@[r_n],ls2@svl)) ([],[]) (done_ls@emp_chains) in
              (* build_emp (Gen.BList.remove_dups_eq (=) ptr_other_chains) maybe_emps *)
              if prune_brs = [] then [] else
                [(r, List.filter (fun id -> not(id=r)) (remove_dups_int ptr_other_chains),prune_brs)]
  in
  if List.length chains < 3 then []
  else find_non_emp_trans chains []

let force_spatial_transitive non_emps (r,chains)=
  let pr0 = string_of_int in
  let pr0a = pr_list pr0 in
  let pr1 = pr_list (pr_triple pr0 pr0a pr0a) in
  let pr2 = pr_pair pr0 (pr_list (pr_triple pr0 pr0a pr0a)) in
  Debug.no_1 "force_spatial_transitive" pr2 pr1
      (fun _ -> force_spatial_transitive_x non_emps (r,chains)) (r,chains)

let force_spatial non_emps chains_grp =
  let emp2= force_spatial_no_dups non_emps chains_grp in
  let emp3 = force_spatial_transitive non_emps chains_grp in
  (emp2@emp3)

(*rule 4 - *)
(*check no distinct loop-free for paths*)
(*root r:
check NO distinct loop-free for one path r-w1
r --u1--> w1
r --u2--> w1
========> create loop: w1=r (w1 != null:: elim null at the intersection of chains)
*)
let dfs_no_loop_x r rn1 rn2 inters adjs=
  let rec visit working done_list res=
    match working with
      | [] -> res
      | id::rest ->
            (*detect loop*)
            if List.mem id done_list then
              visit rest done_list res
            else (*detect ends*)
              if List.mem id inters then
              let new_res =  res@[(id, done_list@[id])] in
              let dfs_res = visit (look_up_adj id adjs) (done_list@[id]) new_res in
              visit rest done_list dfs_res
            else
              let dfs_res = visit (look_up_adj id adjs) (done_list@[id]) res in
              visit rest done_list dfs_res
  in
  let rec check_inter_l2 chains1 ls2=
    List.exists (fun (_,chains2) -> List.length (intersect_int chains1 chains2) < 3) ls2
  in
  let cmp_one_inter i ls1 ls2=
    let ls11 = List.filter (fun (i1,_) -> i1=i) ls1 in
    let ls21 = List.filter (fun (i1,_) -> i1=i) ls2 in
    List.exists (fun (_,chains1) -> check_inter_l2 chains1 ls21) ls11
  in
  let ls_rn1 = visit [rn1] [r] [] in
  let ls_rn2 = visit [rn2] [r] [] in
  (* let pr1 = pr_list (pr_pair string_of_int (pr_list string_of_int)) in *)
  (* let () = Debug.info_pprint (" ls_rn1: "^ (pr1 ls_rn1)) no_pos in *)
  (* let () = Debug.info_pprint (" ls_rn2: "^ (pr1 ls_rn2)) no_pos in *)
  List.fold_left (fun ls i ->
      if cmp_one_inter i ls_rn1 ls_rn2 then (ls@[i]) else ls
  ) [] inters

let dfs_no_loop r rn1 rn2 inters adjs=
  let pr1 = string_of_int in
  let pr2 = pr_list pr1 in
  Debug.no_4 "dfs_no_loop" pr1 pr1 pr1 pr2 pr2
      (fun _ _ _ _ -> dfs_no_loop_x r rn1 rn2 inters adjs)
      r rn1 rn2 inters

(* (\*go back until one*\) *)
let find_first_intersection r inters adjs=
  let rec helper working_list =
    match working_list with
      | [] -> report_error no_pos "hgraph.find_first_intersection"
      | id::rest ->
            let nexts = look_up_adj id adjs in
            let first_cands = Gen.BList.intersect_eq (=) nexts inters in
            if first_cands <> [] then
              List.hd first_cands
            else
              helper (rest@nexts)
  in
  helper [r]

(*chain = nt, ptrs, end*)
(*return eqs of r end intersected end_links*)
let do_force_no_disctinct_loop_free_x adjs (r,chains) =
  let rec find_loop (n_r0, svl0, end_links0) rest0 res=
    match rest0 with
     | [] -> res
     | (n_r1, svl1, end_links1)::rest1 -> (* check loop *)
           (* if List.mem r end_links1 then *)
           (*   find_loop (n_r0, svl0, end_links0) rest1 (res) *)
           (* else *)
           let end_links1 = List.filter (fun id -> not (id=r)) end_links1 in
           if (* not (List.mem r end_links1) && *) true(* end_links1 <> [] *) then
             (*simple check distinct*)
             let all_inters = Gen.BList.intersect_eq (=) svl0 svl1 in
             if List.length all_inters > 2 then
               let all_inters1 = List.filter (fun id -> not (id=r) (* && List.mem id end_links1 *)) all_inters in
               let real_inters = dfs_no_loop r n_r0 n_r1 all_inters1 adjs in
               (* let first_inter = find_first_intersection r all_inters1 adjs in *)
               (* find_loop  (n_r0, svl0, end_links0) rest1 (res@[first_inter]) *)
               find_loop  (n_r0, svl0, end_links0) rest1 (res@real_inters)
             else
               let inter = Gen.BList.intersect_eq (=) end_links0 end_links1 in
               (* let inter1 = *)
               (*   if List.length inter < 2 && *)
               (*     (List.length all_inters1 = List.length inter) then inter *)
               (*   else *)
               (*     find_first_inter adjs all_inters1 inter *)
               (* in *)
               find_loop  (n_r0, svl0, end_links0) rest1 (res@inter)
             else find_loop  (n_r0, svl0, end_links0) rest1 (res)
  in
  let rec find_loops ls res=
    match ls with
      | [] -> (Gen.BList.remove_dups_eq (=) res)
      | (r_n, svl,end_links)::rest ->
            (* let pr1 =pr_list string_of_int in *)
            (* let () = Debug.info_pprint (" r_n: "^ (string_of_int r_n)) no_pos in *)
            (*check have a self loop*)
            let end_links = List.filter (fun id -> not (id=r)) end_links in
            if (* end_links <> [] *)true  then
              let n_inter = find_loop (r_n, svl,end_links) rest [] in
              (* let () = Debug.info_pprint (" n_inter: "^ (pr1 n_inter)) no_pos in *)
              find_loops rest (res@n_inter)
            else
              find_loops rest (res)
  in
  (* let () = Debug.info_pprint (" r: "^ (string_of_int r)) no_pos in *)
  let inter_elinks = find_loops chains [] in
  (* (List.fold_left (fun ls sv -> ls@(combine_sym sym_r sv)) [] inter_elinks, (sym_r@inter_elinks, rems)) *)
  (List.fold_left (fun ls sv -> ls@[(r,sv)]) [] inter_elinks)

let do_force_no_disctinct_loop_free adjs (r,chains)=
  let pr0 = string_of_int in
  let pr0a = pr_list pr0 in
  let pr1 = pr_list (pr_pair pr0 pr0) in
  let pr2 = pr_pair pr0 (pr_list (pr_triple pr0 pr0a pr0a)) in
  Debug.no_1 "do_force_no_disctinct_loop_free" pr2 ( pr1)
      (fun _ -> do_force_no_disctinct_loop_free_x adjs (r,chains)) (r,chains)

let force_no_distinct_loop_x vertexs ls_adjg10 ls_adj10=
  let rec loop_helper is_loop vs adjg1 adj1=
    let overlap_eqs,sccs,topo_order = build_scc (adjg1@adj1) in
    if overlap_eqs = [] then
      let comps = build_comps sccs topo_order adjg1 adj1 in
      let comps1 = List.filter (fun (_,chains) -> List.length chains>1) comps in
      let adjs = adjg1@adj1 in
      let new_eqs0 = List.fold_left (fun ls comp->
        ls@(do_force_no_disctinct_loop_free adjs comp)) [] comps1 in
      (* let new_eqs1 = Gen.BList.remove_dups_eq eq_end_pair new_eqs0 in *)
      (* let new_eqs2 = Gen.BList.difference_eq eq_pair new_eqs1 must_eqs in *)
      if new_eqs0 = [] then (is_loop, vs, adjg1, adj1, comps1) else
        let new_vertexs, new_adjg1, new_adj1 =  merge_alias_hv vs adjg1 adj1 new_eqs0 in
        (* let () = Debug.info_pprint (" *******loop********* ") no_pos in *)
        loop_helper true new_vertexs new_adjg1 new_adj1
    else
      let new_vertexs, new_adjg1, new_adj1 =  merge_alias_hv vs adjg1 adj1 overlap_eqs in
      (* let pr1 = pr_list (pr_pair string_of_int string_of_int) in *)
      (* let () = Debug.info_pprint (" *******overlapped loops*********: " ^ (pr1 overlap_eqs)) no_pos in *)
      loop_helper true new_vertexs new_adjg1 new_adj1
  in
  loop_helper false vertexs ls_adjg10 ls_adj10

let force_no_distinct_loop vertexs ls_adjg1 ls_adj1=
  let pr0 = pr_list string_of_int in
  let pr1 = pr_list print_hv in
  let pr2 = pr_list print_adj in
  (* let pr3 = pr_list (pr_pair string_of_int string_of_int) in *)
  let pr4 = pr_list (pr_pair string_of_int (pr_list (pr_triple string_of_int pr0 pr0) )) in
  let pr5 = pr_penta string_of_bool pr1 pr2 pr2 pr4 in
  Debug.no_3 "force_no_distinct_loop" pr1 pr2 pr2 pr5
      (fun _ _ _ -> force_no_distinct_loop_x vertexs ls_adjg1 ls_adj1)
      vertexs ls_adjg1 ls_adj1

let build_hv_non_emps vertexs non_emps=
  let rec helper ls res=
    match ls with
      | [] -> false,res
      |(sv1,sv2)::rest ->
           let id1 = from_var_to_hv vertexs sv1 in
           let id2 = from_var_to_hv vertexs sv2 in
           if id1 = id2 then (true,res) else
             helper rest (res@[id1,id2])
  in
  helper non_emps []

let prune_comps comps prune_brs=
  let rec partition_helper brs res=
    match brs with
      | [] -> res
      | (r,ls)::rest->
            let same,rems = List.partition (fun (r1,_) -> r1=r) rest in
            let ls1 = List.fold_left (fun res (_,ls1) -> res@ls1) ls same in
            partition_helper rems (res@[(r,remove_dups_int ls1)])
  in
  let do_prune prune_brs (r,chains)=
    try
      let ls_prune = List.assoc r prune_brs in
      let new_chains = List.filter (fun (r_n,_,_) -> not (List.mem r_n ls_prune) ) chains in
      (r,new_chains)
    with Not_found -> (r,chains)
  in
  let prune_brs = partition_helper prune_brs [] in
  List.map (do_prune prune_brs) comps

let rec force_loop_helper_x vertexs ls_adjg1 ls_adj1 ls_non_emp grps=
  (*from var to id for ls_non_emp*)
  let is_conflict,non_emps0 = build_hv_non_emps vertexs ls_non_emp in
  if is_conflict then (true, grps, vertexs, ls_adjg1, ls_adj1) else
    let new_emps_and_prunes =
      List.fold_left (fun ls1 grp ->
          let eqs = (force_spatial non_emps0 grp) in
          (ls1@eqs)
      )
          ([]) grps
    in
    (* let pr0 = pr_list string_of_int in *)
    (* let pr1 = pr_list (pr_triple string_of_int pr0 pr0) in *)
    (* let () = Debug.info_pprint (" new_emps_and_prunes " ^ (pr1 new_emps_and_prunes ) ) no_pos in *)
    if new_emps_and_prunes = [] then (false,  grps, vertexs,ls_adjg1,ls_adj1) else
      let new_emps, prune_brs = List.fold_left (fun (ls1,ls2) (r,svl, brs) ->
          (ls1@[(r,svl)], ls2@[(r,brs)])
      )
        ([],[]) new_emps_and_prunes in
      (*batch update vertexs adjs*)
      (*todo: should use revert abs function*)
      (*todo: find_close of new_emps*)
      let new_vertexs, new_adjsg1, new_adjs1 = merge_emp_chains vertexs ls_adjg1 ls_adj1 new_emps in
      (* let new_comps = prune_comps grps prune_brs in *)
      let _,sccs,topo_order = build_scc (new_adjsg1@new_adjs1) in
      let new_comps = build_comps sccs topo_order  new_adjsg1 new_adjs1 in
      let new_comps = List.filter (fun (_,chains) -> List.length chains > 1) new_comps in
      (* (false,  new_comps, new_vs, new_adjsg1, new_adjs1) *)
      (* let () = Debug.info_pprint (" loop: rule 2-3" ) no_pos in *)
      force_loop_helper new_vertexs new_adjsg1 new_adjs1 ls_non_emp new_comps
          (*dont need to loop*)
          (* if new_emps1 = [] then *)
          (*     (\*quick check conflict on emp abs*\) *)
          (*     cur_emps *)
          (*   else loop_helper (cur_emps@new_emps1) new_grps *)

and force_loop_helper vertexs ls_adjg1 ls_adj1 ls_non_emp grps =
  let pr0 = pr_list string_of_int in
  let pr1 = pr_list print_hv in
  let pr2 = pr_list print_adj in
  let pr3 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
  let pr4 = pr_list (pr_pair string_of_int (pr_list (pr_triple string_of_int pr0 pr0))) in
  Debug.no_5 "force_loop_helper" pr1 pr2 pr2 pr3 pr4 (pr_penta string_of_bool pr4 pr1 pr2 pr2)
      (fun _ _ _ _ _ -> force_loop_helper_x vertexs ls_adjg1 ls_adj1 ls_non_emp grps )
      vertexs ls_adjg1 ls_adj1 ls_non_emp grps

(* let force_no_dups vertexs ls_adjg1 ls_adj1 ls_non_emp comps= *)
(*  let is_conflict, is_changed, new_comps, vertexs1, ls_adjg12, lsadj12 = *)
(*     (\* if is_changed then *\) *)
(*     force_loop_helper vertexs ls_adjg1 ls_adj1 ls_non_emp comps *)
(*     (\* else *\) *)
(*     (\*   (false, vertexs0, ls_adjg11, ls_adj11) *\) *)
(*  in *)
(*  if is_changed then *)
(*    force_no_dups vertexs1 ls_adjg12 lsadj12 ls_non_emp new_comps *)
(*  else *)
(*    (is_conflict, new_comps, vertexs1, new_adjsg12, new_adjs12) *)

(************************************************************************)
            (*******************END RULE FOCRE******************)
(************************************************************************)
let build_emp vertex must_diffs=
  let rec check_conflict aset ls_diff=
    match ls_diff with
      | [] -> false
      | (sv1,sv2)::rest -> if CP.mem_svl sv1 aset && CP.mem_svl sv2 aset then
          (* let () = Debug.info_pprint (" sv1: "^ (!CP.print_sv sv1)) no_pos in *)
          (* let () = Debug.info_pprint (" sv2: "^ (!CP.print_sv sv2)) no_pos in *)
          true
        else check_conflict aset rest
  in
  let rec build_eqs aset res=
    match aset with
      | [] -> res
      | sv1::rest -> build_eqs rest (res@(List.map (fun sv -> (sv1,sv)) rest))
  in
  let process_one hv=
    if List.length hv.hv_lbl < 2 then (false,[])
    else
      let b = check_conflict hv.hv_lbl must_diffs in
      if b then (b,[])
      else (b, build_eqs hv.hv_lbl [])
  in
  let rec helper hvs res=
    match hvs with
      | [] -> false,res
      | hv::rest ->
            let is_conflict,eqs = process_one hv in
            if is_conflict then (true, res@eqs) else
              helper rest (res@eqs)
  in
  helper vertex []

let rec force_inter_predicate_rules vertexs ls_adjg1 ls_adj1 ls_non_emp=
  let is_changed, vertexs0, ls_adjg11, ls_adj11, comps = force_no_distinct_loop vertexs ls_adjg1 ls_adj1 in
  let is_conflict,non_emps0 = build_hv_non_emps vertexs0 ls_non_emp in
  if is_conflict then (true, comps, vertexs, ls_adjg1, ls_adj1) else
    let new_emps_and_prunes =
      List.fold_left (fun ls1 grp ->
          let eqs = (force_spatial non_emps0 grp) in
          (ls1@eqs)
      ) [] comps
    in
    let pr0 = pr_list string_of_int in
    let pr1 = pr_list (pr_triple string_of_int pr0 pr0) in
    let () = Debug.ninfo_pprint (" new_emps_and_prunes " ^ (pr1 new_emps_and_prunes ) ) no_pos in
    if new_emps_and_prunes = [] then (false,  comps, vertexs0,ls_adjg11,ls_adj11) else
      let new_emps, prune_brs = List.fold_left (fun (ls1,ls2) (r,svl, brs) ->
          (ls1@[(r,svl)], ls2@[(r,brs)])
      )
        ([],[]) new_emps_and_prunes in
      (*batch update vertexs adjs*)
      (*todo: should use revert abs function*)
      (*todo: find_close of new_emps*)
      let new_vertexs, new_adjsg1, new_adjs1 = merge_emp_chains vertexs0 ls_adjg11 ls_adj11 new_emps in
      (* let _,sccs,topo_order = build_scc (new_adjsg1@new_adjs1) in *)
      (* let new_comps = build_comps sccs topo_order new_adjsg1 new_adjs1 in *)
      (* let new_comps = List.filter (fun (_,chains) -> List.length chains > 1) new_comps in *)
      (* let () = Debug.info_pprint (" loop: rule 2-3-4" ) no_pos in *)
      force_inter_predicate_rules new_vertexs new_adjsg1 new_adjs1 ls_non_emp

(*
  more complete with case split
  find a vertex v1 point to two diff vertexs v2, v3. case split
  v1 = v2 or v1 = v3
*)
let find_case_split_x vertexs ls_adjg1 ls_adj1 ls_must_diff=
  let rec find ls_adj_pto_2 ls_must_diff0=
    match ls_must_diff0 with
      | [] -> raise Not_found
      | (v_id1, v_id2)::rest -> begin
            let ls = [v_id1;v_id2] in
            try let a = List.find (fun a ->
                Gen.BList.difference_eq (=) ls a.a_nexts = []
            ) ls_adj_pto_2 in
            a
            with _ -> find ls_adj_pto_2 rest
        end
  in
  let look_up_split_cand ls_adj_pto_2=
    let ls_must_diff_ids = List.map (fun (sv1, sv2) ->
        (look_up_vertex sv1 vertexs, look_up_vertex sv2 vertexs)
    ) ls_must_diff in
    find ls_adj_pto_2 ls_must_diff_ids
  in
  if ls_must_diff = [] then [] else
    let ls_adj_pto_2 = List.filter (fun a -> List.length a.a_nexts = 2) ls_adjg1 in
    if ls_adj_pto_2 = [] then [] else begin
      try
        let cand_a = look_up_split_cand ls_adj_pto_2 in
        List.map (fun id -> (cand_a.a_root, id)) cand_a.a_nexts
      with _ -> []
    end

let find_case_split vertexs ls_adjg1 ls_adj1 ls_must_diff=
  let pr1 = pr_list print_hv in
  let pr2 = pr_list print_adj in
  let pr3 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
  let pr4 = pr_list (pr_pair string_of_int string_of_int) in
  Debug.no_3 "find_case_split" pr1 pr2 pr3 pr4
      (fun _ _ _ -> find_case_split_x vertexs ls_adjg1 ls_adj1 ls_must_diff)
      vertexs ls_adjg1  ls_must_diff

(*
  (new_comps, vertexs1, ls_adjg12, lsadj12,ls_adj0)
*)
let norm_graph_x ls_may_eq ls_must_eq ls_must_diff set_ptos do_case_split=
  (******************************************)
  (* edges and ls_adj0: never be updated
  *)
  let rec loop_helper case_split_count vertexs edges ls_adjg1 ls_adj1 ls_adj0=
    let ((is_conflict, new_comps, vertexs1, ls_adjg12, ls_adj12) as res) = force_inter_predicate_rules
      vertexs ls_adjg1 ls_adj1 ls_must_diff in
    if is_conflict then
      let final_graph =  mk_hgraph new_comps vertexs1 edges ls_adjg12 ls_adj12 ls_adj0 [] in
      (true, [],final_graph)
    else
      (*************************************)
      (********build return value for entailment*********)
      let build_graph_for_sat (is_conflict0,new_comps0, vertexs0, ls_adjg10, ls_adj10) =
        let n_edges, non_tough_edges = if set_ptos then
          let edges1 = List.filter (fun e -> (List.exists (fun v -> v.hv_id = e.he_b_id) vertexs0) &&
              List.exists (fun v -> v.hv_id = e.he_e_id) vertexs0) edges in
          set_pto_edges vertexs0 edges1 ls_must_diff
        else edges,[]
        in
        (*build emp from vertexs*)
        let is_conflict, final_emps = build_emp vertexs1 ls_must_diff in
        let final_graph =  mk_hgraph new_comps vertexs0 n_edges ls_adjg10 ls_adj10 ls_adj0 non_tough_edges in
        (is_conflict0, final_emps,final_graph)
      in
      (************************************************)
      (* for each case, combine present eq with current context and try to move fwd*)
      let rec perform_case_split eqs ((is_conflict0,new_comps0, vertexs0, ls_adjg10, ls_adj10) as global_res)=
        match eqs with
          | [] ->  build_graph_for_sat (true,new_comps0, vertexs0, ls_adjg10, ls_adj10)
          | eq::rest ->
                let new_vertexs, new_adjg1, new_adj1 = merge_alias_hv vertexs0 ls_adjg10 ls_adj10 [eq] in
                let is_conflict1,_,_ = loop_helper (case_split_count+1) new_vertexs edges new_adjg1 new_adj1 ls_adj0 in
                if not is_conflict1 then
                  build_graph_for_sat global_res
                else perform_case_split rest global_res
      in
      (*************************************)
      if do_case_split && case_split_count<1 then
        let eqs = find_case_split vertexs1 ls_adjg12 ls_adj12 ls_must_diff in
        if eqs = [] then
           build_graph_for_sat res
        else perform_case_split eqs res
      else
         build_graph_for_sat res
        (* let n_edges, non_tough_edges = if set_ptos then *)
        (*   let edges1 = List.filter (fun e -> (List.exists (fun v -> v.hv_id = e.he_b_id) vertexs1) && *)
        (*       List.exists (fun v -> v.hv_id = e.he_e_id) vertexs1) edges in *)
        (*   set_pto_edges vertexs1 edges1 ls_must_diff *)
        (* else edges,[] *)
        (* in *)
        (* (\*build emp from vertexs*\) *)
        (* let is_conflict, final_emps = build_emp vertexs1 ls_must_diff in *)
        (* let final_graph =  mk_hgraph new_comps vertexs1 n_edges ls_adjg12 lsadj12 ls_adj0 non_tough_edges in *)
        (* (is_conflict, final_emps,final_graph) *)
  in
  (******************************************)
  let vertexs, ini_maps = build_init_ls_vertex ls_may_eq ls_must_eq in
  let edges = build_init_edges ls_may_eq ini_maps in
  let ls_adjg1,ls_adj1,ls_adj0 = build_ls_adj edges in
  (* let ls_must_eq0 = transform ls_must_eq ini_maps in *)
  (* let is_changed, vertexs0, ls_adjg11, ls_adj11, comps = force_no_distinct_loop vertexs ls_adjg1 ls_adj1 in *)
  (* let is_conflict, new_comps, vertexs1, ls_adjg12, lsadj12 = *)
  (*   (\* if is_changed then *\) *)
  (*   force_loop_helper vertexs0 ls_adjg11 ls_adj11 ls_must_diff comps *)
  (*   (\* else *\) *)
  (*   (\*   (false, vertexs0, ls_adjg11, ls_adj11) *\) *)
  (* in *)
  (****************************************************)
  (* Loc: the following is put into  loop_helper *)
  loop_helper 0 vertexs edges ls_adjg1 ls_adj1 ls_adj0
  (* let is_conflict, new_comps, vertexs1, ls_adjg12, lsadj12 = force_inter_predicate_rules *)
  (*    vertexs ls_adjg1 ls_adj1 ls_must_diff in *)
  (* if is_conflict then *)
  (*   let final_graph =  mk_hgraph new_comps vertexs1 edges ls_adjg12 lsadj12 ls_adj0 [] in *)
  (*   (true, [],final_graph) *)
  (* else *)
  (*   let n_edges, non_tough_edges = if set_ptos then *)
  (*     let edges1 = List.filter (fun e -> (List.exists (fun v -> v.hv_id = e.he_b_id) vertexs1) && *)
  (*         List.exists (fun v -> v.hv_id = e.he_e_id) vertexs1) edges in *)
  (*     set_pto_edges vertexs1 edges1 ls_must_diff *)
  (*   else edges,[] *)
  (*   in *)
  (*   (\*build emp from vertexs*\) *)
  (*   let is_conflict, final_emps = build_emp vertexs1 ls_must_diff in *)
  (*   let final_graph =  mk_hgraph new_comps vertexs1 n_edges ls_adjg12 lsadj12 ls_adj0 non_tough_edges in *)
  (*   (is_conflict, final_emps,final_graph) *)
  (****************************************************)

let norm_graph ls_may_eq ls_must_eq ls_must_diff set_ptos do_case_split=
  let pr1 = pr_list (pr_pair !CP.print_sv !CP.print_sv) in
  let pr2 =  print_hgraph in
  Debug.no_4 "norm_graph" pr1 pr1 pr1 string_of_bool (pr_triple string_of_bool pr1 pr2)
      (fun _ _ _ _ -> norm_graph_x ls_may_eq ls_must_eq ls_must_diff set_ptos do_case_split)
      ls_may_eq ls_must_eq ls_must_diff do_case_split

(****************************************************************)
    (*********************homomorphism**********************)
(****************************************************************)

(*
  h: hg1 --> hg2
  find map from hg2 of each vertex of hg1
  map(v1,v2): v1.lbl is subset of v2.lbl
*)

let find_homo_vertex_map_x vs01 vs02=
  (*******************************************)
  let rec look_up_homo_vertex vs2 v1 rest_vs2=
    match vs2 with
      | [] -> raise Not_found
      | v2::rest -> if CP.diff_svl v1.hv_lbl v2.hv_lbl = [] then
            ((v1.hv_id, v2.hv_id), rest_vs2@rest)
        else look_up_homo_vertex rest v1 (rest_vs2@[v2])
  in
  (*******************************************)
  if List.length vs02 < List.length vs01 then (false, [], vs02) else
    begin
      try
        let vertex_map, frame_vertex = List.fold_left (fun (map,rest_vs2) v1->
            let emap, rest_vs2 = look_up_homo_vertex rest_vs2 v1 [] in
            (map@[emap], rest_vs2)
        ) ([], vs02) vs01
        in
        (true, vertex_map, frame_vertex)
      with Not_found -> false,[], vs02
    end

let find_homo_vertex_map vs01 vs02=
  let pr1 = pr_list print_hv in
  let pr2 = pr_list (pr_pair string_of_int string_of_int) in
  Debug.no_2 "find_homo_vertex_map" pr1 pr1 (pr_triple string_of_bool pr2 pr1)
      (fun _ _ -> find_homo_vertex_map_x vs01 vs02) vs01 vs02

(*
  - for each non pto edge og h1, find a corr. path pi of h2
   and nontouch checking for each edge of pi
  - lemma synthesis checking here (todo)
*)

let rec subst sst id=
  match sst with
    | (id1,id2)::rest -> if id1 = id then id2
      else subst rest id
    | [] -> id

let check_homo_edges_x map non_touch_check hg_src hg_tar src_cycle_edges tar_touch_sccs=
   let check_direct_loop = tar_touch_sccs != [] in
  (*******************************)
  (*waiting = (v1...vi * vi) list *)
  let rec dfs_pair e waiting done_vs=
    match waiting with
      | (path, v)::rest -> (*v != e*)
            let v_children = look_up_children v hg_tar.hg_adjg2 hg_tar.hg_adj1 hg_tar.hg_adj0 in
            if List.mem e  v_children then
              (true, path@[(v,e)])
            else
              let not_trav = Gen.BList.difference_eq (=) v_children done_vs in
              let path_children = List.map (fun v_child -> (path@[(v,v_child)], v_child)) not_trav in
              dfs_pair e (path_children@rest) (done_vs@not_trav)
      | [] -> false,[]
  in
  let get_non_touch_constr_from_pto edges (b_id,e_id)=
    let e = look_up_edge edges b_id e_id in
    if e.he_kind then [(b_id)] else []
  in
  let check_non_touch tar_non_touch required_b_non_touch_ids e_non_touch_id=
    let b_non_touch_ids = List.fold_left (fun r (b_id, e_id)->
        if e_id = e_non_touch_id then r@[b_id] else r
    ) [] tar_non_touch in
    Gen.BList.difference_eq (=) required_b_non_touch_ids b_non_touch_ids = []
  in
  (* three conditions:
     if (b_id, e_id) is a pto
     if required_touch then false else
      - (e_id, b_id) is non-touch also (if exist an edge, this edge is also pto)
      - (b_id, tar_e_seg) is non-touch (..)
      - (tar_e_seg, b_id)
  *)
  let is_non_touch_two_way_pto tar_edges tar_e_seg (b_id, e_id)=
    let () = Debug.ninfo_hprint (add_str "(b_id, e_id)" ((pr_pair string_of_int string_of_int))) (b_id, e_id) no_pos in
    let e = look_up_edge tar_edges b_id e_id in
    if e.he_kind then
      let pto_nontouch =
        try
          (*if exist an rev, it should be non-touch also: a!=b <-> b!=a *)
          let rev_e = look_up_edge tar_edges e_id b_id in
          rev_e.he_kind
        with _ -> (*not exist is OK*) true
      in
      let () = Debug.ninfo_hprint (add_str "pto_nontouch" string_of_bool) pto_nontouch no_pos in
      if pto_nontouch then
        try
          let () = Debug.ninfo_hprint (add_str "exam seg: tar_e_seg" string_of_int) tar_e_seg no_pos in
          (* (tar_e_seg, b_id) is non_touch also*)
          let seg_e = look_up_edge tar_edges tar_e_seg b_id in
          seg_e.he_kind
        with _ -> (*not exist is OK*) true
      else
        pto_nontouch
    else true
  in
  let is_non_touch_two_way tar_edges tar_e_seg (b_id, e_id)=
    let () = Debug.ninfo_hprint (add_str "(b_id, e_id)" ((pr_pair string_of_int string_of_int))) (b_id, e_id) no_pos in
    let e = look_up_edge tar_edges b_id e_id in
    if e.he_kind then
      let pto_nontouch =
        try
          (*if exist an rev, it should be non-touch also: a!=b <-> b!=a *)
          let rev_e = look_up_edge tar_edges e_id b_id in
          rev_e.he_kind
        with _ -> (*not exist is OK*) true
      in
       pto_nontouch
    else
      true
  in
  let rec is_touchable path edges=
    match path with
      | [] -> false (* true *) (*all edge are touchable*)
      | (b,e)::rest ->
            let e = look_up_edge edges b e in
            if e.he_kind then is_touchable rest edges else true
            (* if e.he_kind then false else is_touchable rest edges *)
  in
  let rec look_up_touch_edges edges vs res=
    match vs with
      | [] -> res
      | v::rest ->
            let e_vs = look_up_end_of_edges edges v in
            look_up_touch_edges edges rest (res@e_vs)
  in
  let consistent_two_way_touch fwd_path tar_edges src_edges fwd_edge rev_edge=
    let rev_tar_b = subst map rev_edge.he_b_id in
    let rev_tar_e = subst map rev_edge.he_e_id in
    let has_rev_path, rev_path = dfs_pair rev_tar_e [([], rev_tar_b)] [rev_tar_e] in
    if not has_rev_path then false else
      let fwd_touchable = is_touchable fwd_path tar_edges in
      let rev_touchable = is_touchable rev_path tar_edges in
      let () = Debug.ninfo_hprint (add_str "fwd_touchable" (string_of_bool)) fwd_touchable no_pos in
      let () = Debug.ninfo_hprint (add_str "rev_touchable" (string_of_bool)) rev_touchable no_pos in
      ((not fwd_edge.he_kind) && (not rev_edge.he_kind) &&
          ((fwd_touchable && rev_touchable)|| (not fwd_touchable && not rev_touchable)))
      (*11-01*)
      (* let both_non_touch = not fwd_touchable && not rev_touchable in *)
      (* let is_consistent = ((not fwd_edge.he_kind) && (not rev_edge.he_kind) && *)
      (*     ((fwd_touchable && rev_touchable)|| both_non_touch)) *)
      (* in *)
      (* if not is_consistent then false else *)
      (*   if both_non_touch then *)
      (*     let touch_edges = look_up_touch_edges src_edges [rev_edge.he_b_id;rev_edge.he_e_id] [] in *)
      (*     let () = Debug.info_hprint (add_str "touch_edges" (pr_list print_he)) touch_edges no_pos in *)
      (*     touch_edges = [] *)
      (*   else true *)
      (*end 11-01*)
  in
  (*for each edge of src*)
  let check_one_src_edge_old_x sedge=
    (*map to id of tar edge*)
    let tar_b = subst map sedge.he_b_id in
    let tar_e = subst map sedge.he_e_id in
    if sedge.he_kind then
       (* if it is pto: check tar edge is a pto*)
      let tedge = look_up_edge hg_tar.hg_edges tar_b tar_e in
      (tedge.he_kind, [])
    else
      (*otherwise: check it is a path pi*)
      let has_path, path = dfs_pair tar_e [([], tar_b)] [tar_e] in
      if not has_path then (false,[]) else
        let () = Debug.ninfo_hprint (add_str "path" (pr_list (pr_pair string_of_int string_of_int))) path no_pos in
        if not non_touch_check then (true,path) else
          (*has cycle -touchable*)
          let has_cycle, scc =
            if tar_touch_sccs = [] then (false,[]) else
              try
                let path_vertexs = match path with
                  | [] -> []
                  | (id1,id2)::rest -> id1::(List.map (fun (_,id) -> id) path)
                in
                let () = Debug.ninfo_hprint (add_str "path_vertexs" (pr_list string_of_int)) path_vertexs no_pos in
                let inter_scc = List.find (fun scc -> (Gen.BList.difference_eq (=) scc path_vertexs) = [] ) tar_touch_sccs in
                let () = Debug.ninfo_hprint (add_str " inter_scc" (pr_list string_of_int)) inter_scc no_pos in
                let is_touch = inter_scc != [] &&
                  (*at least one pto*)
                   List.exists (fun a -> (get_non_touch_constr_from_pto hg_tar.hg_edges a) !=[]) path
                in
                (is_touch,inter_scc)
              with _ -> (false,[])
          in
          if has_cycle then
            let () = Debug.ninfo_hprint (add_str "has cycle" (pr_list string_of_int)) scc no_pos in
            (false,path)
          else
            (*if non_touch is enable, all edge of pi must be pto*)
            (* let required_tar_non_touch_b_ids = List.fold_left (fun r (b_id,e_id) -> *)
            (*     r@(get_non_touch_constr_from_pto hg_tar.hg_edges (b_id,e_id)) *)
            (* ) [] path in *)
            (* let () = Debug.info_hprint (add_str "required_tar_non_touch_b_ids" (pr_list string_of_int)) required_tar_non_touch_b_ids no_pos in *)
            (*  let is_non_touch = check_non_touch hg_tar.hg_non_touch_edges required_tar_non_touch_b_ids tar_e in *)
            let check_rev =
              try
                let todo_unk = look_up_edge hg_src.hg_edges sedge.he_e_id sedge.he_b_id in
                true
              with _ -> false
            in
            let is_non_touch = if check_rev then
              List.for_all (fun (b_id, e_id) ->
                  (is_non_touch_two_way_pto hg_tar.hg_edges tar_e (b_id, e_id))
              ) path
            else true
            in
            (* let is_non_touch = true in *)
            let () = Debug.ninfo_hprint (add_str "is_non_touch" string_of_bool) is_non_touch no_pos in
            if not is_non_touch then (false,path) else
              (* cycle in conseq: sedge and its inversion have the same feature: touch and non-touch.*)
              let required_touch = List.exists (fun (b_id,e_id) ->
                  b_id = sedge.he_b_id && e_id = sedge.he_e_id) src_cycle_edges in
              let () = Debug.ninfo_hprint (add_str "required_touch" string_of_bool) required_touch no_pos in
              let direct_loop = required_touch && ( List.exists (fun (b_id,e_id) ->
                b_id = sedge.he_e_id && e_id = sedge.he_b_id) src_cycle_edges)
              in
              if not direct_loop then (true,path) else begin
                try
                  let rev_edge = look_up_edge hg_src.hg_edges sedge.he_e_id sedge.he_b_id in
                  let cons_two_way = consistent_two_way_touch path hg_tar.hg_edges hg_src.hg_edges sedge rev_edge in
                  let () = Debug.ninfo_hprint (add_str "cons_two_way" string_of_bool) cons_two_way no_pos in
                  (cons_two_way,path)
                with Not_found -> (true,path)
              end
  in
  (*waiting = (v1...vi * vi) list *)
  let rec dfs e waiting done_vs=
    match waiting with
      | (path, v)::rest -> (*v != e*)
            let v_children = look_up_children v hg_tar.hg_adjg2 hg_tar.hg_adj1 hg_tar.hg_adj0 in
            if List.mem e v_children then
              (true, path@[e])
            else
              let not_trav = Gen.BList.difference_eq (=) v_children done_vs in
              let path_children = List.map (fun v_child -> (path@[(v_child)], v_child)) not_trav in
              dfs e (path_children@rest) (done_vs@not_trav)
      | [] -> false,[]
  in
  let has_non_emp_path path=
    List.exists (fun (b,e) ->
        let tedge = look_up_edge hg_tar.hg_edges b e in
        tedge.he_kind
    ) path
  in
  let has_non_emp_src_path src_e=
    let tar_b = subst map src_e.he_b_id in
    let tar_e = subst map src_e.he_e_id in
    let has_path, path = dfs_pair tar_e [([], tar_b)] [tar_e] in
    if not has_path then false
    else
      (*check whether at least one non empty*)
       has_non_emp_path path
           (*  List.exists (fun (b,e) -> *)
           (*     let tedge = look_up_edge hg_tar.hg_edges b e in *)
           (*     tedge.he_kind *)
           (* ) path *)
  in
  let has_non_emp_src_path1 tar_b tar_e=
    let has_path, path = dfs_pair tar_e [([], tar_b)] [tar_e] in
    if not has_path then raise Not_found
    else
      (*check whether at least one non empty*)
      has_non_emp_path path
  in
  let rec find_first_non_emp waiting done_vertexs=
    let () = Debug.ninfo_hprint (add_str "waiting" (pr_list string_of_int)) waiting no_pos in
    let () = Debug.ninfo_hprint (add_str "done_vertexs" (pr_list string_of_int)) done_vertexs no_pos in
    match waiting with
      | [] -> false
      | e::rest -> begin
            let () = Debug.ninfo_hprint (add_str "last" string_of_int) e no_pos in
            let next_edges = look_up_next_edges hg_tar.hg_edges e in
            try
              let e = List.find (fun e -> e.he_kind) next_edges in
              true
            with _ ->
                (*remove vertexes which travesed*)
                let next_edges_wo = List.filter (fun e ->
                    not (Gen.BList.mem_eq (=) e.he_e_id done_vertexs)) next_edges in
                find_first_non_emp (rest@(List.map (fun e -> e.he_e_id) next_edges_wo)) (done_vertexs@[e])
        end
  in
  (*
    rule 1: break the rhs (a,b) if the lhs is (a,c) * (c,b) * (b,d) and
    (b !=d)
  *)
  let check_valid_unfold_rhs sedge path=
    if List.length path = 1 then
      (*do not need unfold rhs*)
      (*short cut to check direct loop in target*)
      if non_touch_check && check_direct_loop then
        let (tar_b, tar_e) = List.hd path in
        try
          let tar_edge = look_up_edge hg_tar.hg_edges tar_b tar_e in
          let rev_tar_edge = look_up_edge hg_tar.hg_edges tar_e tar_b in
          let non_empty_direct_loop = (tar_edge.he_kind && rev_tar_edge.he_kind) in
          let empty_direct_loop = (not tar_edge.he_kind && not rev_tar_edge.he_kind) in
          let consis_direct = non_empty_direct_loop || empty_direct_loop in
          let () = Debug.ninfo_hprint (add_str "consis_direct 1" string_of_bool) consis_direct no_pos in
          consis_direct
        with _ -> true
      else true
    else if not non_touch_check then (true) else
      begin
        (* let (_,last_tar_e_edge) = Gen.BList.list_last path in *)
        let done_vs,last_tar_e_edge = List.fold_left (fun (r,last) (b,e) -> (r@[b],e)) ([], snd (List.hd path)) (List.tl path) in
        let is_valid(* , nexte_opt *) = find_first_non_emp [last_tar_e_edge] (done_vs) in
        is_valid
      end
  in
  let check_two_way_may_emp_tar_paths sedge tar_path=
    (*rev:*)
    let tar_b = sedge.he_e_id in
    let tar_e = sedge.he_b_id in
    let has_rev_path, rev_path = dfs_pair tar_e [([], tar_b)] [tar_e] in
    if not has_rev_path then true
    else
      let non_emp = has_non_emp_path tar_path in
      let rev_non_emp = (has_non_emp_path rev_path) in
      ((non_emp && rev_non_emp) || (not non_emp && not rev_non_emp))
  in
  (*rule 2:
    if has direct loop, both mapping of src_paths must be non empty
  *)
  let check_non_empty_direct_loop_x sedge tar_path=
    if not non_touch_check || not check_direct_loop then (true) else
      try
        let rev_edge = look_up_edge hg_src.hg_edges sedge.he_e_id sedge.he_b_id in
        if List.exists (fun (b,e) ->
            let tedge = look_up_edge hg_tar.hg_edges b e in
            tedge.he_kind
        ) tar_path then
          let rev_valid = has_non_emp_src_path rev_edge in
          rev_valid
        else
          (* 15-02: two are non pto (maybe) *)
          let rev_valid = has_non_emp_src_path rev_edge in
          let r = not rev_valid in
           (* rule 4: 10-01*)
          (**if they are direct loop, they should be isolated. 10-01 *)
          if not r then r else
            begin
              match tar_path with
                | [(b,e)] -> begin
                    try
                      let rev_tar = look_up_edge hg_tar.hg_edges e b in
                      let tar = look_up_edge hg_tar.hg_edges b e in
                      if not tar.he_kind && not rev_tar.he_kind then
                        let com_edges1 = look_up_coming_edges hg_tar.hg_edges b in
                        if List.length com_edges1 = 1 then
                          let com_edges2 = look_up_coming_edges hg_tar.hg_edges e in
                          List.length com_edges2 = 1
                        else false
                      else r
                    with _ -> r
                    end
                | _ -> r
            end
      with _ ->  (*dont have direct path 16-02*)
          begin
            match tar_path with
              | [(tar_b, tar_e)] -> begin
                  try
                    let tar_edge = look_up_edge hg_tar.hg_edges tar_b tar_e in
                    let rev_non_emp = has_non_emp_src_path1 tar_e tar_b in
                    let non_empty_direct_loop = (tar_edge.he_kind && rev_non_emp) || (not tar_edge.he_kind && not rev_non_emp) in
                    let () = Debug.ninfo_hprint (add_str "non_empty_direct_loop 2" string_of_bool) non_empty_direct_loop no_pos in
                    non_empty_direct_loop
                  with _ -> true
                end
              | _ -> true
          end
  in
  let check_non_empty_direct_loop sedge tar_path=
    let pr1 = print_he in
    let pr2 = pr_list (pr_pair string_of_int string_of_int) in
    Debug.no_2 "check_non_empty_direct_loop" pr1 pr2 string_of_bool
        (fun _ _ -> check_non_empty_direct_loop_x sedge tar_path)
        sedge tar_path
  in
  let check_one_src_edge_x sedge=
    (*map to id of tar edge*)
    let tar_b = subst map sedge.he_b_id in
    let tar_e = subst map sedge.he_e_id in
    if sedge.he_kind then
      try
        (* if it is pto: check tar edge is a pto*)
        let tedge = look_up_edge hg_tar.hg_edges tar_b tar_e in
        (tedge.he_kind, [])
      with _ -> (false,[])
    else
      (*otherwise: check it is a path pi*)
      let has_path, path = dfs_pair tar_e [([], tar_b)] [tar_e] in
      if not has_path then (false,[]) else
        let () = Debug.ninfo_hprint (add_str "path" (pr_list (pr_pair string_of_int string_of_int))) path no_pos in
        (*rule 1*)
        let valid_rhs_unfold = check_valid_unfold_rhs sedge path in
        let () = Debug.ninfo_hprint (add_str " valid_rhs_unfold" string_of_bool) valid_rhs_unfold no_pos in
        if not valid_rhs_unfold then (valid_rhs_unfold, path) else
          let valid_direct_loop = check_non_empty_direct_loop sedge path in
          let () = Debug.ninfo_hprint (add_str "valid_direct_loop" string_of_bool) valid_direct_loop no_pos in
          (valid_direct_loop, path)
  in
  (******************)
  let check_one_src_edge sedge=
    let pr1 = print_he in
    let pr2 = pr_list (pr_pair string_of_int string_of_int) in
    (* let pr3 = pr_list_ln (pr_pair pr1 pr2) *)
    Debug.no_1 "check_one_src_edge" pr1 (pr_pair string_of_bool pr2)
        (fun _ -> check_one_src_edge_x sedge) sedge
  in
  (******************)
  let rec loop_helper sedges acc_sedges_path=
    match sedges with
      | [] -> true,acc_sedges_path
      | sedge::rest -> let b, path = check_one_src_edge sedge in
        if b then
          loop_helper rest (acc_sedges_path@[(sedge,path)])
        else (false,acc_sedges_path)
  in
  (******************)
  (*testcase: ?*)
  let rec check_non_overlap_paths map_sedge_paths=
    match map_sedge_paths with
      | [_] -> true
      | (_,path1)::rest ->
            let () = Debug.ninfo_hprint (add_str "path1" (pr_list (pr_pair string_of_int string_of_int) )) path1 no_pos in
            if List.exists (fun (_,path2) ->
                let () = Debug.ninfo_hprint (add_str "path2" (pr_list (pr_pair string_of_int string_of_int) )) path2 no_pos in
                List.exists (fun id -> List.mem id path2) path1
            ) rest
            then false
            else check_non_overlap_paths rest
      | [] -> true
  in
  (*******************************)
  (* List.for_all check_one_src_edge hg_src.hg_edges *)
  let b, map_src_edge_path = loop_helper hg_src.hg_edges [] in
  b
  (* if b then *)
  (*   check_non_overlap_paths map_src_edge_path *)
  (* else false *)

let check_homo_edges map non_touch_check hg_src hg_tar src_cycle_edges tar_touch_sccs=
  let pr1 = print_hgraph in
  let pr2 = pr_list (pr_pair string_of_int string_of_int) in
  let pr3 = pr_list_ln (pr_list string_of_int) in
  Debug.no_6 "check_homo_edges" pr2 string_of_bool pr1 pr1
      (pr_list (pr_pair string_of_int string_of_int)) pr3 string_of_bool
      (fun _ _ _ _ _ _ -> check_homo_edges_x map non_touch_check hg_src hg_tar src_cycle_edges tar_touch_sccs)
      map non_touch_check hg_src hg_tar src_cycle_edges tar_touch_sccs


(*
 purpose: is hg_src homomorphism to hg_tar

out:
  - yes/no
  - maping vertexs
  - need to generate lemma wo graph to prove the entailment
*)
let check_homomorphism_x non_touch_check hg_src hg_tar=
  let is_touch src_edges b_id e_id=
    try
      let e = look_up_edge src_edges b_id e_id in
      not e.he_kind
    with _ -> false
  in
  let rec check_loop first_sv cur_sv rest src_edges res=
    match rest with
      | [] ->
            if is_touch src_edges cur_sv first_sv then res@[(cur_sv, first_sv)] else
              []
      | sv1::rest1 ->
            if is_touch src_edges cur_sv sv1 then
               check_loop first_sv sv1 rest1 src_edges (res@[(cur_sv, sv1)])
            else []
  in
  let look_up_touch_chains src_edges scc=
    match scc with
      | [] | [_] -> []
      | v1::v2::rest -> begin
            try
              if not (is_touch src_edges v1 v2) then [] else
                check_loop v1 v2 rest src_edges [(v1,v2)]
            with _ -> []
        end
  in
  (*find vertexs mapping from src to tar*)
  let is_vertex_homo, map, frame_vertex_hg_tar = find_homo_vertex_map hg_src.hg_vertexs hg_tar.hg_vertexs in
  if not is_vertex_homo then (false, []) else
    (* let src_cycle_touch_edges,tar_touch_sccs = if non_touch_check then *)
    (*   let _,src_sccs,_ = build_scc (hg_src.hg_adjg2@hg_src.hg_adj1) in *)
    (*   let src = List.fold_left (fun r scc -> r@(look_up_touch_chains hg_src.hg_edges scc)) [] src_sccs in *)
    (*   let _,tar_sccs,_ = build_scc (hg_tar.hg_adjg2@hg_tar.hg_adj1) in *)
    (*   (\*10-07*\) *)
    (*   let tar_touch_sccs = List.filter (fun scc -> (look_up_touch_chains hg_tar.hg_edges scc) != []) tar_sccs in *)
    (*   let () = Debug.info_hprint (add_str "tar_touch_sccs" (pr_list_ln (pr_list string_of_int))) tar_touch_sccs no_pos in *)
    (*   (src,tar_touch_sccs) *)
    (* else [],[] *)
    (* in *)
    let _,tar_sccs,_ = build_scc (hg_tar.hg_adjg2@hg_tar.hg_adj1) in
    let src_cycle_touch_edges = [] in
    let is_edge_homo = check_homo_edges map non_touch_check hg_src hg_tar src_cycle_touch_edges tar_sccs in
    if not is_edge_homo then (false, map) else
    true,map

let check_homomorphism non_touch_check hg_src hg_tar=
  let pr1 = print_hgraph in
  let pr2 = pr_list (pr_pair string_of_int string_of_int) in
  Debug.no_2 "check_homomorphism" pr1 pr1 (pr_pair string_of_bool pr2)
      (fun _ _ -> check_homomorphism_x non_touch_check hg_src hg_tar) hg_src hg_tar


(****************************************************************)
   (*******************END homomorphism**********************)
(****************************************************************)
