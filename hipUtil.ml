#include "xdebug.cppo"
(* open VarGen *)
open Gen
(* open Basic *)
open Globals

let proc_files = new stack_noexc "proc_files" "__no_file" pr_id (fun s1 s2 -> s1=s2) 

module Name =
struct
  type t = ident
  let compare = compare
  let hash = Hashtbl.hash
  let equal = ( = )
end

module NG = Graph.Imperative.Digraph.Concrete(Name)
module NGComponents = Graph.Components.Make(NG)
module TopoNG = Graph.Topological.Make(NG)
module DfsNG = Graph.Traverse.Dfs(NG)

class graph =
  object (self)
    val mutable nlst = Hashtbl.create 20
    val mutable grp = None
    val mutable sorted_flag = false
    val mutable scc = []
    val mutable posn_lst = []
    val mutable pto = [] (* pt_to rec & non-rec e.g. p->([q],[r])*)
    (* val mutable self_rec = [] (\* those with self-recursive *\) *)
    (* val mutable self_rec_only = [] (\* those with self-recursive call only *\) *)
    (* val mutable mut_rec = [] (\* those in mutual-recursion *\) *)
    val mutable dom = [] 
    val mutable nodes = [] 

    (* let pr = pr_list (pr_pair pr_id (pr_list pr_id)) *)

    method add_node name =
      if (List.exists (fun x -> x=name) nodes) then ()
      else nodes <- name::nodes

    method (* private *) posn name =
      if grp==None then self # build_scc_void "posn";
      let rec find xs n =
        match xs with
        | [] -> (-1)
        | x::xs -> if x=name then n else find xs (n+1)
      in find posn_lst 0

    method scc_posn name =
      (* if grp==None then self # build_scc_void "scc_posn"; *)
      let rec find xss n =
        match xss with
        | [] -> (-1)
        | xs::xss -> if List.exists (fun a -> a=name) xs then n else find xss (n+1)
      in find scc 0

    method get_scc_posn =
      if grp==None then self # build_scc_void "get_scc_posn";
      posn_lst

    method (* private *) compare name1 name2 =
      let n1 = self # scc_posn name1 in
      let n2 = self # scc_posn name2 in
      if n1<n2 then -1
      else if n1=n2 then 0
      else 1

    method reset =
      grp <- None;
      Hashtbl.clear nlst

    method replace s n lst  =
      grp <- None;
      let () = y_tinfo_hp (add_str (s^"replace") ((pr_pair pr_id (pr_list pr_id)))) (n,lst) in
      Hashtbl.replace nlst n lst;
      self # add_node n

    method add s n lst  =
      grp <- None;
      let () = y_tinfo_hp (add_str (s^"add") ((pr_pair pr_id (pr_list pr_id)))) (n,lst) in
      let () = try
          let old = Hashtbl.find nlst n in
          let () = y_tinfo_hp (add_str (s^"old") (((pr_list pr_id)))) (old) in
          Hashtbl.replace nlst n (Gen.BList.remove_dups_eq string_eq (old@lst));
        with _ -> Hashtbl.replace nlst n lst
      in
      self # add_node n

    method set_sorted = 
      if grp==None then self # build_scc_void "get_sorted";
      sorted_flag <- true

    method is_sorted = 
      sorted_flag

    method remove n  =
      grp <- None;
      let () = y_tinfo_hp (add_str "remove" pr_id) n in
      Hashtbl.remove nlst n

    method private fail_exc e m =
      let () = y_winfo_pp ("Unexpected exception "^m) in
      let () = print_endline_quiet (self # string_of) in
      raise e

    method private fail_with m =
      let () = y_winfo_pp ("Unexpected exception "^m) in
      let () = print_endline_quiet (self # string_of) in
      failwith m

    method unfold_in m n = (* unfold m in n *)
      let msg = ("unfold "^m^" in "^n) in
      let () = y_tinfo_pp msg in
      let unchanged lst =
        match lst with
        | [x] -> x=m
        | _ -> false in
      if n="" then ()
      else
        try
          let edges = Hashtbl.find nlst n in
          if (List.exists (fun a -> a=m) edges) then
            let edges_m = Hashtbl.find nlst m in
            let old_e = List.filter (fun e -> not(e=m)) edges in
            let add_e = BList.difference_eq (=) edges_m old_e in
            if unchanged add_e then ()
            else self # replace "" n (add_e@old_e)
          else
            self # fail_with ("unfold cannot find "^m^" in "^n)
        with e -> self # fail_exc e msg

    method exists n  =
      Hashtbl.mem nlst n

    method is_self_rec n  =
      let r = self # find_rec n in
      List.exists (fun v -> n=v) r

    method is_mutual_rec n  =
      let r = self # find_rec n in
      (List.filter (fun v -> not(n=v)) r)!=[]

    (* method is_self_rec_only n  = *)
    (*   if grp==None then self # build_scc_void; *)
    (*   List.exists (fun v -> n=v) self_rec_only *)

    method find_rec n  =
      (* if pto==[] then self # build_scc_void 1; *)
      if grp==None then self # build_scc_void "find_rec";
      try
        snd(List.find (fun (a,_) -> a=n) pto)
      with _ -> []

    method get_trans n = 
      let extend xs =
        List.fold_left (fun acc x ->
            try
              let nx = Hashtbl.find nlst x in
              nx@acc
            with _ -> acc
          ) [] xs in
      if grp==None then self # build_scc_void "get_trans";
      let scc1 = List.rev scc in
      let rec aux scc acc ans =
        match scc with
        | [] -> ans
        | xs::xss -> 
          if (Gen.BList.intersect_eq (=) xs acc)==[] then aux xss acc ans
          else
            let ans = xs@ans in
            let exts = extend xs in
            let acc = Gen.BList.remove_dups_eq (=) (xs@exts@acc) in
            aux xss acc ans
      in aux scc1 [n] []

    method split  =
      (* important : if not may go into stack overflow for *)
      (*  add_uni_vars_to_view, see ex25a1.slk which has mutual-rec views *)
      if grp==None then self # build_scc_void "split";
      let (nrec_n,rec_n) = List.partition (fun (a,r) -> r==[]) pto in
      let (self_r,mut_r) = List.partition (fun (a,r) -> List.exists (fun m -> a=m) r) rec_n in
      (List.map fst nrec_n,List.map fst self_r,List.map fst mut_r)

    method get_rec  =
      let (_,self_r,mut_r) = self # split in
      (self_r,mut_r)

    method is_rec n  =
      (self # find_rec n) != []

    (* called in astsimp.ml *)
    method in_dom n  =
      (* if grp==None then self # build_scc_void 3; *)
      (List.exists (fun v -> n=v) dom)

    method rebuild_scc s  =
      grp <-None;
      self # build_scc s

    method build_scc s  =
      if not(grp==None) then scc
      else
        let () = y_tinfo_pp ("invoking build_scc "^s)  in
        let g = NG.create () in
        let find_posn n = 
          let rec aux xs i =
            match xs with 
            | [] -> -1
            | x::xs -> if x=n then i else aux xs (i+1)
          in aux nodes 0 in
        let alpha_order e1 e2 = 
          match e1,e2 with
          | n1::_,n2::_ -> 
            let p1 = find_posn n1 in
            let p2 = find_posn n2 in
            p2-p1
          | _,_ -> 0 in
        let is_edges s1 s2 =
          List.exists (fun n1 ->
              List.exists (fun n2 ->
                  NG.mem_edge g n1 n2
                ) s2
            ) s1 in
        let order_scc s1 s2 =
          let r = if is_edges s1 s2 then 1
            else if is_edges s2 s1 then -1
            (* below did not account for transitivity *)
            else 0 (* alpha_order s1 s2 *) in
          let pr = pr_list pr_id in
          let () = y_binfo_hp (add_str "order_scc" (pr_triple pr pr string_of_int)) (s1,s2,r) in
          r
        in
        let sort_scc scc =
          let r = List.sort order_scc scc in
          let pr = pr_list (pr_list pr_id) in
          let () = y_binfo_hp (add_str "sort" (pr_pair pr pr)) (scc,r) in
          r in
        (* self_rec <- []; *)
        pto <- [];
        dom <- Hashtbl.fold (fun n xs acc-> n::acc) nlst [];
        let () = Hashtbl.iter (fun n edges ->
            (* if List.exists (fun v -> n=v) edges then self_rec <- n::self_rec; *)
            List.iter (fun t ->
                NG.add_edge g (NG.V.create n) (NG.V.create t)
              ) edges
          ) nlst in
        let scclist = NGComponents.scc_list g in
        (* let scclist = sort_scc scclist in *)
        scc <- scclist;
        posn_lst <- List.concat scclist;
        sorted_flag <- false;
        grp <- Some g;
        pto <- List.concat
            (List.map (fun sc ->
                 List.map (fun m ->
                     try
                       let edges = Hashtbl.find nlst m in
                       let rec_callee = BList.intersect_eq (=) sc edges in
                       (m,rec_callee)
                     with _ ->
                       (m,[])
                       (* begin *)
                       (*   y_winfo_pp "Unexpected exception"; *)
                       (*   print_endline_quiet ("Cannot find :"^m); *)
                       (*   print_endline_quiet (self # string_of); *)
                       (*   failwith "HipUtil.Graph" *)
                       (* end *)
                   ) sc
               ) scclist);
        (* let mutlist = List.filter (fun lst -> (List.length lst)>1) scclist in *)
        (* mut_rec <- List.concat mutlist; *)
        (* self_rec_only <- BList.difference_eq (=) self_rec mut_rec; *)
        scclist

    method build_scc_void n  =
      let scclist = self # build_scc n in
      ()

    method get_scc  =
      match grp with
      | Some _ -> scc
      | None -> self # build_scc "get_scc"

    method get_graph  =
      match grp with
      | Some g -> g
      | None -> 
        let _ = self # build_scc "get_graph" in
        self # get_graph

    method get_graph_lst = 
      Hashtbl.fold (fun n xs acc-> (n,xs)::acc) nlst []

    method string_of  =
      if grp==None then self # build_scc_void "string_of";
      let str = "SCC:"^((pr_list ((pr_list pr_id))) scc) in
      (* let lst = (Hashtbl.fold (fun n xs acc-> (n,xs)::acc) nlst []) in *)
      let lst = self # get_graph_lst in
      let str2 = pr_list (pr_pair pr_id (pr_list pr_id)) lst in
      let str = str^"\nGraph:"^str2 in 
      (* print_endline_quiet *) str
  end;;

let view_scc_obj = new graph;;
let view_args_scc_obj = new graph;;

let data_scc_obj = new graph;;
