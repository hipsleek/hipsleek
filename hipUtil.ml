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
    val mutable scc = []
    val mutable self_rec = [] (* those with self-recursive *)
    val mutable self_rec_only = [] (* those with self-recursive *)
    val mutable mut_rec = [] (* those in mutual-recursion *)
    val mutable dom = [] (* those in mutual-recursion *)

    method reset =
      grp <- None;
      Hashtbl.clear nlst

    method replace n lst  =
      grp <- None;
      Hashtbl.replace nlst n lst

    method remove n  =
      grp <- None;
      Hashtbl.remove nlst n

    method exists n  =
      Hashtbl.mem nlst n

    method is_self_rec n  =
      if grp==None then self # build_scc;
      List.exists (fun v -> n=v) self_rec

    method is_self_rec_only n  =
      if grp==None then self # build_scc;
      List.exists (fun v -> n=v) self_rec_only

    method is_rec n  =
      if grp==None then self # build_scc;
      (self # is_self_rec_only n) || (List.exists (fun v -> n=v) mut_rec)

    method in_dom n  =
      if grp==None then self # build_scc;
      (List.exists (fun v -> n=v) dom)

    method rebuild_scc  =
      let g = NG.create () in
      self_rec <- [];
      let () = Hashtbl.iter (fun n edges ->
          if List.exists (fun v -> n=v) edges then self_rec <- n::self_rec;
          List.iter (fun t ->
              NG.add_edge g (NG.V.create n) (NG.V.create t)
          ) edges
        ) nlst in
      let scclist = NGComponents.scc_list g in
      let mutlist = List.filter (fun lst -> (List.length lst)>1) scclist in
      mut_rec <- List.concat mutlist;
      self_rec_only <- BList.difference_eq (=) self_rec mut_rec;
      grp <- Some g;
      scc <- scclist;
      dom <- Hashtbl.fold (fun n xs acc-> n::acc) nlst [];
      scclist

    method build_scc  =
      let scclist = self # rebuild_scc in
      ()

    method get_scc  =
      match grp with
      | Some _ -> scc
      | None -> self # rebuild_scc

    method get_rec  =
      match grp with
      | Some _ -> (self_rec_only, mut_rec)
      | None -> let () = self # build_scc in
        (self_rec_only, mut_rec)

    method get_graph  =
      match grp with
      | Some g -> g
      | None -> 
        let () = self # build_scc in
        self # get_graph

    method string_of  =
      if grp==None then self # build_scc;
      let str = "SCC:"^((pr_list ((pr_list pr_id))) scc) in
      let lst = (Hashtbl.fold (fun n xs acc-> (n,xs)::acc) nlst []) in
      let str2 = pr_list (pr_pair pr_id (pr_list pr_id)) lst in
      let str = str^"\nGraph:"^str2 in 
      (* print_endline_quiet *) str
   end;;

let view_scc_obj = new graph;;
