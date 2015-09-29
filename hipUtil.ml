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

class graph  =
  object (self)
    val mutable nlst = Hashtbl.create 20
    val mutable gr = None
    val mutable scc = []
    val mutable self_rec = [] (* those with self-recursive *)
    val mutable self_rec_only = [] (* those with self-recursive *)
    val mutable mut_rec = [] (* those in mutual-recursion *)
    method reset =
      gr <- None;
      Hashtbl.clear nlst
    method replace n lst  =
      gr <- None;
      Hashtbl.replace nlst n lst
    method remove n  =
      gr <- None;
      Hashtbl.remove nlst n
    method exists n  =
      Hashtbl.mem nlst n
    method is_self_rec n  =
      if gr==None then self # build_scc;
      List.exists (fun v -> n=v) self_rec
    method is_self_rec_only n  =
      if gr==None then self # build_scc;
      List.exists (fun v -> n=v) self_rec_only
    method is_rec n  =
      if gr==None then self # build_scc;
      (self # is_self_rec_only n) || (List.exists (fun v -> n=v) mut_rec)
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
      gr <- Some g;
      scc <- scclist;
      scclist
    method build_scc  =
      let scclist = self # rebuild_scc in
      ()
    method get_scc  =
      match gr with
      | Some _ -> scc
      | None -> self # rebuild_scc
    method get_rec  =
      match gr with
      | Some _ -> (self_rec_only,mut_rec)
      | None -> let () = self # build_scc in
        (self_rec_only,mut_rec)
    method get_graph  =
      match gr with
      | Some g -> g
      | None -> 
        let () = self # build_scc in
        self # get_graph
    method string_of  =
      "hello"
   end;;

let view_scc_obj = new graph;;
