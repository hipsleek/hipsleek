#include "xdebug.cppo"
open VarGen
(** Created 20-May-2009
    	Convert global variables into reference parameters
*)

open Globals
open Gen.Basic

module I = Iast

(* Data structure for set of identifiers *)
module Ident = struct
  type t = ident
  let compare = compare
end

module IdentSet = Set.Make(Ident)

(* Data structure for graph of identifiers *)
module Name =
struct
  type t = ident

  let compare = compare

  let hash = Hashtbl.hash

  let equal = ( = )
end

module NG = Graph.Imperative.Digraph.Concrete(Name)

module NGComponents = Graph.Components.Make(NG)

module NGPathCheck = Graph.Path.Check(NG)

(* Global variables *)
let g = NG.create ()

let h = Hashtbl.create 200

let curr_proc = ref ""

(* Utility functions *)

(** Convert a list of identifiers into a set of identifiers 
    	@param l list of identifiers 
    	@return the set of identifiers in l *)
let rec to_IdentSet (l : ident list) : IdentSet.t =
  match l with
    [] -> IdentSet.empty
  | _  -> IdentSet.add (List.hd l) (to_IdentSet (List.tl l))

let to_IS (l : ident list) : IdentSet.t  =
  List.fold_left (fun a e -> IdentSet.add e a) (IdentSet.empty) l

let from_IS (s : IdentSet.t) : (ident list)  =
  IdentSet.elements s


let string_of_IdentSet (s : IdentSet.t) : string =
  "{"^(IdentSet.fold (fun e a -> e^" "^a) s "}")


(** Union a list of identifier sets into a unique identifier set 
    	@param l list of identifier sets
    	@return the union of all the sets in l *)
let rec union_all (l : IdentSet.t list) : IdentSet.t =
  match l with
    [] -> IdentSet.empty
  | _  -> IdentSet.union (List.hd l) (union_all (List.tl l))


(** Get the variable expression in a variable declaration expression.
    	Inputs are of type (ident * exp option * loc)
    	@return the variable expression *)
let get_exp_var (_, exp_op, l)  = 
  match exp_op with
    Some e -> e
  | None -> I.Empty l

(** Get the set of global identifiers in a global variable declaration expression 
    	@param decl variable declaration expression 
    	@return the set of identifiers in the declaration *)
let get_global_id (decl : I.exp_var_decl) : IdentSet.t =
  let ident_list = List.map fst3 decl.I.exp_var_decl_decls in
  to_IdentSet ident_list

let string_of_global_vars (gv) : string =
  let global_id_set = union_all (List.map get_global_id gv) in
  string_of_IdentSet global_id_set 

(** Get the identifier name of a parameter
    	@param parameter the parameter of a method 
    	@return the identifier name of the input parameter *)
let get_local_id (parameter : I.param) : ident =
  parameter.I.param_name 

(** Check whether an identifier in a variable declaration belongs to an identifier set 
    	@param set a set of identifiers
    	@param decl a variable declaration
    	@return true if the identifier in decl is inside set, false otherwise *)
let inIdentSet (set : IdentSet.t) (decl : ident * I.exp option * loc) : bool =
  IdentSet.mem (fst3 decl) set

(** Construct a variable declaration expression from its contents 
    	@param t type of the variables
    	@param pos position of the variables in the program 
    	@param decl an identifier declaration 
    	@return the variable declaration expression constructed from the inputs *)
let to_var_decl (t : typ) (pos : loc) (decl : ident * I.exp option * loc) : I.exp_var_decl =
  { I.exp_var_decl_type = t; I.exp_var_decl_decls = [decl]; I.exp_var_decl_pos = pos }


(** Get the procedure name from a procedure declaration 
    	@param proc procedure declaration
    	@return the procedure name *)
let get_proc_name (proc : I.proc_decl) : ident =
  proc.I.proc_name

(** Add Primed/Unprimed into a pair of identifiers *)
let addp (p : primed) ((id1,id2) : ident*ident) : (ident*primed)*(ident*primed) =
  ((id1,p),(id2,p))

(* Funtions to find read/write global variables *)

(** Find read/write global variables in a block of codes
    	@param global_vars set of global variables
    	@param local_vars set of local variables
    	@param block the input block of codes
    	@return a pair of read/write global variables *)
let rec find_read_write_global_var 
    (global_vars : IdentSet.t) (local_vars : IdentSet.t) (block : I.exp) : (IdentSet.t * IdentSet.t) =
  match block with
  | I.ArrayAlloc _ (*LDK: to eliminate compilation warnings*)
  | I.ArrayAt _ (*to be modified*)
  (* |I.ArrayAlloc _ (\*TODO WN : correct? *\) *)
  |I.Assert _ 
  | I.BoolLit _ 
  | I.Break _ 
  | I.Continue _ 
  | I.Debug _
  | I.Dprint _ 
  | I.Empty _ 
  | I.FloatLit _ 
  | I.IntLit _ 
  | I.Java _
  | I.Null _ 
  | I.This _ 
  | I.Time _ 
  | I.Unfold _ -> 
    (IdentSet.empty, IdentSet.empty)
  | I.Label (_,b)-> find_read_write_global_var global_vars local_vars b
  | I.Assign e ->
    begin
      let (rr,wr) = find_read_write_global_var global_vars local_vars e.I.exp_assign_rhs in
      match e.I.exp_assign_lhs with
      | I.Var e1 ->
        if (IdentSet.mem e1.I.exp_var_name (IdentSet.union global_vars local_vars)) then
          let r = rr in
          let w = IdentSet.union wr (IdentSet.diff (IdentSet.singleton e1.I.exp_var_name) local_vars) in
          (r,w)
        else
          (IdentSet.empty, IdentSet.empty)
      | _ ->
        let (rl, wl) = find_read_write_global_var global_vars local_vars e.I.exp_assign_lhs in
        let r = IdentSet.union rl rr in
        let w = IdentSet.union wl wr in
        (r,w)
    end
  | I.Binary e ->
    begin
      let (r1,w1) = find_read_write_global_var global_vars local_vars e.I.exp_binary_oper1 in
      let (r2,w2) = find_read_write_global_var global_vars local_vars e.I.exp_binary_oper2 in
      let r = IdentSet.union r1 r2 in
      let w = IdentSet.union w1 w2 in
      (r,w)
    end
  | I.Bind e ->
    begin
      let fields_set = to_IdentSet e.I.exp_bind_fields in
      let new_local = IdentSet.union local_vars fields_set in
      let new_global = IdentSet.diff global_vars new_local in
      let (r1,w1) = find_read_write_global_var new_global new_local e.I.exp_bind_body in
      let w = w1 in
      let df = (IdentSet.diff (IdentSet.singleton e.I.exp_bind_bound_var) local_vars) in
      let df = IdentSet.inter  df global_vars in
      let r = IdentSet.union r1 df in
      (r,w)
    end
  | I.Block e -> find_read_write_global_var global_vars local_vars e.I.exp_block_body
  | I.Barrier e -> 
    if (IdentSet.mem e.I.exp_barrier_recv global_vars) then
      (IdentSet.diff (IdentSet.singleton e.I.exp_barrier_recv) local_vars, IdentSet.empty)
    else (IdentSet.empty, IdentSet.empty)
  | I.CallRecv e ->
    begin
      ignore (NG.add_edge g (NG.V.create !curr_proc) (NG.V.create e.I.exp_call_recv_method));
      let read_write_list =  List.map (find_read_write_global_var global_vars local_vars) e.I.exp_call_recv_arguments in
      let rr = union_all (List.map fst read_write_list) in
      let wr = union_all (List.map snd read_write_list) in
      match e.I.exp_call_recv_receiver with
      | I.Var e1 ->
        if (IdentSet.mem e1.I.exp_var_name (IdentSet.union global_vars local_vars)) then
          let r = rr in
          let w = IdentSet.union wr (IdentSet.diff (IdentSet.singleton e1.I.exp_var_name) local_vars) in
          (r,w)
        else
          (IdentSet.empty, IdentSet.empty)
      | _ ->
        let (rl, wl) = find_read_write_global_var global_vars local_vars e.I.exp_call_recv_receiver in
        let r = IdentSet.union rl rr in
        let w = IdentSet.union wl wr in
        (r,w)
    end
  | I.CallNRecv e ->
    if (e.I.exp_call_nrecv_method=Globals.fork_name) then
      (*Construct the async call from parameters of the fork procedure*)
      (*method name is the first arguments*)
      try
        let fn_exp = (List.hd e.I.exp_call_nrecv_arguments) in
        let fn = match fn_exp with
          | I.Var v ->
            v.I.exp_var_name
          | _ -> 
            Error.report_error {Error.error_loc = no_pos; Error.error_text = ("expecting a method name as the first parameter of a fork")}
        in
        let args = List.tl e.I.exp_call_nrecv_arguments in
        let new_e = I.CallNRecv {
            I.exp_call_nrecv_lock = e.I.exp_call_nrecv_lock;
            I.exp_call_nrecv_method = fn;
            I.exp_call_nrecv_arguments = args;
            I.exp_call_nrecv_ho_arg = None;
            I.exp_call_nrecv_path_id = e.I.exp_call_nrecv_path_id;
            I.exp_call_nrecv_pos = e.I.exp_call_nrecv_pos} in
        find_read_write_global_var global_vars local_vars new_e
      with _ ->
        Error.report_error {Error.error_loc = no_pos; Error.error_text = ("expecting fork has at least 1 argument: method name")}
    else if (e.I.exp_call_nrecv_method=Globals.join_name
             || e.I.exp_call_nrecv_method=Globals.init_name
             || e.I.exp_call_nrecv_method=Globals.finalize_name
             || e.I.exp_call_nrecv_method=Globals.acquire_name
             || e.I.exp_call_nrecv_method=Globals.release_name) then
      try
        find_read_write_global_var global_vars local_vars (List.hd e.I.exp_call_nrecv_arguments)
      with _ ->
        Error.report_error {Error.error_loc = no_pos; Error.error_text = ("expecting join has only 1 argument: thread id")}
    else
      begin
        ignore (NG.add_edge g (NG.V.create !curr_proc) (NG.V.create e.I.exp_call_nrecv_method));
        let read_write_list =  List.map (find_read_write_global_var global_vars local_vars) e.I.exp_call_nrecv_arguments in
        let r = union_all (List.map fst read_write_list) in
        let w = union_all (List.map snd read_write_list) in
        (r,w)
      end
  | I.Cast e -> find_read_write_global_var global_vars local_vars e.I.exp_cast_body
  | I.Catch b -> 
    let ident_list = match (b.I.exp_catch_var, b.I.exp_catch_flow_var) with
      | None, None -> []
      | None, Some v -> [v]
      | Some v, None -> [v]
      | Some v1, Some v2 -> v1::[v2] in			
    let ident_set = to_IdentSet ident_list in
    let new_global = IdentSet.diff global_vars ident_set in
    let new_local = IdentSet.union local_vars ident_set in
    (find_read_write_global_var new_global new_local b.I.exp_catch_body)
  | I.Cond e ->
    begin
      let (r1,w1) = find_read_write_global_var global_vars local_vars e.I.exp_cond_then_arm in
      let (r2,w2) = find_read_write_global_var global_vars local_vars e.I.exp_cond_else_arm in
      let (rc,wc) = find_read_write_global_var global_vars local_vars e.I.exp_cond_condition in
      let w = IdentSet.union w1 w2 in
      let r = IdentSet.union (IdentSet.union r1 r2) (IdentSet.diff rc local_vars) in
      (r,w)
    end
  | I.ConstDecl e ->
    begin
      let exp_list = List.map snd3 e.I.exp_const_decl_decls in
      let read_write_list =  List.map (find_read_write_global_var global_vars local_vars) exp_list in
      let r = union_all (List.map fst read_write_list) in
      let w = union_all (List.map snd read_write_list) in
      (r,w)
    end
  | I.Finally b-> find_read_write_global_var global_vars local_vars b.I.exp_finally_body
  | I.Member e -> find_read_write_global_var global_vars local_vars e.I.exp_member_base
  | I.New e ->
    begin
      let read_write_list =  List.map (find_read_write_global_var global_vars local_vars) e.I.exp_new_arguments in
      let r = union_all (List.map fst read_write_list) in
      let w = union_all (List.map snd read_write_list) in
      (r,w)		
    end
  | I.Return e ->
    begin
      match e.I.exp_return_val with
        None -> (IdentSet.empty, IdentSet.empty)
      | Some e1 ->
        find_read_write_global_var global_vars local_vars e1
    end
  | I.Seq e ->
    begin
      match e.I.exp_seq_exp1 with
        I.VarDecl e1 -> 
        let ident_list = List.map fst3 e1.I.exp_var_decl_decls in
        let ident_set = to_IdentSet ident_list in
        let new_global = IdentSet.diff global_vars ident_set in
        let new_local = IdentSet.union local_vars ident_set in
        let (r1,w1) = find_read_write_global_var new_global new_local e.I.exp_seq_exp2 in
        let exp_list = List.map get_exp_var e1.I.exp_var_decl_decls in
        let read_write_list =  List.map (find_read_write_global_var global_vars local_vars) exp_list in
        let r2 = union_all (List.map fst read_write_list) in
        let w2 = union_all (List.map snd read_write_list) in
        let r = IdentSet.union r1 r2 in
        let w = IdentSet.union w1 w2 in
        (r,w)			
      | I.ConstDecl e1 -> 
        let ident_list = List.map fst3 e1.I.exp_const_decl_decls in
        let ident_set = to_IdentSet ident_list in
        let new_global = IdentSet.diff global_vars ident_set in
        let new_local = IdentSet.union local_vars ident_set in
        let (r1,w1) = find_read_write_global_var new_global new_local e.I.exp_seq_exp2 in
        let exp_list = List.map snd3 e1.I.exp_const_decl_decls in
        let read_write_list =  List.map (find_read_write_global_var global_vars local_vars) exp_list in
        let r2 = union_all (List.map fst read_write_list) in
        let w2 = union_all (List.map snd read_write_list) in
        let r = IdentSet.union r1 r2 in
        let w = IdentSet.union w1 w2 in
        (r,w)
      | _ ->
        let (r1,w1) = find_read_write_global_var global_vars local_vars e.I.exp_seq_exp1 in
        let (r2,w2) = find_read_write_global_var global_vars local_vars e.I.exp_seq_exp2 in
        let r = IdentSet.union r1 r2 in
        let w = IdentSet.union w1 w2 in
        (r,w)
    end
  | I.Unary e ->
    begin
      let (r0,w0) = find_read_write_global_var global_vars local_vars e.I.exp_unary_exp in
      match e.I.exp_unary_op with
        I.OpUMinus | I.OpNot -> (r0,w0)
      | I.OpPreInc | I.OpPreDec | I.OpPostInc | I.OpPostDec | I.OpVal | I.OpAddr ->
        begin
          match e.I.exp_unary_exp with
            I.Var e1 ->
            if IdentSet.mem e1.I.exp_var_name (IdentSet.union global_vars local_vars) then
              let v = IdentSet.diff (IdentSet.singleton e1.I.exp_var_name) local_vars in
              let w = IdentSet.union w0 v in
              let r = IdentSet.union r0 v in
              (r,w)
            else
              (r0,w0)
          | _ -> (r0,w0)
        end
    end
  | I.Var e ->
    begin
      (* not(v in Local) & (v in GVars) *)
      if (IdentSet.mem e.I.exp_var_name global_vars) then
        let r = IdentSet.diff (IdentSet.singleton e.I.exp_var_name) local_vars in
        (r, IdentSet.empty)
      else
        (IdentSet.empty, IdentSet.empty)
    end
  | I.VarDecl e ->
    begin
      let exp_list = List.map get_exp_var e.I.exp_var_decl_decls in
      (*exp_list -> list of initialization *)
      let read_write_list =  List.map (find_read_write_global_var global_vars local_vars) exp_list in
      let r = union_all (List.map fst read_write_list) in
      let w = union_all (List.map snd read_write_list) in
      (r,w)
    end
  | I.While e ->
    begin
      let (rb,wb) = find_read_write_global_var global_vars local_vars e.I.exp_while_body in
      let (rc,wc) = find_read_write_global_var global_vars local_vars e.I.exp_while_condition in
      let r = IdentSet.union rc rb in
      let w = IdentSet.union wc wb in
      (r,w)
    end
  | I.Try e ->	
    let (rb,wb) = find_read_write_global_var global_vars local_vars e.I.exp_try_block in
    let l_catch = List.map (find_read_write_global_var global_vars local_vars) e.I.exp_catch_clauses  in
    let l_final = List.map (find_read_write_global_var global_vars local_vars) e.I.exp_finally_clause  in
    let all_r, all_w = List.split ((rb,wb)::(l_catch @ l_final)) in
    ((union_all all_r),(union_all all_w))
  | I.Raise e -> 
    begin 
      match e.I.exp_raise_val with 
      | None  -> (IdentSet.empty, IdentSet.empty)
      | Some e -> find_read_write_global_var global_vars local_vars e
    end 
  | I.Par e ->
    let (rl, wl) = List.split (List.map (fun c -> 
        find_read_write_global_var global_vars local_vars c.I.exp_par_case_body
      ) e.I.exp_par_cases)
    in (union_all rl, union_all wl)


(** Construct the read/write variable declarations from the read/write sets 
    	@param global_var_decls list of global variable declarations 
    	@param readSet the set of read-only global variables
    	@param writeSet the set of read/write global variables 
    	@return a pair of read and write variable declaration lists *)
let rec to_var_decl_list (global_var_decls : I.exp_var_decl list) (readSet : IdentSet.t) (writeSet : IdentSet.t) :
  (I.exp_var_decl list * I.exp_var_decl list) =
  match global_var_decls with
    [] -> [], []
  | h::t ->
    let (readlist,writelist) = to_var_decl_list t readSet writeSet in
    let add_read_decl = List.filter (inIdentSet readSet) h.I.exp_var_decl_decls in
    let add_write_decl = List.filter (inIdentSet writeSet) h.I.exp_var_decl_decls in
    let add_read = List.map (to_var_decl h.I.exp_var_decl_type h.I.exp_var_decl_pos) add_read_decl in
    let add_write = List.map (to_var_decl h.I.exp_var_decl_type h.I.exp_var_decl_pos) add_write_decl in
    let new_read_list = add_read @ readlist in
    let new_write_list = add_write @ writelist in
    (new_read_list, new_write_list)


(** Find read/write global variables in a procedure. 
    	The method put the pair of read/write sets into the global hash table h
    	@param global_id_set set of global identifiers
    	@param proc input procedure declaration 
    	@return unit *)
let find_read_write_global_var_proc (global_id_set : IdentSet.t) (proc : I.proc_decl) : unit =
  (ignore 
     (curr_proc := proc.I.proc_name;
      NG.add_vertex g (NG.V.create !curr_proc))
  );
  let local_vars = to_IdentSet (List.map get_local_id proc.I.proc_args) in
  let global_vars = IdentSet.diff global_id_set local_vars in
  (* let _= print_endline ("BachLe: Find Global vars Debugging..."^proc.I.proc_name)in *)
  let find_in_body global_vars local_vars = (*Find read/write global vars in procedure body*)
    match proc.I.proc_body with
    | None -> (IdentSet.empty,IdentSet.empty)
    | Some e ->
      begin
        let (reads, writes) = find_read_write_global_var global_vars local_vars e in
        (*let readSet = IdentSet.diff reads writes in*)
        let readSet=reads in
        let writeSet = writes in
        (readSet,writeSet)
      end
  in 
  let find_in_specs global_vars= (*Find read/write global vars in specification*)
    let st=proc.I.proc_static_specs in 
    let list_fv=
      let pr,pst = Iformula.struc_split_fv st false in  
      (* Gen.BList.remove_dups_eq (=) pr@pst  *)
      pr@pst 
    in
    let (rl,wl)= List.fold_left (fun (readl,writel) (id,pr) -> 
        if(IdentSet.mem id global_vars) then match pr with
          |Primed -> (readl,writel@[id])
          | Unprimed -> (readl@[id],writel)
        else
          (readl,writel)
      ) ([],[]) (list_fv) 
    in 
    let readSet=to_IdentSet rl in
    let writeSet= to_IdentSet wl in
    (*(IdentSet.empty,IdentSet.empty) *)
    (readSet,writeSet)
  in
  let (r1,w1)= find_in_body global_vars local_vars	in
  let (r2,w2)= find_in_specs global_vars in
  let reads=IdentSet.union r1 r2 in
  let writes=IdentSet.union w1 w2 in
  let readSet = IdentSet.diff reads writes in
  let writeSet= writes in
  (* let _= IdentSet.iter (fun x-> print_endline (proc.I.proc_name^" Find glbv R:" ^x) )readSet in  *)
  (* let _= IdentSet.iter (fun x-> print_endline (proc.I.proc_name^" Find glbv W:" ^x) )writeSet in *)
  Hashtbl.replace h proc.I.proc_name (readSet,writeSet)

let find_read_write_global_var_proc (global_id_set : IdentSet.t) (proc : I.proc_decl) : unit =
  let pr1 proc = proc.I.proc_name in
  let pr2 _ = "" in
  Debug.no_1 "find_read_write_global_var_proc" pr1 pr2 
    (fun _ -> find_read_write_global_var_proc global_id_set proc) proc

(** Get the read/write global variables of a procedure from the hash table 
    	@param global_var_decls list of global variable declarations
    	@param proc input procedure declaration
    	@return a pair of read and write variable declaration lists *)
let get_read_write_global_var (global_var_decls : I.exp_var_decl list) (proc : I.proc_decl) : 
  (I.exp_var_decl list * I.exp_var_decl list) =
  let (reads,writes) = Hashtbl.find h proc.I.proc_name in
  (*LDK*)
  (* let () = print_string ("get_read_write_global_var: proc_name: "^ proc.I.proc_name ^ "\n") in *)
  (* let () = print_string ("read vars: "^(string_of_IdentSet reads)^"\n") in *)
  (* let () = print_string ("writes vars: "^(string_of_IdentSet writes)^"\n") in *)
  let readSet = IdentSet.diff reads writes in
  let writeSet = writes in
  to_var_decl_list global_var_decls readSet writeSet

(** Set the read/write sets for one vertex. The method changes the global hash table h.
    	@param readSet set of read-only identifiers 
    	@param writeSet set of read/write identifiers
    	@param vertex a procedure name
    	@return unit *)
let set_read_write_set (readSet : IdentSet.t) (writeSet : IdentSet.t) (vertex : NG.V.t) : unit =
  Hashtbl.replace h vertex (readSet,writeSet)

(** Merge the read/write variables in one strongly connected component
    	@param scc strongly connected component of a graph
    	@return unit *)
let merge_scc (scc : NG.V.t list ) : unit =
  try(
    let func e = Hashtbl.find h e in
    let read_write_list = List.map (func) scc in
    let read_list = List.map fst read_write_list in
    let write_list = List.map snd read_write_list in
    let readSet = union_all read_list in
    let writeSet = union_all write_list in
    List.iter (set_read_write_set readSet writeSet) scc
  )
  with Not_found ->
    let func_id = List.hd scc in
    if ((func_id = Globals.fork_name) || (func_id = Globals.join_name)
        || (func_id = Globals.acquire_name) || (func_id = Globals.release_name)
        || (func_id = Globals.init_name) || (func_id = Globals.finalize_name)) then
      let () = print_endline_quiet ("[Warning] merge_scc: method names " ^ (string_of_ident_list scc) ^ " not found") in
      ()
    else
      Error.report_error {Error.error_loc = no_pos; Error.error_text = ("scc = " ^ (string_of_ident_list scc) ^ "not found")}

(** Check the connection and merge two strongly connected components
    	@param scc1 the first strongly connected component
    	@param scc2 the second strongly connected component
    	@return unit *)		
let check_and_merge (scc1 : NG.V.t list) (scc2 : NG.V.t list) : unit =
  let pc = NGPathCheck.create g in
  let v1 = List.hd scc1 in
  let v2 = List.hd scc2 in
  if NGPathCheck.check_path pc v1 v2 then
    let (r1,w1) = Hashtbl.find h v1 in
    let (r2,w2) = Hashtbl.find h v2 in
    let r = IdentSet.union r1 r2 in
    let w = IdentSet.union w1 w2 in
    let () = Hashtbl.replace h v1 (r,w) in
    merge_scc scc1

(** Find read write global variables for all procedures using graph data structure 
    	@param prog program declaration
    	@return unit *)
let find_read_write_global_var_all_procs (prog : I.prog_decl) : unit =
  let global_var_decls = prog.I.prog_global_var_decls in
  let global_id_set = union_all (List.map get_global_id global_var_decls) in
  let proc_decls = prog.I.prog_proc_decls in
  let () = List.iter (find_read_write_global_var_proc global_id_set) proc_decls in
  (* let scclist = NGComponents.scc_list g in *)
  (* let sccarr = Array.of_list scclist in    *)
  let sccarr = NGComponents.scc_array g in
  let n = Array.length sccarr in
  let () = Array.iter merge_scc sccarr in
  for k = 0 to n-1 do
    for i = 0 to n-1 do
      for j = 0 to n-1 do
        if i <> j then
          check_and_merge sccarr.(i) sccarr.(j)
      done
    done
  done

(* Extend body of procedures *)

(** Find a method declaration with a given identifier 
    	@param temp_procs list of temporary procedure declarations 
    	@param id an identifier
    	@return the procedure declaration that has name id *)
let rec find_method (temp_procs : I.proc_decl list) (id : ident) : I.proc_decl =
  let head = List.hd temp_procs in
  if head.I.proc_name = id then head
  else find_method (List.tl temp_procs) id

(** Change the expression in a constant declaration 
    	@param temp_procs list of temporary procedure declaration 
    	@param i an identifier
    	@param e the expression in the constant declaration
    	@param l location of the declaration
    	@return the constant declaration with new expression *)
let rec change_decl (temp_procs : I.proc_decl list) ((i,e,l) : ident * I.exp * loc) : ident * I.exp * loc =
  let new_exp = extend_body temp_procs e in
  (i,new_exp,l)

(** Change the expression in a variable declaration 
    	@param temp_procs list of temporary procedure declaration
    	@param i an identifier
    	@param e_opt the expression in the variable declaration
    	@param l location of the declaration
    	@return the variable declaration with new expression *)
and change_opt_decl (temp_procs : I.proc_decl list) ((i,e_opt,l) : ident * I.exp option * loc) : ident * I.exp option * loc =
  match e_opt with
    None -> (i,e_opt,l)
  | Some e ->
    let new_exp = extend_body temp_procs e in
    (i, Some new_exp, l)

(** Extend the arguments of a function call 
    	@param temp_procs list of temporary procedure declaration
    	@param params list of additional parameters 
    	@param args list of arguments 
    	@return new list of arguments *)
and change_args (temp_procs : I.proc_decl list) (params : I.param list) (args : I.exp list) : I.exp list =
  match params with
    [] -> []
  | hp::tp ->
    begin
      match args with
        [] ->
        let new_ta = change_args temp_procs tp [] in
        let var_exp = { I.exp_var_name = hp.I.param_name; I.exp_var_pos = hp.I.param_loc } in
        let new_ha = I.Var var_exp in
        new_ha::new_ta
      | ha::ta -> 
        let new_ta = change_args temp_procs tp ta in
        let new_ha = extend_body temp_procs ha in
        new_ha::new_ta
    end

(** Extend the body of the procedure to the new one 
    	@param temp_procs list of temporary procedure declaration
    	@param exp current body of a procedure 
    	@return new body of the procedure *)
and extend_body (temp_procs : I.proc_decl list) (exp : I.exp) : I.exp =
  match exp with
  | I.ArrayAlloc _ (*LDK: to eliminate compilation warnings*)
  |I.ArrayAt _ (*to be modified*)
  |I.Assert _
  | I.BoolLit _
  | I.Break _
  | I.Continue _
  | I.Debug _
  | I.Dprint _
  | I.Empty _
  | I.FloatLit _
  | I.IntLit _
  | I.Java _
  | I.Null _
  | I.This _
  | I.Time _ 
  | I.Unfold _
  | I.Barrier _
  | I.Var _ -> 
    exp
  | I.Label (p,b)-> I.Label (p, extend_body temp_procs b)
  | I.Assign e -> 
    begin
      let new_lhs = extend_body temp_procs e.I.exp_assign_lhs in
      let new_rhs = extend_body temp_procs e.I.exp_assign_rhs in
      let new_exp = { e with I.exp_assign_lhs = new_lhs; I.exp_assign_rhs = new_rhs } in
      I.Assign new_exp
    end
  | I.Binary e ->
    begin
      let new_oper1 = extend_body temp_procs e.I.exp_binary_oper1 in
      let new_oper2 = extend_body temp_procs e.I.exp_binary_oper2 in
      let new_exp = { e with I.exp_binary_oper1 = new_oper1; I.exp_binary_oper2 = new_oper2 } in
      I.Binary new_exp
    end
  | I.Bind e ->
    begin
      let new_body = extend_body temp_procs e.I.exp_bind_body in
      let new_exp = { e with I.exp_bind_body = new_body } in
      I.Bind new_exp
    end
  | I.Block e ->
    begin
      let new_body = extend_body temp_procs e.I.exp_block_body in
      let new_exp = { e with I.exp_block_body = new_body } in
      I.Block new_exp
    end
  | I.CallRecv e ->
    begin
      let new_meth_decl = find_method temp_procs e.I.exp_call_recv_method in
      let new_args = change_args temp_procs new_meth_decl.I.proc_args e.I.exp_call_recv_arguments in
      let new_exp = { e with I.exp_call_recv_arguments = new_args } in
      I.CallRecv new_exp
    end
  | I.CallNRecv e ->
    if (e.I.exp_call_nrecv_method=Globals.fork_name) then
      (*Construct the async call (new_e) from parameters of the fork procedure*)
      try
        let fn_exp = (List.hd e.I.exp_call_nrecv_arguments) in
        let fn = match fn_exp with
          | I.Var v ->
            v.I.exp_var_name
          | _ -> 
            Error.report_error {Error.error_loc = no_pos; Error.error_text = ("expecting a method name as the first parameter of a fork")}
        in
        let args = List.tl e.I.exp_call_nrecv_arguments in
        let new_e = I.CallNRecv {
            I.exp_call_nrecv_lock = e.I.exp_call_nrecv_lock;
            I.exp_call_nrecv_method = fn;
            I.exp_call_nrecv_arguments = args;
            I.exp_call_nrecv_ho_arg = None;
            I.exp_call_nrecv_path_id = e.I.exp_call_nrecv_path_id;
            I.exp_call_nrecv_pos = e.I.exp_call_nrecv_pos} in
        let new_e1 = extend_body temp_procs new_e in
        (* ================== *)
        match new_e1 with
        | I.CallNRecv e1 ->
          let fn1 = I.Var { I.exp_var_name = e1.I.exp_call_nrecv_method;
                            I.exp_var_pos = e1.I.exp_call_nrecv_pos} 
          in
          let new_fork_exp = I.CallNRecv {
              I.exp_call_nrecv_lock = e.I.exp_call_nrecv_lock;
              I.exp_call_nrecv_method = e.I.exp_call_nrecv_method; (*fork_name*)
              I.exp_call_nrecv_arguments = fn1::(e1.I.exp_call_nrecv_arguments);
              I.exp_call_nrecv_ho_arg = None;
              I.exp_call_nrecv_path_id = e1.I.exp_call_nrecv_path_id;
              I.exp_call_nrecv_pos = e1.I.exp_call_nrecv_pos} 
          in
          new_fork_exp
        | _ -> Error.report_error {Error.error_loc = no_pos; Error.error_text = ("expecting forked method to be a I.CallNRecv")}
      (* ================== *)
      with _ ->
        Error.report_error {Error.error_loc = no_pos; Error.error_text = ("expecting fork has at least 1 argument: method name")}
    else if (e.I.exp_call_nrecv_method=Globals.join_name 
             || e.I.exp_call_nrecv_method=Globals.init_name
             || e.I.exp_call_nrecv_method=Globals.finalize_name
             || e.I.exp_call_nrecv_method=Globals.acquire_name
             || e.I.exp_call_nrecv_method=Globals.release_name) then
      (*no need for join, init ...*)
      exp
    else
      begin
        let new_meth_decl = find_method temp_procs e.I.exp_call_nrecv_method in
        let new_args = change_args temp_procs new_meth_decl.I.proc_args e.I.exp_call_nrecv_arguments in
        let new_exp = { e with I.exp_call_nrecv_arguments = new_args } in
        I.CallNRecv new_exp
      end
  | I.Cast e ->
    begin
      let new_body = extend_body temp_procs e.I.exp_cast_body in
      let new_exp = { e with I.exp_cast_body = new_body } in
      I.Cast new_exp
    end
  | I.Catch e -> I.Catch {e with I.exp_catch_body = extend_body temp_procs e.I.exp_catch_body}
  | I.Cond e ->
    begin
      let new_cond = extend_body temp_procs e.I.exp_cond_condition in
      let new_then = extend_body temp_procs e.I.exp_cond_then_arm in
      let new_else = extend_body temp_procs e.I.exp_cond_else_arm in
      let new_exp = { e with I.exp_cond_condition = new_cond; I.exp_cond_then_arm = new_then; I.exp_cond_else_arm = new_else } in
      I.Cond new_exp
    end
  | I.ConstDecl e ->
    begin
      let new_decls = List.map (change_decl temp_procs) e.I.exp_const_decl_decls in
      let new_exp = { e with I.exp_const_decl_decls = new_decls } in
      I.ConstDecl new_exp
    end
  | I.Finally e -> I.Finally {e with I.exp_finally_body = extend_body temp_procs e.I.exp_finally_body}
  | I.Member e ->
    begin
      let new_base = extend_body temp_procs e.I.exp_member_base in
      let new_exp = { e with I.exp_member_base = new_base } in
      I.Member new_exp
    end
  | I.New e ->
    begin
      let new_exp_list = List.map (extend_body temp_procs) e.I.exp_new_arguments in
      let new_exp = { e with I.exp_new_arguments = new_exp_list } in
      I.New new_exp
    end
  | I.Return e ->
    begin
      match e.I.exp_return_val with
        None -> exp
      | Some e1 ->
        let new_e1 = extend_body temp_procs e1 in
        let new_exp = {e with I.exp_return_val = Some new_e1 } in
        I.Return new_exp
    end
  | I.Seq e -> 
    begin
      let new_exp1 = extend_body temp_procs e.I.exp_seq_exp1 in
      let new_exp2 = extend_body temp_procs e.I.exp_seq_exp2 in
      let new_exp = { e with I.exp_seq_exp1 = new_exp1; I.exp_seq_exp2 = new_exp2 } in
      I.Seq new_exp
    end
  | I.Unary e -> 
    begin
      let new_subexp = extend_body temp_procs e.I.exp_unary_exp in
      let new_exp = { e with I.exp_unary_exp = new_subexp } in
      I.Unary new_exp
    end
  | I.VarDecl e -> 
    begin
      let new_decls = List.map (change_opt_decl temp_procs) e.I.exp_var_decl_decls in
      let new_exp = {e with I.exp_var_decl_decls = new_decls } in
      I.VarDecl new_exp
    end
  | I.While e ->
    begin
      let new_cond = extend_body temp_procs e.I.exp_while_condition in
      let new_body = extend_body temp_procs e.I.exp_while_body in
      let new_exp = { e with I.exp_while_condition = new_cond; exp_while_body = new_body } in
      I.While new_exp
    end
  | I.Try e ->
    I.Try {e with 
           I.exp_try_block = extend_body temp_procs e.I.exp_try_block;
           I.exp_catch_clauses = List.map (extend_body temp_procs) e.I.exp_catch_clauses;
           I.exp_finally_clause = List.map (extend_body temp_procs) e.I.exp_finally_clause;
          }
  | I.Raise e -> I.Raise {e with 
                          I.exp_raise_val = match e.I.exp_raise_val with 
                            | None -> None
                            | Some e -> Some (extend_body temp_procs e)}
  | I.Par e ->
    let cl = List.map (fun c -> { c with 
                                  I.exp_par_case_body = extend_body temp_procs c.I.exp_par_case_body }) e.I.exp_par_cases in
    I.Par { e with I.exp_par_cases = cl; }

(* Rename local variables when there is conflict *)

(** Create a new identifier if there is conflict 
    	@param global_vars set of global variable identifiers 
    	@param id an identifier
    	@return id if id is not in global_vars, otherwise return a new name *)
let create_new_ids (global_vars : IdentSet.t) (id : ident) : ident =
  if (IdentSet.mem id global_vars) then
    fresh_local_var_name id
  else 
    id

(** Create a new parameter name if there is conflict 
    	@param global_vars set of global variable identifiers
    	@param p a parameter 
    	@return p if p is not in global_vars, otherwise return a new name *)
let create_new_params (global_vars : IdentSet.t) (p : I.param) : I.param =
  if (IdentSet.mem p.I.param_name global_vars) then
    { p with I.param_name = (fresh_local_var_name p.I.param_name) }
  else
    p

(** Check the local variables name and change them if necessary 
    	@param global_vars set of global variable identifiers 
    	@param exp an expression
    	@return a new expression *)
let rec check_and_change (global_vars : IdentSet.t) (exp : I.exp) : I.exp =
  match exp with
  | I.ArrayAlloc _ (*LDK: to eliminate compilation warnings*)
  |I.ArrayAt _ (*to be modified*)
  |I.Assert _
  | I.BoolLit _
  | I.Break _
  | I.ConstDecl _
  | I.Continue _
  | I.Debug _
  | I.Dprint _
  | I.Empty _
  | I.FloatLit _
  | I.IntLit _
  | I.Java _
  | I.Null _
  | I.This _
  | I.Time _ 
  | I.Unfold _
  | I.Var _
  | I.Barrier _
  | I.VarDecl _ -> 
    exp
  | I.Label (p,b) -> I.Label (p, check_and_change global_vars b)
  | I.Assign e ->
    begin
      let new_lhs = check_and_change global_vars e.I.exp_assign_lhs in
      let new_rhs = check_and_change global_vars e.I.exp_assign_rhs in
      let new_exp = { e with I.exp_assign_lhs = new_lhs; I.exp_assign_rhs = new_rhs } in
      I.Assign new_exp
    end
  | I.Binary e -> 
    begin
      let new_oper1 = check_and_change global_vars e.I.exp_binary_oper1 in
      let new_oper2 = check_and_change global_vars e.I.exp_binary_oper2 in
      let new_exp = { e with I.exp_binary_oper1 = new_oper1; I.exp_binary_oper2 = new_oper2 } in
      I.Binary new_exp
    end
  | I.Bind e ->
    begin
      (*if IdentSet.mem e.I.exp_bind_bound_var global_vars then
          let list_elem = IdentSet.elements global_vars in
          let () = print_string ("inside bind with globals "^(String.concat "," list_elem)^"\n") in
          let () = print_string ("global vars: "^(Iprinter.string_of_var_list global_vars)^"\n") in
          let new_name = create_new_ids global_vars e.I.exp_bind_bound_var in
        		  let new_body = x_add Astsimp.rename_exp [e.I.exp_bind_bound_var,new_name] e.I.exp_bind_body in
        		  let new_exp = { e with I.exp_bind_bound_var = new_name; I.exp_bind_body = new_body } in
        		  I.Bind new_exp
        		else exp*)
      let new_body = check_and_change global_vars e.I.exp_bind_body in
      let new_exp = { e with I.exp_bind_body = new_body } in
      I.Bind new_exp
    end
  | I.Block e ->
    begin
      let new_body = check_and_change global_vars e.I.exp_block_body in
      let new_exp = { e with I.exp_block_body = new_body } in
      I.Block new_exp
    end
  | I.CallRecv e -> 
    begin
      let new_args = List.map (check_and_change global_vars) e.I.exp_call_recv_arguments in
      let new_exp = { e with I.exp_call_recv_arguments = new_args } in
      I.CallRecv new_exp
    end
  | I.CallNRecv e ->
    begin
      let new_args = List.map (check_and_change global_vars) e.I.exp_call_nrecv_arguments in
      let new_exp = { e with I.exp_call_nrecv_arguments = new_args } in
      I.CallNRecv new_exp
    end
  | I.Cast e ->
    begin
      let new_body = check_and_change global_vars e.I.exp_cast_body in
      let new_exp = { e with I.exp_cast_body = new_body } in
      I.Cast new_exp
    end
  | I.Catch e -> 
    let (f_catch_var, int_catch_var ) = match e.I.exp_catch_var with
      | None -> (None , [])
      | Some v ->
        let s = (create_new_ids global_vars v) in
        (Some s, [s]) in
    let (f_flow_var, int_flow_var ) = match e.I.exp_catch_flow_var with
      | None -> (None , [])
      | Some v ->
        let s = (create_new_ids global_vars v) in
        (Some s, [s]) in				
    let ident_list = int_catch_var @ int_flow_var in
    let new_ident_list = List.map (create_new_ids global_vars) ident_list in
    let renlist = List.combine ident_list new_ident_list in
    let new_exp2 = x_add Astsimp.rename_exp renlist e.I.exp_catch_body in
    I.Catch {e with 
             I.exp_catch_var = f_catch_var;
             I.exp_catch_flow_var = f_flow_var;
             I.exp_catch_body = (check_and_change global_vars new_exp2);}
  | I.Cond e ->
    begin
      let new_cond = check_and_change global_vars e.I.exp_cond_condition in
      let new_then = check_and_change global_vars e.I.exp_cond_then_arm in
      let new_else = check_and_change global_vars e.I.exp_cond_else_arm in
      let new_exp = { e with I.exp_cond_condition = new_cond; I.exp_cond_then_arm = new_then; I.exp_cond_else_arm = new_else } in
      I.Cond new_exp
    end
  | I.Finally e -> I.Finally {e with I.exp_finally_body = check_and_change global_vars e.I.exp_finally_body}
  | I.Member e ->
    begin
      let new_base = check_and_change global_vars e.I.exp_member_base in
      let new_exp = { e with I.exp_member_base = new_base } in
      I.Member new_exp
    end
  | I.New e ->
    begin
      let new_exp_list = List.map (check_and_change global_vars) e.I.exp_new_arguments in
      let new_exp = { e with I.exp_new_arguments = new_exp_list } in
      I.New new_exp
    end
  | I.Return e ->
    begin
      match e.I.exp_return_val with
        None -> exp
      | Some e1 ->
        let new_e1 = check_and_change global_vars e1 in
        let new_exp = {e with I.exp_return_val = Some new_e1 } in
        I.Return new_exp
    end
  | I.Seq e -> 
    begin
      match e.I.exp_seq_exp1 with
        I.VarDecl e1 -> 
        let ident_list = List.map fst3 e1.I.exp_var_decl_decls in
        let new_ident_list = List.map (create_new_ids global_vars) ident_list in 
        let renlist = List.map2 join2 ident_list new_ident_list in
        let new_exp2 = x_add Astsimp.rename_exp renlist e.I.exp_seq_exp2 in
        let new_exp2 = check_and_change global_vars new_exp2 in
        let new_var_decls = List.map2 change_fst3 e1.I.exp_var_decl_decls new_ident_list in
        let new_exp1 = I.VarDecl { e1 with I.exp_var_decl_decls = new_var_decls } in
        let new_exp = { e with I.exp_seq_exp1 = new_exp1; I.exp_seq_exp2 = new_exp2 } in
        I.Seq new_exp
      | I.ConstDecl e1 -> 
        let ident_list = List.map fst3 e1.I.exp_const_decl_decls in
        let new_ident_list = List.map (create_new_ids global_vars) ident_list in
        let renlist = List.map2 join2 ident_list new_ident_list in
        let new_exp2 = x_add Astsimp.rename_exp renlist e.I.exp_seq_exp2 in
        let new_exp2 = check_and_change global_vars new_exp2 in
        let new_const_decls = List.map2 change_fst3 e1.I.exp_const_decl_decls new_ident_list in
        let new_exp1 = I.ConstDecl { e1 with I.exp_const_decl_decls = new_const_decls } in
        let new_exp = { e with I.exp_seq_exp1 = new_exp1; I.exp_seq_exp2 = new_exp2 } in
        I.Seq new_exp
      | _ ->
        let new_exp1 = check_and_change global_vars e.I.exp_seq_exp1 in
        let new_exp2 = check_and_change global_vars e.I.exp_seq_exp2 in
        let new_exp = { e with I.exp_seq_exp1 = new_exp1; I.exp_seq_exp2 = new_exp2 } in
        I.Seq new_exp
    end
  | I.Unary e -> 
    begin
      let new_subexp = check_and_change global_vars e.I.exp_unary_exp in
      let new_exp = { e with I.exp_unary_exp = new_subexp } in
      I.Unary new_exp
    end
  | I.While e ->
    begin
      let new_cond = check_and_change global_vars e.I.exp_while_condition in
      let new_body = check_and_change global_vars e.I.exp_while_body in
      let new_exp = { e with I.exp_while_condition = new_cond; exp_while_body = new_body } in
      I.While new_exp
    end
  | I.Try e ->
    I.Try {e with 
           I.exp_try_block = check_and_change global_vars e.I.exp_try_block;
           I.exp_catch_clauses = List.map (check_and_change global_vars) e.I.exp_catch_clauses;
           I.exp_finally_clause = List.map (check_and_change global_vars) e.I.exp_finally_clause;
          }
  | I.Raise e -> I.Raise {e with 
                          I.exp_raise_val = match e.I.exp_raise_val with 
                            | None -> None
                            | Some e -> Some (check_and_change global_vars e)}
  | I.Par e ->
    let cl = List.map (fun c -> { c with 
                                  I.exp_par_case_body = check_and_change global_vars c.I.exp_par_case_body }) e.I.exp_par_cases in
    I.Par { e with I.exp_par_cases = cl; }

(** Rename the parameters and local variables if there is conflict with global variables 
    	@param proc procedure declaration
    	@return the new procedure declaration without name conflict *)
let resolve_name_conflict (proc : I.proc_decl) : I.proc_decl =
  match proc.I.proc_body with
    None -> proc
  | Some e ->
    begin
      let (r,w) = Hashtbl.find h proc.I.proc_name in
      let global_vars = IdentSet.union r w in
      let new_exp1 = check_and_change global_vars e in
      let new_proc_args = List.map (create_new_params global_vars) proc.I.proc_args in
      let params = List.map get_local_id proc.I.proc_args in
      let new_params = List.map get_local_id new_proc_args in
      let renlist = List.map2 join2 params new_params in
      let new_exp2 = x_add Astsimp.rename_exp renlist new_exp1 in
      let renspeclist1 = List.map (addp Primed) renlist in
      let renspeclist2 = List.map (addp Unprimed) renlist in
      let renspeclist = renspeclist1 @ renspeclist2 in
      let new_static_specs = Iformula.subst_struc renspeclist proc.I.proc_static_specs in
      let new_dynamic_specs = Iformula.subst_struc renspeclist proc.I.proc_dynamic_specs in
      let new_body = Some new_exp2 in
      { proc with I.proc_args = new_proc_args; I.proc_static_specs = new_static_specs; I.proc_dynamic_specs = new_dynamic_specs; I.proc_body = new_body }
    end

(* Functions to translate the program *)

(** Convert a global variable into a parameter 
    	@param modifier the modifier of the new parameter
    	@param var_decl the variable declaration 
    	@return the new parameter *)
let global_to_param (modifier : I.param_modifier) (var_decl : I.exp_var_decl) : I.param =
  let (id, exp, loc) = List.hd var_decl.I.exp_var_decl_decls in
  { I.param_type = var_decl.I.exp_var_decl_type;
    I.param_name = id;
    I.param_mod = modifier;
    I.param_loc = loc; }

(** Add the global variables into the parameter list 
    	@param read_global_var list of read-only global variable declaration
    	@param write_global_var list of read/write global variable declaration
    	@param args list of current parameters
    	@return new list of parameters *)
let add_global_as_param (read_global_var : I.exp_var_decl list) (write_global_var : I.exp_var_decl list) (args : I.param list) : I.param list =
  let read_param_ext = 
    if (!Globals.pass_global_by_value) then
      List.map (global_to_param I.NoMod) read_global_var
    else
      List.map (global_to_param I.RefMod) read_global_var 
  in
  let write_param_ext = List.map (global_to_param I.RefMod) write_global_var in
  let param_ext = read_param_ext @ write_param_ext in
  args @ param_ext


(** Extend the parameter list of a procedure with global variables 
    	@param global_var_decls list of global variable declaration 
    	@param proc current procedure declaration
    	@return new procedure declaration *)
let extend_args (global_var_decls : I.exp_var_decl list) (proc : I.proc_decl) : I.proc_decl =
  let (read_global_var, write_global_var) = 
    get_read_write_global_var global_var_decls proc in
  let new_param_list = add_global_as_param read_global_var write_global_var proc.I.proc_args in
  { proc with I.proc_args = new_param_list }

(** Extend the old procedure declaration to the new one 
    	@param temp_procs list of temporary procedure declarations
    	@param decl current procedure declaration
    	@return new procedure declaration *)
let extend_proc (temp_procs : I.proc_decl list) (decl : I.proc_decl) : I.proc_decl =
  let new_body = 
    match decl.I.proc_body with
      None -> None
    | Some e -> Some (extend_body temp_procs e)
  in
  { decl with I.proc_body = new_body }

(** Infer immutability annotation variables for each heap elements in
    every proc when @imm_pre and/or @imm_post is set.
    @param prog current program declaration
    @return new program declaration *)
let infer_imm_ann (prog: I.prog_decl) : I.prog_decl =
  let fresh_pred loc = fresh_var_name rel_default_prefix_name loc.start_pos.Lexing.pos_lnum in
  let fresh loc = fresh_var_name imm_var_prefix loc.start_pos.Lexing.pos_lnum in

  (** Infer immutability annotation variables for one proc,
        return the resulting proc and required rel declaration *)
  let infer_imm_ann_proc (proc: I.proc_decl) : (I.proc_decl * I.rel_decl option * I.rel_decl option) =
    let open Iformula in
    let proc_loc = proc.proc_loc in
    let use_mutable = ref true in
    let v_stack = new Gen.stack in
    let pre_stack = new Gen.stack in
    let inf_var_stack = new Gen.stack in
    let pre_rel = ref None in
    let post_rel = ref None in
    let assign_ann_or_var ann loc = match ann with
      | Ipure.NoAnn -> if !use_mutable then (Ipure.ConstAnn Mutable, None)
                       else (let f = (fresh loc, Unprimed) in (PolyAnn (f, loc), Some f))
      | Ipure.PolyAnn (f, loc) -> (ann, Some f)
      | ann -> (ann, None) in
    let ann_heap = function
      | HeapNode hp ->
         let loc = hp.h_formula_heap_pos in
         let (h_imm, v) = assign_ann_or_var hp.h_formula_heap_imm loc in
         let () = map_opt_def () (fun v -> v_stack # push v) v in
         Some (HeapNode { hp with h_formula_heap_imm = h_imm })
      | HeapNode2 hp ->
         let loc = hp.h_formula_heap2_pos in
         let (h_imm, v) = assign_ann_or_var hp.h_formula_heap2_imm loc in
         let () = map_opt_def () (fun v -> v_stack # push v) v in
         Some (HeapNode2 { hp with h_formula_heap2_imm = h_imm })
      | _ -> None
    in
    let ann_heap h =
                  Debug.no_1 "ann_heap" Iprinter.string_of_h_formula (pr_opt Iprinter.string_of_h_formula) ann_heap h in
    let and_pure_with_rel relname rel_params formula loc =
      let and_with_rel relname pure =
        let open Ipure in
        let args = List.map (fun i -> Var (i, loc)) rel_params in
        Some (mkAnd pure (BForm ((RelForm (relname, args, loc), None), None)) loc) in
      transform_formula (None, nonef, nonef, (nonef, nonef, (and_with_rel relname), nonef, nonef)) formula
    in
    let mk_rel rel_params loc =
      let rn = fresh_pred loc in
      match rel_params with
      | [] -> None
      | rel_params -> Some ({
        I.rel_name = rn;
        I.rel_typed_vars = List.map (fun (i,_) -> (AnnT, i)) rel_params;
        I.rel_formula = Ipure.mkTrue no_pos
      })
    in
    let rec ann_struc_formula_1 = function
      | EInfer ff ->
         let neither_flag_is_set = (not ff.formula_inf_obj # is_pre_imm) &&
                                     (not ff.formula_inf_obj # is_post_imm) in
         use_mutable := neither_flag_is_set;
         None
      | EAssume ff ->
         pre_stack # push_list (v_stack # get_stk);
         if !use_mutable then Some (EAssume ff) else
           Some (EAssume { ff with formula_assume_simpl =
                                transform_formula transform_1 ff.formula_assume_simpl })
      | _ -> None
    and transform_1 = (ann_struc_formula_1, nonef, ann_heap, (somef, somef, somef, somef, somef)) in
    let ann_postcondition = function
      | EAssume ff ->
         if (not (v_stack # is_empty)) then
            let postcondition = ff.formula_assume_simpl in
            let post_rel = match !post_rel with Some p -> p | None -> failwith "Not possible (infer_imm_ann_proc)" in
            let rel_params = List.map (fun (_,i) -> (i, Unprimed)) post_rel.I.rel_typed_vars in
            let postcondition_with_rel = and_pure_with_rel post_rel.I.rel_name
                                                        rel_params postcondition (pos_of_formula postcondition) in
            let () = x_binfo_hp (add_str "updated_postcondition:" Iprinter.string_of_formula) postcondition_with_rel no_pos in
            Some (EAssume { ff with formula_assume_simpl = postcondition_with_rel })
        else Some (EAssume ff)
      | _ -> None
    in
    (* And the pure part of pre/post condition with relation
       Assumption : pre_rel and post_rel must have been created
     *)
    let ann_struc_formula_2 = function
      | EInfer ff ->
         begin match ff.formula_inf_continuation with
         | EBase ({ formula_struc_base = precondition; formula_struc_pos = loc } as ebase) ->
            let new_ebase =
              if (not (pre_stack # is_empty)) then
                let pre_rel = match !pre_rel with Some p -> p | None -> failwith "Not possible (infer_imm_ann_proc)" in
                let rel_params = List.map (fun (_,i) -> (i, Unprimed)) pre_rel.I.rel_typed_vars in
                let precondition_with_rel = and_pure_with_rel pre_rel.I.rel_name rel_params precondition loc in
                { ebase with formula_struc_base = precondition_with_rel }
              else ebase in
            let new_continuation =
              if (not (v_stack # is_empty)) then
                let transform = (ann_postcondition, nonef, nonef, (nonef, nonef, nonef, nonef, nonef)) in
                let base_continuation = map_opt (transform_struc_formula transform) ebase.formula_struc_continuation in
                EBase { new_ebase with formula_struc_continuation = base_continuation }
              else EBase new_ebase in
            let new_inf_vars =
              if (not (v_stack # is_empty)) then
                let rel_to_var rel = match rel with
                  | Some p -> [(p.I.rel_name, Unprimed)]
                  | None -> [] in
                (rel_to_var !post_rel)@(rel_to_var !pre_rel)@ff.formula_inf_vars
              else ff.formula_inf_vars in
            Some (EInfer { ff with formula_inf_continuation = new_continuation;
                                   formula_inf_vars = new_inf_vars })
         | _ -> None
         end
      | other -> Some other
    in
    let transform_2 = (ann_struc_formula_2, somef, somef, (somef, somef, somef, somef, somef)) in
    let pss =
      let pss_1 = transform_struc_formula transform_1 proc.proc_static_specs in
      if (!use_mutable) then pss_1
      else
        (pre_rel := mk_rel (pre_stack # get_stk) no_pos;
        if (not !use_mutable) then post_rel := mk_rel (v_stack # get_stk) no_pos;
        transform_struc_formula transform_2 pss_1) in
    ({ proc with proc_static_specs = pss }, !pre_rel, !post_rel)
  in
  let (new_proc_decls, rel_list) =
    let helper proc (proc_decls, rel_list) =
      let (proc_decl, pre_rel, post_rel) = infer_imm_ann_proc proc in
      let rel_list_1 = map_opt_def rel_list (fun r -> r::rel_list) pre_rel in
      let rel_list_2 = map_opt_def rel_list_1 (fun r -> r::rel_list) post_rel in
      (proc_decl::proc_decls, rel_list_2) in
    List.fold_right helper prog.prog_proc_decls ([], []) in
  prog.I.prog_rel_decls <- prog.I.prog_rel_decls @ rel_list;
  prog.I.prog_rel_ids <- prog.I.prog_rel_ids @
                           (List.map (fun x ->
                                      let tl,_ = List.split x.I.rel_typed_vars in
                                      (RelT tl,x.rel_name)) rel_list);
  { prog with I.prog_proc_decls = new_proc_decls }

let infer_imm_ann (prog : I.prog_decl) : I.prog_decl =
  let pr = Iprinter.string_of_program in
  Debug.no_1 "infer_imm_ann" pr pr infer_imm_ann prog

(** Translate an input program into an intermediate input program with global variables as parameters
    	@param prog current program declaration
    	@return new program declaration *)
let trans_global_to_param (prog : I.prog_decl) : I.prog_decl =
  let new_prog =
    match prog.I.prog_global_var_decls with
    | [] -> prog
    | _ ->
      let () = find_read_write_global_var_all_procs prog in
      let temp_decls1 = List.map resolve_name_conflict prog.I.prog_proc_decls in
      let temp_decls2 = List.map (extend_args prog.I.prog_global_var_decls) temp_decls1 in
      let new_proc_decls = List.map (extend_proc temp_decls2) temp_decls2 in
      { prog with I.prog_proc_decls = new_proc_decls }
  in
  infer_imm_ann new_prog

let trans_global_to_param (prog : I.prog_decl) : I.prog_decl =
  let pr = Iprinter.string_of_program in
  Debug.no_1 "trans_global_to_param" pr pr 
    trans_global_to_param prog
