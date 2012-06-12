(* global types and utility functions *)

type ident = string
type constant_flow = ident

type nflow = (int*int)(*numeric representation of flow*)

type perm_split = 
  | PLeft
  | PRight 

and perm_modifier = perm_split list
	
	
and branch_label = string	(*formula branches*)
type formula_label = (int*string)
and control_path_id_strict = formula_label
and control_path_id = control_path_id_strict  option(*identifier for if, catch, call*)
type path_label = int (*which path at the current point has been taken 0 -> then branch or not catch or first spec, 1-> else or catch taken or snd spec...*)
type path_trace = (control_path_id_strict * path_label) list 

and loc = {
			start_pos : Lexing.position (* might be expanded to contain more information *);
			mid_pos : Lexing.position;
			end_pos : Lexing.position;
			}

and primed =
  | Primed
  | Unprimed

(* and prim_type =  *)
(*   | TVar of int *)
(*   | Bool *)
(*   | Float *)
(*   | Int *)
(*   | Void *)
(*   | BagT of prim_type *)
(*   | List *)

(* TODO : move typ here in future *)
type typ =
  | UNK 
  | TVar of int
  | Bool
  | Float
  | Int
  | NUM
  | Void
  | List of typ
  | BagT of typ
  (* | Prim of prim_type *)
  | Named of ident (* named type, could be enumerated or object *)
  | Array of (typ * int option) (* base type and optional dimension *)

(*
  Data types for code gen
*)

type mode = 
  | ModeIn
  | ModeOut

(* let rec string_of_prim_type = function  *)
(*   | Bool          -> "boolean" *)
(*   | Float         -> "float" *)
(*   | Int           -> "int" *)
(*   | Void          -> "void" *)
(*   | TVar i       -> "TVar["^(string_of_int i)^"]" *)
(*   | BagT t        -> "bag("^(string_of_prim_type t)^")" *)
(*   | List          -> "list" *)

let proving_loc : (loc option) ref = ref None

let set_proving_loc p =
  proving_loc := Some p

let clear_proving_loc () =
  proving_loc := None



(* pretty printing for types *)
let rec string_of_typ = function 
   (* may be based on types used !! *)
  | UNK          -> "Unknown"
  | Bool          -> "boolean"
  | Float         -> "float"
  | Int           -> "int"
  | Void          -> "void"
  | NUM          -> "NUM"
  | BagT t        -> "bag("^(string_of_typ t)^")"
  | TVar t        -> "TVar["^(string_of_int t)^"]"
  | List t        -> "list("^(string_of_typ t)^")"
  (* | Prim t -> string_of_prim_type t  *)
  | Named ot -> if ((String.compare ot "") ==0) then "null" else ot
  | Array (et, _) -> (string_of_typ et) ^ "[]" (* An Hoa *)
;;

let subs_tvar_in_typ t (i:int) nt =
  let rec helper t = match t with
    | TVar j -> if i==j then nt else t
    | BagT et -> BagT (helper et)
    | List et -> List (helper et)
    | Array (et,d) -> Array (helper et,d)
    | _ -> t
  in helper t
;;

let null_type = Named ""
;;

let dim_subtype d1 d2 =
  match d1,d2 with
    | _, None -> true
    | None, Some _ -> false
    | Some i1, Some i2 -> i1==i2
;;

let rec sub_type (t1 : typ) (t2 : typ) = 
  match t1,t2 with
    | UNK, _ -> true
    | Named c1, Named c2 ->
          if c1=c2 then true
          else c1=""
    | Array (et1,d1), Array (et2,d2) ->
          if dim_subtype d1 d2 then sub_type et1 et2
          else false
    | BagT et1, BagT et2 -> sub_type et1 et2
    | List et1, List et2 -> sub_type et1 et2
    | Int, NUM        -> true
    | Float, NUM        -> true
    | p1, p2 -> p1=p2
;;
 
let rec s_i_list l c = match l with 
  | [] -> ""
  | h::[] -> h 
  | h::t -> h ^ c ^ (s_i_list t c)
;;
let string_of_ident_list l = "["^(s_i_list l ",")^"]"

let idf (x:'a) : 'a = x
let idf2 v e = v 
let nonef v = None
let voidf e = ()
let voidf2 e f = ()
let somef v = Some v
let or_list = List.fold_left (||) false
let and_list = List.fold_left (&&) true

let push_opt_void_pair e = match e with
  | None -> None
  | Some s -> Some (s,()) 

let push_opt_val opt v = match opt with
  | None -> None
  | Some s -> Some (s, v)

let push_opt_val_rev opt v = match opt with
  | None -> None
  | Some s -> Some (v, s)

(* global constants *)

let no_pos = 
	let no_pos1 = { Lexing.pos_fname = "";
				   Lexing.pos_lnum = 0;
				   Lexing.pos_bol = 0; 
				   Lexing.pos_cnum = 0 } in
	{start_pos = no_pos1; mid_pos = no_pos1; end_pos = no_pos1;}

let post_pos = ref no_pos
let set_post_pos p = post_pos := p

let entail_pos = ref no_pos
let set_entail_pos p = entail_pos := p

let flow = "flow"
let top_flow = "__flow"
(*let any_flow = "__Any"*)
let n_flow = "__norm"
let cont_top = "__Cont_top"
let brk_top = "__Brk_top"
let c_flow = "__c-flow"
let raisable_class = "__Exc"
let ret_flow = "__Ret"
let spec_flow = "__Spec"
let false_flow = "__false"
let abnormal_flow = "__abnormal"
let stub_flow = "__stub"

let n_flow_int = ref ((-1,-1):nflow)
let ret_flow_int = ref ((-1,-1):nflow)
let spec_flow_int = ref ((-1,-1):nflow)
let top_flow_int = ref ((-2,-2):nflow)
let exc_flow_int = ref ((-2,-2):nflow) (*abnormal flow*)
let false_flow_int = (0,0)
(*let stub_flow_int = (-3,-3)*)

let res = "res"

let self = "self"

let this = "this"

let perm = "perm"

(*in case the option of saving provers temp files to a different directory is enabled, the value of 
  this variable is going to be changed accordingly in method set_tmp_files_path *)
(*let tmp_files_path = "/tmp/"*)

(* *GLOBAL_VAR* input filename, used by iparser.mly, astsimp.ml and main.ml
 * moved here from iparser.mly *)

(* command line options *)

let instantiation_variants = ref 0

let omega_simpl = ref true

let source_files = ref ([] : string list)

let input_file_name =ref ""

let procs_verified = ref ([] : string list)

let false_ctx_line_list = ref ([] : loc list)

let verify_callees = ref false

let elim_unsat = ref false

(* let lemma_heuristic = ref false *)

let elim_exists = ref true

let allow_imm = ref false

let print_proc = ref false

let perm_prof = ref false

let check_all = ref true

let use_field = ref false

let large_bind = ref false

let print_x_inv = ref false

let hull_pre_inv = ref false

let use_coercion = ref true

let case_split = ref false

let use_set = ref true

let wrap_exist = ref false

let move_exist_to_LHS = ref false

let max_renaming = ref false

let anon_exist = ref true

let simplify_pure = ref false

let enable_norm_simp = ref false

let n_xpure = ref 1

let check_coercions = ref false

let show_gist = ref false

let trace_all = ref false

let print_mvars = ref false

let enable_sat_statistics = ref false

let wrap_exists_implicit_explicit = ref false

let profiling = ref false

let enable_syn_base_case = ref false

let enable_case_inference = ref false

let print_core = ref false

let print_err_sleek = ref false

let enable_prune_cache = ref true

let enable_counters = ref true

let enable_fast_imply = ref false

let failure_analysis = ref false

let seq_to_try = ref false

let print_input = ref false

let pass_global_by_value = ref false

let allow_pred_spec = ref false

let enable_frac_perm = ref false

let enable_frac_print = ref false

let prune_cnt_limit = ref 2

let suppress_warning_msg = ref false
let disable_elim_redundant_ctr = ref false

let enable_strong_invariant = ref false
let enable_aggressive_prune = ref false
let disable_aggressive_prune = ref false
let prune_with_slice = ref false

let enulalias = ref false

let pass_global_by_value = ref false

let exhaust_match = ref false

let memo_verbosity = ref 2

let profile_threshold = 0.5 

let no_cache_formula = ref false

let enable_incremental_proving = ref false


  (*for cav experiments*)
  let f_1_slice = ref false
  let f_2_slice = ref false
  let no_memoisation = ref false
  let no_incremental = ref false
  let no_LHS_prop_drop = ref false
  let no_RHS_prop_drop = ref false
  let do_sat_slice = ref false
  
let add_count (t: int ref) = 
	t := !t+1


(* utility functions *)

let omega_err = ref false

let seq_number = ref 10

let sat_timeout = ref 10.
let imply_timeout = ref 10.
  
(* let reporter = ref (fun _ -> raise Not_found) *)

(* let report_error2 (pos : loc) (msg : string) = *)
(*   let _ = *)
(*     try !reporter pos msg *)
(*     with Not_found -> *)
(*       let report pos msg = *)
(*         let output = Printf.sprintf "\n%s:%d:%d: %s\n" *)
(*           pos.start_pos.Lexing.pos_fname *)
(*           pos.start_pos.Lexing.pos_lnum *)
(*           (pos.start_pos.Lexing.pos_cnum - pos.start_pos.Lexing.pos_bol) *)
(*           msg *)
(*         in *)
(*         print_endline output *)
(*       in *)
(*       reporter := report; *)
(*       report pos msg *)
(*   in *)
(*   failwith "Error detected" *)

let branch_point_id = ref 0

let reset_formula_point_id () = () (*branch_point_id:=0*)

let iast_label_table = ref ([]:(control_path_id*string*((control_path_id*path_label*loc) list)*loc) list)

let locs_of_path_trace (pt: path_trace): loc list =
  let eq_path_id pid1 pid2 = match pid1, pid2 with
    | Some _, None -> false
    | None, Some _ -> false
    | None, None -> true
    | Some (i1, s1), Some (i2, s2) -> i1 = i2
  in
  let path_label_list_of_id pid =
    let _, _, label_list, _ = List.find (fun (id, _, _ , _) -> eq_path_id pid id) !iast_label_table in
    label_list
  in
  let loc_of_label plbl ref_list =
    let _, _, loc = List.find (fun (_, lbl, _) -> plbl = lbl) ref_list in
    loc
  in
  let find_loc pid plbl = 
    let label_list = path_label_list_of_id pid in
    loc_of_label plbl label_list
  in
  List.map (fun (pid, plbl) -> find_loc (Some pid) plbl) pt


let locs_of_partial_context ctx =
  let failed_branches = fst ctx in
  let path_traces = List.map fst failed_branches in
  let loc_list_list = List.map locs_of_path_trace path_traces in
  List.flatten loc_list_list


let fresh_formula_label (s:string) :formula_label = 
	branch_point_id := !branch_point_id + 1;
	(!branch_point_id,s)
  
let fresh_branch_point_id (s:string) : control_path_id = Some (fresh_formula_label s)
let fresh_strict_branch_point_id (s:string) : control_path_id_strict = (fresh_formula_label s)

let tmp_files_path = ref ""

(*path for the temporary files used by the prover. If you change this path here it is 
  mandatory to also change the value of TMP_FILES_PATH in Makefile accordingly to the changes made here*)
let set_tmp_files_path () = 	
	begin
      (try
		ignore (Unix.mkdir ("/tmp/" ^ Unix.getlogin()) 0o766;)		 
      with
		Unix.Unix_error (_, _, _) -> (); );
	  (try
		ignore (Unix.chmod ("/tmp/" ^ Unix.getlogin()) 0o766;)		 
      with
		Unix.Unix_error (_, _, _) -> (); );
      (try
		ignore (Unix.mkdir ("/tmp/" ^ Unix.getlogin() ^ "/prover_tmp_files/") 0o766) 
      with
		Unix.Unix_error (_, _, _) -> (););
	  (try
		ignore (Unix.chmod ("/tmp/" ^ Unix.getlogin() ^ "/prover_tmp_files/") 0o766;)		 
      with
		Unix.Unix_error (_, _, _) -> (););
	tmp_files_path := ("/tmp/" ^ Unix.getlogin() ^ "/prover_tmp_files/")
	end
	
let fresh_int () =
  seq_number := !seq_number + 1;
  !seq_number

let seq_number2 = ref 0

let fresh_int2 () =
  seq_number2 := !seq_number2 + 1;
  !seq_number2

let reset_int2 () =
  seq_number2 := 0

let fresh_int () =
  seq_number := !seq_number + 1;
  !seq_number

let fresh_var_name (tn:string)(ln:int):string = 
	("v_"^tn^"_"^(string_of_int ln)^"_"^(string_of_int (fresh_int ())))

let fresh_trailer () = 
  let str = string_of_int (fresh_int ()) in
  (*-- 09.05.2008 *)
	(*let _ = (print_string ("\n[globals.ml, line 103]: fresh name = " ^ str ^ "\n")) in*)
	(* 09.05.2008 --*)
    "_" ^ str

let fresh_any_name (any:string) = 
  let str = string_of_int (fresh_int ()) in
    any ^"_"^ str

let fresh_name () = 
  let str = string_of_int (fresh_int ()) in
    "f_r_" ^ str

let fresh_label pos = 
 (* let str = string_of_int (fresh_int ()) in*)
    "f_l_" ^ (string_of_int pos.start_pos.Lexing.pos_lnum)^"_"^(string_of_int (fresh_int ()))
	
let fresh_names (n : int) = (* number of names to be generated *)
  let names = ref ([] : string list) in
    for i = 1 to n do
      names := (fresh_name ()) :: !names
    done;
    !names

let formula_cache_no_series = ref 0

let fresh_formula_cache_no  () = 
  formula_cache_no_series := !formula_cache_no_series +1;
  !formula_cache_no_series
    
let gen_ext_name c1 c2 = "Ext~" ^ c1 ^ "~" ^ c2


let string_of_loc (p : loc) = p.start_pos.Lexing.pos_fname ^ "_" ^ (string_of_int p.start_pos.Lexing.pos_lnum)^"_"^
	(string_of_int (p.start_pos.Lexing.pos_cnum-p.start_pos.Lexing.pos_bol))

let string_of_pos (p : Lexing.position) = "("^string_of_int(p.Lexing.pos_lnum) ^","^string_of_int(p.Lexing.pos_cnum-p.Lexing.pos_bol) ^")"
;;

let string_of_full_loc (l : loc) = "{"^(string_of_pos l.start_pos)^","^(string_of_pos l.end_pos)^"}";;

let string_of_loc_by_char_num (l : loc) = 
  Printf.sprintf "(%d-%d)"
    l.start_pos.Lexing.pos_cnum
    l.end_pos.Lexing.pos_cnum

let seq_local_number = ref 0

let fresh_local_int () =
  seq_local_number := !seq_local_number + 1;
  !seq_local_number

let fresh_local_var_name (tn : string) : string =
  tn ^ "_local_" ^ (string_of_int (fresh_local_int ()))

let join2 a b = (a,b)

let fst3 (x,_,_) = x

let snd3 (_,x,_) = x

let change_fst3 (_,b,c) a = (a,b,c)

let path_trace_eq p1 p2 =
  let rec eq pt1 pt2 = match pt1,pt2 with
    | [],[] -> true
    | [],xs -> false
    |  xs,[] -> false
    |  ((a1,_),b1)::zt1,((a2,_),b2)::zt2 -> a1=a2 && b1=b2 && (eq zt1 zt2)
  in eq (List.rev p1) (List.rev p2)

let path_trace_lt p1 p2 =
  let rec lt pt1 pt2 = match pt1,pt2 with
    | [],[] -> false
    | [],xs -> true
    | xs,[] -> false
    | ((a1,_),b1)::zt1,((a2,_),b2)::zt2 -> (a1<a2) || (a1=a2 && b1<b2) || (a1=a2 & b1=b2 && lt zt1 zt2)
  in lt (List.rev p1) (List.rev p2)

let path_trace_gt p1 p2 =
  let rec gt pt1 pt2 = match pt1,pt2 with
    | [],[] -> false
    | [],xs -> false
    |  xs,[] -> true
    | ((a1,_),b1)::zt1,((a2,_),b2)::zt2 -> (a1>a2) || (a1=a2 && b1>b2) || (a1=a2 & b1=b2 && gt zt1 zt2)
  in gt (List.rev p1) (List.rev p2)

 
let dummy_exception () = ()

(* convert a tree-like binary object into a list of objects *)
let bin_op_to_list (op:string)
  (fn : 'a -> (string * ('a list)) option) 
  (t:'a) : ('a list) =
  let rec helper t =
    match (fn t) with
      | None -> [t]
      | Some (op2, xs) -> 
          if (op=op2) then 
            List.concat (List.map helper xs)
          else [t]
  in (helper t)

let bin_to_list (fn : 'a -> (string * ('a list)) option) 
  (t:'a) : string * ('a list) =
  match (fn t) with
    | None -> "", [t]
    | Some (op, _) -> op,(bin_op_to_list op fn t)

(*type of process used for communicating with the prover*)
type prover_process_t = {name:string; pid: int; inchannel: in_channel; outchannel: out_channel; errchannel: in_channel }

(*methods that need to be defined in order to use a prover incrementally - if the prover provides this functionality*)
class type ['a] incremMethodsType = object
  val process: prover_process_t option ref
  method start_p: unit -> prover_process_t
  method stop_p:  prover_process_t -> unit
  method push: prover_process_t -> unit
  method pop: prover_process_t -> unit
  method popto: prover_process_t -> int -> unit
  method imply: (prover_process_t option * bool) option -> 'a -> 'a -> string -> bool
  method set_process: prover_process_t -> unit
  method get_process: unit -> prover_process_t option
  (* method add_to_context: 'a -> unit *)
end


