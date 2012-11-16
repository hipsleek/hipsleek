(* global types and utility functions *)
(* module Lb = Label_only *)
    (* circular with Lb *)

type ('a,'b) twoAns = 
  | FstAns of 'a
  | SndAns of 'b

type ident = string
type constant_flow = string

exception Illegal_Prover_Format of string

let reverify_flag = ref false
let ineq_opt_flag = ref false

let illegal_format s = raise (Illegal_Prover_Format s)


(* type nflow = (int*int)(\*numeric representation of flow*\) *)

type bformula_label = int
and ho_branch_label = string
(*and branch_label = spec_label	(*formula branches*)*)


type formula_label = (int*string)

and control_path_id_strict = formula_label

and control_path_id = control_path_id_strict  option
    (*identifier for if, catch, call*)


let empty_label = (0,"")
let app_e_l c = (empty_label, c)
let combine_lbl (i1,s1)(i2,s2) = match s1 with 
  | "" -> (match s2 with 
            | "" -> (i1,s1)
            | _ -> (i2,s2))
  | _ -> (i1,s1)


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

and heap_ann = Lend | Imm | Mutable

and vp_ann =  VP_Zero | VP_Full | VP_Value (* | VP_Ref *)

and term_ann = 
  | Term    (* definitely terminates *)
  | Loop    (* definitely loops *)
  | MayLoop (* don't know *)
  | Fail of term_fail    (* failed because of invalid trans *)

and term_fail =
  | TermErr_May
  | TermErr_Must

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
  | AnnT
  | Bool
  | Float
  | Int
  | NUM
  | Void
  | List of typ
  | BagT of typ
  (* | Prim of prim_type *)
  | Named of ident (* named type, could be enumerated or object *)
  | Array of (typ * int) (* base type and dimension *)
  | RelT (* relation type *)
  | Tree_sh
  (* | FuncT (\* function type *\) *)


let barrierT = Named "barrier"
(*
  Data types for code gen
*)

type mode = 
  | ModeIn
  | ModeOut
  
  

type perm_type =
  | NoPerm (*no permission at all*)
  | Frac (*fractional permissions*)
  | Count (*counting permissions*)
  | Dperm (*distinct fractional shares*)
  
let perm = ref NoPerm

(* let rec string_of_prim_type = function  *)
(*   | Bool          -> "boolean" *)
(*   | Float         -> "float" *)
(*   | Int           -> "int" *)
(*   | Void          -> "void" *)
(*   | TVar i       -> "TVar["^(string_of_int i)^"]" *)
(*   | BagT t        -> "bag("^(string_of_prim_type t)^")" *)
(*   | List          -> "list" *)

let no_pos = 
	let no_pos1 = { Lexing.pos_fname = "";
				   Lexing.pos_lnum = 0;
				   Lexing.pos_bol = 0; 
				   Lexing.pos_cnum = 0 } in
	{start_pos = no_pos1; mid_pos = no_pos1; end_pos = no_pos1;}

let is_no_pos l = (l.start_pos.Lexing.pos_cnum == 0)

let is_float_type (t:typ) = match t with
  | Float -> true
  | _ -> false

let string_of_heap_ann a =
  match a with
    | Lend -> "@L"
    | Imm -> "@I"
    | Mutable -> "@M"

let int_of_heap_ann a =
  match a with
    | Lend -> 2
    | Imm -> 1
    | Mutable -> 0

let string_of_vp_ann a =  
  (match a with
    | VP_Zero -> "@zero"
    | VP_Full -> "@full"
    | VP_Value -> "@value"
    (* | VP_Ref-> "@p_ref" *)
  )

let string_of_term_ann a =
  match a with
  | Term -> "Term"
  | Loop -> "Loop"
  | MayLoop -> "MayLoop"
  | Fail f -> match f with
    | TermErr_May -> "TermErr_May"
    | TermErr_Must -> "TermErr_Must"

let string_of_loc (p : loc) = 
    Printf.sprintf "File \"%s\",Line:%d,Col:%d"
    p.start_pos.Lexing.pos_fname 
    p.start_pos.Lexing.pos_lnum
	(p.start_pos.Lexing.pos_cnum-p.start_pos.Lexing.pos_bol)
;;

let string_of_pos (p : Lexing.position) = 
    Printf.sprintf "(Line:%d,Col:%d)"
    p.Lexing.pos_lnum
	(p.Lexing.pos_cnum-p.Lexing.pos_bol)
;;

(* let string_of_pos (p : Lexing.position) = "("^string_of_int(p.Lexing.pos_lnum) ^","^string_of_int(p.Lexing.pos_cnum-p.Lexing.pos_bol) ^")" *)
(* ;; *)

(* An Hoa *)
let line_number_of_pos p = string_of_int (p.start_pos.Lexing.pos_lnum)

let string_of_full_loc (l : loc) = "{"^(string_of_pos l.start_pos)^","^(string_of_pos l.end_pos)^"}";;

let string_of_loc_by_char_num (l : loc) = 
  Printf.sprintf "(%d-%d)"
    l.start_pos.Lexing.pos_cnum
    l.end_pos.Lexing.pos_cnum

(* class prog_loc = *)
(*    object  *)
(*      val mutable lc = None *)
(*      method is_avail : bool = match lc with *)
(*        | None -> false *)
(*        | Some _ -> true *)
(*      method set (nl:loc) = lc <- Some nl *)
(*      method get :loc = match lc with *)
(*        | None -> no_pos *)
(*        | Some p -> p *)
(*      method reset = lc <- None *)
(*      method string_of : string = match lc with *)
(*        | None -> "None" *)
(*        | Some l -> (string_of_loc l) *)
(*      method string_of_pos : string = match lc with *)
(*        | None -> "None" *)
(*        | Some l -> (string_of_pos l.start_pos) *)
(*    end;; *)

(* Option for proof logging *)
let proof_logging = ref false
let proof_logging_txt = ref false
let proof_logging_time = ref 0.000
let sleek_src_files = ref ([]: string list)
(*Proof logging facilities*)
class ['a] store (x_init:'a) (epr:'a->string) =
   object 
     val emp_val = x_init
     val mutable lc = None
     method is_avail : bool = match lc with
       | None -> false
       | Some _ -> true
     method set (nl:'a) = lc <- Some nl
     method get :'a = match lc with
       | None -> emp_val
       | Some p -> p
     method reset = lc <- None
     method string_of : string = match lc with
       | None -> "Why None?"
       | Some l -> (epr l)
   end;;

(* this will be set to true when we are in error explanation module *)
class failure_mode =
object
  inherit [bool] store false string_of_bool
end;;


class prog_loc =
object
  inherit [loc] store no_pos string_of_loc
     method string_of_pos : string = match lc with
       | None -> "None"
       | Some l -> (string_of_pos l.start_pos)
end;;

class proving_type =
object
  inherit [string] store "None" (fun x -> x)
     (* method string_of_string : string = match lc with *)
     (*   | None -> "None" *)
     (*   | Some l -> l *)
end;;

(*Some global vars for logging*)
let proving_loc  = new prog_loc
let post_pos = new prog_loc
let proving_kind = new proving_type
let sleek_kind = new proving_type
let explain_mode = new failure_mode
let return_exp_pid = ref ([]: control_path_id list)	
let z3_proof_log_list = ref ([]: string list)
let z3_time = ref 0.0

let add_to_z3_proof_log_list (f: string) =
	z3_proof_log_list := !z3_proof_log_list @ [f]
	 
let proving_info () = 
  if(proving_kind # is_avail) then
    (
	let temp= if(explain_mode # is_avail) then "FAILURE EXPLAINATION" else proving_kind # string_of in
      	if (post_pos # is_avail) 
        then ("Proving Infor spec:"^(post_pos#string_of_pos) ^" loc:"^(proving_loc#string_of_pos)^" kind::"^temp)
        else 
          let loc_info = 
            if (proving_loc # is_avail) then " loc:"^(proving_loc#string_of_pos)
            else " loc: NONE" 
          in ("Proving Infor spec:"^(post_pos#string_of_pos) ^loc_info^" kind::"^temp)
    )
  else "..no proving kind.."(*"who called is_sat,imply,simplify to be displayed later..."*)
	

let wrap_proving_kind (str : string) exec_function args =
  if (!proof_logging_txt) then
    begin
      let b = proving_kind # is_avail in
      let m = proving_kind # get in
      let _ = proving_kind # set str in 	
      let res = exec_function args in
      let _ =  
        if b then proving_kind # set m 
        else proving_kind # reset
        in res
    end
  else 	
    let res = exec_function args 
    in res
 
(* let wrap_proving_kind (str : string) exec_function args = *)
(*   Debug.no_1 "wrap_proving_kind" pr_id pr_none  *)
(*       (fun _ -> wrap_proving_kind str exec_function args) str *)

(* let post_pos = ref no_pos *)
(* let set_post_pos p = post_pos := p *)

let entail_pos = ref no_pos
let set_entail_pos p = entail_pos := p

(* let set_proving_loc p = proving_loc#set p *)
(*   (\* proving_loc := Some p *\) *)

(* let clear_proving_loc () = proving_loc#reset *)
(*   (\* proving_loc := None *\) *)

(* pretty printing for types *)
let rec string_of_typ (x:typ) : string = match x with
   (* may be based on types used !! *)
  | UNK          -> "Unknown"
  | Bool          -> "boolean"
  | Float         -> "float"
  | Int           -> "int"
  | Void          -> "void"
  | NUM          -> "NUM"
  | AnnT          -> "AnnT"
  | BagT t        -> "bag("^(string_of_typ t)^")"
  | TVar t        -> "TVar["^(string_of_int t)^"]"
  | List t        -> "list("^(string_of_typ t)^")"
  | Tree_sh		  -> "Tsh"
  | RelT        -> "RelT"
  (* | Prim t -> string_of_prim_type t  *)
  | Named ot -> if ((String.compare ot "") ==0) then "null" else ot
  | Array (et, r) -> (* An Hoa *)
	let rec repeat k = if (k == 0) then "" else "[]" ^ (repeat (k-1)) in
		(string_of_typ et) ^ (repeat r)
;;

(* aphanumeric name *)
let rec string_of_typ_alpha = function 
   (* may be based on types used !! *)
  | UNK          -> "Unknown"
  | Bool          -> "boolean"
  | Float         -> "float"
  | Int           -> "int"
  | Void          -> "void"
  | NUM          -> "NUM"
  | AnnT          -> "AnnT"
  | Tree_sh		  -> "Tsh"
  | BagT t        -> "bag_"^(string_of_typ t)
  | TVar t        -> "TVar_"^(string_of_int t)
  | List t        -> "list_"^(string_of_typ t)
  | RelT        -> "RelT"
  (* | Prim t -> string_of_prim_type t  *)
  | Named ot -> if ((String.compare ot "") ==0) then "null" else ot
  | Array (et, r) -> (* An Hoa *)
	let rec repeat k = if (k == 0) then "" else "_arr" ^ (repeat (k-1)) in
		(string_of_typ et) ^ (repeat r)
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



let rec s_i_list l c = match l with 
  | [] -> ""
  | h::[] -> h 
  | h::t -> h ^ c ^ (s_i_list t c)
;;

let string_of_ident_list l = "["^(s_i_list l ",")^"]"
;;

let string_of_primed p =
  match p with
    | Primed -> "'"
    | Unprimed -> ""

let string_of_primed_ident (id,p) =
  id ^ string_of_primed p

let rec s_p_i_list l c = match l with 
  | [] -> ""
  | h::[] -> string_of_primed_ident h
  | h::t -> (string_of_primed_ident h) ^ c ^ (s_p_i_list t c)
;;

let string_of_primed_ident_list l = "["^(s_p_i_list l ",")^"]"
;;

let is_substr s id =
  let len_s = String.length s in
  try
    let s_id = String.sub id 0 len_s in
    if (s = s_id) then true
    else false
  with _ -> false
;;
 
let is_dont_care_var id =
  if is_substr "#" id 
  then true
  (* else if is_substr "Anon_" id then true *)
  else false
;;

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

let no_pos1 = { Lexing.pos_fname = "";
				   Lexing.pos_lnum = 0;
				   Lexing.pos_bol = 0; 
				   Lexing.pos_cnum = 0 } 

let res_name = "res"

let sl_error = "separation entailment"
let logical_error = "logical bug"
let fnc_error = "function call"
let lemma_error = "lemma"
let undefined_error = "undefined"
let timeout_error = "timeout"

let eres_name = "eres"


let self = "self"

let this = "this"

let is_self_ident id = self=id

let thread_name = "thread"  (*special thread id*)
let thread_typ = Int  (*special thread id*)
let proc_typ = Void  (*special thread id*)
let fork_name = "fork"  (*generic, its args can vary*)
let join_name = "join"

let init_name = "init"  (*generic, its args can vary*)
let finalize_name = "finalize"
let acquire_name = "acquire"
let release_name = "release"
let lock_name = "lock"

(*precluded files*)
let header_file_list  = ref (["\"prelude.ss\""] : string list)
let pragma_list = ref ([] : string list)

(*in case the option of saving provers temp files to a different directory is enabled, the value of 
  this variable is going to be changed accordingly in method set_tmp_files_path *)
(*let tmp_files_path = "/tmp/"*)

(* *GLOBAL_VAR* input filename, used by iparser.mly, astsimp.ml and main.ml
 * moved here from iparser.mly *)

(* command line options *)

let instantiation_variants = ref 0

let omega_simpl = ref true

let no_simpl = ref false

let source_files = ref ([] : string list)

let input_file_name =ref ""

let use_split_match = ref false

let consume_all = ref false

let enable_split_lemma_gen = ref false

let procs_verified = ref ([] : string list)

let false_ctx_line_list = ref ([] : loc list)

let b_datan = "barrier"

let verify_callees = ref false

let elim_unsat = ref false
let smart_xpure = ref false
let super_smart_xpure = ref false
  (* this flag is dynamically set depending on
     smart_xpure and xpure0!=xpure1 *)
let smart_memo = ref false

(* let lemma_heuristic = ref false *)

let elim_exists = ref true

(* let allow_imm = ref false (\*imm will delay checking guard conditions*\) *)
let allow_imm = ref true (*imm will delay checking guard conditions*)

let ann_derv = ref false

let ann_vp = ref false (* Disable variable permissions in default, turn on in para5*)

let print_proc = ref false

let check_all = ref true
  
let auto_number = ref true

let use_field = ref false

let large_bind = ref false

let print_x_inv = ref false

let hull_pre_inv = ref false

let use_coercion = ref true

let case_split = ref false

let use_set = ref true

let consistency_checking = ref false

let wrap_exist = ref false

let move_exist_to_LHS = ref false

let max_renaming = ref false

let anon_exist = ref true

let simplify_pure = ref false

let enable_norm_simp = ref false

let print_version_flag = ref false

let elim_exists_flag = ref true

let filtering_flag = ref false

let split_rhs_flag = ref true

let n_xpure = ref 1

let check_coercions = ref false

let num_self_fold_search = ref 0

let self_fold_search_flag = ref false

let show_gist = ref false

let trace_failure = ref false

let trace_all = ref false

let print_mvars = ref false

let print_type = ref false

(* let enable_sat_statistics = ref false *)

let wrap_exists_implicit_explicit = ref false

let profiling = ref false

let enable_syn_base_case = ref false

let enable_case_inference = ref false

let print_core = ref false

let print_err_sleek = ref false

let enable_prune_cache = ref true

let enable_counters = ref false

let enable_fast_imply = ref false

let failure_analysis = ref false

let seq_to_try = ref false

let print_input = ref false

let pass_global_by_value = ref false

(* let allow_pred_spec = ref false *)

let disable_failure_explaining = ref true

let simplify_error = ref false

let prune_cnt_limit = ref 2

let suppress_warning_msg = ref false
let disable_elim_redundant_ctr = ref false

let enable_strong_invariant = ref false
let enable_aggressive_prune = ref false
let enable_redundant_elim = ref false

(* let disable_aggressive_prune = ref false *)
(* let prune_with_slice = ref false *)

let enulalias = ref false

let pass_global_by_value = ref false

let exhaust_match = ref false

let memo_verbosity = ref 2

let profile_threshold = 0.5 

let no_cache_formula = ref true

let enable_incremental_proving = ref false

let disable_multiple_specs =ref false

let perm_prof = ref false

  (*for cav experiments*)
  let f_1_slice = ref false
  let f_2_slice = ref false
  let no_memoisation = ref false
  let no_incremental = ref false
  let no_LHS_prop_drop = ref false
  let no_RHS_prop_drop = ref false
  let do_sat_slice = ref false

(* for Termination *)
let dis_term_chk = ref false
let term_verbosity = ref 1
let dis_call_num = ref false
let dis_phase_num = ref false
let term_reverify = ref false
let dis_bnd_chk = ref false
let dis_term_msg = ref false
let dis_post_chk = ref false
let dis_ass_chk = ref false
let log_filter = ref true
  
(* Options for slicing *)
(* let do_slicing = ref false *)
let en_slc_ps = ref false
let dis_ps = ref false
let dis_slc_ann = ref false
let slicing_rel_level = ref 2

let dis_slicing = ref false
let opt_imply = ref 0
let opt_ineq = ref false
let infer_slicing = ref false
let infer_lvar_slicing = ref false
let multi_provers = ref false
let is_sat_slicing = ref false
let delay_case_sat = ref false
let force_post_sat = ref false
let delay_if_sat = ref false
let delay_proving_sat = ref false
let disable_assume_cmd_sat = ref false
let disable_pre_sat = ref true

(* Options for invariants *)
let do_infer_inv = ref false

(* Option for using classical reasoning in separation logic *)
let do_classic_reasoning = ref false

(* Flag decide whether check entailment exactly (no residue) or inexactly (allow residue) *)
let do_checkentail_exact = ref false

(* Options for abduction *)
let do_abd_from_post = ref false

(* Flag of being unable to fold rhs_heap *)
let unable_to_fold_rhs_heap = ref false

(* Used in parse_shape.ml *)
let domain_name = ref ""

(* Options for incremental spec *)
let do_infer_inc = ref false

(* Inference *)
(*let call_graph : ((string list) list) ref = ref [[]]*)

let add_count (t: int ref) = 
	t := !t+1

(* utility functions *)

let omega_err = ref false

let seq_number = ref 10

let sat_timeout_limit = ref 2.
let imply_timeout_limit = ref 3.

let dis_provers_timeout = ref false
let sleek_timeout_limit = ref 0.
  
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

let eq_formula_label (l1:formula_label) (l2:formula_label) : bool = fst(l1)=fst(l2)

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

let fresh_ty_var_name (t:typ)(ln:int):string = 
	("v_"^(string_of_typ_alpha t)^"_"^(string_of_int ln)^"_"^(string_of_int (fresh_int ())))

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

(* An Hoa : option to print proof *)
let print_proof = ref false

(* Create a quoted version of a string, for example, hello --> "hello" *)
let strquote s = "\"" ^ s ^ "\""


let open_log_out s = 
 (try
	Unix.mkdir "logs" 0o750
 with _ -> ());
 open_out ("logs/"^s)

let norm_file_name str =
	for i = 0 to (String.length str) - 1 do
		if str.[i] = '.' || str.[i] = '/' then str.[i] <- '_'
	done;
	str
