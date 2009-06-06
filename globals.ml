(* global types and utility functions *)

type ident = string
type constant_flow = ident


type nflow = (int*int)(*numeric representation of flow*)

	
	
and branch_label = string

and loc = {
			start_pos : Lexing.position (* might be expanded to contain more information *);
			mid_pos : Lexing.position;
			end_pos : Lexing.position;
			}

and primed =
  | Primed
  | Unprimed

and prim_type = 
  | Bool
  | Float
  | Int
  | Void
  | Bag

(*
  Data types for code gen
*)

type mode = 
  | ModeIn
  | ModeOut

(* global constants *)

let no_pos = 
	let no_pos1 = { Lexing.pos_fname = "";
				   Lexing.pos_lnum = 0;
				   Lexing.pos_bol = 0; 
				   Lexing.pos_cnum = 0 } in
	{start_pos = no_pos1; mid_pos = no_pos1; end_pos = no_pos1;}

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

let n_flow_int = ref ((-1,-1):nflow)
let ret_flow_int = ref ((-1,-1):nflow)
let spec_flow_int = ref ((-1,-1):nflow)
let top_flow_int = ref ((-2,-2):nflow)
let exc_flow_int = ref ((-2,-2):nflow) (*abnormal flow*)
let false_flow_int = (0,0)

let res = "res"

let self = "self"

let this = "this"

(* command line options *)

let omega_simpl = ref true

let source_files = ref ([] : string list)

let procs_verified = ref ([] : string list)

let false_ctx_line_list = ref ([] : loc list)

let verify_callees = ref false

let elim_unsat = ref true

let lemma_heuristic = ref false

let elim_exists = ref true

let print_proc = ref false

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

let n_xpure = ref 1

let check_coercions = ref false

let show_gist = ref false

let trace_all = ref false

let print_mvars = ref false

let enable_sat_statistics = ref false

let wrap_exists_implicit_explicit = ref true

let profiling = ref false

let enable_syn_base_case = ref false

let enable_case_inference = ref false

let print_core = ref false

let seq_to_try = ref false

let print_input = ref false

let instantiation_variants = ref 0


let profile_threshold = 0.5 

let true_imply_count = ref 0
let false_imply_count = ref 0
let true_sat_count = ref 0

let add_count (t: int ref) = 
	t := !t+1


(* utility functions *)

let omega_err = ref false

let seq_number = ref 10

let sat_timeout = ref 10.
let imply_timeout = ref 10.

let report_error (pos : loc) (msg : string) =
  print_string ("\n" ^ pos.start_pos.Lexing.pos_fname ^ ":" ^ (string_of_int pos.start_pos.Lexing.pos_lnum) ^":"^(string_of_int 
	(pos.start_pos.Lexing.pos_cnum-pos.start_pos.Lexing.pos_bol))^ ": " ^ msg ^ "\n");
  failwith "Error detected"

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

let gen_ext_name c1 c2 = "Ext~" ^ c1 ^ "~" ^ c2


let string_of_loc (p : loc) = p.start_pos.Lexing.pos_fname ^ "_" ^ (string_of_int p.start_pos.Lexing.pos_lnum)^"_"^
	(string_of_int (p.start_pos.Lexing.pos_cnum-p.start_pos.Lexing.pos_bol))
