(* global types and utility functions *)

type ident = string

and loc = Lexing.position (* might be expanded to contain more information *)

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

let no_pos = { Lexing.pos_fname = "";
			   Lexing.pos_lnum = 0;
			   Lexing.pos_bol = 0; 
			   Lexing.pos_cnum = 0 }

let res = "res"

let self = "self"

let this = "this"

(* command line options *)

let source_files = ref ([] : string list)

let procs_verified = ref ([] : string list)

let verify_callees = ref false

let elim_unsat = ref true

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

let n_xpure = ref 1

let check_coercions = ref false

let show_gist = ref false

let trace_all = ref false

let print_mvars = ref false

(* utility functions *)

let seq_number = ref 10

let report_error (pos : Lexing.position) (msg : string) =
  print_string ("\n" ^ pos.Lexing.pos_fname ^ ":" ^ (string_of_int pos.Lexing.pos_lnum) ^ ": " ^ msg ^ "\n");
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

let fresh_name () = 
  let str = string_of_int (fresh_int ()) in
  (*-- 09.05.2008 *)
	(*let _ = (print_string ("\n[globals.ml, line 103]: fresh name = " ^ str ^ "\n")) in*)
	(* 09.05.2008 --*)
    "f_r_" ^ str

let fresh_names (n : int) = (* number of names to be generated *)
  let names = ref ([] : string list) in
    for i = 1 to n do
      names := (fresh_name ()) :: !names
    done;
    !names

let gen_ext_name c1 c2 = "Ext~" ^ c1 ^ "~" ^ c2


let string_of_loc (p : loc) = p.Lexing.pos_fname ^ "_" ^ (string_of_int p.Lexing.pos_lnum)
