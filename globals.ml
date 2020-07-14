#include "xdebug.cppo"
open VarGen

(* global types and utility functions *)
(* module Lb = Label_only *)
(* circular with Lb *)

let sleek_num_to_verify = ref (-1)
let sleek_print_residue = ref true
let ramification_entailments = ref 0
let noninter_entailments = ref 0
let total_entailments = ref 0

let epure_disj_limit = ref 100 (* 0 means unlimited *)

let trailer_num_list = ref []

let change_flow = ref false

let abs_int = ref 3
let lend_int = ref 2
let imm_int = ref 1
let mut_int = ref 0

type formula_type =
  | Simple
  | Complex

type aliasing_scenario =
  | Not_Aliased
  | May_Aliased
  | Must_Aliased
  | Partial_Aliased

type ('a,'b) twoAns =
  | FstAns of 'a
  | SndAns of 'b

type ident = string
type constant_flow = string

exception Illegal_Prover_Format of string
exception SA_HP_TUPLED
exception SA_HP_NOT_PRED

exception NOT_HANDLE_YET

let reverify_flag = ref false
let reverify_all_flag = ref false
let ineq_opt_flag = ref false

let ptr_arith_flag = ref true (* false *)

let illegal_format s = raise (Illegal_Prover_Format s)

type lemma_kind = LEM_PROP| LEM_SPLIT | LEM_TEST | LEM_TEST_NEW | LEM | LEM_UNSAFE | LEM_SAFE | LEM_INFER | LEM_INFER_PRED | RLEM

let is_lemma_ahead m = match m with
  | LEM_PROP| LEM_SPLIT | LEM | LEM_UNSAFE | LEM_SAFE -> true
  | _ -> false

type lemma_origin =
  | LEM_USER          (* user-given lemma *)
  | LEM_GEN           (* automatically generated/inferred lemma *)

type ho_split_kind =
  | HO_SPLIT
  | HO_NONE

type ho_flow_kind =
  | INFLOW
  | OUTFLOW
  | NEUTRAL

(* type nflow = (int*int)(\*numeric representation of flow*\) *)
type flags =
    Flag_str of string
  | Flag_int of int
  | Flag_float of float

type bformula_label = int
and ho_branch_label = string
(*and branch_label = spec_label	(*formula branches*)*)

type formula_label = (int*string)

and control_path_id_strict = formula_label

and control_path_id = control_path_id_strict option
(*identifier for if, catch, call*)

let eq_ho_flow_kind k1 k2 =
  match k1, k2 with
  | INFLOW, INFLOW
  | OUTFLOW, OUTFLOW
  | NEUTRAL, NEUTRAL -> true
  | _ -> false

let ho_always_split = ref false
let contra_ho_flag = ref true

let gen_lemma_action_invalid = -1

let eq_control_path_id ((p1,_):formula_label) ((p2,_):formula_label) = p1==p2

let eq_str s1 s2 = String.compare s1 s2 = 0

let empty_label = (0,"")
let app_e_l c = (empty_label, c)
let combine_lbl (i1,s1)(i2,s2) = match s1 with
  | "" -> (match s2 with
      | "" -> (i1,s1)
      | _ -> (i2,s2))
  | _ -> (i1,s1)


type path_label = int (*which path at the current point has been taken 0 -> then branch or not catch or first spec, 1-> else or catch taken or snd spec...*)

type path_trace = (control_path_id_strict * path_label) list

(* and loc =  { *)
(*     start_pos : Lexing.position (\* might be expanded to contain more information *\); *)
(*     mid_pos : Lexing.position; *)
(*     end_pos : Lexing.position; *)
(*   } *)

(* moved to Gen *)
(* and primed = *)
(*   | Primed *)
(*   | Unprimed *)

(* indicate whether lemma_split is applicable or not*)
and split_ann =
    SPLIT0 (* do not split, exact match - DEFAULT *)
  | SPLIT1 (* always split *)
  | SPLIT2 (* both split and match *)

and heap_ann = Lend | Imm | Mutable | Accs

and vp_ann =
  | VP_Zero | VP_Full | VP_Value
  | VP_Lend | VP_Frac of Frac.frac
  (* | VP_Ref * *)

let eq_vp_ann a1 a2 =
  match a1, a2 with
  | VP_Zero, VP_Zero -> true
  | VP_Full, VP_Full -> true
  | VP_Lend, VP_Lend -> true
  | VP_Value, VP_Value -> true
  | VP_Frac f1, VP_Frac f2 -> Frac.eq_frac f1 f2
  | _ -> false

(* and rel = REq | RNeq | RGt | RGte | RLt | RLte | RSubAnn *)
let imm_top = Accs
let imm_bot = Mutable

type hp_arg_kind=
  | I
  | NI

let print_arg_kind i= match i with
  | I -> ""
  | NI -> "#"

let string_of_arg_kind i= match i with
  | I -> "@I"
  | NI -> "@NI"

(* and prim_type =  *)
(*   | TVar of int *)
(*   | Bool *)
(*   | Float *)
(*   | Int *)
(*   | Void *)
(*   | BagT of prim_type *)
(*   | List *)

type view_kind =
  | View_PRIM
  | View_HREL
  | View_NORM
  | View_EXTN
  | View_DERV
  | View_SPEC


(* TODO : move typ here in future *)
type typ =
  | FORM (* Type for formula *)
  | UNK
  | TVar of int
  | AnnT
  | Bool
  | Float
  | Int
  | INFInt
  | Tup2 of typ * typ
  | NUM
  | Void
  | List of typ
  | BagT of typ
  (* | Prim of prim_type *)
  | Named of ident (* named type, could be enumerated or object *)
  (* Named "R" *)
  | Array of (typ * int) (* base type and dimension *)
  | RelT of (typ list) (* relation type *)
  | HpT (* heap predicate relation type *)
  | Tree_sh
  | FuncT of typ * typ
  | UtT of bool (* unknown temporal type - pre(true)/post(false)*)
  | Bptyp
  | Pointer of typ (* base type and dimension *)
(* | SLTyp (* type of ho formula *) *)

(* let eq_type t1 t2 = match *)
(*     | FORM, FORM  *)
(*     | UNK, UNK *)
(*   | AnnT *)
(*   | Bool *)
(*   | Float *)
(*   | Int *)
(*   | INFInt *)
(*   | Tup2 of typ * typ *)
(*   | NUM *)
(*   | Void *)
(*   | List of typ *)
(*   | BagT of typ *)
(*   (\* | Prim of prim_type *\) *)
(*   | Named of ident (\* named type, could be enumerated or object *\) *)
(*   (\* Named "R" *\) *)
(*   | Array of (typ * int) (\* base type and dimension *\) *)
(*   | RelT of (typ list) (\* relation type *\) *)
(*   | HpT (\* heap predicate relation type *\) *)
(*   | Tree_sh *)
(*   | FuncT of typ * typ *)
(*   | UtT of bool (\* unknown temporal type - pre(true)/post(false)*\) *)
(*   | Bptyp *)
(*   | Pointer of typ (\* base type and dimension *\) *)
(*     | ,   *)
(*       -> true *)
(*     | TVar i1, TVar i2 -> i1=i2 *)
(*     | _, _ -> false *)

type typed_ident = (typ * ident)

let string_of_view_kind k = match k with
  | View_PRIM -> "View_PRIM"
  | View_HREL -> "View_HREL"
  | View_NORM -> "View_NORM"
  | View_EXTN -> "View_EXTN"
  | View_DERV -> "View_DERV"
  | View_SPEC -> "View_SPEC"

let is_undef_typ t =
  match t with
  | UNK | RelT _ | HpT | UtT _ -> true
  | _ -> false


let is_ptr_arith t =
  match t with
  | Named id -> true (* String.compare id "" != 0 *)
  | Array _ -> true
  | _ -> false

let is_node_typ t =
  match t with
  | Named id -> true (* String.compare id "" != 0 *)
  | _ -> false

let is_possible_node_typ t =
  match t with
  | Named id -> true (* String.compare id "" != 0 *)
  | TVar _ -> true
   (* Unknown can also be a node *)
  | UNK -> true
  | _ -> false

let mkFuncT (param_typ: typ list) (ret_typ: typ): typ =
  match param_typ with
  | [] -> FuncT (Void, ret_typ)
  | _ -> List.fold_right (fun p_typ r_typ -> FuncT (p_typ, r_typ)) param_typ ret_typ

let rec ret_typ_of_FuncT typ =
  match typ with
  | FuncT (_, r_typ) -> ret_typ_of_FuncT r_typ
  | _ -> typ

let rec param_typ_of_FuncT typ =
  match typ with
  | FuncT (p_typ, r_typ) -> p_typ::(param_typ_of_FuncT r_typ)
  | _ -> []

let rec cmp_typ t1 t2=
  match t1,t2 with
  | FORM, FORM
  | UNK, UNK
  | AnnT, AnnT
  | Bool, Bool
  | Float, Float
  | Int, Int
  | INFInt, INFInt
  | NUM, NUM
  | Void, Void -> true
  | TVar i1, TVar i2 -> i1=i2
  | BagT t11, BagT t22
  | List t11, List t22 -> cmp_typ t11 t22
  | Named s1, Named s2 -> String.compare s1 s2 = 0
  | Array (t11, i1), Array (t22, i2) -> i1=i2 && cmp_typ t11 t22
  | RelT lst1, RelT lst2 ->(
      try
        List.for_all (fun (t11,t22) -> cmp_typ t11 t22) (List.combine lst1 lst2)
      with _ -> false
    )
  | HpT, HpT
  | Tree_sh, Tree_sh
  | Bptyp, Bptyp -> true
  | Pointer t11, Pointer t22 -> cmp_typ t11 t22
  | _ -> false

let is_type_var t =
  match t with
  | TVar _ -> true
  | _ -> false


let imm_var_sufix = "_imm"
let imm_var_prefix = "ann"

let is_program_pointer (name:ident) =
  let slen = (String.length name) in
  try
    let n = (String.rindex name '_') in
    (* let () = print_endline ((string_of_int n)) in *)
    let l = (slen-(n+1)) in
    if (l==0) then (false,name)
    else
      let str = String.sub name (n+1) (slen-(n+1)) in
      if (str = "ptr") then
        let s = String.sub name 0 n in
        (true,s)
      else
        (false,name)
  with  _ -> (false,name)

let is_pointer_typ (t:typ) : bool =
  match t with
  | Pointer _ -> true
  | _ -> false

let convert_typ (t:typ) : typ =
  match t with
  | Pointer t1 ->
    (match t1 with
     | Int -> Named "int_ptr"
     | Pointer t2 ->
       (match t2 with
        | Int -> Named "int_ptr_ptr"
        | _ -> t2 (*TO CHECK: need to generalize for float, bool, ...*)
       )
     | _ -> t1 (*TO CHECK: need to generalize for float, bool, ...*)
    )
  | _ -> t

let revert_typ (t:typ) : typ =
  (match t with
   | Named t1 ->
     (match t1 with
      | "int_ptr" -> Int
      | "int_ptr_ptr" -> Named "int_ptr"
      | _ -> Named "Not_Support")
   | _ -> Named "Not_Support")

let name_of_typ (t:typ) : string =
  (match t with
   | Named t1 ->
     t1
   | _ ->
     "Not_Support")

let is_pointer t=
  match t with
  | Named _ -> true
  | _ -> false

let barrierT = Named "barrier"

let convert_prim_to_obj (t:typ) : typ =
  (match t with
   | Int -> Named "int_ptr"
   | Named t1 ->
     (match t1 with
      | "int_ptr" -> Named "int_ptr_ptr"
      | _-> t (*TO CHECK: need to generalize for float, bool, ...*)
     )
   | _ -> t (*TO CHECK: need to generalize for float, bool, ...*)
  )

(*for heap predicate*)
let default_prefix_pure_hprel = "_pure_of_"
let hp_default_prefix_name = "HP_"
let rel_default_prefix_name = "P_"
let hppost_default_prefix_name = "GP_"
let unkhp_default_prefix_name = "DP_"
let dang_hp_default_prefix_name = "DP_DP"
let ex_first = "v"
let size_rel_name = "size"
let size_rel_arg = "n"
let seg_arg = "p"
let field_rec_ann = "REC"
let field_val_ann = "VAL"

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
  | Bperm (*bounded permissions*)

let perm = ref NoPerm

(* moved to Gen *)
(* let no_pos =  *)
(* 	let no_pos1 = { Lexing.pos_fname = ""; *)
(* 				   Lexing.pos_lnum = 0; *)
(* 				   Lexing.pos_bol = 0;  *)
(* 				   Lexing.pos_cnum = 0 } in *)
(* 	{start_pos = no_pos1; mid_pos = no_pos1; end_pos = no_pos1;} *)
(* let is_no_pos l = (l.start_pos.Lexing.pos_cnum == 0) *)

let is_float_type (t:typ) = match t with
  | Float -> true
  | _ -> false

(*Remove all blanks in a string*)
let remove_blanks = Str.global_replace (Str.regexp " ") ""

let string_of_split_ann a =
  match a with
  | SPLIT0 -> ""
  | SPLIT1 -> "@S1"
  | SPLIT2 -> "@S2"

let string_of_heap_ann a =
  match a with
  | Accs -> "@A"
  | Lend -> "@L"
  | Imm -> "@I"
  | Mutable -> "@M"

let int_of_heap_ann a =
  match a with
  | Accs -> !abs_int
  | Lend -> !lend_int
  | Imm -> !imm_int
  | Mutable -> !mut_int

let is_absent a =
  match a with
  | Accs -> true
  | _ -> false

let heap_ann_of_int i =
  if i = !mut_int then Mutable
  else if i = !imm_int then Imm
  else if i = !lend_int then Lend
  else Accs

let string_of_vp_ann a =
  (match a with
   | VP_Zero -> "@zero"
   | VP_Full -> "@full"
   | VP_Value -> "@value"
   | VP_Lend -> "@lend"
   | VP_Frac f -> "@" ^ (Frac.string_of_frac f)
   (* | VP_Ref-> "@p_ref" *)
  )


let string_of_ho_flow_kind (k:ho_flow_kind) =
  match k with
  | INFLOW -> "-"
  | OUTFLOW -> "+"
  | NEUTRAL -> "."

let string_of_ho_split_kind (k:ho_split_kind) =
  match k with
  | HO_SPLIT -> "@Split"
  | HO_NONE -> ""

let string_of_loc (p : loc) =
  Printf.sprintf "1 File \"%s\",Line:%d,Col:%d"
    p.start_pos.Lexing.pos_fname
    p.start_pos.Lexing.pos_lnum
    (p.start_pos.Lexing.pos_cnum-p.start_pos.Lexing.pos_bol)
;;

let is_valid_loc p=
  (p.start_pos.Lexing.pos_lnum>=0 &&
   p.start_pos.Lexing.pos_cnum-p.start_pos.Lexing.pos_bol>=0)

let string_of_pos (p : Lexing.position) =
  Printf.sprintf "(Line:%d,Col:%d)"
    p.Lexing.pos_lnum
    (p.Lexing.pos_cnum-p.Lexing.pos_bol)
;;

let string_of_pos_plain (p : Lexing.position) =
  Printf.sprintf "%d_%d"
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
let log_proof_details = ref true
let proof_logging_time = ref 0.000
(* let sleek_src_files = ref ([]: string list) *)
let time_limit_large = ref 0.5


let prelude_file = ref (None: string option) (* Some "prelude.ss" *)

(*sleek logging*)
let sleek_logging_txt = ref false
let sleek_log_all = ref false
let dump_proof = ref false
let dump_sleek_proof = ref false
let sleek_gen_vc = ref false
let sleek_gen_vc_exact = ref false
let sleek_gen_sat = ref false




(*Some global vars for logging*)
let explain_mode = new failure_mode
let return_exp_pid = ref ([]: control_path_id list)
let z3_proof_log_list = ref ([]: string list)
let z3_time = ref 0.0

let add_to_z3_proof_log_list (f: string) =
  z3_proof_log_list := !z3_proof_log_list @ [f]



(* let set_proving_loc p = proving_loc#set p *)
(*   (\* proving_loc := Some p *\) *)

(* let clear_proving_loc () = proving_loc#reset *)
(*   (\* proving_loc := None *\) *)

let pr_lst s f xs = String.concat s (List.map f xs)

let pr_list_brk open_b close_b f xs  = open_b ^(pr_lst ";" f xs)^close_b
let pr_list f xs = pr_list_brk "[" "]" f xs
let pr_list_angle f xs = pr_list_brk "<" ">" f xs
let pr_list_round f xs = pr_list_brk "(" ")" f xs

let pr_pair f1 f2 (x,y) = "("^(f1 x)^","^(f2 y)^")"

(* pretty printing for types *)
let rec string_of_typ (x:typ) : string = match x with
  (* may be based on types used !! *)
  | FORM          -> "Formula"
  | UNK          -> "Unknown"
  | Bool          -> "boolean"
  | Float         -> "float"
  | Int           -> "int"
  | INFInt        -> "INFint"
  | Void          -> "void"
  | NUM          -> "NUM"
  | AnnT          -> "AnnT"
  | Tup2 (t1,t2)  -> "tup2("^(string_of_typ t1) ^ "," ^(string_of_typ t2) ^")"
  | BagT t        -> "bag("^(string_of_typ t)^")"
  | TVar t        -> "TVar["^(string_of_int t)^"]"
  | List t        -> "list("^(string_of_typ t)^")"
  | Tree_sh		  -> "Tsh"
  | Bptyp		  -> "Bptyp"
  | RelT a      -> "RelT("^(pr_list string_of_typ a)^")"
  | Pointer t        -> "Pointer{"^(string_of_typ t)^"}"
  | FuncT (t1, t2) -> (string_of_typ t1) ^ "->" ^ (string_of_typ t2)
  | UtT b        -> "UtT("^(if b then "pre" else "post")^")"
  | HpT        -> "HpT"
  (* | SLTyp -> "SLTyp" *)
  | Named ot -> if ((String.compare ot "") ==0) then "null_type" else ot
  | Array (et, r) -> (* An Hoa *)
    let rec repeat k = if (k <= 0) then "" else "[]" ^ (repeat (k-1)) in
    (string_of_typ et) ^ (repeat r)
;;

let string_of_typed_ident (typ,id) =
  "("^(string_of_typ typ)^","^id^")"

let is_RelT x =
  match x with
  | RelT _ | UtT _  (* | HpT _  *)-> true
  | _ -> false
;;

let is_UtT x =
  match x with
  | UtT _ -> true
  | _ -> false

let is_FuncT = function
  | FuncT _ -> true
  | _ -> false

let is_HpT x =
  match x with
  | HpT -> true
  | _ -> false
;;

(* aphanumeric name *)
let rec string_of_typ_alpha = function
  (* may be based on types used !! *)
  | FORM          -> "Formula"
  | UNK          -> "Unknown"
  | Bool          -> "boolean"
  | Float         -> "float"
  | Int           -> "int"
  | INFInt        -> "INFint"
  | Void          -> "void"
  | NUM          -> "NUM"
  | AnnT          -> "AnnT"
  | Tree_sh		  -> "Tsh"
  | Bptyp		  -> "Bptyp"
  | Tup2 (t1,t2)  -> "tup2_"^(string_of_typ t1)^"_"^(string_of_typ t2)
  | BagT t        -> "bag_"^(string_of_typ t)
  | TVar t        -> "TVar_"^(string_of_int t)
  | List t        -> "list_"^(string_of_typ t)
  | RelT a      -> "RelT("^(pr_list string_of_typ a)^")"
  | Pointer t        -> "Pointer{"^(string_of_typ t)^"}"
  | FuncT (t1, t2) -> (string_of_typ t1) ^ "_" ^ (string_of_typ t2)
  | UtT b        -> "UtT("^(if b then "pre" else "post")^")"
  | HpT        -> "HpT"
  (* | SLTyp -> "SLTyp" *)
  | Named ot -> if ((String.compare ot "") ==0) then "null_type" else ot
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


(* let null_type = Named "" *)
(* ;;                       *)

(* let is_null_type t=      *)
(*   match t with           *)
(*     | Named "" -> true   *)
(*     | _ -> false         *)

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
  "("^id^","^(string_of_primed p)^")"

(* let string_of_primed_ident ( = *)
(*   id ^ string_of_primed p *)

(* let pr_ident_list = pr_list (fun (i,p) -> i^(string_of_primed p)) *)

let pr_ident_list = pr_list string_of_primed_ident
let pr_primed_ident_list = pr_list string_of_primed_ident

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
let nonef2 e f = None
let voidf e = ()
let voidf2 e f = ()
let somef v = Some v
let somef2 v f = Some f
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
(* let null_name = "null" *)
let null_name = "_null"
let null_type = Named ""

let is_null name =
  name == null_name

let is_null_type t  =
  match t with
  | Named "" -> true
  | _ -> false

let inline_field_expand = "_"

(*use error type in the error msg*)
type error_type=
  | Mem of int
  | Heap
  | Pure

let sl_error = "separation entailment" (* sl_error is a may error *)
let logical_error = "logical bug" (* this kind of error: depend of sat of lhs*)
let fnc_error = "function call"
let mem_leak_error = "mem leak detection"
let mem_deref_error = "mem deref detection"
let mem_dfree_error = "mem double free detection"
let lemma_error = "lemma" (* may error *)
let mem_leak = "memory leak"
let undefined_error = "undefined"
let timeout_error = "timeout"

let eres_name = "eres"


let self = "self"

let constinfinity = "ZInfinity"
let deep_split_disjuncts = ref true (* false *)
let check_integer_overflow = ref false

let preprocess_disjunctive_consequence = ref false

let this = "this"

let is_self_ident id = self=id

let concrete_name = "concrete"
let waitS_name = "waitS"
let set_comp_name = "set_comp"
let acyclic_name = "acyclic"
let cyclic_name = "cyclic"

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
let lock_typ = Named "lock"

let ls_name = "LS"
let lsmu_name = "LSMU"
let ls_data_typ = "lock"

let waitlevel_name = "waitlevel"
let waitlevel_typ = Int

let level_pred = "level"
let level_name = "mu"
let level_data_typ = Int
let ls_typ = BagT (Named ls_data_typ)
let lsmu_typ = BagT (Int)

let thrd_name = "thrd"
let thrd_typ = Named "thrd"


(*precluded files*)
let header_file_list  = ref (["\"prelude.ss\""] : string list)
let pragma_list = ref ([] : string list)
let lib_files = ref ([] : string list)

(*in case the option of saving provers temp files to a different directory is enabled, the value of
  this variable is going to be changed accordingly in method set_tmp_files_path *)
(*let tmp_files_path = "/tmp/"*)

(* *GLOBAL_VAR* input filename, used by iparser.mly, astsimp.ml and main.ml
 * moved here from iparser.mly *)

(* command line options *)

let split_fixcalc = ref false (* present split is unsound *)

let ptr_to_int_exact = ref false

let is_sleek_running = ref false
let is_hip_running = ref false

let temp_opt_flag = ref false
let temp_opt_flag2 = ref false

let remove_label_flag = ref false
let label_split_conseq = ref true
let label_split_ante = ref true
let label_aggressive_sat = ref true
let label_aggressive_imply = ref true

let force_verbose_xpure = ref false

let texify = ref false
let testing_flag = ref false

let instantiation_variants = ref 0

let omega_simpl = ref true

let no_simpl = ref false


let no_float_simpl = ref true (*do not simplify fractional constraints to avoid losing precision, such as 1/3 *)

let source_files = ref ([] : string list)

let input_file_name =ref ""

let use_split_match = ref false

let consume_all = ref false

let dis_base_case_unfold = ref false

let enable_split_lemma_gen = ref false
let enable_lemma_rhs_unfold = ref false
let enable_lemma_lhs_unfold = ref false
let enable_lemma_unk_unfold = ref true
let allow_lemma_residue = ref false
let allow_lemma_deep_unfold = ref true
let allow_lemma_switch = ref true

let allow_rd_lemma = ref false
(* unsound *)

let allow_lemma_fold = ref true
(* unsound if false for lemma/bugs/app-t2c1.slk *)

let allow_lemma_norm = ref false
let show_push_list = ref (None:string option)
let show_push_list_rgx = ref (None:Str.regexp option)

let old_unsound_no_progress = ref false
let old_norm_w_coerc = ref false
let old_keep_all_matchres = ref false

let old_do_match_infer_heap = ref true
let old_incr_infer = ref false

(* Enable exhaustive normalization using lemmas *)
let allow_exhaustive_norm = ref true

let dis_show_diff = ref false

(* sap has moved to VarGen; needed by debug.ml *)
let fo_iheap = ref true
let sa_part = ref false

let prelude_is_mult = ref false

let sae = ref false
let sac = ref false
(* transform a predicate to case formula *)
let sa_pred_case = ref false

let sags = ref true
let sa_prefix_emp = ref true

let sa_gen_slk = ref false
let gen_fixcalc = ref false

let tc_drop_unused = ref false
let simpl_unfold3 = ref false
let simpl_unfold2 = ref false
let simpl_unfold1 = ref false
let simpl_memset = ref false

let pretty_print = ref false
let simplify_dprint = ref true

let print_heap_pred_decl = ref true


let print_original_solver_output = ref false
let print_original_solver_input = ref false

let cond_path_trace = ref true

let pred_syn_modular = ref true

let syntatic_mode = ref false (* syntatic mode - default is semantic*)

let sa_dnc = ref false

let pred_reuse = ref false

let pred_trans_view = ref true

(*temp: should be improve*)
let pred_en_oblg = ref true

(* let sa_en_norm = ref false *)

let pred_syn_flag = ref true

let sa_syn = ref true

let mem_leak_detect = ref false

let print_relassume  = ref true

let lemma_syn = ref false

let lemma_syn_count = ref 0
let lemma_tail_rec_count = ref 0

let lemma_syn_bound = 5

let is_lem_syn_in_bound () = true (* !lemma_syn_count < lemma_syn_bound *)

let is_lem_syn_reach_bound () = !lemma_syn_count = lemma_syn_bound

let lemma_gen_safe = ref false       (* generating (and proving) both fold and unfold lemmas for special predicates *)

let lemma_gen_safe_fold = ref false  (* generating (and proving) fold lemmas for special predicates *)

let lemma_gen_unsafe = ref false     (* generating (without proving) both fold and unfold lemmas for special predicates *)

let lemma_rev_unsafe = ref false     (* generating (without proving) both rev lemmas for special predicates *)


let lemma_gen_unsafe_fold = ref false     (* generating (without proving) fold lemmas for special predicates *)

let acc_fold = ref false
let seg_fold = ref false

let print_min = ref false
let smart_lem_search = ref false

let sa_en_split = ref false

let pred_split = ref false

let pred_seg_split = ref false
let pred_norm_overr = ref true

(* let sa_dangling = ref false *)

let sa_refine_dang = ref false

let pred_elim_useless = ref true
let infer_deep_ante_flag = ref false

let pred_infer_flag = ref true

let pred_elim_dangling = ref true

(* let sa_inlining = ref false *)

let sa_sp_split_base = ref false
(* let sa_pure_field = ref false *)

let sa_pure = ref true

(* let iSIZE_PROP = 0 *)
(* let iBAG_VAL_PROP = 1 *)


let sa_ex = ref false

let sa_infer_split_base = ref true

let pred_elim_unused_preds = ref true

(* let sa_keep_unused_preds = ref false *)

let sa_unify_dangling = ref false

let pred_conj_unify = ref false

let pred_disj_unify = ref false

let pred_seg_unify = ref false

let pred_equiv = ref true

(* what is below for? not used! *)
let pred_equiv_one = ref true

(* this is to enable automatic list segment *)
let pred_norm_seg = ref true

let pred_unify_post = ref false

let pred_unify_inter = ref true

let sa_tree_simp = ref false

let sa_subsume = ref false

let norm_elim_useless = ref false

let norm_extract = ref false
let allow_norm_disj = ref true

let sa_fix_bound = ref 2

let norm_cont_analysis = ref true

let sep_pure_fields = ref false

let en_norm_ctx = ref false (* true - not suitable for inference *)

let en_trec_lin = ref false

(*context: (1, M_cyclic c) *)
let cyc_proof_syn = ref true
(* let lemma_infer = ref false *)

(* turn off printing during lemma proving? *)
let lemma_ep = ref true
let lemma_ep_verbose = ref false

let dis_sem = ref false

(* let show_diff_constrs = ref true *)

let procs_verified = ref ([] : string list)

let false_ctx_line_list = ref ([] : loc list)

let pr_option f x = match x with
  | None -> "None"
  | Some v -> "Some("^(f v)^")"

let last_sat_ctx = new store None (pr_option string_of_loc)
let last_infer_lhs_contra = new store false string_of_bool

(* let is_last_infer_lhs_contra () =  *)
(*   !last_infer_lhs_contra *)
(* let set_last_infer_lhs_contra () =  *)
(*   last_infer_lhs_contra:=false *)

let add_false_ctx pos =
  last_sat_ctx # set None;
  last_infer_lhs_contra # reset;
  false_ctx_line_list := pos::!false_ctx_line_list

(* let set_last_ctx (pos:loc) = last_sat_ctx := Some pos  *)


(* use List.rev *)
(* let rev_list list = *)
(*     let rec aux acc = function *)
(*       | [] -> acc *)
(*       | h::t -> aux (h::acc) t in *)
(*     aux [] list *)

(* WN : should this flag be for tpdispatcher, rather than just Omega *)
let b_datan = "barrier"

let verify_callees = ref false

let elim_unsat = ref false
let unsat_consumed_heap = ref false (* to add consumed heap for unsat_now *)
let disj_compute_flag = ref false
let compute_xpure_0 = ref true
let inv_wrap_flag = ref true
let lhs_case_flag = ref false
let infer_case_as_or_flag = ref false
let lhs_case_search_flag = ref false
let smart_xpure = ref true
let super_smart_xpure = ref false
let precise_perm_xpure = ref true
(* this flag is dynamically set depending on
   smart_xpure and xpure0!=xpure1 *)
let smart_memo = ref false

let enable_constraint_based_filtering = ref false

(* let lemma_heuristic = ref false *)

let elim_exists_ff = ref true

let allow_frame = ref false

let graph_norm = ref false

let oc_simplify = ref true

let oc_adv_simplify = ref true

let graph_norm_instance_threshold = 1

let graph_norm_decl_threshold = ref 1

let slice_one = ref (0:int)

let allow_imm = ref false (*imm will delay checking guard conditions*)

let allow_imm_inv = ref true (*imm inv to add of form @M<:v<:@A*)
let allow_imm_subs_rhs = ref true (*imm rhs subs from do_match*)
let allow_field_ann = ref false
let allow_imm_norm = ref false

let remove_abs = ref true
let allow_array_inst = ref false

let imm_merge = ref true                (* true *) (*TODOIMM set default to false when merging to default branch *)

let imm_weak = ref true

let aggressive_imm_simpl = ref false

let imm_simplif_inst = ref true

let int2imm_conv = ref true

let aggresive_imm_inst = ref false

let imm_add = ref true

let allow_noann = ref false

(* infer imm sequatially: first pre, then post *)
let imm_seq = ref true

(* infer imm pre/post simultaneously *)
let imm_sim = ref false

(*Since this flag is disabled by default if you use this ensure that
  run-fast-test mem test cases pass *)
(* let allow_field_ann = ref false  *)
(* disabled by default as it is unstable and
   other features, such as shape analysis are affected by it *)
let allow_ramify = ref false
let allow_mem = ref false
(*enabling allow_mem will turn on field ann as well *)

let gen_coq_file = ref false

let infer_mem = ref false
let filter_infer_search = ref true
let infer_raw_flag = ref true


let pa = ref false

let allow_inf = ref false (*enable support to use infinity (\inf and -\inf) in formulas *)
let allow_inf_qe = ref false (*enable support to use quantifier elimination with infinity (\inf and -\inf) in formulas *)

let allow_inf_qe_coq = ref false
let allow_inf_qe_coq_simp = ref false
(* enable support to use quantifier elimination procedure
   implemented in coq and extracted as infsolver.ml *)
let allow_qe_fix = ref false

let ann_derv = ref false

let print_ann = ref true
let print_derv = ref false

let print_clean_flag = ref false

(*is used during deployment, e.g. on a website*)
(*Will shorten the error/warning/... message delivered
  to end-users*)
(*Unify is_deployed an web_compile_flag*)
(* let is_deployed = ref true *)

let print_assume_struc = ref false
let web_compile_flag = ref false (*enable compilation flag for website*)


(* Decide whether normalization/simplification
   such as x<1 --> x+1<=1 is allowed
   Currently, =true when using -tp parahip|rm
   or using -perm frac
   The reason for this is that when using concurrency verification,
   (floating-point) permission  constraints could be related to
   integer constraints; therefore, this renders the normalization
   unsound.
   Look at example at sleekex/examples/fracperm/locks/bug-simplify.slk
   for more details.
   Currently, conservativly do not allow such simplification
*)

let allow_lsmu_infer = ref false
let infer_false_imply_unknown = ref true (* to support strongest post infer *)

let allow_norm = ref true

let dis_norm = ref false

let dis_ln_z3 = ref false

(* WN : should this flag be for tpdispatcher, rather than just Omega *)
let non_linear_flag = ref true
let oc_warning = ref false

(* eqn solving to be false by default until it is stable or proven*)
(* let oc_matrix_eqn = ref false  *)

let allow_ls = ref false (*enable lockset during verification*)

let allow_locklevel = ref false (*enable locklevel during verification*)

(*
  true -> threads as resource
  false -> threads as AND-conjunctions
*)
let allow_threads_as_resource = ref false

(* let has_locklevel = ref false *)

(* let assert_matrix = ref false *)
let assert_nonlinear = ref false
let assert_unsound_false = ref false
let assert_no_glob_vars = ref false

let new_rm_htrue = ref true
let new_infer_large_step = ref true
let infer_back_ptr = ref true
let old_infer_complex_lhs = ref false
let old_coer_target = ref false
let old_search_always = ref false (* false *)
let old_lemma_unfold = ref false (* false *)
let old_field_tag = ref false (* false *)
let new_trace_classic = ref false (* false *)
let old_pred_extn = ref false (* false *)
let old_lemma_switch = ref false (* false *)
let old_free_var_lhs = ref false (* false *)
let old_tp_simplify = ref false (* false *)
let old_univ_lemma = ref false (* false *)
let old_compute_act = ref false (* false *)
let new_heap_contra = ref true
let mkeqn_opt_flag = ref true (* false *)
let old_view_equiv = ref false (* false *)
  (* false here causes ex21u3e7.slk to go into a loop FIXED *)
let cond_action_always = ref false
let rev_priority = ref false

let old_collect_false = ref false
let old_collect_hprel = ref false
let old_infer_hprel_classic = ref false
let old_classic_rhs_emp = ref false
let old_post_conv_impl = ref true (* affected by incr/ex14d.ss *)
let old_post_impl_to_ex = ref true
let old_keep_triv_relass = ref false
let old_mater_coercion = ref false
let old_infer_heap = ref false
let old_fvars_as_impl_match = ref true
let old_base_case_fold_hprel = ref false
let old_base_case_unfold_hprel = ref false
let warn_do_match_infer_heap = ref false
let warn_nonempty_perm_vars = ref false
let warn_trans_context = ref false
let warn_post_free_vars = ref false
let warn_fvars_rhs_match = ref false
let warn_free_vars_conseq = ref false
let old_infer_collect = ref false
let old_infer_hp_collect = ref false
let old_base_case_unfold = ref false
let old_impl_gather = ref false
let old_parse_fix = ref false
let hrel_as_view_flag = ref false
let init_para_flag = ref false
let adhoc_flag_1 = ref false
let adhoc_flag_2 = ref false
let adhoc_flag_3 = ref false
let adhoc_flag_4 = ref false
let adhoc_flag_5 = ref false
let adhoc_flag_6 = ref false
let old_keep_absent = ref false
let old_univ_vars = ref false
let old_empty_to_conseq = ref true (* false *)
let weaker_pre_flag = ref true

let ann_vp = ref false (* Disable variable permissions in default, turn on in para5*)

(* let ann_vp = ref true (\* Enable variable permissions in rho, any problem *)
(* for run-fast-test? *\) *)

let allow_ptr = ref false (*true -> enable pointer translation*)

let print_proc = ref false

let check_all = ref true

let auto_number = ref true

let sleek_flag = ref false

let sleek_log_filter = ref true
(* flag to filter trivial sleek entailment logs *)
(* particularly child calls *)

let use_field = ref false

let large_bind = ref false

let print_x_inv = ref false
let print_cnv_null = ref false

let hull_pre_inv = ref false

let use_coercion = ref true

let case_split = ref false

let simplified_case_normalize = ref true

let use_set = ref true

let consistency_checking = ref false

let wrap_exist = ref false

let move_exist_to_LHS = ref false

let push_exist_deep = ref false

let max_renaming = ref false


let anon_exist = ref false

let simplify_pure = ref false

let enable_norm_simp = ref false

let print_version_flag = ref false

let elim_exists_flag = ref true

let filtering_flag = ref true
let filtering_false_flag = ref true

let split_rhs_flag = ref true

let n_xpure = ref 1


let fixcalc_disj = ref 2 (* should be n+1 where n is the base-case *)

let pre_residue_lvl = ref 0
(* Lvl 0 - add conjunctive pre to residue only *)
(* Lvl 1 - add all pre to residue *)
(* Lvl -1 - never add any pre to residue *)

let check_coercions = ref false
let eager_coercions = ref true
let dump_lemmas = ref false
let dump_lemmas_med = ref false

let dump_lem_proc = ref false

let num_self_fold_search = ref 0
let array_expansion = ref false;;
let array_translate = ref false;;

let self_fold_search_flag = ref true
(* performance not affected see incr/fix-todo.txt *)

let show_gist = ref false
let imply_top_flag = ref false
let early_contra_flag = ref true

let trace_all = ref false

let print_mvars = ref false

let print_type = ref false
let print_extra = ref true (* set true by default *)

let enforce_type_error = ref true (* strictly enforce type error *)

let print_en_tidy = ref false
(* print tidy is not working properly *)

let print_en_inline = ref true

let print_html = ref false

(* let enable_sat_statistics = ref false *)

let wrap_exists_implicit_explicit = ref false


let enable_syn_base_case = ref false

let enable_case_inference = ref false

let print_core = ref false
let print_core_all = ref false

let print_err_sleek = ref false

let enable_prune_cache = ref true


let enable_time_stats = ref true

let enable_count_stats = ref true

let enable_fast_imply = ref false

let failure_analysis = ref false

let seq_to_try = ref false

let print_input = ref false
let print_input_all = ref false

let print_cil_input = ref false
(* let pass_global_by_value = ref true *)

(* let allow_pred_spec = ref false *)

let disable_failure_explaining = ref false

let enable_error_as_exc = ref false (* true *)

let bug_detect = ref false

let simplify_error = ref false

let prune_cnt_limit = ref 2

let disable_elim_redundant_ctr = ref false

let enable_strong_invariant = ref false
let enable_aggressive_prune = ref false
let enable_redundant_elim = ref false

let enable_constraint_based_filtering = ref false

(* let disable_aggressive_prune = ref false *)
(* let prune_with_slice = ref false *)

let enulalias = ref false

let pass_global_by_value = ref true

let exhaust_match = ref false

let memo_verbosity = ref 2

let no_cache_formula = ref false

let simplify_imply = ref true

let enable_incremental_proving = ref false

let disable_multiple_specs =ref false

let perm_prof = ref false

let validate = ref false

let cp_prefile = ref false

let gen_cpfile = ref false

let validate_target = ref ""

let cpfile = ref ""

(*for cav experiments*)
let f_1_slice = ref false
let f_2_slice = ref false
let no_memoisation = ref false
let no_incremental = ref false
let no_LHS_prop_drop = ref false
let no_RHS_prop_drop = ref false
let do_sat_slice = ref false

let smt_compete_mode = ref false
let svcomp_compete_mode = ref false
let tnt_web_mode = ref false

let return_must_on_pure_failure = ref false
let smt_is_must_failure = ref (None: bool option)
let is_solver_local = ref false (* only --smt-compete:  is_solver_local = true *)

let force_print_residue = ref false

(* for Termination *)
let dis_term_chk = ref false
let term_verbosity = ref 1
let dis_call_num = ref false
let dis_phase_num = ref false
let term_reverify = ref false
let term_bnd_pre_flag = ref true
let dis_bnd_chk = ref false
let dis_term_msg = ref false
let dis_post_chk = ref false
let post_add_eres = ref false
let add_pre = ref false
let post_infer_flow = ref false
let dis_ass_chk = ref false
let log_filter = ref true
let oc_weaken_rel_flag = ref true
let phase_infer_ind = ref false

let infer_const_num = 0
let infer_const = ref ""

(* TNT Inference *)
let tnt_verbosity = ref 1
let tnt_infer_lex = ref true
let tnt_add_post = ref true (* disabled with @term_wo_post or --dis-term-add-post *)
let inc_add_post = ref false
let tnt_abd_strategy = ref 0 (* by default: abd_templ *)
let tnt_infer_nondet = ref true

let nondet_int_proc_name = "__VERIFIER_nondet_int"
let nondet_int_rel_name = "nondet_int__"

let hip_sleek_keywords = ["res"; "max"; "min"]

let rec_field_id = "REC"

type infer_extn = {
  extn_pred: ident;
  mutable extn_props: ident list;
}

let string_of_infer_extn extn =
  pr_pair idf (pr_list idf) (extn.extn_pred, extn.extn_props)

let mk_infer_extn id props = {
  extn_pred = id;
  extn_props = props; }

let add_avai_infer_extn_lst lst extn =
  try
    let pred, props = extn.extn_pred, extn.extn_props in
    let pred_extn = List.find (fun extn -> eq_str extn.extn_pred pred) lst in
    let () = pred_extn.extn_props <- (pred_extn.extn_props @ props) in
    lst
  with _ -> lst @ [extn]

let rec merge_infer_extn_lsts lsts =
  match lsts with
  | [] -> []
  | l::ls ->
    let merged_ls = merge_infer_extn_lsts ls in
    List.fold_left (fun lst extn -> add_avai_infer_extn_lst lst extn) merged_ls l

let expand_infer_extn_lst lst =
  List.concat (List.map (fun extn ->
    List.map (fun prop -> (extn.extn_pred, prop)) extn.extn_props) lst)

type infer_type =
  | INF_TERM (* For infer[@term] *)
  | INF_TERM_WO_POST (* For infer[@term_wo_post] *)
  | INF_POST (* For infer[@post] *)
  | INF_PRE (* For infer[@pre] *)
  | INF_SHAPE (* For infer[@shape] *)
  | INF_SHAPE_PRE (* For infer[@shape_post] *)
  | INF_SHAPE_POST (* For infer[@shape_post] *)
  | INF_SHAPE_PRE_POST (* For infer[@shape_prepost] *)
  | INF_PURE_FIELD (* For infer[@pure_field] *)
  | INF_ERROR (* For infer[@error] *)
  | INF_DE_EXC (* For infer[@dis_err] *)
  | INF_ERR_MUST (* For infer[@err_must] *)
  | INF_PRE_MUST (* For infer[@pre_must] *)
  | INF_ERR_MUST_ONLY (* For infer[@err_must_only] *)
  | INF_ERR_MAY (* For infer[@err_may] *)
  | INF_SIZE (* For infer[@size] *)
  | INF_ANA_NI
  | INF_IMM (* For infer[@imm] *)
  | INF_FIELD_IMM (* For infer[@field_imm] *)
  | INF_ARR_AS_VAR (* For infer[@arrvar] *)
  | INF_EFA (* For infer[@efa] *)
  | INF_DFA (* For infer[@dfa] *)
  | INF_FLOW (* For infer[@flow] *)
  | INF_CLASSIC (* For infer[@leak] *)
  | INF_PAR (* For infer[@par] inside par *)
  | INF_VER_POST (* For infer[@ver_post] for post-checking *)
  | INF_IMM_PRE (* For infer [@imm_pre] for inferring imm annotation on pre *)
  | INF_IMM_POST (* For infer [@imm_post] for inferring imm annotation on post *)
  | INF_EXTN of infer_extn list

let eq_infer_type i1 i2 =
  match i1, i2 with
  | INF_EXTN _, INF_EXTN _ -> true
  | INF_EXTN _, _ -> false
  | _, INF_EXTN _ -> false
  | _, _ -> i1 == i2

(* let int_to_inf_const x = *)
(*   if x==0 then INF_TERM *)
(*   else if x==1 then INF_POST *)
(*   else if x==2 then INF_PRE *)
(*   else if x==3 then INF_SHAPE *)
(*   else if x==4 then INF_IMM *)
(*   else failwith "Invalid int code for iFINF_CONST" *)

let string_of_inf_const x =
  match x with
  | INF_TERM -> "@term"
  | INF_TERM_WO_POST -> "@term_wo_post"
  | INF_POST -> "@post"
  | INF_PRE -> "@pre"
  | INF_SHAPE -> "@shape"
  | INF_SHAPE_PRE -> "@shape_pre"
  | INF_SHAPE_POST -> "@shape_post"
  | INF_SHAPE_PRE_POST -> "@shape_prepost"
  | INF_ERROR -> "@error"
  | INF_DE_EXC -> "@dis_err"
  | INF_ERR_MUST -> "@err_must"
  | INF_PRE_MUST -> "@pre_must"
  | INF_ERR_MUST_ONLY -> "@err_must_only"
  | INF_ERR_MAY -> "@err_may"
  | INF_SIZE -> "@size"
  | INF_ANA_NI -> "@ana_ni"
  | INF_IMM -> "@imm"
  | INF_PURE_FIELD -> "@pure_field"
  | INF_FIELD_IMM -> "@field_imm"
  | INF_ARR_AS_VAR -> "@arrvar"
  | INF_EFA -> "@efa"
  | INF_DFA -> "@dfa"
  | INF_FLOW -> "@flow"
  | INF_CLASSIC -> "@leak"
  | INF_PAR -> "@par"
  | INF_VER_POST -> "@ver_post"
  | INF_IMM_PRE -> "@imm_pre"
  | INF_IMM_POST -> "@imm_post"
  | INF_EXTN lst -> "@extn" ^ (pr_list string_of_infer_extn lst)

let inf_const_of_string s =
  match s with
  | "@term" -> INF_TERM
  | "@term_wo_post" -> INF_TERM_WO_POST
  | "@post" -> INF_POST
  | "@post_n" -> INF_POST
  | "@pre" -> INF_PRE
  | "@shape" -> INF_SHAPE
  | "@shape_pre" -> INF_SHAPE_PRE
  | "@shape_post" -> INF_SHAPE_POST
  | "@shape_prepost" -> INF_SHAPE_PRE_POST
  | "@error" -> INF_ERROR
  | "@dis_err" -> INF_DE_EXC
  | "@err_must" -> INF_ERR_MUST
  | "@pre_must" -> INF_PRE_MUST
  | "@err_must_only" -> INF_ERR_MUST_ONLY
  | "@err_may" -> INF_ERR_MAY
  | "@size" -> INF_SIZE
  | "@imm" -> INF_IMM
  | "@pure_field" -> INF_PURE_FIELD
  | "@field_imm" -> INF_FIELD_IMM
  | "@arrvar" -> INF_ARR_AS_VAR
  | "@efa" -> INF_EFA
  | "@dfa" -> INF_DFA
  | "@flow" -> INF_FLOW
  | "@leak" -> INF_CLASSIC
  | "@par" -> INF_PAR
  | "@ver_post" -> INF_VER_POST
  | "@imm_pre" -> INF_IMM_PRE
  | "@imm_post" -> INF_IMM_POST
  | _ -> failwith (s ^ " is not supported in command line.")

(* let inf_const_to_int x = *)
(*   match x with *)
(*   | INF_TERM -> 0 *)
(*   | INF_POST -> 1 *)
(*   | INF_PRE -> 2 *)
(*   | INF_SHAPE -> 3 *)
(*   | INF_IMM -> 4 *)

(* class inf_obj  = *)
(* object (self) *)
(*   val len = 10 *)
(*   val arr = Array.make 10 false *)
(*   method set_init_arr s =  *)
(*     let helper r c = *)
(*       let reg = Str.regexp r in *)
(*       try *)
(*         begin *)
(*           Str.search_forward reg s 0; *)
(*           Array.set arr (inf_const_to_int c) true; *)
(*           print_endline ("infer option added :"^(string_of_inf_const c)); *)
(*         end *)
(*       with Not_found -> () *)
(*     in *)
(*     begin *)
(*       helper "@term"  INF_TERM; *)
(*       helper "@pre"   INF_PRE; *)
(*       helper "@post"  INF_POST; *)
(*       helper "@imm"   INF_IMM; *)
(*       helper "@shape" INF_SHAPE; *)
(*       let x = Array.fold_right (fun x r -> x || r) arr false in *)
(*       if not(x) then failwith  ("empty -infer option :"^s)  *)
(*     end *)
(*   method is_empty  = not(Array.fold_right (fun x r -> x || r) arr false) *)
(*   (\* method string_at i =  *\) *)
(*   (\*   try *\) *)
(*   (\*     string_of_inf_const (Array.get arr i) *\) *)
(*   (\*   with _ -> "" *\) *)
(*   method string_of_raw =  *)
(*     let str_a = Array.mapi (fun i v -> if v then string_of_inf_const (int_to_inf_const i) else "") arr in *)
(*     let lst_a = Array.to_list str_a in  *)
(*     String.concat "," (List.filter (fun s -> not(s="")) lst_a)  *)
(*   method string_of = "["^(self #string_of_raw)^"]" *)
(*   method get c  = Array.get arr (inf_const_to_int c) *)
(*   method get_int i  = Array.get arr i *)
(*   method is_term  = self # get INF_TERM *)
(*   method is_pre  = self # get INF_PRE *)
(*   method is_post  = self # get INF_POST *)
(*   method is_imm  = self # get INF_IMM *)
(*   method is_shape  = self # get INF_SHAPE *)
(*   method get_arr  = arr *)
(*   method get_lst =  *)
(*     let lst = Array.to_list (Array.mapi (fun i v -> if v then Some (int_to_inf_const i) else None) arr) in *)
(*     List.fold_left (fun l e -> match e with Some e -> e::l | _-> l) [] lst  *)
(*   method set c  = Array.set arr (inf_const_to_int c) true *)
(*   method set_ind i  = Array.set arr i true *)
(*   method set_list l  = List.iter (fun c -> Array.set arr (inf_const_to_int c) true) l *)
(*   method reset c  = Array.set arr (inf_const_to_int c) false *)
(*   method mk_or (o2:inf_obj) =  *)
(*     let o1 = o2 # clone in *)
(*     let () = Array.iteri (fun i a -> if a then o1 # set_ind i) arr in *)
(*     o1 *)
(*   method clone =  *)
(*     let no = new inf_obj in *)
(*     let ar = no # get_arr in *)
(*     let () = Array.iteri (fun i _ -> Array.set ar i (self # get_int i)) ar in *)
(*     (\* let () = print_endline ("Cloning :"^(no #string_of)) in *\) *)
(*     no *)
(* end;; *)

class inf_obj  =
  object (self)
    val mutable arr = []
    method init =
      if !enable_error_as_exc then self # set INF_ERR_MUST;
      if self # is_field_imm then allow_field_ann:=true;
      if self # get INF_ARR_AS_VAR then array_translate :=true
    method set_init_arr s =
      begin
        let inf_cmds = Str.split (Str.regexp "@") s in
        let inf_cmds = List.map (fun cmd -> "@" ^ cmd) inf_cmds in
        (* let () = print_endline_q ("inf cmd: " ^ s) in                                    *)
        (* let () = print_endline_q ("inf_cmds: " ^ (pr_list (fun cmd -> cmd) inf_cmds)) in *)
        let inf_const_lst = List.fold_left (fun acc cmd ->
            try acc @ [(inf_const_of_string cmd)]
            with _ -> print_endline_q (cmd ^ " is not supported in command line."); acc
          ) [] inf_cmds
        in
        let () = arr <- inf_const_lst @ arr in
        let () = print_endline_q ("infer option added: " ^ (pr_list string_of_inf_const inf_const_lst)) in

      (* let helper i r c =                                                                                             *)
      (*   let reg = Str.regexp r in                                                                                    *)
      (*   try                                                                                                          *)
      (*     begin                                                                                                      *)
      (*       Str.search_forward reg s i; (* This search causes information lost, e.g. "@shape_prepost@post_n@term" *) *)
      (*       arr <- c::arr;                                                                                           *)
      (*       (* Trung: temporarily disable printing for svcomp15, undo it later *)                                    *)
      (*       print_endline_q ("infer option added :"^(string_of_inf_const c));                                        *)
      (*       i + (String.length (string_of_inf_const c))                                                              *)
      (*     end                                                                                                        *)
      (*   with Not_found -> i                                                                                          *)
      (* in                                                                                                             *)
      (* begin                                                                                                          *)
      (*   let i = helper 0 "@term_wo_post"  INF_TERM_WO_POST in (* same prefix with @term *)                           *)
      (*   let i = helper i "@pure_field"    INF_PURE_FIELD in                                                          *)
      (*   let i = helper i "@field_imm"     INF_FIELD_IMM in                                                           *)
      (*   let i = helper i "@arrvar"        INF_ARR_AS_VAR in                                                          *)
      (*   let i = helper i "@shape_prepost" INF_SHAPE_PRE_POST in (* same prefix with @shape_pre *)                    *)
      (*   let i = helper i "@shape_pre"     INF_SHAPE_PRE in                                                           *)
      (*   let i = helper i "@shape_post"    INF_SHAPE_POST in                                                          *)
      (*   let i = helper i "@shape"         INF_SHAPE in                                                               *)
      (*   let i = helper i "@term"          INF_TERM in                                                                *)
      (*   let i = helper i "@pre"           INF_PRE in                                                                 *)
      (*   let i = helper i "@post"          INF_POST in                                                                *)
      (*   let i = helper i "@imm"           INF_IMM in                                                                 *)
      (*   let i = helper i "@error"         INF_ERROR in                                                               *)
      (*   let i = helper i "@dis_err"       INF_DE_EXC in                                                              *)
      (*   let i = helper i "@err_may"       INF_ERR_MAY in                                                             *)
      (*   let i = helper i "@err_must_only" INF_ERR_MUST_ONLY in (* same prefix with @err_must *)                      *)
      (*   let i = helper i "@err_must"      INF_ERR_MUST in                                                            *)
      (*   let i = helper i "@size"          INF_SIZE in                                                                *)
      (*   let i = helper i "@efa"           INF_EFA in                                                                 *)
      (*   let i = helper i "@dfa"           INF_DFA in                                                                 *)
      (*   let i = helper i "@flow"          INF_FLOW in                                                                *)
      (*   let i = helper i "@leak"          INF_CLASSIC in                                                             *)
      (*   let i = helper i "@classic"       INF_CLASSIC in                                                             *)
      (*   let i = helper i "@par"           INF_PAR in                                                                 *)
      (*   let i = helper i "@ver_post"      INF_VER_POST in (* @ato, @arr_to_var *)                                    *)
      (*   let i = helper i "@imm_pre"       INF_IMM_PRE in                                                             *)
      (*   let i = helper i "@imm_post"      INF_IMM_POST in                                                            *)
      (*   (* let x = Array.fold_right (fun x r -> x || r) arr false in *)                                              *)
        if arr==[] then failwith  ("empty -infer option :"^s)
      end
    method is_empty  = arr==[]
    (* method string_at i =  *)
    (*   try *)
    (*     string_of_inf_const (Array.get arr i) *)
    (*   with _ -> "" *)
    method string_of_raw =
      let lst_a = List.map string_of_inf_const arr in
      String.concat "," lst_a
    method string_of = "["^(self #string_of_raw)^"]"
    method get c  = List.mem c arr
    (* method get_int i  = Array.get arr i *)
    method is_term = (self # get INF_TERM) || (self # get INF_TERM_WO_POST)
    (* termination inference *)
    method is_term_wo_post = self # get INF_TERM_WO_POST
    (* termination inference wo post-condition *)
    method is_pre  = self # get INF_PRE
    method is_pre_imm = self # get INF_IMM_PRE || self # get INF_IMM
    (* pre-condition inference *)
    method is_post  = self # get INF_POST
    method is_post_imm = self # get INF_IMM_POST ||  self # get INF_IMM
    (* post-condition inference *)
    method is_ver_post  = self # get INF_VER_POST
    method is_field_imm = self # get INF_FIELD_IMM
    method is_arr_as_var  = self # get INF_ARR_AS_VAR
    method is_imm  = self # get INF_IMM
    method is_pure_field  = self # get INF_PURE_FIELD (* || !sa_pure_field *)
    (* immutability inference *)
    method is_field = (self # get INF_FIELD_IMM)
    method is_shape  = self # get INF_SHAPE
    method is_shape_pre  = self # get INF_SHAPE_PRE
    method is_shape_post  = self # get INF_SHAPE_POST
    method is_shape_pre_post  = self # get INF_SHAPE_PRE_POST
    (* shape inference *)
    method is_error  = self # get INF_ERROR
    method is_dis_err  = self # get INF_DE_EXC
                         || (not(self # get INF_ERR_MUST)
                             && not(self # get INF_ERR_MAY))
    method is_err_must  = not(self # get INF_DE_EXC)
                          && not(self # get INF_ERR_MAY)
                          && self # get INF_ERR_MUST
    method is_pre_must  = not(self # get INF_DE_EXC)
                          && self # get INF_PRE_MUST
    method is_err_must_only  = not(self # get INF_DE_EXC)
                               && not(self # get INF_ERR_MAY)
                               && not(self # get INF_ERR_MUST)
                               && self # get INF_ERR_MUST_ONLY
    method is_err_may  = not(self # get INF_DE_EXC)
                         && self # get INF_ERR_MAY
    method is_size  = self # get INF_SIZE
    method is_ana_ni  = self # get INF_ANA_NI
    method is_efa  = self # get INF_EFA
    method is_dfa  = self # get INF_DFA
    method is_classic  = self # get INF_CLASSIC
    method is_par  = self # get INF_PAR
    method is_add_flow  = self # get INF_FLOW
    method is_extn =
      List.exists (fun inf ->
        match inf with | INF_EXTN _ -> true | _ -> false) arr
    method get_infer_extn_lst =
      try
        let inf_extn = List.find (fun inf ->
          match inf with | INF_EXTN _ -> true | _ -> false) arr in
        match inf_extn with
        | INF_EXTN lst -> lst
        | _ -> []
      with _ -> []
    method add_infer_extn_lst pred props =
      let rec helper inf_obj_lst pred props =
        let inf_extn = mk_infer_extn pred props in
        match inf_obj_lst with
        | [] -> [(INF_EXTN [inf_extn])]
        | inf::infs ->
          (begin match inf with
          | INF_EXTN lst ->
            let n_lst = add_avai_infer_extn_lst lst inf_extn in
            (INF_EXTN n_lst)::infs
          | _ -> inf::(helper infs pred props)
          end)
      in
      arr <- (helper arr pred props)
    (* method get_arr  = arr *)
    method is_infer_type t  = self # get t
    method get_lst = arr
    method get_lst_sel =
      let  is_selected e =
        match e with
        | INF_TERM | INF_TERM_WO_POST | INF_PRE | INF_POST -> true
        | _ -> false in
      List.filter is_selected arr
    method set c  = if self#get c then () else arr <- c::arr
    method set_list l  = List.iter (fun c -> self # set c) l
    method reset c  = arr <- List.filter (fun x -> not (eq_infer_type c x)) arr
    method reset_list l  = arr <- List.filter (fun x-> List.for_all (fun c -> not (c=x)) l) arr
    method reset_inf_shape = self # reset_list [INF_SHAPE_PRE_POST; INF_SHAPE_PRE; INF_SHAPE_POST; INF_SHAPE]
    method reset_all = arr <- []
    (* method mk_or (o2:inf_obj) =  *)
    (*   let o1 = o2 # clone in *)
    (*   let l = self # get_lst in *)
    (*   let () = o1 # set_list l in *)
    (*   o1 *)
    (* method clone =  *)
    (*   let no = new inf_obj in *)
    (*   let () = no # set_list arr in *)
    (*   (\* let () = print_endline ("Cloning :"^(no #string_of)) in *\) *)
    (*   no *)
    (* method is__all  = super # is_ || infer_const_obj # is_ *)
    (* method is_classic_all  = *)
    (*   print_endline "WARNING:invoking super#is_classic_all"; *)
    (*   self # is_classic *)
    (* method is_ver_post_all  = *)
    (*   print_endline "WARNING:invoking super#is_verify_post_all"; *)
    (*   self # is_ver_post *)
    (* method is_par_all  = *)
    (*   print_endline "WARNING:invoking super#is_par_all"; *)
    (*   self # is_par *)
  end;;

(* class inf_w_lst = *)
(*   object (self) *)
(*     val mutable arr = [] *)
(*     method string_of_raw =  *)
(*       let lst_a = List.map string_of_inf_const arr in *)
(*       String.concat "," lst_a *)
(*     method string_of = "["^(self #string_of_raw)^"]" *)
(*     method get_lst = arr *)
(*   end *)

let infer_const_obj = new inf_obj;;

let global_efa_exc ()  = not(infer_const_obj # is_dis_err)

let is_en_efa_exc ()=
  infer_const_obj # is_err_must || infer_const_obj # is_err_may

(* local setting takes precedence over global setting *)
(*    dis_err > err_may > err_must *)
(*      dis_err & err_may --> dis_err *)
(*      dis_err & err_must --> dis_err *)
(*      err_may & err_must --> err_may *)

(* let global_is_dis_err ()  = infer_const_obj # is_dis_err *)
(* let global_is_err_may ()  = not(infer_const_obj # is_dis_err)  *)
(*                             && infer_const_obj # is_err_may *)
(* let global_is_err_must ()  = not(infer_const_obj # is_dis_err)  *)
(*                              && not(infer_const_obj # is_err_may)  *)
(*                              && infer_const_obj # is_err_must *)

(* let local_is_dis_err obj  = obj # is_dis_err  *)
(*                             || infer_const_obj # is_dis_err *)
(* let local_is_err_may obj  = obj # is_err_may || global_is_err_may () *)
(* let local_is_err_must obj  = obj # is_err_must || global_is_err_must () *)


class inf_obj_sub  =
  object (self)
    inherit inf_obj as super
    method is_arr_as_var_all  =
      self # get INF_ARR_AS_VAR
      || infer_const_obj # is_arr_as_var
    method is_dis_err_all  = self # get INF_DE_EXC
                             || (not(self # get INF_ERR_MUST) && not(self # get INF_ERR_MAY)
                                 && infer_const_obj # is_dis_err)
    method is_err_may_all  = self # get INF_ERR_MAY
                             || (not(self # get INF_ERR_MUST) && not(self # get INF_DE_EXC)
                                 && infer_const_obj # is_err_may)
    method is_err_must_all  = self # get INF_ERR_MUST
                              || (not(self # get INF_ERR_MAY) && not(self # get INF_DE_EXC)
                                  && infer_const_obj # is_err_must)
    method is_classic_all  = super # is_classic || infer_const_obj # is_classic
    method is_imm_all  = super # is_imm || infer_const_obj # is_imm
    method is_pure_field_all  = super # is_pure_field || infer_const_obj # is_pure_field
    (* method is__all  = super # is_ || infer_const_obj # is_ *)
    method is_ver_post_all  = super # is_ver_post || infer_const_obj # is_ver_post
    method is_par_all  = super # is_par || infer_const_obj # is_par
    (* to pick selected items to propagate from global to local *)
    method mk_or_sel (o2:inf_obj) =
      let o1 = self # clone in
      let l = o2 # get_lst_sel in
      let () = o1 # set_list l in
      o1
    method mk_or_all (o2:inf_obj) =
      let o1 = self # clone in
      let l = o2 # get_lst in
      let () = o1 # set_list l in
      o1
    method mk_or_lst (l) =
      let o1 = self # clone in
      let () = o1 # set_list l in
      o1
    method clone =
      let no = new inf_obj_sub in
      let () = no # set_list arr in
      (* let () = print_endline ("Cloning :"^(no #string_of)) in *)
      no
    method empty = arr <- []
  end;;

let clone_sub_infer_const_obj_all () =
  let obj = new inf_obj_sub in
  obj # mk_or_all infer_const_obj

let clone_sub_infer_const_obj_sel () =
  let obj = new inf_obj_sub in
  obj # mk_or_sel infer_const_obj

(* let set_infer_const s = *)

let tnt_thres = ref 6
let tnt_verbose = ref 1

(* String Inference *)
let new_pred_syn = ref true
let pred_elim_node = ref false

(* Template: Option for Template Inference *)
let templ_term_inf = ref false
let gen_templ_slk = ref false
let templ_piecewise = ref false

(* Options for slicing *)
let en_slc_ps = ref false
let auto_eps_flag = ref true
let override_slc_ps = ref false (*used to force disabling of en_slc_ps, for run-fast-tests testing of modular examples*)
let dis_ps = ref false
let dis_slc_ann = ref false
let slicing_rel_level = ref 2

(* let do_slicing = ref false *)
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
let do_test_inv = ref true (* false *)

(** for classic frame rule of separation logic *)
(* let opt_classic = ref false                (\* option --classic is turned on or not? *\) *)
(* replaced by check_is_classic () & infer_const_obj *)
(* let do_classic_frame_rule = ref false      (\* use classic frame rule or not? *\) *)

let dis_impl_var = ref false (* Disable implicit vars *)

let show_unexpected_ents = ref true

(* generate baga inv from view *)
let double_check = ref false
let gen_baga_inv = ref false
let delay_eelim_baga_inv = ref false
let dis_baga_inv_check = ref false

let is_inferring = ref false
let use_baga = ref false

(* let unsat_count_syn = ref (0:int) *)
(* let unsat_count_sem = ref (0:int) *)

let prove_invalid = ref false
let gen_baga_inv_threshold = 7 (* number of preds <=6, set gen_baga_inv = false*)
let do_under_baga_approx = ref false (* flag to choose under_baga *)
(* let baga_xpure = ref true (\* change to true later *\) *)
let baga_imm = ref false                 (* wen on true, ignore @L nodes while building baga --  this is forced into true when computing baga for vdef*)

(* get counter example *)
let get_model = ref false

(** for type of frame inference rule that will be used in specs commands *)
(* type = None       --> option --classic will be used to decides whether using classic rule or not? *)
(*        Some true  --> always perform classic rule, regardless of --classic option                 *)
(*        Some false --> always perform intutitive rule, regardless of --classic option              *)
type ensures_type = bool option
type assert_type = bool option
type entail_type = bool option

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

let omega_err = ref false

let seq_number = ref 10

let sat_timeout_limit = ref 5.
let user_sat_timeout = ref false
let imply_timeout_limit = ref 10.

let dis_provers_timeout = ref false
let sleek_timeout_limit = ref 5.


let dis_inv_baga () =
  if (not !web_compile_flag) then print_endline_q "Disabling baga inv gen ..";
  let () = gen_baga_inv := false in
  ()

let dis_bk ()=
  let () = oc_simplify := true in
  let () = sat_timeout_limit:= 5. in
  let () = user_sat_timeout := false in
  let () = imply_timeout_limit := 10. in
  (* let () = en_slc_ps := false in *)
  ()

let dis_pred_sat () =
  if (not !web_compile_flag) then print_endline_q "Disabling pred sat ..";
  (* let () = gen_baga_inv := false in *)
  let () = prove_invalid := false in
  (*baga bk*)
  let () = dis_bk () in
  ()

let en_bk () =
  let () = oc_simplify := false in
  let () = sat_timeout_limit:= 1. in
  let () = user_sat_timeout := true in
  let () = imply_timeout_limit := 1. in
  (* let () = en_slc_ps := true in *)
  ()

let en_pred_sat () =
  (* print_endline_q "Enabling baga inv gen .."; *)
  (* let () = gen_baga_inv := true in *)
  let () = prove_invalid := true in
  (*baga bk*)
  let () = en_bk ()  in
  ()

(* let () = if !smt_compete_mode then *)
(*   begin *)
(*     (\* Debug.trace_on := false; *\) *)
(*     (\* Debug.devel_debug_on:= false; *\) *)
(*     silence_output:=true; *)
(*     enable_count_stats:=false; *)
(*     enable_time_stats:=false; *)
(*     print_core:=false; *)
(*     print_core_all:=false; *)
(*     (\* gen_baga_inv := true; *\) *)
(*     en_pred_sat (); *)
(*     (\* do_infer_inv := true; *\) *)
(*     lemma_gen_unsafe := true; *)
(*     graph_norm := true; *)
(*     smt_compete_mode:=true *)
(*   end *)

(* let reporter = ref (fun _ -> raise Not_found) *)

(* let report_error2 (pos : loc) (msg : string) = *)
(*   let () = *)
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

(* generate smt from slk *)
let gen_smt = ref false


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

let mk_strict_branch_point (id:control_path_id) (s:string) : control_path_id_strict =
  match id with
  | Some i -> i
  | None -> fresh_formula_label s

let eq_formula_label (l1:formula_label) (l2:formula_label) : bool = fst(l1)=fst(l2)

let fresh_int () =
  let rec find i lst = match lst with
    | [] -> false,[]
    | hd::tl ->
      try
        let hd_int = int_of_string hd in
        if i = hd_int then true,tl
        else if i < hd_int then false,lst
        else find i tl
      with _ -> find i tl
  and helper i =
    let is_mem,trailer_num_list_tail = find i !trailer_num_list in
    let () = trailer_num_list := trailer_num_list_tail in
    if is_mem then helper (i+1) else i
    (* let rec helper i = *)
    (*   if List.mem (string_of_int i) !trailer_num_list *)
    (*   then *)
    (*     let () = trailer_num_list := List.tl !trailer_num_list in *)
    (*     helper (i+1) *)
    (*   else i *)
  in
  seq_number := helper (!seq_number + 1);
  !seq_number


(* let seq_number2 = ref 0 *)

(* let fresh_int2 () = *)
(*   seq_number2 := !seq_number2 + 1; *)
(*   !seq_number2 *)

(* let reset_int2 () = *)
(*   seq_number2 := 0 *)

(* let get_int2 () = *)
(*   !seq_number2 *)

(* let fresh_int () = *)
(*   seq_number := !seq_number + 1; *)
(*   !seq_number *)

let string_eq s1 s2 =  String.compare s1 s2=0

let fresh_ty_var_name (t:typ)(ln:int):string =
  let ln = if ln<0 then 0 else ln in
  ("v_"^(string_of_typ_alpha t)^"_"^(string_of_int ln)^"_"^(string_of_int (fresh_int ())))

let fresh_var_name (tn:string)(ln:int):string =
  ("v_"^tn^"_"^(string_of_int ln)^"_"^(string_of_int (fresh_int ())))

let fresh_trailer () =
  let str = string_of_int (fresh_int ()) in
  (*-- 09.05.2008 *)
  (*let () = (print_string ("\n[globals.ml, line 103]: fresh name = " ^ str ^ "\n")) in*)
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
  let line = if pos.start_pos.Lexing.pos_lnum > 0 then
      string_of_int pos.start_pos.Lexing.pos_lnum
    else "0" in
  "f_l_" ^ line ^ "_"^(string_of_int (fresh_int ()))

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


let string_of_formula_label ((i,s):formula_label) =
  "(" ^ (string_of_int i) ^ " , " ^ s ^ ")"

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

let concat_pair_of_lists l1 l2 =
  (((fst l1)@(fst l2)), ((snd l1)@(snd l2)))

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
    | ((a1,_),b1)::zt1,((a2,_),b2)::zt2 -> (a1<a2) || (a1=a2 && b1<b2) || (a1=a2 && b1=b2 && lt zt1 zt2)
  in lt (List.rev p1) (List.rev p2)

let path_trace_gt p1 p2 =
  let rec gt pt1 pt2 = match pt1,pt2 with
    | [],[] -> false
    | [],xs -> false
    |  xs,[] -> true
    | ((a1,_),b1)::zt1,((a2,_),b2)::zt2 -> (a1>a2) || (a1=a2 && b1>b2) || (a1=a2 && b1=b2 && gt zt1 zt2)
  in gt (List.rev p1) (List.rev p2)

let dummy_exception e = ()

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


(* An Hoa : option to print proof *)
let print_proof = ref false

(* Create a quoted version of a string, for example, hello --> "hello" *)
let strquote s = "\"" ^ s ^ "\""

let norm_file_name str =
  let str_bytes = Bytes.of_string str in
  for i = 0 to (Bytes.length str_bytes) - 1 do
    if Bytes.get str_bytes i = '.' || Bytes.get str_bytes i = '/' then str_bytes.[i] <- '_'
  done;
  Bytes.to_string str_bytes

(* let wrap_classic et f a = *)
(*   let flag = !do_classic_frame_rule in *)
(*   do_classic_frame_rule := (match et with *)
(*     | None -> !opt_classic *)
(*     | Some b -> b); *)
(*   try  *)
(*     let res = f a in *)
(*     (\* restore flag do_classic_frame_rule  *\) *)
(*     do_classic_frame_rule := flag; *)
(*     res *)
(*   with _ as e -> *)
(*       (do_classic_frame_rule := flag; *)
(*       raise e) *)

(* let wrap_gen save_fn set_fn restore_fn flags f a = *)
(*   (\* save old_value *\) *)
(*   let old_values = save_fn flags in *)
(*   let () = set_fn flags in *)
(*   try  *)
(*     let res = f a in *)
(*     (\* restore old_value *\) *)
(*     restore_fn old_values; *)
(*     res *)
(*   with _ as e -> *)
(*       (restore_fn old_values; *)
(*       raise e) *)

(* let wrap_one_bool flag new_value f a = *)
(*   let save_fn flag = (flag,!flag) in *)
(*   let set_fn flag = flag := new_value in *)
(*   let restore_fn (flag,old_value) = flag := old_value in *)
(*   wrap_gen save_fn set_fn restore_fn flag f a *)

(* let wrap_two_bools flag1 flag2 new_value f a = *)
(*   let save_fn (flag1,flag2) = (flag1,flag2,!flag1,!flag2) in *)
(*   let set_fn (flag1,flag2) = flag1 := new_value; flag2:=new_value in *)
(*   let restore_fn (flag1,flag2,old1,old2) = flag1 := old1; flag2:=old2 in *)
(*   wrap_gen save_fn set_fn restore_fn (flag1,flag2) f a *)

(* (\* let wrap_general flag new_value f a = *\) *)
(* (\*   (\\* save old_value *\\) *\) *)
(* (\*   let old_value = !flag in *\) *)
(* (\*   flag := new_value; *\) *)
(* (\*   try  *\) *)
(* (\*     let res = f a in *\) *)
(* (\*     (\\* restore old_value *\\) *\) *)
(* (\*     flag := old_value; *\) *)
(* (\*     res *\) *)
(* (\*   with _ as e -> *\) *)
(* (\*       (flag := old_value; *\) *)
(* (\*       raise e) *\) *)

(* let wrap_no_filtering f a = *)
(*   wrap_one_bool filtering_flag false f a *)

(* let wrap_lbl_dis_aggr f a = *)
(*   wrap_two_bools label_aggressive_sat label_aggressive_imply false f a *)

let proof_no = ref 0

let next_proof_no () =
  proof_no := !proof_no + 1;
  !proof_no

(* let next_proof_no_str () = *)
(*   proof_no := !proof_no + 1; *)
(*   string_of_int !proof_no *)

let get_proof_no () = !proof_no

let get_proof_no_str () = string_of_int !proof_no

let sleek_proof_no = ref 0

let last_sleek_fail_no = ref 0

let get_sleek_no () = !sleek_proof_no

let set_sleek_no n = sleek_proof_no:=n

let get_last_sleek_fail () = !last_sleek_fail_no

let set_last_sleek_fail () =
  last_sleek_fail_no := !sleek_proof_no

(* let next_sleek_int () : int = *)
(*   sleek_proof_no := !sleek_proof_no + 1;  *)
(*   (!sleek_proof_no) *)


(* let read_from_debug_file chn : string list = *)
(*   let line = ref [] in *)
(*   let quitloop = ref false in *)
(*   (try *)
(*     while true do *)
(*       let xs = (input_line chn) in *)
(*       let n = String.length xs in *)
(*       (\* let s = String.sub xs 0 1 in *\) *)
(*       if n > 0 && xs.[0]=='#' (\* String.compare s "#" !=0 *\) then begin *)
(*         line := xs::!line; *)
(*       end; *)
(*     done; *)
(*   with _ -> ()); *)
(*   !line *)

(* let debug_map = Hashtbl.create 50 *)

(* let read_main () = *)
(*   let xs = read_from_debug_file (debug_file ()) in *)
(*   (\* let () = print_endline ((pr_list (fun x -> x)) xs) in *\) *)
(*   List.iter (fun x -> *)
(*       try *)
(*         let l = String.index x ',' in *)
(*         let m = String.sub x 0 l in *)
(*         let split = String.sub x (l+1) ((String.length x) -l -1) in *)
(*         let () = print_endline (m) in *)
(*         let () = print_endline (split) in *)
(*         let kind = if String.compare split "Trace" == 0 then DO_Trace else *)
(*           if String.compare split "Loop" == 0 then DO_Loop else *)
(*             DO_Normal *)
(*         in *)
(*         Hashtbl.add debug_map m kind *)
(*       with _ -> *)
(*       Hashtbl.add debug_map x DO_Normal *)
(*   ) xs *)

(* let in_debug x = *)
(*   try *)
(*     Hashtbl.find debug_map x *)
(*   with _ -> DO_None *)

(* let inf_number = ref 0 *)

(* let fresh_inf_number() =  *)
(*   inf_number := !inf_number + 1; *)
(*   string_of_int(!inf_number) *)

let gen_field_ann t=
  match t with
  | Named _ -> fresh_any_name field_rec_ann
  | _ -> fresh_any_name field_val_ann

let gen_field_ann t =
  if !old_field_tag then [gen_field_ann t]
  else []

let un_option opt default_val = match opt with
  | Some v -> v
  | None -> default_val

let rec gcd (a: int) (b: int): int =
  if b == 0 then a
  else gcd b (a mod b)

let gcd_l (l: int list): int =
  let l = List.filter (fun x -> x != 0) l in
  match l with
  | [] -> 1
  | x::[] -> 1
  | x::xs -> List.fold_left (fun a x -> gcd a x) x xs

let abs (x: int) = if x < 0 then -x else x

let lcm (a: int) (b: int): int = (a * b) / (gcd a b)

let lcm_l (l: int list): int =
  if List.exists (fun x -> x == 0) l then 0
  else match l with
    | [] -> 1
    | x::[] -> x
    | x::xs -> List.fold_left (fun a x -> lcm a x) x xs

let smt_return_must_on_error ()=
  let () = if !return_must_on_pure_failure then
      (* let () = smt_is_must_failure := (Some true) in *) ()
    else ()
  in ()

let string_of_lemma_kind (l: lemma_kind) =
  match l with
  | LEM           -> "LEM"
  | LEM_PROP      -> "LEM_PROP"
  | LEM_SPLIT      -> "LEM_SPLIT"
  | LEM_TEST      -> "LEM_TEST"
  | LEM_TEST_NEW  -> "LEM_TEST_NEW"
  | LEM_UNSAFE    -> "LEM_UNSAFE"
  | LEM_SAFE      -> "LEM_SAFE"
  | LEM_INFER     -> "LEM_INFER"
  | LEM_INFER_PRED   -> "LEM_INFER_PRED"
  | RLEM -> "RLEM"

type debug_lvl = Short | Normal | Long
let debug_level = ref Normal

let prim_method_names = [ nondet_int_proc_name ]

let is_prim_method pn =
  List.exists (fun mn -> String.compare pn mn == 0) prim_method_names

let check_is_classic_local obj =
  let r = obj (* infer_const_obj *) # get INF_CLASSIC in
  if !new_trace_classic then print_endline ("Globals.check_is_classic: " ^ (string_of_bool r));
  r

let check_is_classic () = check_is_classic_local infer_const_obj

let check_is_pure_field_local obj =
  let r = obj (* infer_const_obj *) # get INF_PURE_FIELD in
  r

let check_is_pure_field () = check_is_pure_field_local infer_const_obj

type 'a regex_list =
  | REGEX_STAR
  | REGEX_LIST of 'a list

type regex_id_list = ident regex_list

let string_of_regex_list pr m =
  match m with
  | REGEX_STAR -> "*"
  | REGEX_LIST lst -> pr_list pr lst

type regex_id_star_list = (ident * bool) regex_list

let string_of_regex_star_list m = string_of_regex_list (fun (i,b) -> i^(if b then "*" else "")) m

let string_of_regex_id_star_list =
  string_of_regex_list (pr_pair idf string_of_bool)

let build_sel_scc scc_lst get_name lst =
  List.map
    (fun scc
      -> List.map (fun c ->
          List.find (fun v -> (get_name v)=c) lst
        ) scc
    ) scc_lst
