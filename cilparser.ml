#include "xdebug.cppo"

open VarGen
open Globals
open Exc.GTable
open Gen.Basic

module IF = Iformula

(*******************************************************)
(*         string conversion functions for CIL         *)
(*******************************************************)
let string_of_cil_exp (e: Cil.exp) : string =
  (match e with
   | Cil.Const _ -> "Const "
   | Cil.Lval _ -> "Lval "
   | Cil.SizeOf _ -> "SizeOf "
   | Cil.SizeOfE _ -> "SizeOfE "
   | Cil.SizeOfStr _ -> "SizeOfStr "
   | Cil.AlignOf _ -> "AlignOf "
   | Cil.AlignOfE _ -> "AlignOfE "
   | Cil.UnOp _ -> "UnOp "
   | Cil.BinOp _ -> "BinOp "
   | Cil.Question _ -> "Question "
   | Cil.CastE _ -> "CastE "
   | Cil.AddrOf _ -> "AddrOf "
   | Cil.StartOf _ -> "StartOf ") ^
  (Pretty.sprint 10 (Cil.d_exp () e))

let string_of_cil_unop (o: Cil.unop) : string =
  Pretty.sprint 10 (Cil.d_unop () o)

let string_of_cil_binop (o: Cil.binop) : string =
  Pretty.sprint 10 (Cil.d_binop () o)

let string_of_cil_loc (l: Cil.location) : string =
  Pretty.sprint 10 (Cil.d_loc () l)

let string_of_cil_lval (lv: Cil.lval) : string =
  Pretty.sprint 10 (Cil.d_lval () lv)

let string_of_cil_offset (off: Cil.offset) : string =
  Pretty.sprint 10 (Cil.d_offset Pretty.nil () off)

let string_of_cil_init (i: Cil.init) : string =
  Pretty.sprint 10 (Cil.d_init () i)

let string_of_cil_typ (t: Cil.typ) : string =
  Pretty.sprint 10 (Cil.d_type () t)

let string_of_cil_attrlist (a: Cil.attributes) : string =
  Pretty.sprint 10 (Cil.d_attrlist () a)

let string_of_cil_attr (a: Cil.attribute) : string =
  Pretty.sprint 10 (Cil.d_attr () a)

let string_of_cil_attrparam (e: Cil.attrparam) : string =
  Pretty.sprint 10 (Cil.d_attrparam () e)

let string_of_cil_label (l: Cil.label) : string =
  Pretty.sprint 10 (Cil.d_label () l)

let string_of_cil_stmt (s: Cil.stmt) : string =
  Pretty.sprint 10 (Cil.d_stmt () s)

let string_of_cil_block (b: Cil.block) : string =
  Pretty.sprint 10 (Cil.d_block () b)

let string_of_cil_fundec (fd: Cil.fundec) : string =
  Pretty.sprint 10 (Cil.d_fundec () fd)

let string_of_cil_instr (i: Cil.instr) : string =
  Pretty.sprint 10 (Cil.d_instr () i)

let string_of_cil_global (g: Cil.global) : string =
  Pretty.sprint 10 (Cil.d_global () g)

let string_of_cil_file (f: Cil.file) : string =
  let globals = f.Cil.globals in
  String.concat "\n\n" (List.map (fun g -> string_of_cil_global g) globals)

(* ---   end of string conversion   --- *)

(* --------------------- *)
(* Global variables      *)
(* --------------------- *)

let str_addr = "addr_"
let str_value = "value"
let str_char = "val" (*the value field of char* a.k.a string*)
let str_offset = "offset"

let eq_str s1 s2 = String.compare s1 s2 == 0

(* let tbl_typedef : (string, Cil.typ) Hashtbl.t = Hashtbl.create 1 *)
let tbl_typedef = new Gen.hash_table "tbl_typedef" pr_id string_of_cil_typ

(* hash table contains Globals.typ structures that are used to represent Cil.typ pointers *)
(* let tbl_pointer_typ : (Cil.typ, Globals.typ) Hashtbl.t = Hashtbl.create 1 *)
let tbl_pointer_typ = new Gen.hash_table "tbl_pointer_typ" string_of_cil_typ Globals.string_of_typ

(* hash table contains Iast.data_decl structures that are used to represent pointer types *)
(* let tbl_data_decl : (Globals.typ, Iast.data_decl) Hashtbl.t = Hashtbl.create 1 *)
let tbl_data_decl = new Gen.hash_table "tbl_data_decl" Globals.string_of_typ !Iast.print_data_decl

(* hash table map lval expressions (in string form) to their address holder generated-pointers *)
(* let tbl_addrof_info : (string, string) Hashtbl.t = Hashtbl.create 1 *)
let tbl_addrof_info = new Gen.hash_table "tbl_addr_info" pr_id pr_id

(* let print_tbl_addrof () =
   (* let  () = Printf.printf "Table of tbl_addrof \n" in *)
   let s = Hashtbl.fold (fun a b c -> (a^"->"^b^";"^c)) tbl_addrof_info "" in
   ("["^s^"]") *)

(* list of nondeterministic variables *)
let nondet_vars : string list ref = ref []

(* list of address-represented pointer declaration *)
let aux_local_vardecls : Iast.exp list ref = ref []

(* hashtbl contains all auxiliary procedures, proc_name -> proc_decl *)
let tbl_aux_proc: (string, Iast.proc_decl) Hashtbl.t = Hashtbl.create 1

(* reset all global vars for the next use *)
let reset_global_vars () =
  tbl_pointer_typ # clear;
  tbl_data_decl # clear

(* ---------------------------------------- *)
(* supporting function                      *)
(* ---------------------------------------- *)

let rec loc_of_iast_exp (e: Iast.exp) : VarGen.loc =
  match e with
  | Iast.ArrayAt e -> e.Iast.exp_arrayat_pos
  | Iast.ArrayAlloc e -> e.Iast.exp_aalloc_pos
  | Iast.Assert e -> e.Iast.exp_assert_pos
  | Iast.Assign e -> e.Iast.exp_assign_pos
  | Iast.Binary e -> e.Iast.exp_binary_pos
  | Iast.Bind e -> e.Iast.exp_bind_pos
  | Iast.Block e -> e.Iast.exp_block_pos
  | Iast.BoolLit e -> e.Iast.exp_bool_lit_pos
  | Iast.Break e -> e.Iast.exp_break_pos
  | Iast.Barrier e -> e.Iast.exp_barrier_pos
  | Iast.CallRecv e -> e.Iast.exp_call_recv_pos
  | Iast.CallNRecv e -> e.Iast.exp_call_nrecv_pos
  | Iast.Cast e -> e.Iast.exp_cast_pos
  | Iast.Cond e -> e.Iast.exp_cond_pos
  | Iast.ConstDecl e -> e.Iast.exp_const_decl_pos
  | Iast.Continue e -> e.Iast.exp_continue_pos
  | Iast.Catch e -> e.Iast.exp_catch_pos
  | Iast.Debug e -> e.Iast.exp_debug_pos
  | Iast.Dprint e -> e.Iast.exp_dprint_pos
  | Iast.Empty l -> l
  | Iast.FloatLit e -> e.Iast.exp_float_lit_pos
  | Iast.Finally e -> e.Iast.exp_finally_pos
  | Iast.IntLit e -> e.Iast.exp_int_lit_pos
  | Iast.Java e -> e.Iast.exp_java_pos
  | Iast.Label (_, e1) -> loc_of_iast_exp e1
  | Iast.Member e -> e.Iast.exp_member_pos
  | Iast.New  e -> e.Iast.exp_new_pos
  | Iast.Null l -> l
  | Iast.Raise e -> e.Iast.exp_raise_pos
  | Iast.Return e -> e.Iast.exp_return_pos
  | Iast.Seq e -> e.Iast.exp_seq_pos
  | Iast.This e -> e.Iast.exp_this_pos
  | Iast.Time (_, _, l) -> l
  | Iast.Try e -> e.Iast.exp_try_pos
  | Iast.Unary e -> e.Iast.exp_unary_pos
  | Iast.Unfold e -> e.Iast.exp_unfold_pos
  | Iast.Var e -> e.Iast.exp_var_pos
  | Iast.VarDecl e -> e.Iast.exp_var_decl_pos
  | Iast.While e -> e.Iast.exp_while_pos
  | Iast.Par e -> e.Iast.exp_par_pos

let loc_of_cil_exp (exp: Cil.exp) : Cil.location =
  match exp with
  | Cil.Const (_, l)
  | Cil.Lval (_, l)
  | Cil.SizeOf (_, l)
  | Cil.SizeOfE (_, l)
  | Cil.SizeOfStr (_, l)
  | Cil.AlignOf (_, l)
  | Cil.AlignOfE (_, l)
  | Cil.UnOp (_, _, _, l)
  | Cil.BinOp (_, _, _, _, l)
  | Cil.Question (_, _, _, _, l)
  | Cil.CastE (_, _, l)
  | Cil.AddrOf (_, l)
  | Cil.StartOf (_, l) -> l

(* create an Iast.exp from a list of Iast.exp *)
let merge_iast_exp (es: Iast.exp list) : Iast.exp =
  match es with
  | [] -> (Iast.Empty no_pos)
  | [e] -> e
  | hd::tl ->
    List.fold_left (fun x y ->
        let posx = loc_of_iast_exp x in
        let posy = loc_of_iast_exp y in
        let newpos = {VarGen.start_pos = posx.VarGen.start_pos;
                      VarGen.mid_pos = posy.VarGen.mid_pos;
                      VarGen.end_pos = posy.VarGen.end_pos;} in
        Iast.mkSeq x y newpos
      ) hd tl


(* get type *)
let typ_of_cil_lval (lv: Cil.lval) : Cil.typ =
  Cil.typeOfLval lv

let typ_of_cil_exp (e: Cil.exp) : Cil.typ =
  Cil.typeOf e

(* remove all unnecessary attributes *)
let rec get_core_cil_typ (t: Cil.typ) : Cil.typ = (
  let core_typ = (
    match t with
    | Cil.TVoid _ -> Cil.TVoid []
    | Cil.TInt (Cil.IUChar, _)
    | Cil.TInt (Cil.ISChar, _)
    | Cil.TInt (Cil.IChar, _) -> Cil.TInt(Cil.IChar, [])
    | Cil.TInt (ik, _) -> Cil.TInt (Cil.IInt, [])
    | Cil.TFloat (fk, _) -> Cil.TFloat (Cil.FFloat, [])
    | Cil.TPtr (ty, _) -> Cil.TPtr (get_core_cil_typ ty, [])
    | Cil.TArray (ty, e, _) -> Cil.TArray (get_core_cil_typ ty, e, [])
    | Cil.TFun (ty, ids_opt, b, _) ->
      let new_ty = get_core_cil_typ ty in
      let new_ids_opt = (match ids_opt with
          | Some ids ->
            let new_ids = List.map (fun (id,t,_) ->
                (id, get_core_cil_typ t, [])
              ) ids in
            Some new_ids
          | None -> None
        ) in
      Cil.TFun (new_ty, new_ids_opt, b, [])
    | Cil.TNamed (tinfo, _) -> get_core_cil_typ tinfo.Cil.ttype
    | Cil.TComp (cinfo, _) -> (
        try
          let ty = tbl_typedef # find cinfo.Cil.cname in
          get_core_cil_typ ty
        with _ -> t
      )
    | Cil.TEnum (enum, _) ->
      let new_enum = {enum with Cil.eattr = []} in
      Cil.TEnum (new_enum, [])
    | Cil.TBuiltin_va_list _ -> t
  ) in
  core_typ
)

let get_core_cil_typ (t: Cil.typ) : Cil.typ =
  let pr = string_of_cil_typ in
  Debug.no_1 "get_core_cil_typ" pr pr get_core_cil_typ t

let rec is_cil_struct_pointer (ty: Cil.typ) : bool = (
  match ty with
  | Cil.TPtr (Cil.TComp (comp, _), _) -> true
  | Cil.TPtr (Cil.TNamed (tinfo, _), a) ->
    let _ = Debug.ninfo_hprint (add_str "tinfo" string_of_cil_typ) tinfo.Cil.ttype no_pos in
    let ty = get_core_cil_typ tinfo.Cil.ttype in
    is_cil_struct_pointer (Cil.TPtr (ty, a))
  (* true *)
  | Cil.TPtr (ty, _) ->
    let _ = Debug.ninfo_hprint (add_str "ty" string_of_cil_typ) ty no_pos in
    is_cil_struct_pointer ty
  | _ -> false
)

let is_cil_struct_pointer (ty: Cil.typ) : bool =
  Debug.no_1 "is_cil_struct_pointer" string_of_cil_typ string_of_bool
    is_cil_struct_pointer ty

(* location  functions *)
let makeLocation (startPos: Lexing.position) (endPos: Lexing.position) : VarGen.loc =
  let newloc = {VarGen.start_pos = startPos;
                VarGen.mid_pos = startPos;
                VarGen.end_pos = endPos;} in
  newloc

let startPos (loc: VarGen.loc) : Lexing.position =
  loc.VarGen.start_pos

let endPos (loc: VarGen.loc) : Lexing.position =
  loc.VarGen.end_pos

let is_arith_comparison_op op =
  match op with
  | Cil.Lt
  | Cil.Gt
  | Cil.Le
  | Cil.Ge
  | Cil.Eq
  | Cil.Ne -> true
  | _ -> false

let get_vars_exp (e: Iast.exp): ident list =
  let f e =
    match e with
    | Iast.Var { Iast.exp_var_name = id } -> Some [id]
    | Iast.CallRecv { Iast.exp_call_recv_method = id } -> Some [id]
    | Iast.CallNRecv { Iast.exp_call_nrecv_method = id } -> Some [id]
    | _ -> None
  in Iast.fold_exp e f (List.concat) []


(************************************************************)
(***************** remove goto statements *******************)
(************************************************************)

(* Collect all statement which either is goto statement or has labels                  *)
(* Information about each collected statement includes (statement, index, depth level) *)
let rec collect_goto_label_in_block (blk: Cil.block) (index: int) (depth: int)
  : ((Cil.stmt * int * int) list * (Cil.stmt * int * int) list * int) =
  let stmts = blk.Cil.bstmts in
  let depth = depth + 1 in
  collect_goto_label_in_stmts stmts index depth

and collect_goto_label_in_stmt (stmt: Cil.stmt) (index: int) (depth: int)
  : ((Cil.stmt * int * int) list * (Cil.stmt * int * int) list * int) =
  match stmt.Cil.skind with
  | Cil.Block blk -> collect_goto_label_in_block blk index depth
  | _ -> ([], [], index)

and collect_goto_label_in_stmts (stmts: Cil.stmt list) (index: int) (depth: int)
  : ((Cil.stmt * int * int) list * (Cil.stmt * int * int) list * int) =
  let (gotos, labels, index) = List.fold_left (
      fun (gts, lbls, index) stmt ->
        (* collect label statements *)
        let new_lbls1, index = (match stmt.Cil.labels with
            | [] -> [], index
            | _ ->
              let index = index + 1 in
              let new_lbls = [(stmt, index, depth)] in
              (new_lbls, index)
          ) in
        (* collect goto statements *)
        let new_gts, new_lbls2, index = (match stmt.Cil.skind with
            | Cil.Goto (st, _) ->
              (* because Goto is always placed in an If-statment, *)
              (* the depth of Goto is consider to be equal to the depth of If-statement *)
              let index = index + 1 in
              let goto_depth = depth - 1 in
              let new_gts = [(!st, index, goto_depth)] in
              (new_gts, [], index)
            | Cil.If (_, blk1, blk2, _) ->
              let g1, l1, index = collect_goto_label_in_block blk1 index depth in
              let g2, l2, index = collect_goto_label_in_block blk2 index depth in
              (g1 @ g2, l1 @ l2, index)
            | Cil.Switch (_, blk, stmts, _) ->
              let g1, l1, index = collect_goto_label_in_block blk index depth in
              let g2, l2, index = collect_goto_label_in_stmts stmts index depth in
              (g1 @ g2, l1 @ l2, index)
            | Cil.Loop (blk, _, _, stmt1_opt, stmt2_opt) ->
              let g1, l1, index = collect_goto_label_in_block blk index depth in
              let g2, l2, index = (match stmt1_opt with
                  | Some s -> collect_goto_label_in_stmt s index depth
                  | _ -> [], [], index) in
              let g3, l3, index = (match stmt2_opt with
                  | Some s -> collect_goto_label_in_stmt s index depth
                  | _ -> [], [], index) in
              (g1 @ g2 @ g3, l1 @ l2 @ l3, index)
            | Cil.Block blk ->
              collect_goto_label_in_block blk index depth
            | Cil.TryFinally _
            | Cil.TryExcept _ ->
              let () = print_endline_quiet ("Cilparser: handle TryFinally, TryExcept later") in
              ([], [], index)
            | _ -> ([], [], index)
          ) in
        (gts @ new_gts, lbls @ new_lbls1 @ new_lbls2, index)
    ) ([], [], index) stmts in
  (gotos, labels, index)

let rec collect_goto_label_in_fundec_x (fd: Cil.fundec) =
  let body = fd.Cil.sbody in
  collect_goto_label_in_block body 0 0

and collect_goto_label_in_fundec (fd: Cil.fundec)
  : ((Cil.stmt * int * int) list * (Cil.stmt * int * int) list * int) =
  let pr_in = add_str "fundec: " string_of_cil_fundec in
  let pr_out = (fun (gotos, labels, _) ->
      let pr_stmt (stmt, i, j) = ("[[ (" ^ (string_of_cil_stmt stmt) ^ "), <"
                                  ^ (string_of_int i) ^ ", " ^ (string_of_int j) ^ "> ]]") in
      let gotos_str = add_str "\n  - gotos: " (pr_list pr_stmt) gotos in
      let labels_str = add_str "\n  - labels: " (pr_list pr_stmt) labels in
      gotos_str ^ labels_str
    ) in
  Debug.no_1 "collect_goto_label_in_fundec" pr_in pr_out
    (fun _ -> collect_goto_label_in_fundec_x fd) fd

(* Normalizing all goto-statements:                          *)
(* all goto-statement must be conditioned by an If-statment  *)
(* an unconditional goto is converted into "If (true) goto"  *)
let rec normalize_goto_stmt (stmt: Cil.stmt) : Cil.stmt =
  let skind = stmt.Cil.skind in
  let new_skind = (match skind with
      | Cil.Instr _ -> skind
      | Cil.Return _ -> skind
      | Cil.Goto (_, p) -> (* translate unconditional Goto to If (true) Goto *)
        let true_exp = Cil.Const (Cil.CInt64 (Int64.one, Cil.IInt, None), p) in
        let goto_blk = Cil.mkBlock [stmt] in
        let empty_blk = Cil.mkBlock [] in
        Cil.If (true_exp, goto_blk, empty_blk, p)
      | Cil.Break _ -> skind
      | Cil.Continue _ -> skind
      | Cil.If (exp, blk1, blk2, p) ->
        let new_blk1 = (match blk1.Cil.bstmts with
            | [st] -> (match st.Cil.skind with
                | Cil.Goto _ -> blk1
                | _ -> normalize_goto_block blk1
              )
            | _ -> normalize_goto_block blk1
          ) in
        let new_blk2 = (match blk2.Cil.bstmts with
            | [st] -> (match st.Cil.skind with
                | Cil.Goto _ -> blk2
                | _ -> normalize_goto_block blk2
              )
            | _ -> normalize_goto_block blk2
          ) in
        Cil.If (exp, new_blk1, new_blk2, p)
      | Cil.Switch (exp, blk, stmts, p) ->
        let new_blk = normalize_goto_block blk in
        let new_stmts = List.map normalize_goto_stmt stmts in
        Cil.Switch (exp, new_blk, new_stmts, p)
      | Cil.Loop (blk, sf, p, stmt1, stmt2) ->
        let new_blk = normalize_goto_block blk in
        let new_stmt1 = map_opt normalize_goto_stmt stmt1 in
        let new_stmt2 = map_opt normalize_goto_stmt stmt2 in
        Cil.Loop (new_blk, sf, p, new_stmt1, new_stmt2)
      | Cil.Block blk ->
        Cil.Block (normalize_goto_block blk)
      | Cil.TryFinally (blk1, blk2, p) ->
        let new_blk1 = normalize_goto_block blk1 in
        let new_blk2 = normalize_goto_block blk2 in
        Cil.TryFinally (new_blk1, new_blk2, p)
      | Cil.TryExcept (blk1, ies, blk2, p) ->
        let new_blk1 = normalize_goto_block blk1 in
        let new_blk2 = normalize_goto_block blk2 in
        Cil.TryExcept (new_blk1, ies, new_blk2, p)
      | Cil.HipStmt _ -> skind
    ) in
  {stmt with Cil.skind = new_skind}

and normalize_goto_block (blk: Cil.block) : Cil.block =
  let new_stmts = List.map normalize_goto_stmt blk.Cil.bstmts in
  {blk with Cil.bstmts = new_stmts}

let rec normalize_goto_fundec_x (fd: Cil.fundec) : Cil.fundec =
  let new_body = normalize_goto_block fd.Cil.sbody in
  {fd with Cil.sbody = new_body}

and normalize_goto_fundec (fd: Cil.fundec) : Cil.fundec =
  let pr_in = string_of_cil_fundec in
  let pr_out = string_of_cil_fundec in
  Debug.no_1 "normalize_goto_fundec" pr_in pr_out
    (fun _ -> normalize_goto_fundec_x fd) fd

let match_stmt stmt1 stmt2 =
  let s1 = string_of_cil_stmt stmt1 in
  let s2 = string_of_cil_stmt stmt2 in
  if (String.compare s1 s2 == 0) then true else false

let match_label lbl1 lbl2 =
  let s1 = string_of_cil_label lbl1 in
  let s2 = string_of_cil_label lbl2 in
  if (String.compare s1 s2 == 0) then true else false

let rec remove_goto_with_if_stmts goto label stmts =
  let rec get_stmts stmts = match stmts with
    | [] -> report_error no_pos "remove goto with if stmts: not find matched label!"
    | stmt::stmts ->
      if (List.exists (fun stmt_lbl ->
          match_label label stmt_lbl
        ) stmt.Cil.labels)
      then ([],stmt::stmts)
      else
        let (stmts1, stmts2) = get_stmts stmts in
        (stmt::stmts1, stmts2)
  in
  match stmts with
  | [] -> []
  | stmt::stmts ->
    let skind = stmt.Cil.skind in
    let (new_skind, new_stmts) = match skind with
      | Cil.If (e, b1, b2, p) ->
        let fst_stmt = List.hd b1.Cil.bstmts in
        let fst_skind = fst_stmt.Cil.skind in
        ( match fst_skind with
          | Cil.Goto (goto_stmt, _) ->
            if (match_stmt goto !goto_stmt)
            then
              let false_exp = Cil.Const (Cil.CInt64 (Int64.zero, Cil.IInt, None), p) in
              let (stmts1, stmts2) = get_stmts stmts in
              let new_b1 = Cil.mkBlock stmts1 in
              (Cil.If (false_exp, new_b1, b2, p), stmts2)
            else
              (skind, stmts)
          | _ -> (Cil.If (e, remove_goto_with_if_block goto label b1, remove_goto_with_if_block goto label b2, p), stmts) )
      | Cil.Switch (exp, blk, stmts1, p) -> (Cil.Switch (exp, remove_goto_with_if_block goto label blk, stmts1, p), stmts)
      | Cil.Block blk -> (Cil.Block (remove_goto_with_if_block goto label blk), stmts)
      | Cil.Loop (blk, sf, p, stmt1, stmt2) -> (Cil.Loop (remove_goto_with_if_block goto label blk, sf, p, stmt1, stmt2), stmts)
      | Cil.TryFinally (blk1, blk2, p) -> (Cil.TryFinally (remove_goto_with_if_block goto label blk1, remove_goto_with_if_block goto label blk2, p), stmts)
      | Cil.TryExcept (blk1, ies, blk2, p) -> (Cil.TryExcept (remove_goto_with_if_block goto label blk1, ies, remove_goto_with_if_block goto label blk2, p), stmts)
      | _ -> (skind, stmts)
    in
    {stmt with Cil.skind = new_skind}::(remove_goto_with_if_stmts goto label new_stmts)

and remove_goto_with_if_block goto label blk =
  let new_stmts = remove_goto_with_if_stmts goto label blk.Cil.bstmts in
  {blk with Cil.bstmts = new_stmts}

let remove_goto_with_if_fundec goto label fd =
  let new_body = remove_goto_with_if_block goto label fd.Cil.sbody in
  {fd with Cil.sbody = new_body}

let rec remove_goto_with_while_stmts goto label stmts =
  let rec get_stmts stmts = match stmts with
    | [] -> report_error no_pos "remove goto with while stmts: not find matched goto!"
    | stmt::stmts ->
      let skind = stmt.Cil.skind in
      match skind with
      | Cil.If (_, b1, _, _) ->
        let fst_stmt = List.hd b1.Cil.bstmts in
        let fst_skind = fst_stmt.Cil.skind in
        ( match fst_skind with
          | Cil.Goto (goto_stmt, _) ->
            if (match_stmt goto !goto_stmt)
            then ([],stmts)
            else
              let (stmts1, stmts2) = get_stmts stmts in
              (stmt::stmts1, stmts2)
          | _ ->
            let (stmts1, stmts2) = get_stmts stmts in
            (stmt::stmts1, stmts2) )
      | _ ->
        let (stmts1, stmts2) = get_stmts stmts in
        (stmt::stmts1, stmts2)
  in
  match stmts with
  | [] -> []
  | stmt::stmts ->
    if (List.exists (fun stmt_lbl ->
        match_label label stmt_lbl
      ) stmt.Cil.labels)
    then
      let (stmts1, stmts2) = get_stmts (stmt::stmts) in
      let true_exp = Cil.Const (Cil.CInt64 (Int64.one, Cil.IInt, None), Cil.get_stmtLoc stmt.Cil.skind) in
      stmts1@(Cil.mkWhile true_exp stmts1 (Iformula.mkETrueF ()))@(remove_goto_with_while_stmts goto label stmts2)
    else
      let skind = stmt.Cil.skind in
      let new_skind = match skind with
        | Cil.If (e, b1, b2, p) -> Cil.If (e, remove_goto_with_if_block goto label b1, remove_goto_with_if_block goto label b2, p)
        | Cil.Switch (exp, blk, stmts1, p) -> Cil.Switch (exp, remove_goto_with_if_block goto label blk, stmts1, p)
        | Cil.Block blk -> Cil.Block (remove_goto_with_if_block goto label blk)
        | Cil.Loop (blk, sf, p, stmt1, stmt2) -> Cil.Loop (remove_goto_with_if_block goto label blk, sf, p, stmt1, stmt2)
        | Cil.TryFinally (blk1, blk2, p) -> Cil.TryFinally (remove_goto_with_if_block goto label blk1, remove_goto_with_if_block goto label blk2, p)
        | Cil.TryExcept (blk1, ies, blk2, p) -> Cil.TryExcept (remove_goto_with_if_block goto label blk1, ies, remove_goto_with_if_block goto label blk2, p)
        | _ -> skind
      in
      {stmt with Cil.skind = new_skind}::(remove_goto_with_while_stmts goto label stmts)

and remove_goto_with_while_block goto label blk =
  let new_stmts = remove_goto_with_while_stmts goto label blk.Cil.bstmts in
  {blk with Cil.bstmts = new_stmts}

let remove_goto_with_while_fundec goto label fd =
  let new_body = remove_goto_with_while_block goto label fd.Cil.sbody in
  {fd with Cil.sbody = new_body}

let remove_goto (fd: Cil.fundec) : Cil.fundec =
  let rec find_matched_label goto labels =
    match labels with
    | [] -> report_error no_pos "remove goto: not find matched label!"
    | (label,i,j)::labels ->
      if (match_stmt goto label)
      then (label,i,j)
      else find_matched_label goto labels
  in
  let fd = normalize_goto_fundec fd in
  let (gotos, labels, _) = collect_goto_label_in_fundec fd in
  let new_fd = List.fold_left (fun fd (goto, gi, gj) ->
      let (matched_label,li,lj) = find_matched_label goto labels in
      if (gj != lj)
      then report_error no_pos "remove goto: goto and label are not the same level!"
      else
        let label = List.hd goto.Cil.labels in
        if (gi < li)
        then remove_goto_with_if_fundec goto label fd
        else remove_goto_with_while_fundec goto label fd
    ) fd gotos in
  new_fd

(**********************************************)
(****** create intermediate procedures  *******)
(**********************************************)

let create_void_pointer_casting_proc (typ_name: string) : Iast.proc_decl =
  let proc_name = "__cast_void_pointer_to_" ^ typ_name ^ "__" in
  let proc_decl = (
    try
      Hashtbl.find tbl_aux_proc proc_name
    with Not_found -> (
        let data_name, base_data = (
          let re = Str.regexp "\\(_star\\)" in
          try
            let (todo_unk:int) = Str.search_forward re typ_name 0 in
            let dname = Str.global_replace re "^" typ_name in
            let bdata = Str.global_replace re "" typ_name in
            (dname, bdata)
          with Not_found -> (typ_name, typ_name)
        ) in
        let param = (
          match base_data with
          | "int"   -> "<_>"
          | "bool"  -> "<_>"
          | "float" -> "<_>"
          | "void"  -> "<_>"
          | "char"  -> "<_,q>"
          | _ -> (
              try
                let data_decl = tbl_data_decl # find ~loc:x_loc (Globals.Named base_data) in
                match data_decl.Iast.data_fields with
                | []   -> report_error no_pos "create_void_pointer_casting_proc: Invalid data_decl fields"
                | [hd] -> "<_>"
                | hd::tl ->
                  "<" ^ (List.fold_left (fun s _ -> s ^ ", _") "_" tl) ^ ">"
              with Not_found -> report_error no_pos ("create_void_pointer_casting_proc: Unknown data type: " ^ base_data)
            )
        ) in
        let cast_proc = (
          match base_data with
          | "char" -> typ_name ^ " " ^ proc_name ^ " (void_star p)\n" ^
                      "  case { \n" ^
                      "    p =  null -> ensures res = null; \n" ^
                      "    p != null -> requires p::memLoc<h,s> & h\n" ^
                      "                 ensures res::WFSegN<q,s>; \n" ^
                      "  }\n"
          | _ -> typ_name ^ " " ^ proc_name ^ " (void_star p)\n" ^
                 "  case { \n" ^
                 "    p =  null -> ensures res = null; \n" ^
                 "    p != null -> requires p::memLoc<h,s> & h\n" ^
                 "                 ensures res::" ^ data_name ^ param ^ " * res::memLoc<h,s> & h; \n" ^
                 (* "                 ensures res::" ^ data_name ^ param ^ (* " & o>=0; \n" *) "; \n" ^ *)
                 "  }\n"
          (* | _ -> typ_name ^ " " ^ proc_name ^ " (void_star p)\n" ^
           *   "  case { \n" ^
           *   "    p =  null -> ensures res = null; \n" ^
           *   "    p != null -> requires p::void_star<_> \n" ^
           *   "                 ensures res::" ^ typ_name ^ "<_> & res=p;\n" ^
           *   "  }\n" *)
        ) in
        let _ = Debug.ninfo_zprint (lazy ((" cast_proc:\n  " ^ cast_proc))) no_pos in
        let pd = Parser.parse_c_aux_proc "void_pointer_casting_proc" cast_proc in
        if Hashtbl.mem tbl_aux_proc proc_name then ()
        else Hashtbl.add tbl_aux_proc proc_name pd;
        pd
      )
  ) in
  (* return *)
  proc_decl


let create_void_pointer_casting_proc (typ_name: string)
  : Iast.proc_decl =
  Debug.no_1 "create_void_pointer_casting_proc" pr_id Iprinter.string_of_proc_decl create_void_pointer_casting_proc typ_name

(* check if a type is pointer type *)
let is_pointer_typ_name (typ_name: string) : bool =
  let len = String.length typ_name in
  if (len <= 5) then false
  else
    let suffix = String.sub typ_name (len - 5) 5 in
    (* let () = print_endline ("suffix = " ^ suffix) in *)
    eq_str suffix "_star"


let create_pointer_casting_proc (in_typ_name: string) (out_typ_name: string)
  : Iast.proc_decl =
  let proc_name = "__cast_" ^ in_typ_name ^ "_to_" ^ out_typ_name ^ "__" in
  let proc_decl = (
    try Hashtbl.find tbl_aux_proc proc_name
    with Not_found -> (
        (* node is a pointer type? *)
        if (is_pointer_typ_name in_typ_name) && (is_pointer_typ_name out_typ_name) then(
          let cast_proc = (
            out_typ_name ^ " " ^ proc_name ^ " (" ^ in_typ_name ^ " p)\n" ^
            "  case { \n" ^
            "    p =  null -> ensures res = null; \n" ^
            "    p != null -> requires p::" ^ in_typ_name ^ "<_,o> & o>=0\n" ^
            (* "                 ensures res::" ^ data_name ^ param ^ " * res::memLoc<h,s> & h; \n" ^ *)
            "                 ensures res::" ^ out_typ_name ^ "<_,o> & o>=0;\n" ^
            "  }\n"
          ) in
          (* overwrites the above version which contains the extra 0 argument *)
          (* TODO: we need to check how many paramenters the actual data type has
             and create the specs accordingly. Currently the heap is hardcoded to
             one anonymous parameter. *)
          (* let cast_proc = (
           *   out_typ_name ^ " " ^ proc_name ^ " (" ^ in_typ_name ^ " p)\n" ^
           *   "  case { \n" ^
           *   "    p =  null -> ensures res = null; \n" ^
           *   "    p != null -> requires p::" ^ in_typ_name ^ "<_> \n" ^
           *   "                 ensures res::" ^ out_typ_name ^ "<_> & res=p;\n" ^
           *   "  }\n"
           * ) in *)
          let proc_decl = Parser.parse_c_aux_proc "void_pointer_casting_proc" cast_proc in
          Hashtbl.add tbl_aux_proc proc_name proc_decl;
          proc_decl
        )
        else
          let msg = "create_pointer_casting_proc: expect pointer types but found: "
                    ^ in_typ_name ^ " & " ^ out_typ_name in
          report_error no_pos msg
      )
  ) in
  (* return *)
  proc_decl

let create_pointer_casting_proc (in_typ_name: string) (out_typ_name: string)
  : Iast.proc_decl =
  Debug.no_2 "create_pointer_casting_proc" pr_id pr_id Iprinter.string_of_proc_decl create_pointer_casting_proc in_typ_name out_typ_name

let rec create_pointer_to_int_casting_proc (pointer_typ_name: string) : Iast.proc_decl =
  let proc_name = "__cast_" ^ pointer_typ_name ^ "_to_int__" in
  let proc_decl = (
    try
      Hashtbl.find tbl_aux_proc proc_name
    with Not_found -> (
        let pointer = "p::" ^ pointer_typ_name ^ "<val, addr>" in
        let cast_proc = (
          "int " ^ proc_name ^ " (" ^ pointer_typ_name ^ " p)\n" ^
          "  case { \n" ^
          "    p =  null -> ensures res = 0; \n" ^
          "    p != null -> requires " ^ pointer ^ " ensures " ^ pointer ^ " & res = addr & res != 0; \n" ^
          "  }\n"
        ) in
        let pd = Parser.parse_c_aux_proc "pointer_to_int_casting_proc" cast_proc in
        Hashtbl.add tbl_aux_proc proc_name pd;
        pd
      )
  ) in
  (* return *)
  proc_decl

and create_int_to_pointer_casting_proc (pointer_typ_name: string) : Iast.proc_decl =
  let proc_name = "__cast_int_to_" ^ pointer_typ_name ^ "__" in
  let proc_decl = (
    try
      Hashtbl.find tbl_aux_proc proc_name
    with Not_found -> (
        let cast_proc = (
          match pointer_typ_name with
          | "char_star" -> pointer_typ_name ^ " " ^ proc_name ^ " (int p)\n" ^
                           "  case { \n" ^
                           "    p =  0 -> ensures res::char_star<0,_>; \n" ^
                           "    p != 0 -> ensures res::char_star<p,_> & p!=0; \n" ^
                           "  }\n"
          | _ -> pointer_typ_name ^ " " ^ proc_name ^ " (int p)\n" ^
                 "  case { \n" ^
                 "    p =  0 -> ensures res =  null; \n" ^
                 "    p != 0 -> ensures res != null; \n" ^
                 "  }\n"
        ) in
        let pd = Parser.parse_c_aux_proc "int_to_pointer_casting_proc" cast_proc in
        Hashtbl.add tbl_aux_proc proc_name pd;
        pd
      )
  ) in
  (* return *)
  proc_decl

and create_logical_not_proc (typ: Globals.typ) : Iast.proc_decl =
  let typ_name = Globals.string_of_typ typ in
  let proc_name = "__make_not_of_" ^ typ_name ^ "__" in
  try
    Hashtbl.find tbl_aux_proc proc_name
  with Not_found -> (
      let proc = (
        match typ with
        | Globals.Named typ_name -> (
            typ_name ^ " " ^ proc_name ^ "(" ^ typ_name ^ " param)\n" ^
            "  case { param =  null -> ensures res != null;\n" ^
            "         param != null -> ensures res = null; }\n"
          )
        | Globals.Int -> (
            "int " ^ proc_name ^ "(int param)\n" ^
            "  case { param =  0 -> ensures res != 0;\n" ^
            "         param != 0 -> ensures res = 0; }\n"
          )
        | Globals.Float -> (
            "float " ^ proc_name ^ "(float param)\n" ^
            "  case { param =  0. -> ensures res != 0.;\n" ^
            "         param != 0. -> ensures res = 0.; }\n"
          )
        | _ -> report_error no_pos "create_logical_not_proc: Invalid type"
      ) in
      let proc_decl = Parser.parse_c_aux_proc "inter_logical_not_proc" proc in
      Hashtbl.add tbl_aux_proc proc_name proc_decl;
      proc_decl
    )


and create_bool_casting_proc (typ: Globals.typ) : Iast.proc_decl =
  let typ_name = Globals.string_of_typ typ in
  let proc_name = "__bool_of_" ^ typ_name ^ "___" in
  try
    Hashtbl.find tbl_aux_proc proc_name
  with Not_found -> (
      let proc = (
        match typ with
        | Globals.Named typ_name -> (
            "bool " ^ proc_name ^ "(" ^ typ_name ^ " param)\n" ^
            "  case { param =  null -> ensures !res;\n" ^
            "         param != null -> ensures res; }\n"
          )
        | Globals.Int -> (
            "bool " ^ proc_name ^ "(int param)\n" ^
            "  case { param != 0 -> ensures res;\n" ^
            "         param = 0  -> ensures !res; }\n"
          )
        | Globals.Float -> (
            "bool " ^ proc_name ^ "(float param)\n" ^
            "  case { param != 0. -> ensures res;\n" ^
            "         param = 0.  -> ensures !res; }\n"
          )
        | _ -> report_error no_pos ("create_bool_casting_proc: Invalid type" ^ (Globals.string_of_typ typ))
      ) in
      let proc_decl = Parser.parse_c_aux_proc "inter_bool_casting_proc" proc in
      Hashtbl.add tbl_aux_proc proc_name proc_decl;
      proc_decl
    )

and create_string_proc (t1: Cil.typ) (t2: Cil.typ) =
  let coretyp1 = get_core_cil_typ t1 in   (* translate all char types into one *)
  let coretyp2 = get_core_cil_typ t2 in
  let typ1 = translate_typ coretyp1 no_pos in
  let typ2 = translate_typ coretyp2 no_pos in
  let typ1_name = string_of_typ typ1 in
  let typ2_name = string_of_typ typ2 in
  let proc_name = (
    match coretyp1, coretyp2 with
      | Cil.TPtr(Cil.TInt(Cil.IChar,_),_), Cil.TInt(Cil.IChar,_)
      | Cil.TInt(Cil.IChar,_), Cil.TPtr(Cil.TInt(Cil.IChar,_),_) -> "__write_char"
      | Cil.TPtr(Cil.TInt(Cil.IChar,_),_), Cil.TPtr(Cil.TInt(Cil.IChar,_),_) -> "__get_char"
      | Cil.TPtr(Cil.TInt(Cil.IChar,_),_), _
      | _, Cil.TPtr(Cil.TInt(Cil.IChar,_),_) -> "__plus_plus_char"
      | _ ->
        let msg = "Invalid string operator: " ^ (add_str "t1" Cil.string_of_typ) t1 ^ (add_str "t2" Cil.string_of_typ) t2 in
        report_error no_pos msg
    )
  in
  try
    Hashtbl.find tbl_aux_proc proc_name
  with Not_found -> (
      Debug.ninfo_hprint (add_str "proc_name" pr_id) proc_name no_pos;
      Debug.ninfo_hprint (add_str "t1" Cil.string_of_typ) t1 no_pos;
      Debug.ninfo_hprint (add_str "t2" Cil.string_of_typ) t2 no_pos;
      let proc_str = (
        match coretyp1, coretyp2 with
        | Cil.TPtr(Cil.TInt(Cil.IChar,_),_), Cil.TPtr(Cil.TInt(Cil.IChar,_),_) ->
             typ1_name ^ " " ^ proc_name ^ " (" ^ typ1_name ^ " x)\n"
           ^ "requires x::char_star<v,_>@L & Term[] \n"
           ^ "ensures res=v ;\n"
        | Cil.TInt(Cil.IChar,_), Cil.TPtr(Cil.TInt(Cil.IChar,_),_) ->
             typ2_name ^ " " ^ proc_name ^ " (" ^ typ1_name ^ " x, " ^ typ2_name ^ " v)\n"
           ^ "requires x::char_star<_,q>@L & Term[] \n"
           ^ "ensures x::char_star<v,q> ;\n"
        | _, Cil.TPtr(Cil.TInt(Cil.IChar,_),_) ->
             typ2_name ^ " " ^ proc_name ^ "(" ^ typ2_name ^ " x)\n"
           ^ "requires x::char_star<_,q>@L & Term[] \n"
           ^ "ensures res=q ;\n"
        | Cil.TPtr(Cil.TInt(Cil.IChar,_),_), Cil.TInt(Cil.IChar,_) ->
             typ1_name ^ " " ^ proc_name ^ " (" ^ typ1_name ^ " x, " ^ typ2_name ^ " v)\n"
           ^ "requires x::char_star<_,q>@L & Term[] \n"
           ^ "ensures x::char_star<v,q> ;\n"
        | Cil.TPtr(Cil.TInt(Cil.IChar,_),_), _ ->
             typ1_name ^ " " ^ proc_name ^ "(" ^ typ1_name ^ " x)\n"
           ^ "requires x::char_star<_,q>@L & Term[] \n"
           ^ "ensures res=q ;\n"
        | _ ->
          let msg = "Incompatible pointers when translating pointer arithmetic: "
                    ^ typ1_name ^ " vs " ^ typ2_name in
          report_error no_pos msg
      ) in
      Debug.ninfo_hprint (add_str "pointer_arith_proc_str" pr_id) proc_str no_pos;
      let proc_decl = Parser.parse_c_aux_proc "pointer_arithmetic_proc" proc_str in
      let _ = Debug.ninfo_hprint (add_str "proc_decl" pr_id) proc_decl.Iast.proc_name no_pos in
      Hashtbl.add tbl_aux_proc proc_name proc_decl;
      proc_decl
    )



and create_pointer_arithmetic_proc (op: Cil.binop) (t1: Cil.typ) (t2: Cil.typ) =
  let typ1 = translate_typ t1 no_pos in
  let typ2 = translate_typ t2 no_pos in
  let (op_name, op_str) = (match op with
      | Cil.MinusPI | Cil.MinusPP -> ("minus", "-")
      | Cil.PlusPI | Cil.IndexPI -> (
	match t1, t2 with
(*          | Cil.TPtr(Cil.TInt(Cil.IChar,_),_), _ -> ("plus", "+")*)
(*          | _, Cil.TPtr(Cil.TInt(Cil.IChar,_),_) -> ("plus", "+")*)
          | _, _ -> ("add", "+")
      )
      | Cil.Lt -> ("lt", "<")
      | Cil.Le -> ("le", "<=")
      | Cil.Gt -> ("gt", ">")
      | Cil.Ge -> ("ge", ">=")
      | Cil.Eq -> ("eq", "==")
      | Cil.Ne -> ("ne", "!=")
      | _ ->
        let msg = "Invalid pointer arithmetic operator: " ^ (string_of_cil_binop op) in
        report_error no_pos msg
    ) in
  let typ1_name = string_of_typ typ1 in
  let typ2_name = string_of_typ typ2 in
  let proc_name = (
    match t1, t2 with
(*      | Cil.TPtr(Cil.TInt(Cil.IChar,_),_), Cil.TInt(Cil.IChar,_)*)
(*      | Cil.TInt(Cil.IChar,_), Cil.TPtr(Cil.TInt(Cil.IChar,_),_) -> "__write_char"*)
(*      | Cil.TPtr(Cil.TInt(Cil.IChar,_),_), _*)
(*      | _, Cil.TPtr(Cil.TInt(Cil.IChar,_),_) -> "__plus_" ^ op_name ^ "_char"*)
      | _, _ -> "__pointer_" ^ op_name ^ "__" ^ typ1_name ^ "__" ^ typ2_name ^ "__"
    )
  in
  try
    Hashtbl.find tbl_aux_proc proc_name
  with Not_found -> (
      x_ninfo_hp (add_str "proc_name" pr_id) proc_name no_pos;
      x_ninfo_hp (add_str "op_name" pr_id) op_name no_pos;
      x_ninfo_hp (add_str "op_str" pr_id) op_str no_pos;
      x_ninfo_hp (add_str "t1" Cil.string_of_typ) t1 no_pos;
      x_ninfo_hp (add_str "t2" Cil.string_of_typ) t2 no_pos;
      let proc_str = (
        match t1, t2 with
(*        | Cil.TInt(Cil.IChar,_), Cil.TPtr(Cil.TInt(Cil.IChar,_),_) -> *)
(*             typ2_name ^ " " ^ proc_name ^ " (" ^ typ1_name ^ " x, " ^ typ2_name ^ " v)\n"*)
(*           ^ "requires x::char_star<_,_>@L & Term[] \n"*)
(*           ^ "ensures x::char_star<v,_> ;\n"*)
(*        | _, Cil.TPtr(Cil.TInt(Cil.IChar,_),_) ->*)
(*             typ2_name ^ " " ^ proc_name ^ "(" ^ typ2_name ^ " x)\n"*)
(*           ^ "requires x::char_star<_,q>@L & Term[] \n"*)
(*           ^ "ensures res=q ;\n"*)
        | Cil.TInt _, Cil.TPtr _ ->
            typ2_name ^ " " ^ proc_name ^ " (" ^ typ1_name ^ " i, " ^ typ2_name ^ " p)\n"
            ^ "  requires p::" ^ typ2_name ^ "<val>\n"
            ^ "  ensures p::" ^ typ2_name ^ "<val>"
            (* ^ " * res::" ^ typ2_name ^ "<val " ^ op_str ^ " i>;\n" *)
            ^ " & res = p " ^ op_str ^ " i;\n"
(*        | Cil.TPtr(Cil.TInt(Cil.IChar,_),_), Cil.TInt(Cil.IChar,_) -> *)
(*             typ1_name ^ " " ^ proc_name ^ " (" ^ typ1_name ^ " x, " ^ typ2_name ^ " v)\n"*)
(*           ^ "requires x::char_star<_,_>@L & Term[] \n"*)
(*           ^ "ensures x::char_star<v,_> ;\n"*)
(*        | Cil.TPtr(Cil.TInt(Cil.IChar,_),_), _ ->*)
(*             typ1_name ^ " " ^ proc_name ^ "(" ^ typ1_name ^ " x)\n"*)
(*           ^ "requires x::char_star<_,q>@L & Term[] \n"*)
(*           ^ "ensures res=q ;\n"*)
        | Cil.TPtr _, Cil.TInt _ ->
            typ1_name ^ " " ^ proc_name ^ "(" ^ typ1_name ^ " p, " ^ typ2_name ^ " i)\n"
            ^ "  requires p::" ^ typ1_name^ "<val>\n"
            ^ "  ensures p::" ^ typ1_name^ "<val>"
            (* ^ " * res::" ^ typ1_name^ "<val " ^ op_str ^ " i>;\n" *)
            ^ " & res = p " ^ op_str ^ " i;\n"
        | Cil.TPtr _, Cil.TPtr _ when (cmp_typ typ1 typ2) ->
          let tn = typ1_name in
          tn ^ " " ^ proc_name ^ "(" ^ tn ^ " p, " ^ tn ^ " q)\n"
          ^ "  requires p::" ^ tn ^ "<val1, offset1> * q::" ^ tn ^ "<val2, offset2>\n"
          ^ "  ensures p::" ^ tn^ "<val1, offset1> * q::" ^ tn^ "<val2, offset2>\n"
          ^ " * res::" ^ tn^ "<_, offset1 " ^ op_str ^ " offset2>;\n"
        | _ ->
          let msg = "Incompatible pointers when translating pointer arithmetic: "
                    ^ typ1_name ^ " vs " ^ typ2_name in
          report_error no_pos msg
      ) in
      Debug.ninfo_hprint (add_str "pointer_arith_proc_str" pr_id) proc_str no_pos;
      let proc_decl = Parser.parse_c_aux_proc "pointer_arithmetic_proc" proc_str in
      let _ = Debug.ninfo_hprint (add_str "proc_decl" pr_id) proc_decl.Iast.proc_name no_pos in
      Hashtbl.add tbl_aux_proc proc_name proc_decl;
      proc_decl
    )



(************************************************************)
(****** collect information about address-of operator *******)
(************************************************************)

and gather_addrof_fundec (fd: Cil.fundec) : unit =
  Debug.no_1 "gather_addrof_fundec"  string_of_cil_fundec (fun _ -> tbl_addrof_info # to_string )  gather_addrof_fundec_x fd

and gather_addrof_fundec_x (fd: Cil.fundec) : unit =
  (* reset some local setting *)
  tbl_addrof_info # clear;
  (* start gathering addrof_info in each function *)
  let blk = fd.Cil.sbody in
  gather_addrof_block blk

and gather_addrof_block (blk: Cil.block) : unit =
  let stmts = blk.Cil.bstmts in
  List.iter gather_addrof_stmt stmts

and gather_addrof_stmt (stmt: Cil.stmt) : unit =
  match stmt.Cil.skind with
  | Cil.Instr is -> List.iter gather_addrof_instr is
  | Cil.Return (eopt, _) -> (
      match eopt with
      | None -> ()
      | Some e -> gather_addrof_exp e
    )
  | Cil.Goto (sref, l) -> ()
  | Cil.Break _ -> ()
  | Cil.Continue _ -> ()
  | Cil.If (e, b1, b2, _) ->
    let () = gather_addrof_exp e in
    let () = gather_addrof_block b1 in
    let () = gather_addrof_block b2 in
    ()
  | Cil.Switch (_, _, _, l) -> ()
  | Cil.Loop (blk, _, _, stmt_opt1, stmt_opt2) -> (
      let () = gather_addrof_block blk in
      let () = (match stmt_opt1 with
          | None -> ()
          | Some s -> gather_addrof_stmt s
        ) in
      let () = (match stmt_opt2 with
          | None -> ()
          | Some s -> gather_addrof_stmt s
        ) in ()
    )
  | Cil.Block blk -> gather_addrof_block blk
  | Cil.TryFinally (b1, b2, _) ->
    let () = gather_addrof_block b1 in
    let () = gather_addrof_block b2 in
    ()
  | Cil.TryExcept (b1, (is, e), b2, _) ->
    let () = gather_addrof_block b1 in
    let () = List.iter gather_addrof_instr is in
    let () = gather_addrof_exp e in
    let () = gather_addrof_block b2 in
    ()
  | Cil.HipStmt (iast_exp, l) -> ()

and gather_addrof_instr (i: Cil.instr) : unit =
  match i with
  | Cil.Set (_, e, _) -> gather_addrof_exp e
  | Cil.Call (_, e, es, _) ->
    let () = gather_addrof_exp e in
    let () = List.iter gather_addrof_exp es in
    ()
  | Cil.Asm _ -> ()

and gather_addrof_exp (e: Cil.exp) : unit =
  match e with
  | Cil.Const _ -> ()
  | Cil.Lval (lv, _) -> ()
  | Cil.SizeOf _ -> ()
  | Cil.SizeOfE _ -> ()
  | Cil.SizeOfStr _ -> ()
  | Cil.AlignOf _ -> ()
  | Cil.AlignOfE _ -> ()
  | Cil.UnOp (_, e1, _, _) -> gather_addrof_exp e1
  | Cil.BinOp (_, e1, e2, _, _) -> (
      let () = gather_addrof_exp e1 in
      let () = gather_addrof_exp e2 in
      ()
    )
  | Cil.Question (e1, e2, e3, _, _) -> (
      let () = gather_addrof_exp e1 in
      let () = gather_addrof_exp e2 in
      let () = gather_addrof_exp e3 in
      ()
    )
  | Cil.CastE (_, e, _) -> gather_addrof_exp e
  | Cil.AddrOf (lv, l) -> (
      let pos = translate_location l in
      let lv_str = string_of_cil_lval lv in
      let lv_ty = typ_of_cil_lval lv in
      match lv_ty with
      (* | Cil.TComp _ -> () *)
      | _ -> (
          try
            let todo_unk = tbl_addrof_info # find ~loc:x_loc lv_str in ()
          with Not_found ->
          (* let () = y_binfo_pp "XX1\n" in *)
          begin match lv_ty with
            | Cil.TPtr (refined_ty, _) when (is_cil_struct_pointer lv_ty) ->
                let addr_var_name = str_addr ^ lv_str in
                  begin try
                  let addr_data_typ = tbl_pointer_typ # find ~loc:x_loc refined_ty in
                  let addr_data_decl = tbl_data_decl # find ~loc:x_loc addr_data_typ in
                  let addr_data_name =
                    begin match addr_data_typ with
                    | Globals.Named s -> s
                    | _ -> report_error pos "gather_addrof_exp: unexpected type!"
                    end in
                  let addr_var_decl =
                    let init_params = [(translate_lval lv)] in
                    let init_data = Iast.mkNew addr_data_name [] pos in
                    Iast.mkVarDecl addr_data_typ [(addr_var_name, Some init_data, pos)] pos
                    in
                  aux_local_vardecls := !aux_local_vardecls @ [addr_var_decl];
                  tbl_addrof_info # add ~loc:x_loc lv_str addr_var_name;
              with Not_found ->
                tbl_addrof_info # add ~loc:x_loc lv_str lv_str;
                  (* Muoi: Address of a struct is itself *)
              end
            | Cil.TVoid attr
            | Cil.TFloat (_, attr)
            | Cil.TPtr (_, attr)
            | Cil.TArray (_, _,attr)
            | Cil.TFun (_, _, _, attr)
            | Cil.TNamed (_, attr)
            | Cil.TComp (_, attr)
            | Cil.TEnum (_, attr)
            | Cil.TBuiltin_va_list attr
            | Cil.TInt (_, attr) -> (* Not struct pointer *)
                let addr_var_name = str_addr ^ lv_str in
                begin try
                  let addr_data_typ = translate_typ (Cil.TPtr (lv_ty, attr)) pos in
                  let addr_data_decl = tbl_data_decl # find ~loc:x_loc addr_data_typ in
                  let addr_data_name =
                    begin match addr_data_typ with
                    | Globals.Named s -> s
                    | _ -> report_error pos "gather_addrof_exp: unexpected type!"
                    end in
                  let addr_var_decl =
                    let init_params = [(translate_lval lv)] in
                    let init_data = Iast.mkNew addr_data_name [] pos in
                    Iast.mkVarDecl addr_data_typ [(addr_var_name, Some init_data, pos)] pos
                    in
                  aux_local_vardecls := !aux_local_vardecls @ [addr_var_decl];
                  tbl_addrof_info # add ~loc:x_loc lv_str addr_var_name;
                with Not_found ->
                  (* report_error pos ("Data declaration for address data structure of \"" ^ string_of_cil_typ lv_ty ^"\" could not be found") *)
                  tbl_addrof_info # add ~loc:x_loc lv_str addr_var_name;
                end
            (* | _ ->
                let addr_var_name = str_addr ^ lv_str in
                begin try
                    let addr_data_typ = tbl_pointer_typ # find ~loc:x_loc lv_ty in
                    let addr_data_decl = tbl_data_decl # find ~loc:x_loc addr_data_typ in
                    let addr_data_name =
                      begin match addr_data_typ with
                      | Globals.Named s -> s
                      | _ -> report_error pos "gather_addrof_exp: unexpected type!"
                      end in
                    let addr_var_decl =
                      let init_params = [(translate_lval lv)] in
                      let init_data = Iast.mkNew addr_data_name init_params pos in
                      Iast.mkVarDecl addr_data_typ [(addr_var_name, Some init_data, pos)] pos
                      in
                    aux_local_vardecls := !aux_local_vardecls @ [addr_var_decl];
                    tbl_addrof_info # add ~loc:x_loc lv_str addr_var_name;
                with Not_found ->
                  tbl_addrof_info # add ~loc:x_loc lv_str addr_var_name (* lv_str *); (* Muoi: Address of a struct is itself *)
                end *)
          end
          (* with Not_found -> (
              let refined_ty = (match lv_ty with
                  | Cil.TPtr (ty, _) when (is_cil_struct_pointer lv_ty) -> ty      (* pointer to struct goes down 1 level *)
                  | _ -> lv_ty
                ) in

             let addr_vname = str_addr ^ lv_str in
              try
                let addr_dtyp = tbl_pointer_typ # find ~loc:x_loc refined_ty in
                let () = y_binfo_hp (add_str "tbl pointer typ" (pr_hashtbl string_of_cil_typ Globals.string_of_typ)) tbl_pointer_typ in
                let addr_ddecl = tbl_data_decl # find ~loc:x_loc addr_dtyp in
                let addr_dname = (
                  match addr_dtyp with
                  | Globals.Named s -> s
                  | _ -> report_error pos "gather_addrof_exp: unexpected type!"
                ) in
                let addr_vdecl = (
                  (* create and temporarily initiate a new object *)
                  let init_params = [(translate_lval lv)] in
                  let init_data = Iast.mkNew addr_dname init_params pos in
                  Iast.mkVarDecl addr_dtyp [(addr_vname, Some init_data, pos)] pos
                ) in
                aux_local_vardecls := !aux_local_vardecls @ [addr_vdecl];
                tbl_addrof_info # add ~loc:x_loc lv_str addr_vname;
              with Not_found -> tbl_addrof_info # add ~loc:x_loc lv_str addr_var_name (* lv_str *); (*Muoi: Address of a struct is itself*)
 *)
              (* let deref_ty = translate_typ refined_ty pos in *)
              (* let (addr_dtyp, addr_dname, addr_ddecl) = ( *)
              (*   try *)
              (*     let dtyp = Hashtbl.find tbl_pointer_typ refined_ty in *)
              (*     let ddecl = Hashtbl.find tbl_data_decl dtyp in *)
              (*     let dname = ( *)
              (*       match dtyp with *)
              (*       | Globals.Named s -> s *)
              (*       | _ -> report_error pos "gather_addrof_exp: unexpected type!" *)
              (*     ) in *)
              (*     (dtyp, dname, ddecl) *)
              (*   with Not_found -> ( *)
              (*       (\* create new Globals.typ and Iast.data_decl, then update to a hash table *\) *)
              (*       let ftyp = deref_ty in *)
              (*       let fname = str_value in *)
              (*       let val_field = ((ftyp, fname), no_pos, false, (gen_field_ann ftyp) (\* Iast.F_NO_ANN *\)) in *)
              (*       let offset_field = ((Int, str_offset), no_pos, false, (gen_field_ann Int)) in *)
              (*       let dfields = [val_field; offset_field] in *)
              (*       let dname = (Globals.string_of_typ ftyp) ^ "_star" in *)
              (*       let dtyp = Globals.Named dname in *)
              (*       Hashtbl.add tbl_pointer_typ refined_ty dtyp; *)
              (*       let ddecl = Iast.mkDataDecl dname dfields "Object" [] false [] in *)
              (*       Hashtbl.add tbl_data_decl dtyp ddecl; *)
              (*       (dtyp, dname, ddecl) *)
              (*     ) *)
              (* ) in *)
              (* (\* define new pointer var px that will be used to represent x: {x, &x} --> {*px, px} *\) *)
              (* let addr_vname = str_addr ^ lv_str in *)
              (* let addr_vdecl = ( *)
              (*   (\* create and temporarily initiate a new object *\) *)
              (*   let init_params = [(translate_lval lv)] in *)
              (*   let init_data = Iast.mkNew addr_dname init_params pos in *)
              (*   Iast.mkVarDecl addr_dtyp [(addr_vname, Some init_data, pos)] pos *)
              (* ) in *)
              (* aux_local_vardecls := !aux_local_vardecls @ [addr_vdecl]; *)
              (* Hashtbl.add tbl_addrof_info lv_str addr_vname; *)
            )
        )
  | Cil.StartOf (lv, _) -> ()

(************************************************************)
(*************** main translation functions *****************)
(************************************************************)

and translate_location (loc: Cil.location) : VarGen.loc =
  let cilsp = loc.Cil.start_pos in
  let cilep = loc.Cil.end_pos in
  let start_pos = {Lexing.pos_fname = cilsp.Cil.file;
                   Lexing.pos_lnum = cilsp.Cil.line;
                   Lexing.pos_bol = cilsp.Cil.line_begin;
                   Lexing.pos_cnum = cilsp.Cil.byte - 1;} in
  let end_pos = {Lexing.pos_fname = cilep.Cil.file;
                 Lexing.pos_lnum = cilep.Cil.line;
                 Lexing.pos_bol = cilep.Cil.line_begin;
                 Lexing.pos_cnum = cilep.Cil.byte - 1;} in
  let newloc = {VarGen.start_pos = start_pos;
                VarGen.mid_pos = end_pos; (* TRUNG CODE: this should be computed later *)
                VarGen.end_pos = end_pos;} in (* TRUNG CODE: this should be computed later *)
  (* return *)
  newloc

(* (\* remove all unnecessary attributes *\) *)
(* and get_core_cil_typ (t: Cil.typ) : Cil.typ = ( *)
(*   let core_typ = ( *)
(*     match t with *)
(*     | Cil.TVoid _ -> Cil.TVoid [] *)
(*     | Cil.TInt (ik, _) -> Cil.TInt (Cil.IInt, []) *)
(*     | Cil.TFloat (fk, _) -> Cil.TFloat (Cil.FFloat, []) *)
(*     | Cil.TPtr (ty, _) -> Cil.TPtr (get_core_cil_typ ty, []) *)
(*     | Cil.TArray (ty, e, _) -> Cil.TArray (get_core_cil_typ ty, e, []) *)
(*     | Cil.TFun (ty, ids_opt, b, _) ->  *)
(*         let new_ty = get_core_cil_typ ty in *)
(*         let new_ids_opt = (match ids_opt with *)
(*           | Some ids -> *)
(*               let new_ids = List.map (fun (id,t,_) -> *)
(*                 (id, get_core_cil_typ t, []) *)
(*               ) ids in *)
(*               Some new_ids *)
(*           | None -> None  *)
(*         ) in *)
(*         Cil.TFun (new_ty, new_ids_opt, b, []) *)
(*     | Cil.TNamed (tinfo, _) -> get_core_cil_typ tinfo.Cil.ttype *)
(*     | Cil.TComp (cinfo, _) -> ( *)
(*         try *)
(*           let ty = Hashtbl.find tbl_typedef cinfo.Cil.cname in *)
(*           get_core_cil_typ ty *)
(*         with _ -> t *)
(*       ) *)
(*     | Cil.TEnum (enum, _) -> *)
(*         let new_enum = {enum with Cil.eattr = []} in *)
(*         Cil.TEnum (new_enum, [])  *)
(*     | Cil.TBuiltin_va_list _ -> t *)
(*   ) in *)
(*   core_typ *)
(* ) *)

and translate_typ_x (t: Cil.typ) pos : Globals.typ =
  let newtype =
    match t with
    | Cil.TVoid _ -> Globals.Void
    | Cil.TInt (Cil.IBool, _) -> Globals.Bool
    (*| Cil.TInt (Cil.IChar, _) -> Globals.Named "char"*)
    | Cil.TInt _ -> Globals.Int
    | Cil.TFloat _ -> Globals.Float
    | Cil.TPtr (ty, _) -> (
        let core_type = get_core_cil_typ ty in
        (* create a new Globals.typ and a new Iast.data_decl to represent the pointer data structure *)
        let newt = (
          (* find if this pointer was handled before or not *)
          try
           tbl_pointer_typ # find ~loc:x_loc core_type
          with Not_found -> (
              (* create new Globals.typ and Iast.data_decl update to hash tables *)
              let value_typ = translate_typ core_type pos in
              let value_field = ((value_typ, str_value), no_pos, false, (gen_field_ann value_typ) (* Iast.F_NO_ANN *)) in
              let dname = match ty with
		            | Cil.TInt(Cil.IChar, _) -> "char_star"
                | _ -> (Globals.string_of_typ value_typ) ^ "_star"
              in
              let dtype = Globals.Named dname in
(*              let offset_field = match ty with*)
(*                | Cil.TInt(Cil.IChar, _) -> ((dtype, str_offset), no_pos, false, (gen_field_ann dtype))*)
(*                | _ -> ((Int, str_offset), no_pos, false, (gen_field_ann Int)) (*other types have an integer offset*)*)
(*              in*)
              let dfields = match ty with
                | Cil.TInt(Cil.IInt, _) -> [value_field] (* int_star type stores only one value *)
                | _ -> [value_field(*; offset_field*)]
              in
              tbl_pointer_typ # add ~loc:x_loc core_type dtype;
              let ddecl = Iast.mkDataDecl dname dfields "Object" [] false [] in
              x_binfo_hp (add_str "core_type" string_of_cil_typ) core_type no_pos;
              x_binfo_hp (add_str "new ddecl for pointer type" !Iast.print_data_decl) ddecl no_pos;
              tbl_data_decl # add ~loc:x_loc dtype ddecl;
              (* return new type*)
              dtype
            )
        ) in
        newt
      )
    | Cil.TArray (ty, _, _) ->
      let arrayty = translate_typ ty pos in
      Globals.Array (arrayty, 1)
    | Cil.TFun _ ->
      report_error pos "TRUNG TODO: handle TFun later! Maybe it's function pointer case?"
    | Cil.TNamed _ ->                                          (* typedef type *)
      let ty = get_core_cil_typ t in
      translate_typ ty pos
    | Cil.TComp (comp, _) -> Globals.Named comp.Cil.cname                          (* struct or union type*)
    | Cil.TEnum _ -> report_error pos "TRUNG TODO: handle TEnum later!"
    | Cil.TBuiltin_va_list _ -> report_error pos "TRUNG TODO: handle TBuiltin_va_list later!" in
  (* return *)
  newtype


and translate_typ (t: Cil.typ) pos : Globals.typ =
  let pr_t = (add_str "cil type" string_of_cil_typ) in
  let pr_res = (add_str "res" string_of_typ) in
  Debug.no_1 "translate_typ" pr_t pr_res
    (fun _ -> translate_typ_x t pos) t


and translate_var (vinfo: Cil.varinfo) (lopt: Cil.location option) : Iast.exp =
  let pos = match lopt with None -> no_pos | Some l -> translate_location l in
  let name = vinfo.Cil.vname in
  if (String.compare name "null" = 0) then
    (Iast.Null pos)
  else
    (Iast.mkVar name pos)


and translate_var_decl (vinfo: Cil.varinfo) : Iast.exp =
  (* let vname = vinfo.Cil.vname in *)
  let pos = translate_location vinfo.Cil.vdecl in
  let ty = vinfo.Cil.vtype in
  let (new_ty, need_init) = (match ty with
      | Cil.TPtr (ty1, _) when (is_cil_struct_pointer ty) ->
        (translate_typ ty1 pos, false)                 (* heap allocated data *)
      | Cil.TComp _ -> (translate_typ ty pos, true)      (* stack allocated data *)
      | Cil.TNamed _ -> (translate_typ ty pos, true)
      | _ -> (translate_typ ty pos, false)
    ) in
  let name = vinfo.Cil.vname in
  let newexp = (
    match new_ty with
    | Globals.Int
    | Globals.Bool
    | Globals.Float
    | Globals.Array _
    | Globals.Named "void_star" -> Iast.mkVarDecl new_ty [(name, None, pos)] pos
    | Globals.Named typ_name -> (
        if (need_init) then (
          let init_data = Iast.mkNew typ_name [] pos in
          Iast.mkVarDecl new_ty [(name, Some init_data, pos)] pos
        )
        else Iast.mkVarDecl new_ty [(name, None, pos)] pos
      )
    | _ -> report_error pos ("translate_var_decl: Unexpected typ 2 - " ^ (Globals.string_of_typ new_ty))
  ) in
  newexp


and translate_constant (c: Cil.constant) (lopt: Cil.location option) : Iast.exp =
  let pos = match lopt with None -> no_pos | Some l -> translate_location l in
  match c with
  | Cil.CInt64 (i, _, _) -> Iast.mkIntLit (Int64.to_int i) pos
  | Cil.CStr s -> report_error pos "TRUNG TODO: Handle Cil.CStr later!"
  | Cil.CWStr _ -> report_error pos "TRUNG TODO: Handle Cil.CWStr later!"
  (*| Cil.CChr _ -> report_error pos "TRUNG TODO: Handle Cil.CChr later!"*)
  | Cil.CChr c -> Iast.mkIntLit (Char.code c) pos
  | Cil.CReal (f, _, _) -> Iast.mkFloatLit f pos
  | Cil.CEnum _ -> report_error pos "TRUNG TODO: Handle Cil.CEnum later!"


(* translate a field of a struct                       *)
(*     return: field type * location * inline property *)
and translate_fieldinfo (field: Cil.fieldinfo) (lopt: Cil.location option)
  : (typed_ident * loc * bool * (ident list)(* Iast.data_field_ann *)) =
  let pos = match lopt with None -> no_pos | Some l -> translate_location l in
  let name = field.Cil.fname in
  let ftyp = field.Cil.ftype in
  match ftyp with
  | Cil.TComp (comp, _) ->
    let ty = Globals.Named comp.Cil.cname in
    ((ty, name), pos, true, (gen_field_ann ty) (* Iast.F_NO_ANN *))                     (* struct ~~> inline data *)
  | Cil.TPtr (ty, _) ->
    let _ = Debug.ninfo_hprint (add_str "ftyp" string_of_cil_typ) ftyp no_pos in
    let _ = Debug.ninfo_hprint (add_str "ty" string_of_cil_typ) ty no_pos in
    let new_ty = (
      (* Loc: why do we ignore the outest pointer? *)
      if (is_cil_struct_pointer ftyp) then
        translate_typ ty pos    (* pointer goes down 1 level *)
      else
        translate_typ ftyp pos
    ) in
    ((new_ty, name), pos, false, (gen_field_ann new_ty) (* Iast.F_NO_ANN *))
  | _ ->
    let ty = translate_typ ftyp pos in
    ((ty, name), pos, false, (gen_field_ann ty) (* Iast.F_NO_ANN *))


and translate_compinfo (comp: Cil.compinfo) (lopt: Cil.location option) : unit =
  let name = comp.Cil.cname in
  let _ = Debug.ninfo_hprint (add_str "name" pr_id) name no_pos in
  let fields = List.map (fun x -> translate_fieldinfo x lopt) comp.Cil.cfields in
  let datadecl = Iast.mkDataDecl name fields "Object" [] false [] in
  tbl_data_decl # add ~loc:x_loc (Globals.Named name) datadecl;


and translate_unary_operator (op : Cil.unop) pos : Iast.uni_op =
  match op with
  | Cil.Neg -> Iast.OpUMinus
  | Cil.BNot -> report_error pos "Error!!! Iast doesn't support BNot (bitwise complement) operator!"
  | Cil.LNot -> Iast.OpNot


and translate_binary_operator (op : Cil.binop) pos : Iast.bin_op =
  match op with
  | Cil.PlusA -> Iast.OpPlus
  | Cil.PlusPI -> Iast.OpPlus        (* Trung: need to be considered *)
  | Cil.IndexPI -> Iast.OpPlus       (* Trung: need to be considered *)
  | Cil.MinusA -> Iast.OpMinus
  | Cil.MinusPI -> Iast.OpMinus      (* Trung: need to be considered *)
  | Cil.MinusPP -> Iast.OpMinus      (* Trung: need to be considered *)
  | Cil.Mult -> Iast.OpMult
  | Cil.Div -> Iast.OpDiv
  | Cil.Mod -> Iast.OpMod
  | Cil.Shiftlt -> report_error pos "Error!!! Iast doesn't support Cil.Shiftlf operator!"
  | Cil.Shiftrt -> report_error pos "Error!!! Iast doesn't support Cil.Shiftrt operator!"
  | Cil.Lt -> Iast.OpLt
  | Cil.Gt -> Iast.OpGt
  | Cil.Le -> Iast.OpLte
  | Cil.Ge -> Iast.OpGte
  | Cil.Eq -> Iast.OpEq
  | Cil.Ne -> Iast.OpNeq
  | Cil.BAnd -> report_error pos "Error!!! Iast doesn't support Cil.BAnd operator!"
  | Cil.BXor -> report_error pos "Error!!! Iast doesn't support Cil.BXor operator!"
  | Cil.BOr -> report_error pos "Error!!! Iast doesn't support Cil.BOr operator!"
  | Cil.LAnd -> Iast.OpLogicalAnd
  | Cil.LOr -> Iast.OpLogicalOr


and translate_lval_x (lv: Cil.lval) : Iast.exp =
  let _, _, l = lv in
  let pos = translate_location l in
  let lv_str = string_of_cil_lval lv in
  try
    let addr_vname = tbl_addrof_info # find ~loc:x_loc lv_str in
    let addr_var = Iast.mkVar addr_vname pos in
    Iast.mkMember addr_var [str_value] None pos
  with Not_found -> (
      let (lhost, offset, loc) = lv in
      let pos = translate_location loc in
      let rec create_complex_exp (base : Iast.exp) (offset : Cil.offset)
          (found_fields : string list) pos
        : Iast.exp =
        let _ = Debug.ninfo_hprint (add_str "base" Iprinter.string_of_exp) base no_pos in
        (
          match offset with
          | Cil.NoOffset -> (
              match found_fields with
              | [] -> base
              | _ -> Iast.mkMember base found_fields None pos
            )
          | Cil.Field ((field, l1), off, _) ->
            (* let p = makeLocation (startPos pos) (endPos (translate_location l1)) in *)
            create_complex_exp base off (found_fields @ [field.Cil.fname]) pos
          | Cil.Index (e, off, _) ->
            let l1 = loc_of_cil_exp e in
            let new_base = (match found_fields with
                | [] -> Iast.mkArrayAt base [(translate_exp e)] pos
                | _ ->
                  let p = makeLocation (startPos pos) (endPos (translate_location l1)) in
                  let b = Iast.mkMember base found_fields None p in
                  Iast.mkArrayAt b [(translate_exp e)] p
              ) in
            let _ = Debug.ninfo_hprint (add_str "new_base" Iprinter.string_of_exp) new_base no_pos in
            create_complex_exp new_base off [] pos
        ) in
      match lhost with
      | Cil.Var (v, l) ->
        let base = translate_var v (Some l) in
        let newexp = create_complex_exp base offset [] pos in
        let _ = Debug.ninfo_hprint (add_str "new exp" Iprinter.string_of_exp) base no_pos in
        newexp
      | Cil.Mem e ->
        (* access to data in pointer variable *)
        let base_typ = typ_of_cil_exp e in
        let _ = x_tinfo_hp (add_str "base_typ" string_of_cil_typ) base_typ no_pos in
        match base_typ with
        | Cil.TPtr (Cil.TComp _, _)
        | Cil.TPtr (Cil.TNamed _, _) ->
          let base = translate_exp e  in
          create_complex_exp base offset [] pos
        (* | Cil.TPtr (Cil.TNamed _, _) ->                             *)
        (*   let ptr_base = translate_exp e  in                        *)
        (*   let data_fields = [str_value] in                          *)
        (*   let base = Iast.mkMember ptr_base data_fields None pos in *)
        (*   create_complex_exp base offset [] pos                     *)
        | Cil.TPtr (Cil.TInt (Cil.IUChar, _), _)
        | Cil.TPtr (Cil.TInt (Cil.ISChar, _), _)
        | Cil.TPtr (Cil.TInt (Cil.IChar, _), _) -> (
            let pointer_arith_proc = create_string_proc base_typ base_typ in
            let proc_name = pointer_arith_proc.Iast.proc_name in
            let le = translate_exp e in
            let base = Iast.mkCallNRecv proc_name None [le] None None pos in
            create_complex_exp base offset [] pos
            (*let data_base = translate_exp e  in
            let data_fields = [str_char] in
            let base = Iast.mkMember data_base data_fields None pos in
            create_complex_exp base offset [] pos*)
          )
        | _ -> (
            let data_base = translate_exp e  in
            let data_fields = [str_value] in
            let typ = translate_typ base_typ in
            let base = Iast.mkMember data_base data_fields None pos in
            create_complex_exp base offset [] pos
          )
    )

and translate_lval (lv: Cil.lval) : Iast.exp =
  let pr_e = (add_str "cil_lv" string_of_cil_lval) in
  let pr_res = (add_str "res" !Iast.print_exp) in
  Debug.no_1 "translate_lval" pr_e pr_res
    (fun _ -> translate_lval_x lv) lv

and translate_exp_x (e: Cil.exp) : Iast.exp =
  match e with
  | Cil.Const (c, l) -> translate_constant c (Some l)
  | Cil.Lval (lv, _) -> translate_lval lv
  | Cil.SizeOf (_, l) ->  (* currently assume SizeOf = 1, TRUNG TODO: compute exact value later *)
    let pos = translate_location l in
    Iast.mkIntLit 1 pos
  | Cil.SizeOfE (_, l) -> (* currently assume SizeOfE = 1, TRUNG TODO: compute exact value later *)
    let pos = translate_location l in
    Iast.mkIntLit 1 pos
  | Cil.SizeOfStr (s, l) ->
    let pos = translate_location l in
    Iast.mkIntLit (String.length s) pos
  | Cil.AlignOf (_, l) ->
    let pos = translate_location l in
    report_error pos "TRUNG TODO: Handle Cil.AlignOf later!"
  | Cil.AlignOfE (_, l) ->
    let pos = translate_location l in
    report_error pos "TRUNG TODO: Handle Cil.AlignOfE later!"
  | Cil.UnOp (op, exp, ty, l) -> (
      let pos = translate_location l in
      let o = translate_unary_operator op pos in
      let e = translate_exp exp in
      let unexp = (
        let t = typ_of_cil_exp exp in
        let new_t = (match t with
            | Cil.TPtr (t1, _) when (is_cil_struct_pointer t) -> translate_typ t1 pos
            | _ -> translate_typ t pos
          ) in
        (* match new_t with                                      *)
        (*   | Globals.Bool -> (                                 *)
        (*       let not_proc = create_logical_not_proc new_t in *)
        (*       let proc_name = not_proc.Iast.proc_name in      *)
        (*       Iast.mkCallNRecv proc_name None [e] None pos    *)
        (*     )                                                 *)
        (*   | _ -> Iast.mkUnary o e None pos                    *)
        match op with
        | Cil.LNot ->
          let not_proc = create_logical_not_proc new_t in
          let proc_name = not_proc.Iast.proc_name in
          Iast.mkCallNRecv proc_name None [e] None None pos
        | _ -> Iast.mkUnary o e None pos
      ) in
      let target_typ = translate_typ ty pos in
      let newexp = Iast.mkCast target_typ unexp pos in
      newexp
    )
  | Cil.BinOp (op, e1, e2, ty, l) ->
    translate_exp_binary op e1 e2 ty l
  | Cil.Question (exp1, exp2, exp3, ty, l) ->
    let e1 = translate_exp exp1 in
    let e2 = translate_exp exp2 in
    let e3 = translate_exp exp3 in
    let pos = translate_location l in
    let qexp = Iast.mkCond e1 e2 e3 None pos in
    let target_typ = translate_typ ty pos in
    let newexp = Iast.mkCast target_typ qexp pos in
    newexp
  | Cil.CastE (ty, exp, l) -> (
      let pos = (
        if (l != Cil.locUnknown) then translate_location l
        else translate_location (loc_of_cil_exp exp)
      ) in
      let input_typ = (
        let ity = typ_of_cil_exp exp in
        (* let () = Debug.info_hprint (add_str "ity: " string_of_cil_typ) ity pos in *)
        match ity with
        | Cil.TPtr (t, _) when (is_cil_struct_pointer ity) -> translate_typ t pos
        | _ -> translate_typ ity pos
      ) in
      let output_typ = (match ty with
          | Cil.TPtr (ty1, _) when (is_cil_struct_pointer ty) -> translate_typ ty1 pos
          | _ -> translate_typ ty pos
        ) in
      let input_exp = translate_exp exp in
(*      let () = Debug.info_hprint (add_str "output_ty: " string_of_typ) output_typ pos in *)
(*      let () = Debug.info_hprint (add_str "input_ty: " string_of_typ) input_typ pos in *)
(*      let _ = Debug.binfo_hprint (add_str "new_base" Iprinter.string_of_exp) input_exp no_pos in*)
      if (input_typ = output_typ) then
        (* no need casting *)
        input_exp
      else (
        (* do casting *)
        match output_typ, input_typ with
        | Globals.Named otyp_name, Globals.Named ityp_name ->
          if (ityp_name = "void_star") then (
            let cast_proc = create_void_pointer_casting_proc otyp_name in
            Iast.mkCallNRecv cast_proc.Iast.proc_name None [input_exp] None None pos
          )
          else (
            let cast_proc = create_pointer_casting_proc ityp_name otyp_name in
            Iast.mkCallNRecv cast_proc.Iast.proc_name None [input_exp] None None pos
          )
        | Globals.Named otyp_name, Globals.Int ->
          let cast_proc = create_int_to_pointer_casting_proc otyp_name in
          Iast.mkCallNRecv cast_proc.Iast.proc_name None [input_exp] None None pos
        | Globals.Int, Globals.Named ityp_name ->
          (* let cast_proc = create_pointer_to_int_casting_proc ityp_name in *)
          (* Iast.mkCallNRecv cast_proc.Iast.proc_name None [input_exp] None pos *)
          (*Loc: should have a systematic way to handle deep data structures (e.g cll) with arith *)
          input_exp
        | _ ->
          report_error pos ("translate_exp: couldn't cast type 2: "
                            ^ (Globals.string_of_typ input_typ)
                            ^ " to " ^ (Globals.string_of_typ output_typ))
      )
    )
  | Cil.AddrOf (lv, l) -> (
      let pos = translate_location l in
      let lv_ty = typ_of_cil_lval lv in
      match lv_ty with
      | Cil.TComp _ -> translate_lval lv
      | _ -> (
          let lv_str = string_of_cil_lval lv in
          try
            let addr_vname = tbl_addrof_info # find ~loc:x_loc lv_str in
            Iast.mkVar addr_vname pos
          with Not_found ->
            report_error pos ("translate_exp: addr var of '" ^ lv_str ^ "' is not found.")
        )
    )
  | Cil.StartOf (lv, l) ->
    translate_lval lv

and translate_exp (e: Cil.exp) : Iast.exp =
  let pr_e = (add_str "cil exp" string_of_cil_exp) in
  let pr_res = (add_str "res" !Iast.print_exp) in
  Debug.no_1 "translate_exp" pr_e pr_res
    (fun _ -> translate_exp_x e) e


and translate_exp_binary (op: Cil.binop) (exp1: Cil.exp) (exp2: Cil.exp)
    (expected_typ: Cil.typ) (l: Cil.location)
  : Iast.exp =
  let pos = translate_location l in
  let e1 = translate_exp exp1 in
  let e2 = translate_exp exp2 in
  let t1 = typ_of_cil_exp exp1 in
  let t2 = typ_of_cil_exp exp2 in
  match (t1, t2) with
  (* pointer arithmetic *)
  | Cil.TInt(Cil.IChar, _), Cil.TPtr(Cil.TInt(Cil.IChar, _), _)
  | Cil.TPtr(Cil.TInt(Cil.IChar, _), _) , Cil.TInt(Cil.IChar, _) ->
    let pointer_arith_proc = create_string_proc t1 t2 in
    let proc_name = pointer_arith_proc.Iast.proc_name in
    let _ =  Debug.ninfo_hprint (add_str "proc_name" (pr_id)) proc_name no_pos in
    Iast.mkCallNRecv proc_name None [e1; e2] None None pos
  | _, Cil.TPtr(Cil.TInt(Cil.IChar, _), _) ->
    let pointer_arith_proc = create_string_proc t1 t2 in
    let proc_name = pointer_arith_proc.Iast.proc_name in
    let _ =  Debug.ninfo_hprint (add_str "proc_name" (pr_id)) proc_name no_pos in
    Iast.mkCallNRecv proc_name None [e2] None None pos
  | Cil.TPtr(Cil.TInt(Cil.IChar, _), _) , _ ->(
      match exp2 with
       | Cil.Const(Cil.CInt64 (i, _, _),_) -> (*Muoi: char_star+1 = plus_plus_char()*)
         let pointer_arith_proc = create_string_proc t1 t2 in
         let proc_name = pointer_arith_proc.Iast.proc_name in
         let _ =  Debug.binfo_hprint (add_str "proc_name" (pr_id)) proc_name no_pos in
         Iast.mkCallNRecv proc_name None [e1] None None pos
       | _ -> (*Muoi: For finalization string*)
         let coretyp1 = get_core_cil_typ t1 in
         let coretyp2 = get_core_cil_typ t2 in
         let typ1 = translate_typ coretyp1 no_pos in
         let typ2 = translate_typ coretyp2 no_pos in
         let typ1_name = string_of_typ typ1 in
         let typ2_name = string_of_typ typ2 in
         let pname = "__finalize_string" in
         let proc_decl =
         try
           Hashtbl.find tbl_aux_proc pname
         with Not_found -> (
           let proc_str = typ1_name ^ " " ^ pname ^ " (" ^ typ1_name ^ " x, " ^ typ2_name ^ " n)\n"
                          ^ "requires x::WFSegN<p, m> & 0 <= n & n < m & Term \n"
                          (* ^ "ensures x::WFSeg<q,n>*q::char_star<0,r>*r::WFSeg<p,m-n-1> ;\n" *)
                          ^ "ensures x::WSSN<q, n+1>;\n"
           in
           let proc_decl = Parser.parse_c_aux_proc "pointer_arithmetic_proc" proc_str in
           let _ = Debug.binfo_hprint (add_str "proc_decl" pr_id) proc_decl.Iast.proc_name no_pos in
           Hashtbl.add tbl_aux_proc pname proc_decl;
           proc_decl
         ) in
         let proc_name = proc_decl.Iast.proc_name in
         let _ =  Debug.ninfo_hprint (add_str "proc_name" (pr_id)) proc_name no_pos in
         Iast.mkCallNRecv proc_name None [e1;e2] None None pos
      )
  | Cil.TPtr _, Cil.TInt _
  | Cil.TInt _, Cil.TPtr _ ->
    (* | Cil.TPtr _, Cil.TPtr _ -> *)
    let _ =  Debug.ninfo_hprint (add_str "e1" !Iast.print_exp) e1 no_pos in
    let _ =  Debug.ninfo_hprint (add_str "e2" !Iast.print_exp) e2 no_pos in
    let pointer_arith_proc = create_pointer_arithmetic_proc op t1 t2 in
    let proc_name = pointer_arith_proc.Iast.proc_name in
    let _ =  Debug.ninfo_hprint (add_str "proc_name" (pr_id)) proc_name no_pos in
    Iast.mkCallNRecv proc_name None [e1; e2] None None pos
  (* not pointer arithmetic *)
  | _, _ ->
    let o = translate_binary_operator op pos in
    let binexp = Iast.mkBinary o e1 e2 None pos in
    let target_typ = translate_typ expected_typ pos in
    let newexp = Iast.mkCast target_typ binexp pos in
    newexp

and translate_instr (instr: Cil.instr) : Iast.exp =
  (* detect address-of operator *)
  match instr with
  | Cil.Set (lv, exp, l) -> (
      let (lhost, _, _) = lv in
      match lhost with
          | Cil.Mem e -> (
              let base_typ = typ_of_cil_exp e in
              match base_typ with
                | Cil.TPtr(Cil.TInt(Cil.IChar, _), _) -> (   (*Muoi: write_char(char_star s, c) or finalization strings *)
                    match exp with
                      | Cil.CastE(_, Cil.Const((Cil.CChr '\000'),_),_) -> (       (*Muoi: finalization strings when rhs='\0'*)
                          let (e1, e2) = (
                            match e with
                              | Cil.Lval (lv, _) -> (translate_lval lv, Iast.mkIntLit 0 no_pos)
                              | Cil.BinOp (_, e1, e2, _, _) -> (translate_exp e1, translate_exp e2)
                              | _ -> report_error no_pos "Muoi: To handle other Cil.exp types later!"
                            ) in
                           let typ1_name = "char_star" in
                           let typ2_name = "int" in
                           let pname = "__finalize_string" in
                           let proc_decl =
                             try
                               Hashtbl.find tbl_aux_proc pname
                             with Not_found -> (
                               let proc_str = typ1_name ^ " " ^ pname ^ " (" ^ typ1_name ^ " x, " ^ typ2_name ^ " n)\n"
                                              ^ "requires x::WFSegN<p, m> & 0 <= n & n < m & Term\n"
                                              (* ^ "ensures x::WFSeg<q,n>*q::char_star<0,r>*r::WFSeg<p,m-n-1> ;\n" *)
                                              ^ "ensures x::WSSN<q, n+1>;\n"
                                 in
                               let proc_decl = Parser.parse_c_aux_proc "pointer_arithmetic_proc" proc_str in
                               let _ = Debug.binfo_hprint (add_str "proc_decl" pr_id) proc_decl.Iast.proc_name no_pos in
                               Hashtbl.add tbl_aux_proc pname proc_decl;
                               proc_decl
                             ) in
                           let proc_name = proc_decl.Iast.proc_name in
                           let _ =  Debug.ninfo_hprint (add_str "proc_name" (pr_id)) proc_name no_pos in
                           Iast.mkCallNRecv proc_name None [e1;e2] None None no_pos
                        )
                      | _ -> (
                          match e with
                            | Cil.BinOp(_,_,_,_,_) -> failwith (x_tbi^"Muoi: to be implemented case: nondetString[length-1] = '\a';")
                            | _ ->(
                               let pos = translate_location l in
                               let le = translate_exp e in
                               let t1 = typ_of_cil_exp e in
                               let t2 = typ_of_cil_exp exp in
                               let re = translate_exp exp in
                               let pointer_arith_proc = create_string_proc t1 t2 in
                               let proc_name = pointer_arith_proc.Iast.proc_name in
                               Iast.mkCallNRecv proc_name None [le; re] None None pos
                            )
                        )
                  )
(*                    match e with*)
(*                      | Cil.BinOp (_, exp1, exp2, _, _) -> *)
(*                          let t1 = typ_of_cil_exp exp1 in*)
(*                          let t2 = typ_of_cil_exp exp2 in*)
(*                          match (t1,exp2) with*)
(*                            | Cil.TPtr(Cil.TInt(Cil.IChar, _), _), Cil.Const(Cil.CInt64 (i, _, _),_) *)
(*                              -> Iast.mkCallNRecv proc_name None [le; re] None None pos*)
(*                            | Cil.TPtr(Cil.TInt(Cil.IChar, _), _), _ -> le*)
(*                            | _, _ -> Iast.mkCallNRecv proc_name None [le; re] None None pos*)
(*                        )*)
(*                      | _ -> Iast.mkCallNRecv proc_name None [le; re] None None pos*)
                    (*Iast.mkAssign Iast.OpAssign le new_re None pos*)
                | _ -> (
              	    let pos = translate_location l in
                    let le = translate_lval lv in
                    let re = translate_exp exp in
                    (Iast.mkAssign Iast.OpAssign le re None pos)
                  )
            )
          | _ -> (
              let lv_typ = typ_of_cil_lval lv in
      	      let exp_typ = typ_of_cil_exp exp in
              let pos = translate_location l in
              let le = translate_lval lv in
              let re = translate_exp exp in
              let re_vars = get_vars_exp re in
              (if Gen.BList.overlap_eq eq_str re_vars !nondet_vars then
                let le_vars = get_vars_exp le in
                nondet_vars := !nondet_vars @ le_vars
              else ());
              (Iast.mkAssign Iast.OpAssign le re None pos)
            )
    )
  | Cil.Call (lv_opt, exp, exps, l) -> (
      let pos = translate_location l in
      let fname = match exp with
        | Cil.Const (Cil.CStr s, _) -> s
        | Cil.Lval ((Cil.Var (v, _), _, _), _) -> v.Cil.vname
        | _ -> report_error pos "translate_intstr: invalid callee's name!" in
      let args = List.map (fun x -> translate_exp x) exps in
      let _ = Debug.ninfo_hprint (add_str "args" (pr_list !Iast.print_exp)) (args) no_pos in
      let _ =
        if (Iast.is_tnt_prim_proc fname) then
          Hashtbl.add Iast.tnt_prim_proc_tbl fname fname
        else ()
      in
      let func_call = Iast.mkCallNRecv fname None args None None pos in (
        match lv_opt with
        | None -> func_call
        | Some lv ->
          let le = translate_lval lv in
          (if eq_str fname nondet_int_proc_name then
             let le_vars = get_vars_exp le in
             nondet_vars := !nondet_vars @ le_vars
           else ());
          Iast.mkAssign Iast.OpAssign le func_call None pos
      )
    )
  | Cil.Asm (_, _, _, _, _, l) -> (
      let pos = translate_location l in
      (Iast.Empty pos)
    )

and translate_stmt (s: Cil.stmt) : Iast.exp =
  let skind = s.Cil.skind in
  match skind with
  | Cil.Instr instrs ->
    let newexp = (match instrs with
        | [] -> Iast.Empty no_pos
        | [i] -> translate_instr i
        | _ ->
          let es = List.map translate_instr instrs in
          merge_iast_exp es
      ) in
    newexp
  | Cil.Return (eopt, l) ->
    let pos = translate_location l in
    let retval = (
      match eopt with
      | None -> None
      | Some e -> Some (translate_exp e)
    ) in
    let newexp = Iast.mkReturn retval None pos in
    newexp
  | Cil.Goto (sref, l) ->
    let pos = translate_location l in
    report_error pos "translate_stmt: handle GOTO later!"
  | Cil.Break l ->
    let pos = translate_location l in
    let newexp = Iast.mkBreak Iast.NoJumpLabel None pos in
    newexp
  | Cil.Continue l ->
    let pos = translate_location l in
    let newexp = Iast.mkContinue Iast.NoJumpLabel None pos in
    newexp
  | Cil.If (exp, blk1, blk2, l) ->
    let pos = translate_location l in
    let cond = (
      let ty = typ_of_cil_exp exp in
      let new_ty = (match ty with
          | Cil.TPtr (ty1, _) when (is_cil_struct_pointer ty) -> translate_typ ty1 pos
          | _ -> translate_typ ty pos
        ) in
      (* let () =  Debug.info_hprint (add_str "If:new_ty" (string_of_typ)) (new_ty) no_pos in *)
      match new_ty with
      | Globals.Bool -> translate_exp exp
      | _ -> (
          match exp with
          (* simplify conditional expression in if-statement *)
          (* | Cil.BinOp (op, Cil.CastE (t1, exp1, _), Cil.CastE (t2, exp2, _), ty, l) *)
          (*   when (t1 = t2) && ((op = Cil.Eq) || (op = Cil.Ne)) ->                   *)
          | Cil.BinOp (op, exp1, exp2, ty, l)
            when (is_arith_comparison_op op) ->
            let e1 = translate_exp exp1 in
            let e2 = translate_exp exp2 in
            let o = translate_binary_operator op pos in
            Iast.mkBinary o e1 e2 None pos
          | _ ->
            let cast_e e ty =
              let bool_of_proc = create_bool_casting_proc ty in
              let proc_name = bool_of_proc.Iast.proc_name in
              Iast.mkCallNRecv proc_name None [e] None None pos
            in
            let e = translate_exp exp in
            let e_vars = get_vars_exp e in
            if (Gen.BList.overlap_eq eq_str e_vars !nondet_vars) then
              match new_ty with
              | Globals.Int ->
                let zero = Iast.mkIntLit 0 pos in
                Iast.mkBinary Iast.OpGt e zero None pos
              | Globals.Float ->
                let zero = Iast.mkFloatLit 0.0 pos in
                Iast.mkBinary Iast.OpGt e zero None pos
              | _ -> cast_e e new_ty
            else cast_e e new_ty
        )
    ) in
    let e1 = translate_block blk1 in
    let e2 = translate_block blk2 in
    let ifexp = Iast.mkCond cond e1 e2 None pos in
    ifexp
  | Cil.Switch (exp, block, stmt_list, l) ->
    let e = translate_exp exp in
    let pos = translate_location l in
    let rec get_stmt2 sl = match sl with
      | [] -> []
      | s::sl -> match s.Cil.skind with
        | Cil.Break _ -> []
        | _ -> s::(get_stmt2 sl)
    in
    let rec get_stmt1 lbl sl = match sl with
      | [] -> []
      | s::sl -> if (List.mem lbl s.Cil.labels) then s::(get_stmt2 sl) else get_stmt1 lbl sl
    in
    let rec translate e_list = match e_list with
      | (ec,es)::[] -> (
          match ec with
          | Some ec -> let cond = Iast.mkBinary Iast.OpEq e ec None pos in
            Iast.mkCond cond es (Iast.Empty pos) None pos
          | None -> es
        )
      | (ec,es)::tl -> (
          match ec with
          | Some ec -> let cond = Iast.mkBinary Iast.OpEq e ec None pos in
            Iast.mkCond cond es (translate tl) None pos
          | None -> report_error pos "Error: Default!"
        )
      | _ -> report_error pos "Error: Empty list!"
    in
    let e_list = List.flatten (List.map (fun s ->
        List.map (fun lbl ->
            let sl = get_stmt1 lbl block.Cil.bstmts in
            (* let sl = List.filter (fun s -> List.mem lbl s.Cil.labels) block.Cil.bstmts in *)
            let s = merge_iast_exp (List.map (fun s -> translate_stmt s) sl) in
            match lbl with
            | Cil.Case (e_case, _) ->
              (Some (translate_exp e_case), (* translate_stmt *) s)
            | _ -> (None, (* translate_stmt *) s)
          ) s.Cil.labels
      ) stmt_list) in
    translate e_list
  (* report_error pos "TRUNG TODO: Handle Cil.Switch later!" *)
  | Cil.Loop (blk, hspecs, l, stmt_opt1, stmt_opt2) ->
    let p = translate_location l in
    let cond = Iast.mkBoolLit true p in
    let body = translate_block blk in
    let newexp = Iast.While {Iast.exp_while_condition = cond;
                             Iast.exp_while_body = body;
                             Iast.exp_while_addr_vars = [];
                             Iast.exp_while_specs = hspecs;
                             Iast.exp_while_jump_label = Iast.NoJumpLabel;
                             Iast.exp_while_path_id = None ;
                             Iast.exp_while_f_name = "";
                             Iast.exp_while_wrappings = None;
                             Iast.exp_while_pos = p} in
    newexp
  | Cil.Block blk -> translate_block blk
  | Cil.TryFinally (blk1, blk2, l) ->
    let p = translate_location l in
    let e1 = translate_block blk1 in
    let e2 = translate_block blk2 in
    let newexp = Iast.mkTry e1 [] [e2] None p in
    newexp
  | Cil.TryExcept (blk1, (instrs, exp), blk2, l) ->
    let p = translate_location l in
    let e1 = translate_block blk1 in
    let e2 = translate_block blk2 in
    let newexp = Iast.mkTry e1 [] [e2] None p in
    newexp
  | Cil.HipStmt (iast_exp, l) ->
    (* TODO: temporarily skip translate stmt *)
    let p = translate_location l in
    translate_hip_exp iast_exp p
(*iast_exp*)

and translate_hip_exp (exp: Iast.exp) pos : Iast.exp =
  let pr = Iprinter.string_of_exp in
  Debug.no_1 "translate_hip_exp" pr pr (fun _ -> translate_hip_exp_x exp pos) exp

and translate_hip_exp_x (exp: Iast.exp) pos : Iast.exp =
  let rec helper_struc_formula (f: IF.struc_formula): IF.struc_formula = (
    match f with
    | IF.ECase ec ->
      IF.ECase { ec with
                 IF.formula_case_branches = List.map (fun (p, s) -> (helper_pure_formula p, helper_struc_formula s)) ec.IF.formula_case_branches;
               }
    | IF.EBase eb ->
      IF.EBase { eb with
                 IF.formula_struc_base = helper_formula eb.IF.formula_struc_base;
                 IF.formula_struc_continuation = (match eb.IF.formula_struc_continuation with
                     | None -> None
                     | Some sf -> Some (helper_struc_formula sf));
               }
    | IF.EAssume ea ->
      IF.EAssume { ea with
                   IF.formula_assume_simpl = helper_formula ea.IF.formula_assume_simpl;
                   IF.formula_assume_struc = helper_struc_formula ea.IF.formula_assume_struc;
                 }
    | IF.EInfer ei ->
      IF.EInfer { ei with
                  IF.formula_inf_continuation = helper_struc_formula ei.IF.formula_inf_continuation;
                }
    | IF.EList el -> IF.EList (List.map (fun (sl, sf) -> (sl, helper_struc_formula sf)) el)
  )
  and find_typ l id =
    match l with
    | Iast.VarDecl vd :: tl ->
      let idl = List.map (fun (id, _, _) -> id) vd.Iast.exp_var_decl_decls in
      if List.mem id idl then vd.Iast.exp_var_decl_type else find_typ tl id
    | _ -> Globals.Void
  and helper_formula (h: IF.formula) : IF.formula =
    (* let () = print_endline "hello" in *)
    let pr = Iprinter.string_of_formula in
    Debug.no_1 "helper_formula" pr pr helper_formula_x h
  and helper_formula_x (f: IF.formula): IF.formula = (
    match f with
    | IF.Base fb ->
      let r = Str.regexp str_addr in
      let new_heap_formula0 = helper_h_formula fb.IF.formula_base_heap in
      let addr_heap_free_var = List.filter (fun (id, pr) -> Str.string_match r id 0) (IF.h_fv new_heap_formula0) in
      let typ_heap_free_var = List.map (fun (id, pr) ->
          find_typ !aux_local_vardecls id) addr_heap_free_var in
      let new_heap_free_var = List.map (fun (id, pr) -> Ipure.fresh_var (Str.replace_first r "" id, pr)) addr_heap_free_var in
      let new_heap_formula1 = List.fold_left (fun hf ((id1, pr1), (id2, pr2)) -> IF.h_apply_one ((id1, pr1), (id2, pr2)) hf) new_heap_formula0 (List.combine addr_heap_free_var new_heap_free_var) in
      let new_heap_formula2 = List.fold_left
          (fun hf (((id1, pr1), (id2, pr2)), t) ->
             IF.mkStar hf (IF.mkHeapNode (id1, pr1) (string_of_typ t) [] 0 false SPLIT0 (Ipure.ConstAnn Mutable) false false false None
                             [Ipure.Var ((id2, Unprimed), no_pos)] [None] None no_pos) no_pos
          ) new_heap_formula1 (List.combine (List.combine addr_heap_free_var new_heap_free_var) typ_heap_free_var) in
      let npf = helper_pure_formula fb.IF.formula_base_pure in
      let addr_fvs = List.filter (fun (id, pr) -> Str.string_match r id 0) (Ipure.fv npf) in
      let tl = List.map (fun (id, pr) ->
          find_typ !aux_local_vardecls id) addr_fvs in
      let nfvs = List.map (fun (id, pr) -> Ipure.fresh_var (Str.replace_first r "" id, pr)) addr_fvs in
      let npf1 = Ipure.subst (List.combine addr_fvs nfvs) npf in
      let nhf = List.fold_left
          (fun hf (((id1, pr1), (id2, pr2)), t) ->
             IF.mkStar hf (IF.mkHeapNode (id1, pr1) (string_of_typ t) [] 0 false SPLIT0 (Ipure.ConstAnn Mutable) false false false None
                             [Ipure.Var ((id2, Unprimed), no_pos)] [None] None no_pos) no_pos
          ) new_heap_formula2 (List.combine (List.combine addr_fvs nfvs) tl) in
      IF.Base { fb with
                IF.formula_base_heap = nhf;
                IF.formula_base_pure = npf1;
                IF.formula_base_and = List.map helper_one_formula fb.IF.formula_base_and;
              }
    | IF.Exists fe ->
      let r = Str.regexp str_addr in
      let new_heap_formula0 = helper_h_formula fe.IF.formula_exists_heap in
      let addr_heap_free_var = List.filter (fun (id, pr) -> Str.string_match r id 0) (IF.h_fv new_heap_formula0) in
      let typ_heap_free_var = List.map (fun (id, pr) ->
          find_typ !aux_local_vardecls id) addr_heap_free_var in
      let new_heap_free_var = List.map (fun (id, pr) -> Ipure.fresh_var (Str.replace_first r "" id, pr)) addr_heap_free_var in
      let new_heap_formula1 = List.fold_left (fun hf ((id1, pr1), (id2, pr2)) -> IF.h_apply_one ((id1, pr1), (id2, pr2)) hf) new_heap_formula0 (List.combine addr_heap_free_var new_heap_free_var) in
      let new_heap_formula2 = List.fold_left
          (fun hf (((id1, pr1), (id2, pr2)), t) ->
             IF.mkStar hf (IF.mkHeapNode (id1, pr1) (string_of_typ t) [] 0 false SPLIT0 (Ipure.ConstAnn Mutable) false false false None
                             [Ipure.Var ((id2, Unprimed), no_pos)] [None] None no_pos) no_pos
          ) new_heap_formula1 (List.combine (List.combine addr_heap_free_var new_heap_free_var) typ_heap_free_var) in
      let npf = helper_pure_formula fe.IF.formula_exists_pure in
      let addr_fvs = List.filter (fun (id, pr) -> Str.string_match r id 0) (Ipure.fv npf) in
      let tl = List.map (fun (id, pr) ->
          find_typ !aux_local_vardecls id) addr_fvs in
      let nfvs = List.map (fun (id, pr) -> Ipure.fresh_var (Str.replace_first r "" id, pr)) addr_fvs in
      let npf1 = Ipure.subst (List.combine addr_fvs nfvs) npf in
      let nhf = List.fold_left
          (fun hf (((id1, pr1), (id2, pr2)), t) ->
             IF.mkStar hf (IF.mkHeapNode (id1, Primed) (string_of_typ t)
                             [] (*TODO:HO*) 0 false SPLIT0 (Ipure.ConstAnn Mutable) false false false None
                             [Ipure.Var ((id2, Unprimed), no_pos)] [None] None no_pos) no_pos
          ) new_heap_formula2 (List.combine (List.combine addr_fvs nfvs) tl) in
      IF.Exists { fe with
                  IF.formula_exists_heap = nhf;
                  IF.formula_exists_pure = npf1;
                  IF.formula_exists_and = List.map helper_one_formula fe.IF.formula_exists_and;
                }
    | IF.Or fo ->
      IF.Or { fo with
              IF.formula_or_f1 = helper_formula_x fo.IF.formula_or_f1;
              IF.formula_or_f2 = helper_formula_x fo.IF.formula_or_f2;
            }
  )
  and helper_one_formula (o: IF.one_formula): IF.one_formula = (
    match o with
    | ofo ->
      { ofo with
        IF.formula_heap = helper_h_formula ofo.IF.formula_heap;
        IF.formula_pure = helper_pure_formula ofo.IF.formula_pure;
        IF.formula_delayed = helper_pure_formula ofo.IF.formula_delayed;
      }
  )
  and helper_h_formula (h: IF.h_formula) : IF.h_formula =
    (* let () = print_endline "hello" in *)
    let pr = Iprinter.string_of_h_formula in
    Debug.no_1 "helper_h_formula" pr pr helper_h_formula_x h
  and helper_h_formula_x (h: IF.h_formula) : IF.h_formula = (
    match h with
    | IF.Phase hfp ->
      IF.Phase { hfp with
                 IF.h_formula_phase_rd = helper_h_formula_x hfp.IF.h_formula_phase_rd;
                 IF.h_formula_phase_rw = helper_h_formula_x hfp.IF.h_formula_phase_rw;
               }
    | IF.Conj hfc ->
      IF.Conj { hfc with
                IF.h_formula_conj_h1 = helper_h_formula_x hfc.IF.h_formula_conj_h1;
                IF.h_formula_conj_h2 = helper_h_formula_x hfc.IF.h_formula_conj_h2;
              }
    | IF.ConjStar hfcs ->
      IF.ConjStar { hfcs with
                    IF.h_formula_conjstar_h1 = helper_h_formula_x hfcs.IF.h_formula_conjstar_h1;
                    IF.h_formula_conjstar_h2 = helper_h_formula_x hfcs.IF.h_formula_conjstar_h2;
                  }
    | IF.ConjConj hfcc ->
      IF.ConjConj { hfcc with
                    IF.h_formula_conjconj_h1 = helper_h_formula_x hfcc.IF.h_formula_conjconj_h1;
                    IF.h_formula_conjconj_h2 = helper_h_formula_x hfcc.IF.h_formula_conjconj_h2;
                  }
    | IF.Star hfs ->
      IF.Star { hfs with
                IF.h_formula_star_h1 = helper_h_formula_x hfs.IF.h_formula_star_h1;
                IF.h_formula_star_h2 = helper_h_formula_x hfs.IF.h_formula_star_h2;
              }
    | IF.StarMinus hfsm ->
      IF.StarMinus { hfsm with
                     IF.h_formula_starminus_h1 = helper_h_formula_x hfsm.IF.h_formula_starminus_h1;
                     IF.h_formula_starminus_h2 = helper_h_formula_x hfsm.IF.h_formula_starminus_h2;
                   }
    | IF.HeapNode hn ->
      begin
        let (id, pr) = hn.IF.h_formula_heap_node in
        try
          let addr_vname = tbl_addrof_info # find ~loc:x_loc id in
          IF.HeapNode { hn with
                        IF.h_formula_heap_node = (addr_vname, pr)
                      }
        with _ -> h
      end
    | IF.HeapNode2 hn2 ->
      begin
        let (id, pr) = hn2.IF.h_formula_heap2_node in
        try
          let addr_vname = tbl_addrof_info # find ~loc:x_loc id in
          IF.HeapNode2 { hn2 with
                         IF.h_formula_heap2_node = (addr_vname, pr)
                       }
        with _ -> h
      end
    | IF.ThreadNode _
    | IF.HRel _ | IF.HTrue | IF.HFalse | IF.HEmp | IF.HVar _ -> h
  )
  and helper_pure_formula (p : Ipure.formula) : Ipure.formula = (
    match p with
    | Ipure.BForm (bf, fl) ->
      Ipure.BForm (helper_b_formula bf, fl)
    | Ipure.And (f1, f2, pos) ->
      Ipure.And (helper_pure_formula f1, helper_pure_formula f2, pos)
    | Ipure.AndList l ->
      Ipure.AndList (List.map (fun (t, f) -> (t, helper_pure_formula f)) l)
    | Ipure.Or (f1, f2, fl, pos) ->
      Ipure.Or (helper_pure_formula f1, helper_pure_formula f2, fl, pos)
    | Ipure.Not (f, fl, pos) ->
      Ipure.Not (helper_pure_formula f, fl, pos)
    | Ipure.Forall (idp, f, fl, pos) ->
      Ipure.Forall (idp, helper_pure_formula f, fl, pos)
    | Ipure.Exists (idp, f, fl, pos) ->
      Ipure.Exists (idp, helper_pure_formula f, fl, pos)
  )
  and helper_b_formula (b : Ipure.b_formula) : Ipure.b_formula = (
    match b with
    | (pf, biel) ->
      (helper_p_formula pf, biel)
  )
  and helper_p_formula (p : Ipure.p_formula) : Ipure.p_formula = (
    match p with
    | Ipure.Frm a -> Ipure.Frm a
    | Ipure.XPure xv ->
      Ipure.XPure xv
    | Ipure.BConst (b, pos) ->
      Ipure.BConst (b, pos)
    | Ipure.BVar ((id, pr), pos) ->
      p (* TODO *)
    | Ipure.SubAnn (e1, e2, pos) ->
      Ipure.SubAnn (helper_exp e1, helper_exp e2, pos)
    | Ipure.Lt (e1, e2, pos) ->
      Ipure.Lt (helper_exp e1, helper_exp e2, pos)
    | Ipure.Lte (e1, e2, pos) ->
      Ipure.Lte (helper_exp e1, helper_exp e2, pos)
    | Ipure.Gt (e1, e2, pos) ->
      Ipure.Gt (helper_exp e1, helper_exp e2, pos)
    | Ipure.Gte (e1, e2, pos) ->
      Ipure.Gte (helper_exp e1, helper_exp e2, pos)
    | Ipure.Eq (e1, e2, pos) ->
      Ipure.Eq (helper_exp e1, helper_exp e2, pos)
    | Ipure.Neq (e1, e2, pos) ->
      Ipure.Neq (helper_exp e1, helper_exp e2, pos)
    | Ipure.EqMax (e1, e2, e3, pos) ->
      Ipure.EqMax (helper_exp e1, helper_exp e2, helper_exp e3, pos)
    | Ipure.EqMin (e1, e2, e3, pos) ->
      Ipure.EqMin (helper_exp e1, helper_exp e2, helper_exp e3, pos)
    | Ipure.LexVar (ta, el1, el2, pos) ->
      Ipure.LexVar (ta, List.map (fun (e : Ipure.exp) -> helper_exp e) el1, List.map (fun (e : Ipure.exp) -> helper_exp e) el2, pos)
    | Ipure.BagIn (ip, e, pos) ->
      Ipure.BagIn (ip, helper_exp e, pos) (* TODO *)
    | Ipure.BagNotIn (ip, e, pos) ->
      Ipure.BagNotIn (ip, helper_exp e, pos) (* TODO *)
    | Ipure.BagSub (e1, e2, pos) ->
      Ipure.BagSub (helper_exp e1, helper_exp e2, pos)
    | Ipure.BagMin _ ->
      p (* TODO *)
    | Ipure.BagMax _ ->
      p (* TODO *)
    (* | Ipure.VarPerm (va, ipl, pos) -> *)
    (*       p (* TODO *)                *)
    | Ipure.ListIn (e1, e2, pos) ->
      Ipure.ListIn (helper_exp e1, helper_exp e2, pos)
    | Ipure.ListNotIn (e1, e2, pos) ->
      Ipure.ListNotIn (helper_exp e1, helper_exp e2, pos)
    | Ipure.ListAllN (e1, e2, pos) ->
      Ipure.ListAllN (helper_exp e1, helper_exp e2, pos)
    | Ipure.ListPerm (e1, e2, pos) ->
      Ipure.ListPerm (helper_exp e1, helper_exp e2, pos)
    | Ipure.ImmRel (an, cond, pos) ->
      Ipure.ImmRel (helper_p_formula an, cond, pos)
    | Ipure.RelForm (id, el, pos) ->
      Ipure.RelForm (id, List.map (fun e -> helper_exp e) el, pos) (* TODO *)
  )
  and helper_exp (e : Ipure.exp) : Ipure.exp = (
    match e with
    | Ipure.Ann_Exp (e, t, pos) ->
      Ipure.Ann_Exp (helper_exp e, t, pos)
    | Ipure.Null pos ->
      Ipure.Null pos
    | Ipure.Level ((id, pr), pos) ->
      e (* TODO *)
    | Ipure.Var ((id, pr), pos) ->
      begin
        try
          let addr_vname = tbl_addrof_info # find ~loc:x_loc id in
          Ipure.Var ((addr_vname, pr), pos)
        with _ -> e
      end
    (*let addr_var = Iast.mkVar addr_vname pos in
      Iast.mkMember addr_var ["deref"] None pos*)
    | Ipure.IConst (i, pos) ->
      Ipure.IConst (i, pos)
    | Ipure.FConst (f, pos) ->
      Ipure.FConst (f, pos)
    | Ipure.AConst (ha, pos) ->
      Ipure.AConst (ha, pos)
    | Ipure.InfConst (id, pos)
    | Ipure.NegInfConst (id, pos) ->
      e (* TODO *)
    | Ipure.Tsconst (t, pos) ->
      Ipure.Tsconst (t, pos)
    | Ipure.Tup2 ((e1, e2), pos) ->
      Ipure.Tup2 ((helper_exp e1, helper_exp e2), pos)
    | Ipure.Bptriple ((e1, e2, e3), pos) ->
      Ipure.Bptriple ((helper_exp e1, helper_exp e2, helper_exp e3), pos)
    | Ipure.Add (e1, e2, pos) ->
      Ipure.Add (helper_exp e1, helper_exp e2, pos)
    | Ipure.Subtract (e1, e2, pos) ->
      Ipure.Subtract (helper_exp e1, helper_exp e2, pos)
    | Ipure.Mult (e1, e2, pos) ->
      Ipure.Mult (helper_exp e1, helper_exp e2, pos)
    | Ipure.Div (e1, e2, pos) ->
      Ipure.Div (helper_exp e1, helper_exp e2, pos)
    | Ipure.Max (e1, e2, pos) ->
      Ipure.Max (helper_exp e1, helper_exp e2, pos)
    | Ipure.Min (e1, e2, pos) ->
      Ipure.Min (helper_exp e1, helper_exp e2, pos)
    | Ipure.TypeCast (t, e, pos) ->
      Ipure.TypeCast (t, e, pos)
    | Ipure.Bag (el, pos) ->
      Ipure.Bag (List.map (fun e -> helper_exp e) el, pos)
    | Ipure.BagUnion (el, pos) ->
      Ipure.BagUnion (List.map (fun e -> helper_exp e) el, pos)
    | Ipure.BagIntersect (el, pos) ->
      Ipure.BagIntersect (List.map (fun e -> helper_exp e) el, pos)
    | Ipure.BagDiff (e1, e2, pos) ->
      Ipure.BagDiff (helper_exp e1, helper_exp e2, pos)
    | Ipure.List (el, pos) ->
      Ipure.List (List.map (fun e -> helper_exp e) el, pos)
    | Ipure.ListCons (e1, e2, pos) ->
      Ipure.ListCons (helper_exp e1, helper_exp e2, pos)
    | Ipure.ListHead (e, pos) ->
      Ipure.ListHead (helper_exp e, pos)
    | Ipure.ListTail (e, pos) ->
      Ipure.ListTail (helper_exp e, pos)
    | Ipure.ListLength (e, pos) ->
      Ipure.ListLength (helper_exp e, pos)
    | Ipure.ListAppend (el, pos) ->
      Ipure.ListAppend (List.map (fun e -> helper_exp e) el, pos)
    | Ipure.ListReverse (e, pos) ->
      Ipure.ListReverse (helper_exp e, pos)
    | Ipure.ArrayAt ((id, pr), el, pos) ->
      e (* TODO *)
    | Ipure.Func (id, el, pos) ->
      e (* TODO *)
    | Ipure.Template _ -> e
    | Ipure.BExpr _ -> e
  ) in
  match exp with
  | Iast.Assert a -> (
      match a.Iast.exp_assert_asserted_formula with
      | Some (f, b) ->
        Iast.Assert { a with
                      Iast.exp_assert_asserted_formula = Some ((helper_struc_formula f), b);
                    }
      | None -> exp
    )
  | _ -> exp

and translate_block (blk: Cil.block): Iast.exp =
  let stmts = blk.Cil.bstmts in
  match stmts with
  | [] -> Iast.Empty no_pos
  | [s] -> translate_stmt s
  | _ -> (
      let exps = List.map translate_stmt stmts in
      let body = merge_iast_exp exps in
      let pos = translate_location (blk.Cil.bloc) in
      Iast.mkBlock body Iast.NoJumpLabel [] pos
    )

and translate_init (init: Cil.init) (lopt: Cil.location option) : Iast.exp =
  let pos = match lopt with
    | None -> no_pos
    | Some l -> translate_location l in
  match init with
  | Cil.SingleInit exp -> translate_exp exp
  | Cil.CompoundInit (typ, offset_init_list) -> (
      let newtyp = translate_typ typ pos in
      match newtyp with
      (* translate data structure *)
      | Globals.Named newtyp_name ->
        (* collect init fields and store in a hashtbl *)
        let tbl_fields_init = Hashtbl.create 1 in
        List.iter (fun x ->
            let off, init2 = x in
            let fname = match off with
              | Cil.NoOffset -> report_error pos "translate_init: handle Cil.NoOffset later!"
              | Cil.Field ((f, _), Cil.NoOffset, _) -> f.Cil.fname
              | Cil.Field ((f, _), (Cil.Field _), _) -> report_error pos "translate_init: handle Cil.Field later!"
              | Cil.Field ((f, _), (Cil.Index _), _) -> report_error pos "translate_init: handle Cil.Index later!"
              | Cil.Index _ -> report_error pos "translate_init: handle Cil.Index later!" in
            let fexp = translate_init init2 lopt in
            Hashtbl.add tbl_fields_init fname fexp;
          ) offset_init_list;
        (* init all fields of *)
        let data_decl = (
          try tbl_data_decl # find ~loc:x_loc newtyp
          with Not_found -> report_error pos ("translate_init: couldn't find typ - " ^ newtyp_name)
        ) in
        let init_params = List.fold_left (
            fun params field ->
              let ((ftyp, fid), _, _, _) = field in
              let finit = (
                try Hashtbl.find tbl_fields_init fid
                with Not_found -> (
                    match ftyp with
                    | Globals.Int -> Iast.mkIntLit 0 pos
                    | Globals.Bool -> Iast.mkBoolLit true pos
                    | Globals.Float -> Iast.mkFloatLit 0. pos
                    | Globals.Named _ -> Iast.mkNull pos
                    | _ -> report_error pos ("Unexpected typ 3: " ^ (Globals.string_of_typ ftyp))
                  )
              ) in
              params @ [finit]
          ) [] data_decl.Iast.data_fields in
        let init_exp = Iast.mkNew newtyp_name init_params pos in
        init_exp
      | _ -> report_error pos ("translate_init: handle other type later - "
                               ^ (Globals.string_of_typ newtyp))
    )


and translate_global_var (vinfo: Cil.varinfo) (iinfo: Cil.initinfo)
    (lopt: Cil.location option)
  : Iast.exp_var_decl =
  let pos = match lopt with None -> no_pos | Some l -> translate_location l in
  let ty = vinfo.Cil.vtype in
  let new_ty = (match ty with
      | Cil.TPtr (ty1, _) when (is_cil_struct_pointer ty) ->
        translate_typ ty1 pos                          (* heap allocated data *)
      | Cil.TComp _ -> translate_typ ty pos              (* stack allocated data *)
      | _ -> translate_typ ty pos
    ) in
  let name = vinfo.Cil.vname in
  let decl = (
    match iinfo.Cil.init with
    | None -> [(name, None, pos)]
    | Some init ->
      let init_exp = translate_init init lopt in
      [(name, Some init_exp, pos)]
  ) in
  let vardecl = {Iast.exp_var_decl_type = new_ty;
                 Iast.exp_var_decl_decls = decl;
                 Iast.exp_var_decl_pos = pos} in
  vardecl

and translate_fundec (fundec: Cil.fundec) (lopt: Cil.location option) : Iast.proc_decl =
  Debug.no_1 "translate_fundec" string_of_cil_fundec Iprinter.string_of_proc_decl
    (fun x -> translate_fundec_x x lopt) fundec

and generate_free_exprs addr_var_decls =
  List.map
    (function
      | Iast.VarDecl { exp_var_decl_type; exp_var_decl_decls; exp_var_decl_pos } ->
          List.map
            (fun (v, _, pos) ->
              let fname = "free" in
              let args = [Iast.mkVar v pos] in
              Iast.mkCallNRecv fname None args None None pos
            )
            exp_var_decl_decls
      | _ -> report_error no_pos "Not var decl in addr_var_decls"
    )
    addr_var_decls
    |> List.concat

and translate_fundec_x (fundec: Cil.fundec) (lopt: Cil.location option) : Iast.proc_decl =
  aux_local_vardecls := [];
  nondet_vars := [Globals.nondet_int_proc_name]; (* To handle nondeterministic if conditions *)
  let () = x_add_1 gather_addrof_fundec fundec in
  (* start translating function *)
  let pos = match lopt with None -> no_pos | Some l -> translate_location l in
  let fheader = fundec.Cil.svar in
  let name = fheader.Cil.vname in
  let mingled_name = "" in (* TRUNG TODO: check mingled_name later *)
  let static_specs = fundec.Cil.hipfuncspec in
  let return_typ = (
    match fheader.Cil.vtype with
    | Cil.TFun (ty, params, _, _) -> (*translate_typ ty pos*)
      (match ty with
       | Cil.TComp (comp, _) -> (Globals.Named comp.Cil.cname)
       | Cil.TPtr (ty1, _) when (is_cil_struct_pointer ty) ->
         (translate_typ ty1 pos)
       | _ -> (translate_typ ty pos)
      )
    | _ -> report_error pos "Error!!! Invalid type! Have to be TFun only."
  ) in
  let funargs = (
    let ftyp = fheader.Cil.vtype in
    let pos = translate_location fheader.Cil.vdecl in
    match ftyp with
    | Cil.TFun (_, p, _, _) -> (
        let params = Cil.argsToList p in
        let translate_one_param (p : string * Cil.typ * Cil.attributes)
          : Iast.param = (
          let (name, ty, _) = p in
          let (param_ty, param_mod) = (match ty with
              | Cil.TComp (comp, _) ->
                (Globals.Named comp.Cil.cname, Iast.CopyMod)
              | Cil.TPtr (ty1, _) when (is_cil_struct_pointer ty) -> begin
                  (* let _ = Debug.info_hprint (add_str "name" pr_id) "2" no_pos in *)
                  let ityp = translate_typ ty1 no_pos in
                  (* let _ = Debug.info_hprint (add_str "ityp" string_of_typ) ityp no_pos in *)
                  (* to convet to _star for pointer arimetic *)
                  (* let ityp2 = match ityp with *)
                  (*   | Named id -> Named (id ^ "_star") *)
                  (*   | _ -> ityp *)
                  (* in *)
                  (ityp, Iast.NoMod)
                end
              | _ -> (translate_typ ty no_pos, Iast.NoMod)
            ) in
          let newparam = {Iast.param_type = param_ty;
                          Iast.param_name = name;
                          Iast.param_mod = param_mod;
                          Iast.param_loc = pos; } in
          newparam
        ) in
        List.map translate_one_param params
      )
    | _ -> report_error pos "Invalid function header!"
  ) in
  let funbody = (
    match fundec.Cil.sbody.Cil.bstmts with
    | [] -> None
    | _ ->
      let slocals = List.map translate_var_decl fundec.Cil.slocals in
      let slocals =
        List.fold_left (fun acc v -> match v with
          | Iast.VarDecl { exp_var_decl_type; exp_var_decl_decls; exp_var_decl_pos } ->
              let filtered_vars = List.filter (fun (name, _, _) -> not (tbl_addrof_info # contains name)) exp_var_decl_decls in
              begin match filtered_vars with
                | [] -> acc
                | l ->
                  let filtered_var_decl = Iast.mkVarDecl exp_var_decl_type l exp_var_decl_pos
                  in filtered_var_decl :: acc
              end
          | e -> e :: acc
        )
        []
        slocals
      in
      let sbody = translate_block fundec.Cil.sbody in
      let free_exprs = generate_free_exprs !aux_local_vardecls in
      let catch_expr =
        let new_name = fresh_var_name "fi" pos.start_pos.Lexing.pos_lnum in
        let new_flow_var_name = fresh_var_name "flv" pos.start_pos.Lexing.pos_lnum in
        let raise_expr =
          Iast.mkRaise (Iast.Var_flow new_flow_var_name) false (Some (Iast.mkVar new_name pos)) true None pos in
        Iast.mkCatch
          (Some new_name)
          None
          raisable_class
          (Some new_flow_var_name)
          (merge_iast_exp (free_exprs @ [raise_expr]))
          pos in
      let try_expr =
        Iast.mkTry
          (merge_iast_exp (sbody :: free_exprs))
          [catch_expr]
          []
          None
          pos
          in
      (* let body = merge_iast_exp (slocals @ !aux_local_vardecls @ [sbody] @ free_exprs) in *)
      (* let body = merge_iast_exp (slocals @ !aux_local_vardecls @ [sbody]) in *)
      let body = merge_iast_exp (slocals @ !aux_local_vardecls @ [try_expr]) in
      let pos = translate_location fundec.Cil.sbody.Cil.bloc in
      Some (Iast.mkBlock body Iast.NoJumpLabel [] pos)
  ) in
  let filename = pos.start_pos.Lexing.pos_fname in
  let has_shape_args = List.exists (fun p ->
      (* let () = print_endline (string_of_typ p.Iast.param_type) in *)
      is_node_typ p.Iast.param_type
    ) (funargs) in
  let static_specs1, hp_decls, args_wi =
      if (not has_shape_args && not (is_node_typ return_typ)) || not !Globals.sags then
      static_specs, [], List.map (fun p -> (p.Iast.param_name,Globals.I)) funargs
      else
        let () = Debug.ninfo_hprint (add_str "static_specs" !Iformula.print_struc_formula) static_specs no_pos in
        match static_specs with
      | Iformula.EList [] -> begin
          match funbody with
          | Some _ ->
                let () =  Debug.ninfo_hprint (add_str "infer_const_obj 1" (pr_id)) (Globals.infer_const_obj#string_of) no_pos in
                if Globals.infer_const_obj # is_shape then
                    let ss, hps, args_wi = Iast.genESpec name funbody funargs return_typ
                      (Iformula.mkTrue_nf pos) (Iformula.mkTrue_nf pos) INF_SHAPE [] pos in
                    let () = Debug.ninfo_hprint (add_str "ss" !Iformula.print_struc_formula) ss no_pos in
                    (ss, hps, args_wi)
                else static_specs, [], List.map (fun p -> (p.Iast.param_name,Globals.I)) funargs
          | None -> static_specs, [], List.map (fun p -> (p.Iast.param_name,Globals.I)) funargs
        end
        |  Iformula.EInfer i_sf ->
               let () =  Debug.ninfo_hprint (add_str "infer_const_obj 2" (pr_id)) (Globals.infer_const_obj#string_of) no_pos in
               if Globals.infer_const_obj # is_shape || i_sf.Iformula.formula_inf_obj # is_shape (* || *)
                 (* Globals.infer_const_obj # is_shape_pre || i_sf.Iformula.formula_inf_obj # is_shape_pre || *)
                 (* Globals.infer_const_obj # is_shape_post || i_sf.Iformula.formula_inf_obj # is_shape_post *)
               then
          let is_simpl, pre,post = Iformula.get_pre_post i_sf.Iformula.formula_inf_continuation in
          if is_simpl then
            let ss, hps, args_wi = Iast.genESpec name funbody funargs return_typ pre post INF_SHAPE (i_sf.Iformula.formula_inf_obj # get_lst)  pos in
            let ss = match ss with
              | Iformula.EInfer i_sf2 -> Iformula.EInfer {i_sf2 with
                                                          Iformula.formula_inf_obj = i_sf.Iformula.formula_inf_obj # mk_or_lst (i_sf2.Iformula.formula_inf_obj # get_lst);}
              | _ -> ss
            in
               let () = Debug.ninfo_hprint (add_str "ss" !Iformula.print_struc_formula) ss no_pos in
            (ss,hps,args_wi)
          else
            static_specs, [], List.map (fun p -> (p.Iast.param_name,Globals.I)) funargs
        else
          static_specs, [], List.map (fun p -> (p.Iast.param_name,Globals.I)) funargs
      | _ ->
            static_specs, [], List.map (fun p -> (p.Iast.param_name,Globals.I)) funargs
  in
  let newproc : Iast.proc_decl = {
    Iast.proc_name = name;
    Iast.proc_mingled_name = mingled_name;
    Iast.proc_data_decl = None;
    Iast.proc_flags = [] ;
    Iast.proc_hp_decls = hp_decls;
    Iast.proc_constructor = false;
    Iast.proc_args = funargs;
    Iast.proc_ho_arg = None;
    Iast.proc_args_wi = args_wi;
    Iast.proc_source = ""; (* WN : need to change *)
    Iast.proc_return = return_typ;
    Iast.proc_static_specs = static_specs1;
    Iast.proc_dynamic_specs = Iformula.mkEFalseF ();
    Iast.proc_exceptions = [];
    Iast.proc_body = funbody;
    Iast.proc_is_main = Gen.is_some funbody;
    Iast.proc_is_while = false;
    Iast.proc_has_while_return = false;
    Iast.proc_is_invoked = false;
    Iast.proc_verified_domains = [INF_SHAPE];
    Iast.proc_file = filename;
    Iast.proc_loc = pos;
    Iast.proc_test_comps = None;
  } in
  newproc

and merge_iast_prog (main_prog: Iast.prog_decl) (aux_prog: Iast.prog_decl)
  : Iast.prog_decl =
  let newprog : Iast.prog_decl = {
    Iast.prog_data_decls = main_prog.Iast.prog_data_decls @ aux_prog.Iast.prog_data_decls;
    Iast.prog_include_decls = main_prog.Iast.prog_include_decls @ aux_prog.Iast.prog_include_decls;
    Iast.prog_global_var_decls = main_prog.Iast.prog_global_var_decls @ aux_prog.Iast.prog_global_var_decls;
    Iast.prog_logical_var_decls = main_prog.Iast.prog_logical_var_decls @ aux_prog.Iast.prog_logical_var_decls;
    Iast.prog_enum_decls = main_prog.Iast.prog_enum_decls @ aux_prog.Iast.prog_enum_decls;
    Iast.prog_view_decls = main_prog.Iast.prog_view_decls @ aux_prog.Iast.prog_view_decls;
    Iast.prog_func_decls = main_prog.Iast.prog_func_decls @ aux_prog.Iast.prog_func_decls;
    Iast.prog_rel_decls = main_prog.Iast.prog_rel_decls @ aux_prog.Iast.prog_rel_decls;
    Iast.prog_rel_ids = main_prog.Iast.prog_rel_ids @ aux_prog.Iast.prog_rel_ids;
    Iast.prog_axiom_decls = main_prog.Iast.prog_axiom_decls @ aux_prog.Iast.prog_axiom_decls;
    Iast.prog_hopred_decls = main_prog.Iast.prog_hopred_decls @ aux_prog.Iast.prog_hopred_decls;
    Iast.prog_proc_decls = main_prog.Iast.prog_proc_decls @ aux_prog.Iast.prog_proc_decls;
    Iast.prog_barrier_decls = main_prog.Iast.prog_barrier_decls @ aux_prog.Iast.prog_barrier_decls;
    Iast.prog_coercion_decls = main_prog.Iast.prog_coercion_decls @ aux_prog.Iast.prog_coercion_decls;
    Iast.prog_hp_decls = main_prog.Iast.prog_hp_decls @ aux_prog.Iast.prog_hp_decls;
    Iast.prog_hp_ids = main_prog.Iast.prog_hp_ids @ aux_prog.Iast.prog_hp_ids;
    Iast.prog_templ_decls = main_prog.Iast.prog_templ_decls @ aux_prog.Iast.prog_templ_decls;
    Iast.prog_test_comps = [];
    Iast.prog_ut_decls = main_prog.Iast.prog_ut_decls @ aux_prog.Iast.prog_ut_decls;
    Iast.prog_ui_decls = main_prog.Iast.prog_ui_decls @ aux_prog.Iast.prog_ui_decls;
  } in
  newprog

and translate_file (file: Cil.file) : Iast.prog_decl =
  (* initial values *)
  let data_decls : Iast.data_decl list ref = ref [] in
  let global_var_decls : Iast.exp_var_decl list ref = ref [] in
  let logical_var_decls : Iast.exp_var_decl list ref = ref [] in
  let enum_decls : Iast.enum_decl list ref = ref [] in
  let view_decls : Iast.view_decl list ref = ref [] in
  let func_decls : Iast.func_decl list ref = ref [] in
  let rel_decls : Iast.rel_decl list ref = ref [] in
  let rel_ids : (typ * ident) list ref = ref [] in
  let templ_decls: Iast.templ_decl list ref = ref [] in
  let ut_decls: Iast.ut_decl list ref = ref [] in
  let ui_decls: Iast.ui_decl list ref = ref [] in
  let axiom_decls : Iast.axiom_decl list ref = ref [] in
  let hopred_decls : Iast.hopred_decl list ref = ref [] in
  let proc_decls : Iast.proc_decl list ref = ref [] in
  let barrier_decls : Iast.barrier_decl list ref = ref [] in
  let coercion_decls : Iast.coercion_decl_list list ref = ref [] in
  let aux_progs : Iast.prog_decl list ref = ref [] in

  (* TODO: this is a naive way of checking if this is a cast function.
           to add a flag in teh specs to distinguish between cast functions and othere functions. *)
  let is_cast_function proc_name =
    let str = "__cast" in
    if (String.length proc_name < String.length str) then false
    else
      0 == String.compare (String.sub proc_name 0 (String.length str)) str
  in

  (* reset & init global vars *)
  tbl_pointer_typ # reset;
  tbl_data_decl # reset;
  Hashtbl.reset tbl_aux_proc;
  aux_local_vardecls := [];

  (* begin to translate *)
  let globals = file.Cil.globals in
  (* collect premitive info first *)
  List.iter (fun gl ->
      match gl with
      | Cil.GType (tinfo, _) ->                                   (* collect typedef info *)
        let core_typ = get_core_cil_typ tinfo.Cil.ttype in
        tbl_typedef # add ~loc:x_loc tinfo.Cil.tname core_typ;
      | _ -> ();
    ) globals;
  (* translate the rest *)
  List.iter (fun gl ->
      match gl with
      | Cil.GType (tinfo, _) -> ();
      | Cil.GCompTag (comp, l) -> translate_compinfo comp (Some l)
      | Cil.GCompTagDecl _ ->
        (* let () = print_endline ("== gl GCompTagDecl = " ^ (string_of_cil_global gl)) in *)
        ()
      | Cil.GEnumTag _ ->
        (* let () = print_endline ("== gl GEnumTag = " ^ (string_of_cil_global gl)) in *)
        ()
      | Cil.GEnumTagDecl _ ->
        (* let () = print_endline ("== gl GEnumTagDecl = " ^ (string_of_cil_global gl)) in *)
        ()
      | Cil.GVarDecl (v, l) ->
        (* let () = print_endline ("== gl GVarDecl = " ^ (string_of_cil_global gl)) in *)
        ()
      | Cil.GVar (v, init, l) ->
        let gvar = translate_global_var v init (Some l) in
        global_var_decls := !global_var_decls @ [gvar];
      | Cil.GFun (fd, l) ->
        let fd = remove_goto fd in
        let proc = translate_fundec fd (Some l) in
        (* if the user provided a cast method then replace the auto generated one with the user provided one *)
        if (is_cast_function proc.Iast.proc_name) then
          Hashtbl.add tbl_aux_proc proc.Iast.proc_name proc
        else
          proc_decls := !proc_decls @ [proc]
      | Cil.GAsm _ ->
        (* let () = print_endline ("== gl GAsm = " ^ (string_of_cil_global gl)) in *)
        ()
      | Cil.GPragma _ ->
        (* let () = print_endline ("== gl GPragma = " ^ (string_of_cil_global gl)) in *)
        ()
      | Cil.GText _ ->
        (* let () = print_endline ("== gl GText = " ^ (string_of_cil_global gl)) in *)
        ()
      | Cil.GHipProgSpec (hipprog, _) ->
        aux_progs := !aux_progs @ [hipprog]
    ) globals;
  (* let obj_def = {Iast.data_name = "Object"; *)
  (*                Iast.data_fields = []; *)
  (*                Iast.data_pos = no_pos; *)
  (*                Iast.data_parent_name = ""; *)
  (*                Iast.data_invs = []; *)
  (*                Iast.data_is_template = false; *)
   (*              Iast.data_pure_inv = None;*)
  (*                Iast.data_methods = []} in *)
  (* let string_def = {Iast.data_name = "String"; *)
  (*                   Iast.data_pos = no_pos; *)
  (*                   Iast.data_fields = []; *)
  (*                   Iast.data_parent_name = "Object"; *)
  (*                   Iast.data_invs = []; *)
  (*                   Iast.data_is_template = false; *)
(*                    Iast.data_pure_inv = None;*)
  (*                   Iast.data_methods = []} in *)
  (* update some global settings *)
  (* Hashtbl.iter (fun _ data -> if ((String.compare  data.Iast.data_name "char_star")!=0) (*&& ((String.compare  data.Iast.data_name "int_star")!=0)*)  then data_decls := data::!data_decls) tbl_data_decl; *)
  let data = tbl_data_decl # values |> List.filter (fun d -> d.Iast.data_name <> "char_star") in
  data_decls := data @ !data_decls;
  (* aux procs *)
  Hashtbl.iter (fun _ p -> proc_decls := p :: !proc_decls) tbl_aux_proc;
  (* Hashtbl.iter (fun _ p -> if ((String.compare p.Iast.proc_name "__plus_plus_char")!=0) && ((String.compare p.Iast.proc_name "__get_char")!=0) && ((String.compare p.Iast.proc_name "__write_char")!=0) && ((String.compare p.Iast.proc_name "__pointer_add__int_star__int__")!=0) then  proc_decls := p::!proc_decls) tbl_aux_proc; *)
  (* return *)
  let newprog : Iast.prog_decl = {
    Iast.prog_data_decls = (* obj_def :: string_def ::  *)!data_decls;
    Iast.prog_include_decls = []; (*WN : need to fill *)
    Iast.prog_global_var_decls = !global_var_decls;
    Iast.prog_logical_var_decls = !logical_var_decls;
    Iast.prog_enum_decls = !enum_decls;
    Iast.prog_view_decls = !view_decls;
    Iast.prog_func_decls = !func_decls;
    Iast.prog_rel_decls = !rel_decls;
    Iast.prog_rel_ids = !rel_ids;
    Iast.prog_templ_decls = !templ_decls;
    Iast.prog_ut_decls = !ut_decls;
    Iast.prog_ui_decls = !ui_decls;
    Iast.prog_axiom_decls = !axiom_decls;
    Iast.prog_hopred_decls = !hopred_decls;
    Iast.prog_proc_decls = !proc_decls;
    Iast.prog_barrier_decls = !barrier_decls;
    Iast.prog_coercion_decls = !coercion_decls;
    Iast.prog_hp_decls = List.fold_left (fun r proc ->r@proc.Iast.proc_hp_decls) [] !proc_decls;
    Iast.prog_hp_ids = [];
    Iast.prog_test_comps = []
  } in
  let newprog = List.fold_left (fun x y -> merge_iast_prog x y) newprog !aux_progs in
  newprog

(*****************   end of translation functions *******************)
(********************************************************************)

(**************************************************************)
(*****************   main parsing functions *******************)
(**************************************************************)

let parse_one_file (filename: string) : Cil.file =
  (* PARSE and convert to CIL *)
  if !Cilutil.printStages then ignore (Errormsg.log "Parsing %s\n" filename);
  let cil = Frontc.parse filename () in
  if (not !Epicenter.doEpicenter) then (
    (* sm: remove unused temps to cut down on gcc warnings  *)
    (* (Stats.time "usedVar" Rmtmps.removeUnusedTemps cil);  *)
    (* (trace "sm" (dprintf "removing unused temporaries\n")); *)
    (Rmtmps.removeUnusedTemps cil)
  );
  (* return *)
  cil

let process_one_file (cil: Cil.file) : unit =
  if !Cilutil.doCheck then (
    ignore (Errormsg.log "First CIL check\n");
    if not (Check.checkFile [] cil) && !Cilutil.strictChecking then (
      Errormsg.bug ("CIL's internal data structures are inconsistent "
                    ^^"(see the warnings above).  This may be a bug "
                    ^^"in CIL.\n")
    )
  );
  let prog = translate_file cil in
  let () = print_endline_quiet ("------------------------") in
  let () = print_endline_quiet ("--> translated program: ") in
  let () = print_endline_quiet ("------------------------") in
  let () = print_endline_quiet (Iprinter.string_of_program prog) in
  ()

let parse_prep (filename: string): Iast.prog_decl =
  let cil = parse_one_file filename in
  if !Cilutil.doCheck then (
    ignore (Errormsg.log "First CIL check\n");
    if not (Check.checkFile [] cil) && !Cilutil.strictChecking then (
      Errormsg.bug ("CIL's internal data structures are inconsistent "
                    ^^ "(see the warnings above).  This may be a bug "
                    ^^ "in CIL.\n")
    )
  );
  if (!Globals.print_cil_input) then (
    print_endline_quiet "";
    print_endline_quiet ("***********************************");
    print_endline_quiet ("********* input cil file **********");
    print_endline_quiet (string_of_cil_file cil);
    print_endline_quiet ("******** end of cil file **********");
    print_endline_quiet "";
  );
  (* finally, translate cil to iast *)
  let prog = translate_file cil in
  prog

let parse_hip (filename: string) : Iast.prog_decl =
  (* do the preprocess by GCC first *)
  let prep_filename = filename ^ ".prep" in
  let cmd = "gcc " ^ "-I ../ " ^ " -I /usr/lib/x86_64-linux-gnu/glib-2.0/include/  "^ " -C -E " ^ filename ^ " -o " ^ prep_filename in
  if not !compete_mode then (
    print_endline_quiet ("GCC Preprocessing...");
    print_endline_quiet cmd;
  );
  let exit_code = Sys.command cmd in
  if (exit_code != 0) then
    report_error no_pos "GCC Preprocessing failed!";
  (* then use CIL to parse the preprocessed file *)
  (* let cil = parse_one_file prep_filename in                            *)
  (* if !Cilutil.doCheck then (                                           *)
  (*   ignore (Errormsg.log "First CIL check\n");                         *)
  (*   if not (Check.checkFile [] cil) && !Cilutil.strictChecking then (  *)
  (*     Errormsg.bug ("CIL's internal data structures are inconsistent " *)
  (*                   ^^ "(see the warnings above).  This may be a bug " *)
  (*                   ^^ "in CIL.\n")                                    *)
  (*   )                                                                  *)
  (* );                                                                   *)
  (* if (!Globals.print_cil_input) then (                                 *)
  (*   print_endline "";                                                  *)
  (*   print_endline ("***********************************");             *)
  (*   print_endline ("********* input cil file **********");             *)
  (*   print_endline (string_of_cil_file cil);                            *)
  (*   print_endline ("******** end of cil file **********");             *)
  (*   print_endline "";                                                  *)
  (* );                                                                   *)
  (* (* finally, translate cil to iast *)                                 *)
  (* let prog = translate_file cil in                                     *)
  let prog = parse_prep prep_filename in
  (* and clean temp files *)
  let cmd = ("rm " ^ prep_filename) in
  let todo_unk = Sys.command cmd in
  (* return *)
  prog
