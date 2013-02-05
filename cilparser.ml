open Globals
open Error
open Exc.GTable

(* --------------------- *)
(* Global variables      *)
(* --------------------- *)

(* TRUNG: use stack to store type and variables *)

(* intermediate casting procs generated during the translation *)
let tbl_cast_procs : (Globals.typ * Globals.typ, Iast.proc_decl) Hashtbl.t = Hashtbl.create 10

(* hash table contains Globals.typ structures that are used to represent Cil.typ pointers *)
let tbl_data_type : (Cil.typ, Globals.typ) Hashtbl.t = Hashtbl.create 10

(* hash table contains Iast.data_decl structures that are used to represent pointer types *)
let tbl_data_decl : (Globals.typ, Iast.data_decl) Hashtbl.t = Hashtbl.create 10

(* address of global vars *)
let gl_addressof_data : (Cil.lval, Iast.exp) Hashtbl.t = Hashtbl.create 10

(* address of local vars *)
let lc_addressof_data : (Cil.lval, Iast.exp) Hashtbl.t = Hashtbl.create 10


let supplement_exp : Iast.exp list ref = ref []


(* reset all global vars for the next use *)
let reset_global_vars () =
  Hashtbl.clear tbl_data_type;
  Hashtbl.clear tbl_data_decl

(* ---------------------------------------- *)
(* string conversion functions for CIL      *)
(* ---------------------------------------- *)
let string_of_cil_exp (e: Cil.exp) : string =
  Pretty.sprint 10 (Cil.d_exp () e)

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

let string_of_cil_instr (i: Cil.instr) : string =
  Pretty.sprint 10 (Cil.d_instr () i)

let string_of_cil_global (g: Cil.global) : string =
  Pretty.sprint 10 (Cil.d_shortglobal () g)
(* ---   end of string conversion   --- *) 


(* ---------------------------------------- *)
(* supporting function                      *)
(* ---------------------------------------- *)

let rec loc_of_iast_exp (e: Iast.exp) : Globals.loc =
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


(* create an Iast.exp from a list of Iast.exp *)
let merge_iast_exp (es: Iast.exp list) : Iast.exp =
  match es with
  | [] -> (Iast.Empty no_pos)
  | [e] -> e
  | hd::tl ->
      List.fold_left (fun x y ->
        let posx = loc_of_iast_exp x in
        let posy = loc_of_iast_exp y in
        let newpos = {Globals.start_pos = posx.Globals.start_pos;
                      Globals.mid_pos = posy.Globals.mid_pos;
                      Globals.end_pos = posy.Globals.end_pos;} in
        Iast.Seq {Iast.exp_seq_exp1 = x;
                  Iast.exp_seq_exp2 = y;
                  Iast.exp_seq_pos = newpos;}
      ) hd tl


(* get type *)
let typ_of_cil_lval (lv: Cil.lval) : Cil.typ =
  Cil.typeOfLval lv

let typ_of_cil_exp (e: Cil.exp) : Cil.typ =
  Cil.typeOf e

let rec is_global_cil_exp (e: Cil.exp) : bool =
  match e with
  | Cil.Const _ ->
      report_error_msg "Error!!! is_global_cil_exp: not handle Cil.Const!"
  | Cil.Lval (lval, _) -> is_global_cil_lval lval
  | Cil.SizeOf _ ->
      report_error_msg "Error!!! is_global_cil_exp: not handle Cil.SizeOf!"
  | Cil.SizeOfE _ ->
      report_error_msg "Error!!! is_global_cil_exp: not handle Cil.SizeOfE!"
  | Cil.SizeOfStr _ ->
      report_error_msg "Error!!! is_global_cil_exp: not handle Cil.SizeOfStr!"
  | Cil.AlignOf _ ->
      report_error_msg "Error!!! is_global_cil_exp: not handle Cil.AlignOf!"
  | Cil.AlignOfE _ ->
      report_error_msg "Error!!! is_global_cil_exp: not handle Cil.AlignOfE!"
  | Cil.UnOp _ ->
      report_error_msg "Error!!! is_global_cil_exp: not handle Cil.UnOp!"
  | Cil.BinOp _ ->
      report_error_msg "Error!!! is_global_cil_exp: not handle Cil.BinOp!"
  | Cil.Question _ ->
      report_error_msg "Error!!! is_global_cil_exp: not handle Cil.Question!"
  | Cil.CastE (_, e1, _) -> is_global_cil_exp e1
  | Cil.AddrOf (lv, _) -> is_global_cil_lval lv
  | Cil.StartOf (lv, _) -> is_global_cil_lval lv 


and is_global_cil_lval (lv: Cil.lval) : bool =
  let lhost, _, _ = lv in
  match lhost with
  | Cil.Var (v, _) -> v.Cil.vglob;
  | Cil.Mem m -> is_global_cil_exp m


(* -------------------------------------- -------------------------------- *)
(* pre-translate: travel through CIL data to collect necessary information *)
(* ----------------------------------------------------------------------- *)
let travel_typ (t: Cil.typ) : unit =
  match t with
  | Cil.TVoid _ -> ()
  | Cil.TInt _ -> ()
  | Cil.TFloat _ -> ()
  | Cil.TPtr (ty, _) -> () (* TRUNG TODO: implement here *)
  | Cil.TArray (ty, _, _) -> () (* TRUNG TODO: implement here *)
  | Cil.TFun _ -> () (* TRUNG TODO: implement here *)
  | Cil.TNamed (tname, _) -> () (* TRUNG TODO: implement here *)
  | Cil.TComp (comp, _) -> () (* TRUNG TODO: implement here *)
  | Cil.TEnum _ -> () (* TRUNG TODO: implement here *)
  | Cil.TBuiltin_va_list _ -> () (* TRUNG TODO: implement here *)


let travel_var (vinfo: Cil.varinfo) : unit =
  ()


let travel_var_decl (vinfo: Cil.varinfo) : unit =
  ()


let travel_constant (c: Cil.constant) : unit =
  match c with
  | Cil.CInt64 (i, _, _) -> ()
  | Cil.CStr s -> ()
  | Cil.CWStr _ -> ()
  | Cil.CChr _ -> ()
  | Cil.CReal (f, fkind, _) -> () (* TRUNG TODO: implement here *)
  | Cil.CEnum _ -> () (* TRUNG TODO: implement here *)


let travel_fieldinfo (field: Cil.fieldinfo) : unit =
  match field.Cil.ftype with
  | Cil.TPtr _ -> () (* TRUNG TODO: implement here *)
  | _ -> ()


let travel_compinfo (comp: Cil.compinfo) : unit =
  () (* TRUNG TODO: implement here *)


let travel_unary_operator (op : Cil.unop) : unit =
  match op with
  | Cil.Neg -> ()
  | Cil.BNot -> ()
  | Cil.LNot -> ()


let travel_binary_operator (op : Cil.binop) : unit =
  match op with
  | Cil.PlusA -> ()
  | Cil.PlusPI -> ()
  | Cil.IndexPI -> ()
  | Cil.MinusA -> ()
  | Cil.MinusPI -> ()
  | Cil.MinusPP -> ()
  | Cil.Mult -> ()
  | Cil.Div -> ()
  | Cil.Mod -> ()
  | Cil.Shiftlt -> ()
  | Cil.Shiftrt -> ()
  | Cil.Lt -> ()
  | Cil.Gt -> ()
  | Cil.Le -> ()
  | Cil.Ge -> ()
  | Cil.Eq -> ()
  | Cil.Ne -> ()
  | Cil.BAnd -> ()
  | Cil.BXor -> ()
  | Cil.BOr -> ()
  | Cil.LAnd -> ()
  | Cil.LOr -> ()


let travel_lval (lv: Cil.lval) : unit =
  () (* TRUNG TODO: implement here *)


and travel_exp (e: Cil.exp) : unit =
  match e with
  | Cil.Const (c, l) -> ()
  | Cil.Lval (lv, _) -> () 
  | Cil.SizeOf (_, l) -> ()
  | Cil.SizeOfE (_, l) -> ()
  | Cil.SizeOfStr (s, l) -> ()
  | Cil.AlignOf _ -> ()
  | Cil.AlignOfE _ -> ()
  | Cil.UnOp (op, exp, ty, l) -> ()
  | Cil.BinOp (op, exp1, exp2, ty, l) -> ()
  | Cil.Question (exp1, exp2, exp3, _, l) -> ()
  | Cil.CastE (ty, exp, l) -> ()
  | Cil.AddrOf (lval, l) -> ()
  | Cil.StartOf _ -> ()


let travel_instr (instr: Cil.instr) : unit =
  match instr with
  | Cil.Set (lv, exp, l) -> ()
  | Cil.Call (lv_opt, exp, exps, l) -> ()
  | Cil.Asm _ -> ()


let travel_stmt (s: Cil.stmt) : unit =
  let skind = s.Cil.skind in
  match skind with
  | Cil.Instr instrs -> ()
  | Cil.Return (eopt, l) -> ()
  | Cil.Goto (sref, l) -> ()
  | Cil.Break l -> ()
  | Cil.Continue l -> ()
  | Cil.If (exp, blk1, blk2, l) -> ()
  | Cil.Switch _ -> ()
  | Cil.Loop (blk, hspecs, l, stmt_opt1, stmt_opt2) -> ()
  | Cil.Block blk -> ()
  | Cil.TryFinally (blk1, blk2, l) -> ()
  | Cil.TryExcept (blk1, (instrs, exp), blk2, l) -> ()
  | Cil.HipStmt (iast_exp, l) -> ()


let travel_block (blk: Cil.block) : unit =
  let stmts = blk.Cil.bstmts in
  match stmts with
  | [] -> ()
  | [s] -> ()
  | _ -> ()


let travel_init (vname: ident) (init: Cil.init) : unit =
  match init with
  | Cil.SingleInit exp -> ()
  | Cil.CompoundInit (_, offset_init_list) -> ()


let travel_global_var (vinfo: Cil.varinfo) (iinfo: Cil.initinfo) : unit =
  () (* TRUNG TODO: implement here *)

let travel_fundec (fundec: Cil.fundec) : unit =
  () (* TRUNG TODO: implement here *)


let travel_file (file: Cil.file) : unit =
  () (* TRUNG TODO: implement here *)



(* ---------------------------------------- *)
(* translation functions from Cil -> Iast   *)
(* ---------------------------------------- *)


(* let create_memory_cast_function (output_typ: Globals.typ) : Iast.proc_decl = *)
(*   let name = "cast_" ^ (Globals.string_of_typ "memory")                      *)
(*              ^ "_to_" ^ (Globals.string_of_typ output) in                    *)
(*   let param = {                                                              *)
(*     Iast.param_type = output_typ;                                            *)
(*     Iast.param_name = "typ";                                                 *)
(*     Iast.param_mod = Iast.NoMod;                                             *)
(*     Iast.param_loc = no_pos;                                                 *)
(*   } in                                                                       *)
(*   let static_specs = (                                                       *)
(*     let case1 =                                                              *)
(*     let struc_case_f = {                                                     *)
(*       Iformula.formula_case_branches =                                       *)
(*       Iformula.formula_case_pos = no_pos;                                    *)
(*     } in                                                                     *)
(*     Iformula.ECase struc_case_f                                              *)
(*   ) in                                                                       *)
(*   let proc_decl = {                                                          *)
(*     Iast.proc_name = name;                                                   *)
(*     Iast.proc_mingled_name = "";         (* TRUNG: check later *)            *)
(*     Iast.proc_data_decl = None;                                              *)
(*     Iast.proc_source = "";               (* TRUNG: check later *)            *)
(*     Iast.proc_constructor = false;                                           *)
(*     Iast.proc_args = [param];                                                *)
(*     Iast.proc_return = output_typ;                                           *)
(*     Iast.proc_static_specs = static_specs;                                   *)
(*     Iast.proc_dynamic_specs = Iformula.mkEFalseF ();                         *)
(*     Iast.proc_exceptions = [];                                               *)
(*     Iast.proc_body = None;                                                   *)
(*     Iast.proc_is_main = false;                                               *)
(*     Iast.proc_file = "intermediate-translation";                             *)
(*     Iast.proc_loc = no_pos;                                                  *)
(*     Iast.proc_test_comps = None;                                             *)
(*   } in                                                                       *)
(*   proc_decl                                                                  *)

let create_data_cast_proc (input_typ: Globals.typ) (output_typ: Globals.typ)
                          : Iast.proc_decl option =
  match input_typ, output_typ with
  | Globals.Named input_typ_name, Globals.Named output_typ_name -> (
      try
        Some (Hashtbl.find tbl_cast_procs (input_typ, output_typ))
      with Not_found -> (
        let proc_name = "cast_" ^ input_typ_name ^ "_to_" ^ output_typ_name in
        let output_typ_param = ( 
          let data_decl = (
            try Hashtbl.find tbl_data_decl output_typ
            with Not_found -> report_error_msg "Error: Unknown ouput_typ"
          ) in
          match data_decl.Iast.data_fields with
          | []   -> report_error_msg "Error: Invalid data_decl fields"
          | [hd] -> "<_>"
          | hd::tl -> "<" ^ (List.fold_left (fun s _ -> s ^ ", _") "_" tl) ^ ">"
        ) in
        let cast_proc = (
          output_typ_name ^ " " ^ proc_name ^ " (" ^ input_typ_name ^ " param)\n" ^
          "  case { \n" ^
          "    param =  null -> requires true ensures res = null; \n" ^
          "    param != null -> requires true ensures res::" ^ output_typ_name ^ output_typ_param ^ "; \n" ^
          "  }\n" 
        ) in
        let proc_decl = Parser.parse_proc_string "intermediate_proc" cast_proc in
        (* update *)
        Hashtbl.add tbl_cast_procs (input_typ, output_typ) proc_decl;
        (* return *)
        Some proc_decl
      )
    )
  | _, _ -> None

let translate_location (loc: Cil.location) : Globals.loc =
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
  let newloc = {Globals.start_pos = start_pos;
                Globals.mid_pos = end_pos; (* TRUNG CODE: this should be computed later *)
                Globals.end_pos = end_pos;} in (* TRUNG CODE: this should be computed later *)
  (* return *)
  newloc


let rec translate_typ (t: Cil.typ) : Globals.typ =
  let newtype = 
    match t with
    | Cil.TVoid _ -> Globals.Void
    | Cil.TInt _ -> Globals.Int
    | Cil.TFloat _ -> Globals.Float
    | Cil.TPtr (ty, _) ->
        (* create a new Globals.typ and a new Iast.data_decl to represent the pointer data structure *)
        let newt = (
          (* find if this pointer was handled before or not *)
          try Hashtbl.find tbl_data_type ty 
          with Not_found -> (
            (* create new Globals.typ and update to a hash table *)
            let index = Hashtbl.length tbl_data_type in
            let data_name = "pointer_type_" ^ (string_of_int index) in
            let data_type = Globals.Named data_name in
            Hashtbl.add tbl_data_type ty data_type;
            (* create new Iast.data_decl and update to a hash table *)
            let ftype = translate_typ ty in
            let fname = "pdata" in
            let data_decl = {Iast.data_name = data_name;
                             Iast.data_fields = [((ftype, fname), no_pos, false)];
                             Iast.data_parent_name = "Object";
                             Iast.data_invs = [];
                             Iast.data_is_template = false;
                             Iast.data_methods = [];} in
            Hashtbl.add tbl_data_decl data_type data_decl;
            (* return new type*)
            data_type
          )
        ) in
        newt
    | Cil.TArray (ty, _, _) ->
        let arrayty = translate_typ ty in
        Globals.Array (arrayty, 1)
    | Cil.TFun _ ->
        let _ = print_endline ("== t TFun = " ^ (string_of_cil_typ t)) in
        report_error_msg "TRUNG TODO: handle TFun later! Maybe it's function pointer case?"
    | Cil.TNamed (tname, _) -> translate_typ tname.Cil.ttype                       (* typedef type *)
    | Cil.TComp (comp, _) -> Globals.Named comp.Cil.cname                          (* struct or union type*)
    | Cil.TEnum _ -> report_error_msg "TRUNG TODO: handle TEnum later!"
    | Cil.TBuiltin_va_list _ -> report_error_msg "TRUNG TODO: handle TBuiltin_va_list later!" in
  (* return *)
  newtype

let translate_var (vinfo: Cil.varinfo) (lopt: Cil.location option) : Iast.exp =
  let pos = match lopt with None -> no_pos | Some l -> translate_location l in
  let name = vinfo.Cil.vname in
  let newexp = (
    if (name = "NULL") then
      (* the "NULL" variable is considered as a null expression *)
      Iast.Null pos
    else
      Iast.Var {Iast.exp_var_name = name;
                Iast.exp_var_pos = pos}
  ) in
  newexp


let translate_var_decl (vinfo: Cil.varinfo) : Iast.exp =
  let pos = translate_location vinfo.Cil.vdecl in
  let ty = translate_typ vinfo.Cil.vtype in
  let name = vinfo.Cil.vname in
  let decl = [(name, None, pos)] in
  let newexp = Iast.VarDecl {Iast.exp_var_decl_type = ty;
                             Iast.exp_var_decl_decls = decl;
                             Iast.exp_var_decl_pos = pos} in
  newexp


let translate_constant (c: Cil.constant) (lopt: Cil.location option) : Iast.exp =
  let pos = match lopt with None -> no_pos | Some l -> translate_location l in
  match c with
  | Cil.CInt64 (i, _, _) -> Iast.IntLit {Iast.exp_int_lit_val = Int64.to_int i;
                                         Iast.exp_int_lit_pos = pos}
  | Cil.CStr s -> report_error_msg "TRUNG TODO: Handle Cil.CStr later!"
  | Cil.CWStr _ -> report_error_msg "TRUNG TODO: Handle Cil.CWStr later!"
  | Cil.CChr _ -> report_error_msg "TRUNG TODO: Handle Cil.CChr later!"
  | Cil.CReal (f, fkind, _) -> (
      match fkind with
      | Cil.FFloat -> Iast.FloatLit {Iast.exp_float_lit_val = f;
                                     Iast.exp_float_lit_pos = pos}
      | Cil.FDouble -> report_error_msg "TRUNG TODO: Handle Cil.FDouble later!"
      | Cil.FLongDouble -> report_error_msg "TRUNG TODO: Handle Cil.FLongDouble later!"
    )
  | Cil.CEnum _ -> report_error_msg "TRUNG TODO: Handle Cil.CEnum later!"


(* translate a field of a struct                       *)
(*     return: field type * location * inline property *)
let translate_fieldinfo (field: Cil.fieldinfo) (lopt: Cil.location option) 
                        : (Iast.typed_ident * loc * bool) =
  let pos = match lopt with None -> no_pos | Some l -> translate_location l in
  let name = field.Cil.fname in
  match field.Cil.ftype with
  | Cil.TComp (comp, _) ->
      let ty = Globals.Named comp.Cil.cname in
      ((ty, name), pos, false)
  | Cil.TPtr (Cil.TComp (comp, _), _) ->
      let ty = Globals.Named comp.Cil.cname in
      ((ty, name), pos, false)
  | _ ->
      let ty = translate_typ field.Cil.ftype in
      ((ty, name), pos, false)


let translate_compinfo (comp: Cil.compinfo) (lopt: Cil.location option)
                       : Iast.data_decl =
  let name = comp.Cil.cname in
  let fields = List.map (fun x -> translate_fieldinfo x lopt) comp.Cil.cfields in
  let datadecl = {Iast.data_name = name;
                  Iast.data_fields = fields;
                  Iast.data_parent_name = "Object";
                  Iast.data_invs = [];
                  Iast.data_is_template = false;
                  Iast.data_methods = [];} in
  datadecl


let translate_unary_operator (op : Cil.unop) : Iast.uni_op =
  match op with
  | Cil.Neg -> Iast.OpUMinus
  | Cil.BNot -> report_error_msg "Error!!! Iast doesn't support BNot (bitwise complement) operator!"
  | Cil.LNot -> Iast.OpNot


let translate_binary_operator (op : Cil.binop) : Iast.bin_op =
  match op with
  | Cil.PlusA -> Iast.OpPlus
  | Cil.PlusPI -> report_error_msg "TRUNG TODO: Handle Cil.PlusPI later!"
  | Cil.IndexPI -> report_error_msg "TRUNG TODO: Handle Cil.IndexPI later!"
  | Cil.MinusA -> Iast.OpMinus
  | Cil.MinusPI -> report_error_msg "TRUNG TODO: Handle Cil.MinusPI later!"
  | Cil.MinusPP -> report_error_msg "TRUNG TODO: Handle Cil.MinusPP later!"
  | Cil.Mult -> Iast.OpMult
  | Cil.Div -> Iast.OpDiv
  | Cil.Mod -> Iast.OpMod
  | Cil.Shiftlt -> report_error_msg "Error!!! Iast doesn't support Cil.Shiftlf operator!"
  | Cil.Shiftrt -> report_error_msg "Error!!! Iast doesn't support Cil.Shiftrt operator!"
  | Cil.Lt -> Iast.OpLt
  | Cil.Gt -> Iast.OpGt
  | Cil.Le -> Iast.OpLte
  | Cil.Ge -> Iast.OpGte
  | Cil.Eq -> Iast.OpEq
  | Cil.Ne -> Iast.OpNeq
  | Cil.BAnd -> report_error_msg "Error!!! Iast doesn't support Cil.BAnd operator!"
  | Cil.BXor -> report_error_msg "Error!!! Iast doesn't support Cil.BXor operator!"
  | Cil.BOr -> report_error_msg "Error!!! Iast doesn't support Cil.BOr operator!"
  | Cil.LAnd -> Iast.OpLogicalAnd
  | Cil.LOr -> Iast.OpLogicalOr


let rec translate_lval (lv: Cil.lval) : Iast.exp =
  let (lhost, offset, loc) = lv in
  let pos = translate_location loc in
  (* find whether lval is subtituted by another pointer variable or not *)
  let pvar = (
    try
      if (is_global_cil_lval lv) then Some (Hashtbl.find gl_addressof_data lv)
      else Some (Hashtbl.find lc_addressof_data lv)
    with Not_found -> None
  ) in
  match pvar with
  | Some p -> (
      (* this lval was represented by a structure before, return this structure data *)
      let fields = ["pdata"] in
      let newexp = Iast.Member {Iast.exp_member_base = p;
                                Iast.exp_member_fields = fields;
                                Iast.exp_member_path_id = None;
                                Iast.exp_member_pos = pos} in
      newexp
    )
  | None -> (
      (* translate directly the lval *)
      let rec collect_index (off: Cil.offset) : Iast.exp list = (
        match off with
        | Cil.NoOffset -> []
        | Cil.Field _ -> report_error_msg "TRUNG TODO: collect_index: handle Cil.Field _ later"
        | Cil.Index (e, o, _) -> [(translate_exp e)] @ (collect_index o)
      ) in
      let rec collect_field (off: Cil.offset) : ident list = (
        match off with
        | Cil.NoOffset -> []
        | Cil.Field ((f, _), o, _) -> [(f.Cil.fname)] @ (collect_field o)
        | Cil.Index _ -> report_error_msg "TRUNG TODO: collect_field: handle Cil.Index _ later"
      ) in
      match (lhost, offset) with
      | Cil.Var (v, l), Cil.NoOffset ->
          let newexp = translate_var v (Some l) in
          newexp
      | Cil.Var (v, l), Cil.Index _ ->
          let base = translate_var v (Some l) in
          let index = collect_index offset in
          let newexp = Iast.ArrayAt {Iast.exp_arrayat_array_base = base;
                                     Iast.exp_arrayat_index = index;
                                     Iast.exp_arrayat_pos = pos} in
          newexp
      | Cil.Var (v, l), Cil.Field _ ->
          let base = translate_var v (Some l) in
          let fields = collect_field offset in
          let newexp = Iast.Member {Iast.exp_member_base = base;
                                    Iast.exp_member_fields = fields;
                                    Iast.exp_member_path_id = None;
                                    Iast.exp_member_pos = pos} in
          newexp
      | Cil.Mem e, Cil.NoOffset ->
          (* access to data in pointer variable *)
          let base = translate_exp e in
          let fields = ["pdata"] in
          let newexp = Iast.Member {Iast.exp_member_base = base;
                                    Iast.exp_member_fields = fields;
                                    Iast.exp_member_path_id = None;
                                    Iast.exp_member_pos = pos} in
          newexp
      | Cil.Mem e, Cil.Index _ ->
          let base = translate_exp e  in
          let index = collect_index offset in
          let newexp = Iast.ArrayAt {Iast.exp_arrayat_array_base = base;
                                     Iast.exp_arrayat_index = index;
                                     Iast.exp_arrayat_pos = pos} in
          newexp
      | Cil.Mem e, Cil.Field _ ->
          let base = translate_exp e in
          let fields = collect_field offset in
          let newexp = Iast.Member {Iast.exp_member_base = base;
                                    Iast.exp_member_fields = fields;
                                    Iast.exp_member_path_id = None;
                                    Iast.exp_member_pos = pos} in
          newexp
  )

and translate_exp (e: Cil.exp) : Iast.exp =
  match e with
  | Cil.Const (c, l) -> translate_constant c (Some l)
  | Cil.Lval (lv, _) -> translate_lval lv 
  | Cil.SizeOf (_, l) ->  (* currently assume SizeOf = 1, TRUNG TODO: compute exact value later *)
      let pos = translate_location l in
      Iast.IntLit {Iast.exp_int_lit_val = 1;
                   Iast.exp_int_lit_pos = pos}
  | Cil.SizeOfE (_, l) -> (* currently assume SizeOfE = 1, TRUNG TODO: compute exact value later *)
      let pos = translate_location l in
      Iast.IntLit {Iast.exp_int_lit_val = 1;
                   Iast.exp_int_lit_pos = pos}
  | Cil.SizeOfStr (s, l) ->
      let pos = translate_location l in
      Iast.IntLit {Iast.exp_int_lit_val = String.length s;
                   Iast.exp_int_lit_pos = pos}
  | Cil.AlignOf _ -> report_error_msg "TRUNG TODO: Handle Cil.AlignOf later!"
  | Cil.AlignOfE _ -> report_error_msg "TRUNG TODO: Handle Cil.AlignOfE later!"
  | Cil.UnOp (op, exp, ty, l) ->
      let e = translate_exp exp in
      let o = translate_unary_operator op in
      let pos = translate_location l in
      let newexp = Iast.Unary {Iast.exp_unary_op = o;
                               Iast.exp_unary_exp = e;
                               Iast.exp_unary_path_id = None;
                               Iast.exp_unary_pos = pos} in
      newexp
  | Cil.BinOp (op, exp1, exp2, ty, l) ->
      let e1 = translate_exp exp1 in
      let e2 = translate_exp exp2 in
      let o = translate_binary_operator op in
      let pos = translate_location l in
      let newexp = Iast.Binary {Iast.exp_binary_op = o;
                                Iast.exp_binary_oper1 = e1;
                                Iast.exp_binary_oper2 = e2;
                                Iast.exp_binary_path_id = None;
                                Iast.exp_binary_pos = pos} in
      newexp
  | Cil.Question (exp1, exp2, exp3, _, l) ->
      let e1 = translate_exp exp1 in
      let e2 = translate_exp exp2 in
      let e3 = translate_exp exp3 in
      let pos = translate_location l in
      let newexp = Iast.Cond {Iast.exp_cond_condition = e1;
                              Iast.exp_cond_then_arm = e2;
                              Iast.exp_cond_else_arm = e3;
                              Iast.exp_cond_path_id = None;
                              Iast.exp_cond_pos = pos} in
      newexp
  | Cil.CastE (ty, exp, l) ->
      let pos = translate_location l in
      let cast_typ = translate_typ ty in
      let input_exp = translate_exp exp in
      let input_typ = translate_typ (typ_of_cil_exp exp) in
      let cast_proc = create_data_cast_proc input_typ cast_typ in
      let newexp = ( 
        match cast_proc with
        | None -> (
            Iast.Cast {Iast.exp_cast_target_type = cast_typ;
                       Iast.exp_cast_body = input_exp;
                       Iast.exp_cast_pos = pos}
          )
        | Some proc -> (
            Iast.CallNRecv {
              Iast.exp_call_nrecv_method = proc.Iast.proc_name;
              Iast.exp_call_nrecv_lock = None;
              Iast.exp_call_nrecv_arguments = [input_exp];
              Iast.exp_call_nrecv_path_id = None;
              Iast.exp_call_nrecv_pos = pos
            }
          )
      ) in
      newexp
  | Cil.AddrOf (lval, l) ->
      (* create a new Iast.data_decl that has 1 inline field is lval *)
      let newexp = (
        try
          if (is_global_cil_lval lval) then
            Hashtbl.find gl_addressof_data lval               (* global vars *)
          else Hashtbl.find lc_addressof_data lval            (* local vars *)
        with Not_found -> (
          let ty = typ_of_cil_lval lval in
          let pos = translate_location l in
          let (newty, tyname) = (
            try 
              let t = Hashtbl.find tbl_data_type ty in
              let n = match t with
                | Globals.Named s -> s
                | _ -> report_error_msg "Error!!! translate_exp: invalid type!" in
              (t, n)
            with Not_found -> (
              (* create new Globals.typ and update to a hash table *)
              let index = Hashtbl.length tbl_data_type in
              let data_name = "pointer_type_" ^ (string_of_int index) in
              let data_type = Globals.Named data_name in
              Hashtbl.add tbl_data_type ty data_type;
              (* create new Iast.data_decl and update to a hash table *)
              let ftype = translate_typ ty in
              let fname = "pdata" in
              let data_decl = {Iast.data_name = data_name;
                               Iast.data_fields = [((ftype, fname), no_pos, false)];
                               Iast.data_parent_name = "Object";
                               Iast.data_invs = [];
                               Iast.data_is_template = false;
                               Iast.data_methods = [];} in
              Hashtbl.add tbl_data_decl data_type data_decl;
              (data_type, data_name)
            )
          ) in
          let lval_translated = translate_exp (Cil.Lval (lval, l)) in
          (* define new pointer var px that will be used to represent x: {x, &x} --> {*px, px} *)
          let newvar = (
            let vname = (
              if (is_global_cil_lval lval) then
                "gl_p_" ^ (string_of_int (Hashtbl.length gl_addressof_data))
              else "lc_p_" ^ (string_of_int (Hashtbl.length lc_addressof_data))
            ) in
            let decl = [(vname, None, pos)] in
            let vardecl = Iast.VarDecl {Iast.exp_var_decl_type = newty;
                                        Iast.exp_var_decl_decls = decl;
                                        Iast.exp_var_decl_pos = pos} in
            if (is_global_cil_lval lval) then
              Hashtbl.add gl_addressof_data lval vardecl
            else Hashtbl.add lc_addressof_data lval vardecl;
            let var = Iast.Var {Iast.exp_var_name = vname;
                                Iast.exp_var_pos = pos} in
            var;
          ) in
          (* new *)
          (* assign *)
          let tmp_exp_new = Iast.New {Iast.exp_new_class_name = tyname;
                                      Iast.exp_new_arguments = [lval_translated];
                                      Iast.exp_new_pos = pos} in
          let tmp_exp_assign = Iast.Assign {Iast.exp_assign_op = Iast.OpAssign;
                                            Iast.exp_assign_lhs = newvar;
                                            Iast.exp_assign_rhs = tmp_exp_new;
                                            Iast.exp_assign_path_id = None;
                                            Iast.exp_assign_pos = pos} in
          supplement_exp := !supplement_exp @ [tmp_exp_assign];
          newvar
        )
      ) in
      newexp
  | Cil.StartOf _ -> report_error_msg "Error!!! Iast doesn't support Cil.StartOf exp!"


let translate_instr (instr: Cil.instr) : Iast.exp =
  supplement_exp := []; (* reset supplement_exp before each times translate_instr*)
  let translated_instr = (match instr with
    | Cil.Set (lv, exp, l) -> (
        let pos = translate_location l in
        let le = translate_lval lv in
        let re = translate_exp exp in
        Iast.Assign {Iast.exp_assign_op = Iast.OpAssign;
                     Iast.exp_assign_lhs = le;
                     Iast.exp_assign_rhs = re;
                     Iast.exp_assign_path_id = None;
                     Iast.exp_assign_pos = pos}
      )
    | Cil.Call (lv_opt, exp, exps, l) -> (
        let pos = translate_location l in
        let fname = match exp with
          | Cil.Const (Cil.CStr s, _) -> s
          | Cil.Const _ -> report_error_msg "Error!!! translate_intstr: cannot handle Cil.Const _ !"
          | Cil.Lval ((Cil.Var (v, _), _, _), _) -> v.Cil.vname
          | Cil.Lval _ -> report_error_msg "Error!!! translate_intstr: cannot handle Cil.Lval _!"
          | Cil.SizeOf _ -> report_error_msg "Error!!! translate_intstr: cannot handle Cil.SizeOf!" 
          | Cil.SizeOfE _ -> report_error_msg "Error!!! translate_intstr: cannot handle Cil.SizeOfE!"
          | Cil.SizeOfStr _ -> report_error_msg "Error!!! translate_intstr: cannot handle Cil.SizeOfStr!"
          | Cil.AlignOf _ -> report_error_msg "Error!!! translate_intstr: cannot handle Cil.AlignOf!"
          | Cil.AlignOfE _ -> report_error_msg "Error!!! translate_intstr: cannot handle Cil.AlignOfE!" 
          | Cil.UnOp _ -> report_error_msg "Error!!! translate_intstr: cannot handle Cil.UnOp!" 
          | Cil.BinOp _ -> report_error_msg "Error!!! translate_intstr: cannot handle Cil.BinOp!"
          | Cil.Question _ -> report_error_msg "Error!!! translate_intstr: cannot handle Cil.Question!"
          | Cil.CastE _ -> report_error_msg "Error!!! translate_intstr: cannot handle Cil.CastE!"
          | Cil.AddrOf _ -> report_error_msg "Error!!! translate_intstr: cannot handle Cil.AddrOf!" 
          | Cil.StartOf _ -> report_error_msg "Error!!! translate_intstr: cannot handle Cil.StartOf!" in
        let args = List.map (fun x -> translate_exp x) exps in
        let callee = Iast.CallNRecv {Iast.exp_call_nrecv_method = fname;
                                     Iast.exp_call_nrecv_lock = None;
                                     Iast.exp_call_nrecv_arguments = args;
                                     Iast.exp_call_nrecv_path_id = None;
                                     Iast.exp_call_nrecv_pos = pos} in
        match lv_opt with
        | None -> callee;
        | Some lv -> (
            let le = translate_lval lv in
            let re = (
              (* if the callee is "malloc, alloc...", then we need to cast *)
              (* its type to the target's type *)
              match fname with
              | "malloc" -> (
                  (* let new_typ = translate_typ (typ_of_cil_lval lv) in                          *)
                  (* let _ = print_endline ("== new_typ = " ^ (Globals.string_of_typ new_typ)) in *)
                  (* let cast_proc = create_memory_cast_proc new_typ in                           *)
                  (* let casted_callee =                                                          *)
                  (*   Iast.CallNRecv {                                                           *)
                  (*     Iast.exp_call_nrecv_method = cast_proc.Iast.proc_name;                   *)
                  (*     Iast.exp_call_nrecv_lock = None;                                         *)
                  (*     Iast.exp_call_nrecv_arguments = [callee];                                *)
                  (*     Iast.exp_call_nrecv_path_id = None;                                      *)
                  (*     Iast.exp_call_nrecv_pos = pos                                            *)
                  (*   } in                                                                       *)
                  (* casted_callee                                                                *)
                  callee
                )
              | _ -> callee
            ) in
            let lv_loc = Cil.get_lvalLoc lv in
            let asgn_loc = Cil.makeLoc (Cil.startPos lv_loc) (Cil.endPos l) in
            let asgn_pos = translate_location asgn_loc in
            Iast.Assign {Iast.exp_assign_op = Iast.OpAssign;
                         Iast.exp_assign_lhs = le;
                         Iast.exp_assign_rhs = re;
                         Iast.exp_assign_path_id = None;
                         Iast.exp_assign_pos = asgn_pos}
          )
      )
    | Cil.Asm _ ->
        report_error_msg "TRUNG TODO: Handle Cil.Asm later!"
  ) in
  let collected_exps = !supplement_exp @ [translated_instr] in
  merge_iast_exp collected_exps


let rec translate_stmt (s: Cil.stmt) : Iast.exp =
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
      let retval = match eopt with
        | None -> None
        | Some e -> Some (translate_exp e) in
      let newexp = Iast.Return {Iast.exp_return_val = retval;
                                Iast.exp_return_path_id = None;
                                Iast.exp_return_pos = pos} in
      newexp
  | Cil.Goto (sref, l) ->
      (* detect a infinite loop in Goto statement *)
      let _ = print_endline ("== goto") in 
      if (!sref.Cil.sid = s.Cil.sid) then (
        let pos = translate_location l in
        let cond = Iast.BoolLit {Iast.exp_bool_lit_val = true;
                                 Iast.exp_bool_lit_pos = pos} in
        let infinite_loop = Iast.While {Iast.exp_while_condition = cond;
                                        Iast.exp_while_body = Iast.Empty pos;
                                        Iast.exp_while_specs = Iast.mkSpecTrue n_flow pos;
                                        Iast.exp_while_jump_label = Iast.NoJumpLabel;
                                        Iast.exp_while_path_id = None ;
                                        Iast.exp_while_f_name = "";
                                        Iast.exp_while_wrappings = None;
                                        Iast.exp_while_pos = pos} in
        infinite_loop
      )
      else translate_stmt !sref
  | Cil.Break l ->
      let pos = translate_location l in
      let newexp = Iast.Break {Iast.exp_break_jump_label = Iast.NoJumpLabel;
                               Iast.exp_break_path_id = None;
                               Iast.exp_break_pos = pos} in
      newexp
  | Cil.Continue l ->
      let pos = translate_location l in
      let newexp = Iast.Continue {Iast.exp_continue_jump_label = Iast.NoJumpLabel;
                                  Iast.exp_continue_path_id = None;
                                  Iast.exp_continue_pos = pos} in
      newexp
  | Cil.If (exp, blk1, blk2, l) ->
      let pos = translate_location l in
      let econd = translate_exp exp in
      let e1 = translate_block blk1 in
      let e2 = translate_block blk2 in
      let newexp = Iast.Cond {Iast.exp_cond_condition = econd;
                              Iast.exp_cond_then_arm = e1;
                              Iast.exp_cond_else_arm = e2;
                              Iast.exp_cond_path_id = None;
                              Iast.exp_cond_pos = pos} in
      newexp
  | Cil.Switch _ -> report_error_msg "TRUNG TODO: Handle Cil.Switch later!"
  | Cil.Loop (blk, hspecs, l, stmt_opt1, stmt_opt2) ->
      let p = translate_location l in
      let cond = Iast.BoolLit {Iast.exp_bool_lit_val = true;
                               Iast.exp_bool_lit_pos = p} in
      let body = translate_block blk in
      let newexp = Iast.While {Iast.exp_while_condition = cond;
                               Iast.exp_while_body = body;
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
      let newexp = Iast.Try {Iast.exp_try_block = e1;
                             Iast.exp_catch_clauses = [];
                             Iast.exp_finally_clause = [e2];
                             Iast.exp_try_path_id = None;
                             Iast.exp_try_pos = p} in
      newexp
  | Cil.TryExcept (blk1, (instrs, exp), blk2, l) ->
      let p = translate_location l in
      let e1 = translate_block blk1 in
      let e2 = translate_block blk2 in
      let newexp = Iast.Try {Iast.exp_try_block = e1;
                             (* TRUNG TODO: need to handle the catch_clause with parameter (instrs, exp) *)
                             Iast.exp_catch_clauses = [];
                             Iast.exp_finally_clause = [e2];
                             Iast.exp_try_path_id = None;
                             Iast.exp_try_pos = p} in
      newexp
  | Cil.HipStmt (iast_exp, l) -> iast_exp


and translate_block (blk: Cil.block): Iast.exp =
  let stmts = blk.Cil.bstmts in
  match stmts with
  | [] -> Iast.Empty no_pos
  | [s] -> translate_stmt s
  | _ -> (
      let collected_exps = ref [] in
      List.iter (fun s ->
        supplement_exp := []; (* reset supplement_exp before each times translate_stmt*)
        let newe = translate_stmt s in
        List.iter (fun se -> collected_exps := !collected_exps @ [se]) !supplement_exp;
        collected_exps := !collected_exps @ [newe]
      ) stmts;
      let blkbody = merge_iast_exp !collected_exps in
      let blkpos = translate_location (blk.Cil.bloc) in
      Iast.Block {Iast.exp_block_body = blkbody;
                  Iast.exp_block_jump_label = Iast.NoJumpLabel;
                  Iast.exp_block_local_vars = [];
                  Iast.exp_block_pos = blkpos}
    )


let translate_init (vname: ident) (init: Cil.init) (lopt: Cil.location option)
                   : (ident * Iast.exp option * loc) list =
  let pos = match lopt with None -> no_pos | Some l -> translate_location l in
  (* let _ = print_endline ("== init loc start lnum = " ^ (string_of_int pos.Globals.start_pos.Lexing.pos_lnum)) in *)
  (* let _ = print_endline ("== init loc start cnum = " ^ (string_of_int pos.Globals.start_pos.Lexing.pos_cnum)) in *)
  (* let _ = print_endline ("== init loc start bol = " ^ (string_of_int pos.Globals.start_pos.Lexing.pos_bol)) in   *)
  match init with
  | Cil.SingleInit exp ->
      let e = translate_exp exp in
      [(vname, Some e, pos)]
  | Cil.CompoundInit (_, offset_init_list) -> (
      List.map (fun x ->
        let off, ini = x in
        let name = match off with
          | Cil.NoOffset -> report_error_msg "TRUNG TODO: translate_init: handle Cil.NoOffset later!"
          | Cil.Field ((f, _), o, _) -> (
              match o with
              | Cil.NoOffset -> f.Cil.fname
              | Cil.Field _ -> report_error_msg "TRUNG TODO: translate_init: handle Cil.Field later!"
              | Cil.Index _ -> report_error_msg "TRUNG TODO: translate_init: handle Cil.Index later! 1"
            )
          | Cil.Index _ -> report_error_msg "TRUNG TODO:  translate_init: handle Cil.Index later! 2" in
        let exp = match ini with
          | Cil.SingleInit e -> translate_exp e
          | Cil.CompoundInit _ -> report_error_msg "TRUNG TODO:  translate_init: handle Cil.CompoundInit later!" in
        (name, Some exp, pos)
      ) offset_init_list
    )


let translate_global_var (vinfo: Cil.varinfo) (iinfo: Cil.initinfo) (lopt: Cil.location option)
                         : Iast.exp_var_decl =
  let pos = match lopt with None -> no_pos | Some l -> translate_location l in
  let ty = translate_typ vinfo.Cil.vtype in
  let name = vinfo.Cil.vname in
  let decl = match iinfo.Cil.init with
    | None -> [(name, None, pos)]
    | Some init -> translate_init name init lopt in
  let vardecl = {Iast.exp_var_decl_type = ty;
                 Iast.exp_var_decl_decls = decl;
                 Iast.exp_var_decl_pos = pos} in
  vardecl


let translate_fundec (fundec: Cil.fundec) (lopt: Cil.location option)
                     : Iast.proc_decl =
  (* reset some local setting *)
  Hashtbl.clear lc_addressof_data;
  (* supporting functions *)
  let translate_funtyp (ty: Cil.typ) : Globals.typ = (
    match ty with
    | Cil.TFun (t, params, _, _) -> translate_typ t
    | _ -> report_error_msg "Error!!! Invalid type! Have to be TFun only."
  ) in
  let collect_params (fheader: Cil.varinfo) : Iast.param list = (
    let ftyp = fheader.Cil.vtype in
    let pos = translate_location fheader.Cil.vdecl in
    match ftyp with
    | Cil.TFun (_, p, _, _) -> (
        let params = Cil.argsToList p in
        let translate_one_param (p : string * Cil.typ * Cil.attributes) : Iast.param = (
          let (name, ty, attrs) = p in
          let (ptyp, pmod) = match ty with
            | Cil.TPtr (ty0, _) -> (translate_typ ty0, Iast.RefMod) 
            | _ -> (translate_typ ty, Iast.NoMod) in
          let newparam = {Iast.param_type = ptyp;
                          Iast.param_name = name;
                          Iast.param_mod = pmod;
                          Iast.param_loc = pos; } in
          newparam
        ) in
        List.map translate_one_param params
      )
    | _ -> report_error_msg "Invalid function header!"
  ) in
  
  (* start translating function *)
  let pos = match lopt with None -> no_pos | Some l -> translate_location l in
  let fheader = fundec.Cil.svar in
  let name = fheader.Cil.vname in
  let mingled_name = "" in (* TRUNG TODO: check mingled_name later *)
  let static_specs = fundec.Cil.sspecs in
  let return = translate_funtyp (fheader.Cil.vtype) in
  let args = collect_params fheader in
  let funbody = (
    match fundec.Cil.sbody.Cil.bstmts with
    | [] -> None
    | _ ->
        let slocals = List.map translate_var_decl fundec.Cil.slocals in
        let sbody = translate_block fundec.Cil.sbody in
        (* collect intermediate information after translating body *) 
        let supplement_local_vars = (
          let vars = ref [] in
          Hashtbl.iter (fun _ e -> vars := !vars @ [e]) lc_addressof_data;
          !vars;
        ) in
        let blkbody = merge_iast_exp (slocals @ supplement_local_vars @ [sbody]) in
        let blkpos = translate_location fundec.Cil.sbody.Cil.bloc in
        Some (Iast.Block {Iast.exp_block_body = blkbody;
                          Iast.exp_block_jump_label = Iast.NoJumpLabel;
                          Iast.exp_block_local_vars = [];
                          Iast.exp_block_pos = blkpos})
  ) in
  let filename = pos.start_pos.Lexing.pos_fname in
  let newproc : Iast.proc_decl = {
    Iast.proc_name = name;
    Iast.proc_mingled_name = mingled_name;
    Iast.proc_data_decl = None;
    Iast.proc_constructor = false;
    Iast.proc_args = args;
    Iast.proc_source = ""; (* WN : need to change *)
    Iast.proc_return = return;
    Iast.proc_static_specs = static_specs;
    Iast.proc_dynamic_specs = Iformula.mkEFalseF ();
    Iast.proc_exceptions = [];
    Iast.proc_body = funbody;
    Iast.proc_is_main = true;
    Iast.proc_file = filename;
    Iast.proc_loc = pos;
    Iast.proc_test_comps = None;
  } in
  newproc


let translate_file (file: Cil.file) : Iast.prog_decl =
  (* initial values *)
  let data_decls : Iast.data_decl list ref = ref [] in
  let global_var_decls : Iast.exp_var_decl list ref = ref [] in
  let logical_var_decls : Iast.exp_var_decl list ref = ref [] in
  let enum_decls : Iast.enum_decl list ref = ref [] in
  let view_decls : Iast.view_decl list ref = ref [] in
  let func_decls : Iast.func_decl list ref = ref [] in
  let rel_decls : Iast.rel_decl list ref = ref [] in
  let rel_ids : (typ * ident) list ref = ref [] in
  let axiom_decls : Iast.axiom_decl list ref = ref [] in
  let hopred_decls : Iast.hopred_decl list ref = ref [] in
  let proc_decls : Iast.proc_decl list ref = ref [] in
  let barrier_decls : Iast.barrier_decl list ref = ref [] in
  let coercion_decls : Iast.coercion_decl list ref = ref [] in
  (* begin to translate *)
  let globals = file.Cil.globals in
  List.iter (fun gl ->
    match gl with
    | Cil.GType _ ->
        (* let _ = print_endline ("== gl GType = " ^ (string_of_cil_global gl)) in *)
        ()
    | Cil.GCompTag (comp, l) ->
        (* let _ = print_endline ("== gl GCompTag = " ^ (string_of_cil_global gl)) in *)
        let datadecl = translate_compinfo comp (Some l) in
        data_decls := !data_decls @ [datadecl]
    | Cil.GCompTagDecl _ ->
        (* let _ = print_endline ("== gl GCompTagDecl = " ^ (string_of_cil_global gl)) in *)
        ()
        (* report_error_msg "TRUNG TODO: Handle Cil.GCompTagDecl later!" *)
    | Cil.GEnumTag _ ->
        (* let _ = print_endline ("== gl GEnumTag = " ^ (string_of_cil_global gl)) in *)
        (* ()                                                                         *)
        report_error_msg "TRUNG TODO: Handle Cil.GEnumTag later!"
    | Cil.GEnumTagDecl _ ->
        (* let _ = print_endline ("== gl GEnumTagDecl = " ^ (string_of_cil_global gl)) in *)
        (* ()                                                                             *)
        report_error_msg "TRUNG TODO: Handle Cil.GEnumTagDecl later!"
    | Cil.GVarDecl (v, l) -> ()
        (* let _ = print_endline ("== gl GVarDecl = " ^ (string_of_cil_global gl)) in *)
        (* report_error_msg "TRUNG TODO: Handle Cil.GVarDecl later!"                  *)
    | Cil.GVar (v, init, l) ->
        (* let _ = print_endline ("== translate_file: collect GVar") in *)
        let gvar = translate_global_var v init (Some l) in
        global_var_decls := !global_var_decls @ [gvar];
    | Cil.GFun (fd, l) ->
        (* let _ = print_endline ("== gl GFun = " ^ (string_of_cil_global gl)) in *)
        let proc = translate_fundec fd (Some l) in
        proc_decls := !proc_decls @ [proc]
    | Cil.GAsm _ ->
        (* let _ = print_endline ("== gl GAsm = " ^ (string_of_cil_global gl)) in *)
        ()
        (* report_error_msg "TRUNG TODO: Handle Cil.GAsm later!" *)
    | Cil.GPragma _ ->
        (* let _ = print_endline ("== gl GPragma = " ^ (string_of_cil_global gl)) in *)
        (* ()                                                                         *)
        report_error_msg "TRUNG TODO: Handle Cil.GPragma later!"
    | Cil.GText _ ->
        let _ = print_endline ("== gl GText = " ^ (string_of_cil_global gl)) in
        ()
        (* report_error_msg "TRUNG TODO: Handle Cil.GText later!" *)
  ) globals;
  let obj_def = {Iast.data_name = "Object";
                 Iast.data_fields = [];
                 Iast.data_parent_name = "";
                 Iast.data_invs = [];
                 Iast.data_is_template = false;
                 Iast.data_methods = []} in
  let string_def = {Iast.data_name = "String";
                    Iast.data_fields = [];
                    Iast.data_parent_name = "Object";
                    Iast.data_invs = [];
                    Iast.data_is_template = false;
                    Iast.data_methods = []} in
  (* update some global settings *)
  Hashtbl.iter (fun _ data -> data_decls := !data_decls @ [data]) tbl_data_decl;
  Hashtbl.iter (fun _ var ->
    match var with
    | Iast.VarDecl vdecl -> global_var_decls := !global_var_decls @ [vdecl]
    | _ -> report_error_msg "Error!!! v has to be in form of (Iast.VarDecl _)."
  ) gl_addressof_data;
  Hashtbl.iter (fun _ proc -> proc_decls := !proc_decls @ [proc]) tbl_cast_procs;
  let newprog : Iast.prog_decl = ({
    Iast.prog_data_decls = obj_def :: string_def :: !data_decls;
    Iast.prog_include_decls = []; (*WN : need to fill *)
    Iast.prog_global_var_decls = !global_var_decls;
    Iast.prog_logical_var_decls = !logical_var_decls;
    Iast.prog_enum_decls = !enum_decls;
    Iast.prog_view_decls = !view_decls;
    Iast.prog_func_decls = !func_decls;
    Iast.prog_rel_decls = !rel_decls;
    Iast.prog_rel_ids = !rel_ids;
    Iast.prog_axiom_decls = !axiom_decls;
    Iast.prog_hopred_decls = !hopred_decls;
    Iast.prog_proc_decls = !proc_decls;
    Iast.prog_barrier_decls = !barrier_decls;
    Iast.prog_coercion_decls = !coercion_decls;
    Iast.prog_hp_decls = [];
    Iast.prog_hp_ids = [];
  }) in
  newprog
(* ---   end of translation   --- *)


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
  let _ = print_endline ("------------------------") in
  let _ = print_endline ("--> translated program: ") in
  let _ = print_endline ("------------------------") in 
  let _ = print_endline (Iprinter.string_of_program prog) in 
  ()


let parse_hip (filename: string) : Iast.prog_decl =
  let cil = parse_one_file filename in
  if !Cilutil.doCheck then (
    ignore (Errormsg.log "First CIL check\n");
    if not (Check.checkFile [] cil) && !Cilutil.strictChecking then (
      Errormsg.bug ("CIL's internal data structures are inconsistent "
                    ^^"(see the warnings above).  This may be a bug "
                    ^^"in CIL.\n")
    )
  );
  let prog = translate_file cil in
  (* return *)
  prog
