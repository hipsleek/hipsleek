open Globals
open Error
open Exc.GTable

(* --------------------- *)
(* Global variables      *)
(* --------------------- *)

(* hash table contains Globals.typ structures that are used to represent Cil.typ pointers *)
let tbl_pointer_typ : (Cil.typ, Globals.typ) Hashtbl.t = Hashtbl.create 3

(* hash table contains Iast.data_decl structures that are used to represent pointer types *)
let tbl_pointer_data_decl : (Globals.typ, Iast.data_decl) Hashtbl.t = Hashtbl.create 3

(* hash table contains Iast.data_decl structures that are used to represent pointer types *)
let tbl_struct_data_decl : (Globals.typ, Iast.data_decl) Hashtbl.t = Hashtbl.create 1

(* hash table map between a lval (in string form) and a pointer to its address *)
let tbl_addrof_lval : (string, Iast.exp) Hashtbl.t = Hashtbl.create 3

(* list of address-represented pointer declaration *)
let ls_addr_pointer_vardecl : Iast.exp list ref = ref []

let need_pointer_casting_proc : bool ref = ref false

let need_not_operator_proc : bool ref = ref false


(* reset all global vars for the next use *)
let reset_global_vars () =
  Hashtbl.clear tbl_pointer_typ;
  Hashtbl.clear tbl_pointer_data_decl

(*******************************************************)
(*         string conversion functions for CIL         *)
(*******************************************************)
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

(**********************************************)
(****** create intermediate procedures  *******)
(**********************************************)

let create_pointer_casting_proc (pointer_typ: Globals.typ) : Iast.proc_decl option =
  match pointer_typ with
  | Globals.Named "void__star" -> None
  | Globals.Named typ_name -> (
      let re = Str.regexp "\(__star\)" in
      try (
        let _ = Str.search_forward re typ_name 0 in
        let proc_name = "cast_void_pointer_to_" ^ typ_name in
        let data_name = Str.global_replace re "^" typ_name in
        let param = (
          let base_data = Str.global_replace re "" typ_name in
          match base_data with
          | "int" -> "<_>"
          | "bool" -> "<_>"
          | "float" -> "<_>"
          | "void" -> "<_>"
          | _ -> (
              try 
                let data_decl = Hashtbl.find tbl_struct_data_decl (Globals.Named base_data) in
                match data_decl.Iast.data_fields with
                | []   -> report_error_msg "Error: Invalid data_decl fields"
                | [hd] -> "<_>"
                | hd::tl -> "<" ^ (List.fold_left (fun s _ -> s ^ ",_") "_" tl) ^ ">"
              with Not_found -> report_error_msg ("Error: Unknown data type: " ^ base_data)
            ) 
        ) in
        let cast_proc = (
          typ_name ^ " " ^ proc_name ^ " (void__star p)\n" ^
          "  case { \n" ^
          "    p =  null -> requires true ensures res = null; \n" ^
          "    p != null -> requires true ensures res::" ^ data_name ^ param ^ "; \n" ^
          "  }\n"
        ) in
        let proc_decl = Parser.parse_c_aux_proc "inter_pointer_casting_proc" cast_proc in
        (* return *)
        Some proc_decl
      )
      with Not_found -> None
    )
  | _ -> None

let create_not_operator_proc (input_typ: Globals.typ) : Iast.proc_decl =
  match input_typ with
  | Globals.Named input_typ_name -> (
      let neg_proc = (
        "bool not___(" ^ input_typ_name ^ " param)\n" ^
        "  case { param =  null -> ensures res;\n" ^
        "         param != null -> ensures !res; }\n"
      ) in
      let proc_decl = Parser.parse_c_aux_proc "inter_negation_data_proc" neg_proc in
      proc_decl
    )
  | _ -> report_error_msg "Error: Invalid type"


(************************************************************)
(****** collect information about address-of operator *******)
(************************************************************)

let rec gather_addrof_info_stmt (stmt: Cil.stmt)  : unit =
  let skind = stmt.Cil.skind in
  match skind with
  | Cil.Instr ins -> List.iter gather_addrof_info_instr ins
  | Cil.Return (eopt, _) -> (
      match eopt with
      | None -> ()
      | Some e -> gather_addrof_info_exp e
    )
  | Cil.Goto (sref, _) -> report_error_msg "gather_addrof_info_stmt: handle GOTO later!"
  | Cil.Break _ -> ()
  | Cil.Continue _ -> ()
  | Cil.If (e, blk1, blk2, _) -> (
      gather_addrof_info_exp e;
      gather_addrof_info_block blk1;
      gather_addrof_info_block blk2;
    )
  | Cil.Switch (e, blk, stmts, _) -> (
      gather_addrof_info_exp e;
      gather_addrof_info_block blk;
      List.iter gather_addrof_info_stmt stmts;
    )
  | Cil.Loop (blk, _, _, stmt_opt1, stmt_opt2) -> (
      gather_addrof_info_block blk;
      (match stmt_opt1 with
        | None -> ()
        | Some stmt -> gather_addrof_info_stmt stmt);
      (match stmt_opt2 with
        | None -> ()
        | Some stmt -> gather_addrof_info_stmt stmt);
    )
  | Cil.Block blk -> gather_addrof_info_block blk
  | Cil.TryFinally (blk1, blk2, _) -> (
      gather_addrof_info_block blk1;
      gather_addrof_info_block blk2;
    )
  | Cil.TryExcept (blk1, (ins, e), blk2, l) -> (
      gather_addrof_info_block blk1;
      List.iter gather_addrof_info_instr ins;
      gather_addrof_info_exp e;
      gather_addrof_info_block blk2;
    )
  | Cil.HipStmtSpec (iast_exp, l) -> ()


and gather_addrof_info_block (blk: Cil.block) : unit =
  let stmts = blk.Cil.bstmts in
  List.iter gather_addrof_info_stmt stmts;


and gather_addrof_info_exp (e: Cil.exp) : unit =
  match e with
  | Cil.Const _ -> ()
  | Cil.Lval (lv, _) -> ()
  | Cil.SizeOf _ -> ()
  | Cil.SizeOfE _ -> ()
  | Cil.SizeOfStr _ -> ()
  | Cil.AlignOf _ -> ()
  | Cil.AlignOfE _ -> ()
  | Cil.UnOp (_, e1, _, _) -> gather_addrof_info_exp e1
  | Cil.BinOp (_, e1, e2, _, _) -> (
      gather_addrof_info_exp e1;
      gather_addrof_info_exp e2;
    )
  | Cil.Question (e1, e2, e3, _, _) -> (
      gather_addrof_info_exp e1;
      gather_addrof_info_exp e2;
      gather_addrof_info_exp e3;
    )
  | Cil.CastE (_, e, _) -> gather_addrof_info_exp e
  | Cil.AddrOf (lv, l) -> (
      let pos = translate_location l in
      let lv_str = string_of_cil_lval lv in
      try
        let _ = Hashtbl.find tbl_addrof_lval lv_str in ()
      with Not_found -> (
        let lv_ty = typ_of_cil_lval lv in
        let (datatyp, dataname, datadecl) = (
          try 
            let dtyp = Hashtbl.find tbl_pointer_typ lv_ty in
            let ddecl = Hashtbl.find tbl_pointer_data_decl dtyp in
            let dname = (
              match dtyp with
              | Globals.Named s -> s
              | _ -> report_error_msg "gather_addrof_info_exp: unexpected type!"
            ) in
            (dtyp, dname, ddecl)
          with Not_found -> (
            (* create new Globals.typ and Iast.data_decl, then update to a hash table *)
            let ftyp = translate_typ lv_ty in
            let fname = "pdata" in
            let dname = (Globals.string_of_typ ftyp) ^ "__star" in
            let dtyp = Globals.Named dname in
            Hashtbl.add tbl_pointer_typ lv_ty dtyp;
            let ddecl = {Iast.data_name = dname;
                         Iast.data_fields = [((ftyp, fname), no_pos, false, Iast.F_NO_ANN)];
                         Iast.data_parent_name = "Object";
                         Iast.data_invs = [];
                         Iast.data_is_template = false;
                         Iast.data_methods = [];} in
            Hashtbl.add tbl_pointer_data_decl dtyp ddecl;
            (dtyp, dname, ddecl)
          )
        ) in
        (* define new pointer var px that will be used to represent x: {x, &x} --> {*px, px} *)
        let vname = "addr_p_" ^ (string_of_int (Hashtbl.length tbl_addrof_lval)) in
        let init_params = List.fold_left (
          fun params field ->
            let ((ftyp, _), _, _, _) = field in
            let exp = (
              match ftyp with
              | Globals.Int -> Iast.IntLit { Iast.exp_int_lit_val = 0;
                                             Iast.exp_int_lit_pos = no_pos }
              | Globals.Bool -> Iast.BoolLit { Iast.exp_bool_lit_val = true;
                                               Iast.exp_bool_lit_pos = no_pos }
              | Globals.Float -> Iast.FloatLit { Iast.exp_float_lit_val = 0.;
                                                 Iast.exp_float_lit_pos = no_pos }
              | Globals.Named _ -> Iast.Null no_pos
              | _ -> report_error_msg ("Unexpected typ 1: " ^ (Globals.string_of_typ ftyp))
            ) in
            params @ [exp]
        ) [] datadecl.Iast.data_fields in
        let init_data = Iast.New { Iast.exp_new_class_name = dataname;
                                   Iast.exp_new_arguments = init_params;
                                   Iast.exp_new_pos = no_pos } in
        let decl = [(vname, Some init_data, pos)] in
        let vardecl = Iast.VarDecl {Iast.exp_var_decl_type = datatyp;
                                    Iast.exp_var_decl_decls = decl;
                                    Iast.exp_var_decl_pos = pos} in
        ls_addr_pointer_vardecl := !ls_addr_pointer_vardecl @ [vardecl];
        let holder_var = Iast.Var {Iast.exp_var_name = vname;
                                   Iast.exp_var_pos = pos} in
        Hashtbl.add tbl_addrof_lval lv_str holder_var;
      )
    )
  | Cil.StartOf (lv, _) -> ()


and gather_addrof_info_instr (instr: Cil.instr) : unit =
  match instr with
  | Cil.Set (_, e, _) -> gather_addrof_info_exp e
  | Cil.Call (_, _, es, _) -> List.iter gather_addrof_info_exp es;
  | Cil.Asm _ -> ()


and collect_addrof_exp (e: Cil.exp) : (Cil.lval * Iast.exp) list =
  let eq_lval (lv1, _) (lv2, _) = (
    let s1 = string_of_cil_lval lv1 in
    let s2 = string_of_cil_lval lv2 in
    s1 = s2
  ) in
  match e with
  | Cil.Const _ -> []
  | Cil.Lval _ -> []
  | Cil.SizeOf _ -> []
  | Cil.SizeOfE _ -> []
  | Cil.SizeOfStr _ -> []
  | Cil.AlignOf _ -> []
  | Cil.AlignOfE _ -> []
  | Cil.UnOp (_, e1, _, _) -> collect_addrof_exp e1
  | Cil.BinOp (_, e1, e2, _, _) -> (
      let r1 = collect_addrof_exp e1 in
      let r2 = collect_addrof_exp e2 in
      Gen.BList.remove_dups_eq eq_lval (r1 @ r2)
    )
  | Cil.Question (e1, e2, e3, _, _) -> (
      let r1 = collect_addrof_exp e1 in
      let r2 = collect_addrof_exp e2 in
      let r3 = collect_addrof_exp e3 in
      Gen.BList.remove_dups_eq eq_lval (r1 @ r2 @ r3)
    )
  | Cil.CastE (_, e, _) -> collect_addrof_exp e
  | Cil.AddrOf (lv, _) -> (
      let lv_str = string_of_cil_lval lv in
      let lv_holder = (
        try
          Hashtbl.find tbl_addrof_lval lv_str
        with Not_found ->
          report_error_msg ("collect_addrof_exp: lval holder of '" ^ lv_str ^ "' is not found.")
      ) in
      [lv, lv_holder]
    )
  | Cil.StartOf (lv, _) -> []

and collect_addrof_exp_list (exps: Cil.exp list) : (Cil.lval * Iast.exp) list =
  let eq_lval (lv1, _) (lv2, _) = (
    let s1 = string_of_cil_lval lv1 in
    let s2 = string_of_cil_lval lv2 in
    s1 = s2
  ) in
  let r = List.concat (List.map collect_addrof_exp exps) in
  Gen.BList.remove_dups_eq eq_lval r

(************************************************************)
(*************** main translation functions *****************)
(************************************************************)

and translate_location (loc: Cil.location) : Globals.loc =
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


and translate_typ (t: Cil.typ) : Globals.typ =
  let newtype = 
    match t with
    | Cil.TVoid _ -> Globals.Void
    | Cil.TInt _ -> Globals.Int
    | Cil.TFloat _ -> Globals.Float
    | Cil.TPtr (ty, _) -> (
        (* create a new Globals.typ and a new Iast.data_decl to represent the pointer data structure *)
        let newt = (
          (* find if this pointer was handled before or not *)
          try 
            Hashtbl.find tbl_pointer_typ ty
          with Not_found -> (
            match ty with
            | Cil.TNamed (tname, _) -> (
                (* unroll the pointer type to a defined type  *)
                let ftype = translate_typ tname.Cil.ttype in
                let fname = "pdata" in
                let data_name = tname.Cil.tname ^ "__star" in
                let data_type = Globals.Named data_name in
                Hashtbl.add tbl_pointer_typ ty data_type;
                let data_decl = {Iast.data_name = data_name;
                                 Iast.data_fields = [((ftype, fname), no_pos, false, Iast.F_NO_ANN)];
                                 Iast.data_parent_name = "Object";
                                 Iast.data_invs = [];
                                 Iast.data_is_template = false;
                                 Iast.data_methods = [];} in
                Hashtbl.add tbl_pointer_data_decl data_type data_decl;
                data_type
              )
            | _ -> (
                (* create new Globals.typ and Iast.data_decl update to hash tables *)
                let ftype = translate_typ ty in
                let fname = "pdata" in
                let data_name = (Globals.string_of_typ ftype) ^ "__star" in
                let data_type = Globals.Named data_name in
                Hashtbl.add tbl_pointer_typ ty data_type;
                let data_decl = {Iast.data_name = data_name;
                                 Iast.data_fields = [((ftype, fname), no_pos, false, Iast.F_NO_ANN)];
                                 Iast.data_parent_name = "Object";
                                 Iast.data_invs = [];
                                 Iast.data_is_template = false;
                                 Iast.data_methods = [];} in
                Hashtbl.add tbl_pointer_data_decl data_type data_decl;
                (* return new type*)
                data_type
              )
          )
        ) in
        newt
      )
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

and translate_var (vinfo: Cil.varinfo) (lopt: Cil.location option) : Iast.exp =
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


and translate_var_decl (vinfo: Cil.varinfo) : Iast.exp =
  let pos = translate_location vinfo.Cil.vdecl in
  let ty = translate_typ vinfo.Cil.vtype in
  let name = vinfo.Cil.vname in
  let newexp = (
    match ty with
    | Globals.Int
    | Globals.Bool
    | Globals.Float
    | Globals.Array _
    | Globals.Named "void__star" -> (
        Iast.VarDecl { Iast.exp_var_decl_type = ty;
                       Iast.exp_var_decl_decls = [(name, None, pos)];
                       Iast.exp_var_decl_pos = pos }
      )
    | Globals.Named typ_name -> (
        (* look for the corresponding data structure *)
        let data_decl = (
          try Hashtbl.find tbl_struct_data_decl ty
          with Not_found -> (
            try Hashtbl.find tbl_pointer_data_decl ty
            with Not_found -> report_error_msg ("Unfound typ: " ^ (Globals.string_of_typ ty))
          )
        ) in
        (* create and initiate a new object *)
        let init_params = List.fold_left (
          fun params field ->
            let ((ftyp, _), _, _, _) = field in
            let exp = (
              match ftyp with
              | Globals.Int -> Iast.IntLit { Iast.exp_int_lit_val = 0;
                                             Iast.exp_int_lit_pos = no_pos }
              | Globals.Bool -> Iast.BoolLit { Iast.exp_bool_lit_val = true;
                                               Iast.exp_bool_lit_pos = no_pos }
              | Globals.Float -> Iast.FloatLit { Iast.exp_float_lit_val = 0.;
                                                 Iast.exp_float_lit_pos = no_pos }
              | Globals.Named _ -> Iast.Null no_pos
              | _ -> report_error_msg ("Unexpected typ 1: " ^ (Globals.string_of_typ ftyp))
            ) in
            params @ [exp]
        ) [] data_decl.Iast.data_fields in
        let init_data = Iast.New { Iast.exp_new_class_name = typ_name;
                                   Iast.exp_new_arguments = init_params;
                                   Iast.exp_new_pos = no_pos } in
        Iast.VarDecl { Iast.exp_var_decl_type = ty;
                       Iast.exp_var_decl_decls = [(name, Some init_data, pos)];
                       Iast.exp_var_decl_pos = pos }
      )
    | _ -> report_error_msg ("Unexpected typ 2: " ^ (Globals.string_of_typ ty))
  ) in
  newexp


and translate_constant (c: Cil.constant) (lopt: Cil.location option) : Iast.exp =
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
and translate_fieldinfo (field: Cil.fieldinfo) (lopt: Cil.location option) 
                        : (Iast.typed_ident * loc * bool * Iast.data_field_ann) =
  let pos = match lopt with None -> no_pos | Some l -> translate_location l in
  let name = field.Cil.fname in
  match field.Cil.ftype with
  | Cil.TComp (comp, _) ->
      let ty = Globals.Named comp.Cil.cname in
      ((ty, name), pos, false, Iast.F_NO_ANN)
  | _ ->
      let ty = translate_typ field.Cil.ftype in
      ((ty, name), pos, false, Iast.F_NO_ANN)


and translate_compinfo (comp: Cil.compinfo) (lopt: Cil.location option) : Iast.data_decl =
  let name = comp.Cil.cname in
  let fields = List.map (fun x -> translate_fieldinfo x lopt) comp.Cil.cfields in
  let datadecl = {Iast.data_name = name;
                  Iast.data_fields = fields;
                  Iast.data_parent_name = "Object";
                  Iast.data_invs = [];
                  Iast.data_is_template = false;
                  Iast.data_methods = [];} in
  Hashtbl.add tbl_struct_data_decl (Globals.Named name) datadecl;
  datadecl


and translate_unary_operator (op : Cil.unop) : Iast.uni_op =
  match op with
  | Cil.Neg -> Iast.OpUMinus
  | Cil.BNot -> report_error_msg "Error!!! Iast doesn't support BNot (bitwise complement) operator!"
  | Cil.LNot -> Iast.OpNot


and translate_binary_operator (op : Cil.binop) : Iast.bin_op =
  match op with
  | Cil.PlusA -> Iast.OpPlus
  | Cil.PlusPI -> Iast.OpPlus
  | Cil.IndexPI -> Iast.OpPlus
  | Cil.MinusA -> Iast.OpMinus
  | Cil.MinusPI -> Iast.OpMinus
  | Cil.MinusPP -> Iast.OpMinus
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


and translate_lval (lv: Cil.lval) : Iast.exp =
  let (lhost, offset, loc) = lv in
  let pos = translate_location loc in
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
  | Cil.Var (v, l), Cil.NoOffset -> (
      let newexp = translate_var v (Some l) in
      newexp
    )
  | Cil.Var (v, l), Cil.Index _ -> (
      let base = translate_var v (Some l) in
      let index = collect_index offset in
      let newexp = Iast.ArrayAt {Iast.exp_arrayat_array_base = base;
                                 Iast.exp_arrayat_index = index;
                                 Iast.exp_arrayat_pos = pos} in
      newexp
    )
  | Cil.Var (v, l), Cil.Field _ -> (
      let base = translate_var v (Some l) in
      let fields = collect_field offset in
      let newexp = Iast.Member {Iast.exp_member_base = base;
                                Iast.exp_member_fields = fields;
                                Iast.exp_member_path_id = None;
                                Iast.exp_member_pos = pos} in
      newexp
    )
  | Cil.Mem e, Cil.NoOffset -> (
      (* access to data in pointer variable *)
      let base = translate_exp e in
      let fields = ["pdata"] in
      let newexp = Iast.Member {Iast.exp_member_base = base;
                                Iast.exp_member_fields = fields;
                                Iast.exp_member_path_id = None;
                                Iast.exp_member_pos = pos} in
      newexp
    )
  | Cil.Mem e, Cil.Index _ -> (
      let data_base = translate_exp e  in
      let data_fields = ["pdata"] in
      let array_base = Iast.Member {Iast.exp_member_base = data_base;
                                    Iast.exp_member_fields = data_fields;
                                    Iast.exp_member_path_id = None;
                                    Iast.exp_member_pos = pos} in
      let array_index = collect_index offset in
      let newexp = Iast.ArrayAt {Iast.exp_arrayat_array_base = array_base;
                                 Iast.exp_arrayat_index = array_index;
                                 Iast.exp_arrayat_pos = pos} in
      newexp
    )
  | Cil.Mem e, Cil.Field _ -> (
      let data_base = translate_exp e  in
      let data_fields = ["pdata"] in
      let member_base = Iast.Member {Iast.exp_member_base = data_base;
                                     Iast.exp_member_fields = data_fields;
                                     Iast.exp_member_path_id = None;
                                     Iast.exp_member_pos = pos} in
      let member_fields = collect_field offset in
      let newexp = Iast.Member {Iast.exp_member_base = member_base;
                                Iast.exp_member_fields = member_fields;
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
      let t = translate_typ ty in
      if (o = Iast.OpNot) then (
        match t with
        | Globals.Named _ -> need_not_operator_proc := true;
        | _ -> ();
      );
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
  | Cil.CastE (ty, exp, l) -> (
      let pos = translate_location l in
      let output_typ = translate_typ ty in
      let input_exp = translate_exp exp in
      match input_exp with
      | Iast.Null _ -> input_exp
      | _ -> (
          let input_typ = translate_typ (typ_of_cil_exp exp) in
          match input_typ, output_typ with
          | Globals.Named "void__star", Globals.Named output_typ_name -> (
              need_pointer_casting_proc := true;
              let cast_proc_name = "cast_void_pointer_to_" ^ output_typ_name in
              Iast.CallNRecv {
                Iast.exp_call_nrecv_method = cast_proc_name;
                Iast.exp_call_nrecv_lock = None;
                Iast.exp_call_nrecv_arguments = [input_exp];
                Iast.exp_call_nrecv_path_id = None;
                Iast.exp_call_nrecv_pos = pos
              }
            )
          | _ -> input_exp
        )
    )
  | Cil.AddrOf (lv, l) ->
      let lv_str = string_of_cil_lval lv in
      let lv_holder = (
        try
          Hashtbl.find tbl_addrof_lval lv_str
        with Not_found ->
          report_error_msg ("translate_exp: lval holder of '" ^ lv_str ^ "' is not found.")
      ) in
      lv_holder
  | Cil.StartOf _ -> report_error_msg "translate_exp: Iast doesn't support Cil.StartOf exp!"


and translate_instr (instr: Cil.instr) : Iast.exp =
  (* detect address-of operator *)
  let new_exp = (match instr with
    | Cil.Set (lv, exp, l) -> (
        let pos = translate_location l in
        let addrof_exp_info = collect_addrof_exp exp in
        let aux_exps_before = List.map (
          fun e ->
            let lv, lv_holder = e in
            let exp1 = Iast.Member {Iast.exp_member_base = lv_holder;
                                    Iast.exp_member_fields = ["pdata"];
                                    Iast.exp_member_path_id = None;
                                    Iast.exp_member_pos = pos} in
            let exp2 = translate_lval lv in
            let exp3 = Iast.Assign {Iast.exp_assign_op = Iast.OpAssign;
                                    Iast.exp_assign_lhs = exp1;
                                    Iast.exp_assign_rhs = exp2;
                                    Iast.exp_assign_path_id = None;
                                    Iast.exp_assign_pos = pos} in
            exp3
        ) addrof_exp_info in
        let le = translate_lval lv in
        let re = translate_exp exp in
        let set_exp = Iast.Assign {Iast.exp_assign_op = Iast.OpAssign;
                                   Iast.exp_assign_lhs = le;
                                   Iast.exp_assign_rhs = re;
                                   Iast.exp_assign_path_id = None;
                                   Iast.exp_assign_pos = pos} in
        let aux_exps_after = List.map (
          fun e ->
            let lv, lv_holder = e in
            let exp1 = translate_lval lv in
            let exp2 = Iast.Member {Iast.exp_member_base = lv_holder;
                                    Iast.exp_member_fields = ["pdata"];
                                    Iast.exp_member_path_id = None;
                                    Iast.exp_member_pos = pos} in
            let exp3 = Iast.Assign {Iast.exp_assign_op = Iast.OpAssign;
                                    Iast.exp_assign_lhs = exp1;
                                    Iast.exp_assign_rhs = exp2;
                                    Iast.exp_assign_path_id = None;
                                    Iast.exp_assign_pos = pos} in
            exp3
        ) addrof_exp_info in
        merge_iast_exp (aux_exps_before @ [set_exp] @ aux_exps_after)
      )
    | Cil.Call (lv_opt, exp, exps, l) -> (
        let pos = translate_location l in
        let fname = match exp with
          | Cil.Const (Cil.CStr s, _) -> s
          | Cil.Lval ((Cil.Var (v, _), _, _), _) -> v.Cil.vname
          | _ -> report_error_msg "translate_intstr: invalid callee's name!" in
        let addrof_exp_info = collect_addrof_exp_list exps in
        let aux_exps_before = List.map (
          fun e ->
            let lv, lv_holder = e in
            let exp1 = Iast.Member {Iast.exp_member_base = lv_holder;
                                    Iast.exp_member_fields = ["pdata"];
                                    Iast.exp_member_path_id = None;
                                    Iast.exp_member_pos = pos} in
            let exp2 = translate_lval lv in
            let exp3 = Iast.Assign {Iast.exp_assign_op = Iast.OpAssign;
                                    Iast.exp_assign_lhs = exp1;
                                    Iast.exp_assign_rhs = exp2;
                                    Iast.exp_assign_path_id = None;
                                    Iast.exp_assign_pos = pos} in
            exp3
        ) addrof_exp_info in
        let args = List.map (fun x -> translate_exp x) exps in
        let callee = Iast.CallNRecv {Iast.exp_call_nrecv_method = fname;
                                     Iast.exp_call_nrecv_lock = None;
                                     Iast.exp_call_nrecv_arguments = args;
                                     Iast.exp_call_nrecv_path_id = None;
                                     Iast.exp_call_nrecv_pos = pos} in
        let call_exp = (
          match lv_opt with
          | None -> callee;
          | Some lv -> (
              let le = translate_lval lv in
              let re = callee in
              let lv_loc = Cil.get_lvalLoc lv in
              let asgn_loc = Cil.makeLoc (Cil.startPos lv_loc) (Cil.endPos l) in
              let asgn_pos = translate_location asgn_loc in
              Iast.Assign {Iast.exp_assign_op = Iast.OpAssign;
                           Iast.exp_assign_lhs = le;
                           Iast.exp_assign_rhs = re;
                           Iast.exp_assign_path_id = None;
                           Iast.exp_assign_pos = asgn_pos}
            )
        ) in
        let aux_exps_after = List.map (
          fun e ->
            let lv, lv_holder = e in
            let exp1 = translate_lval lv in
            let exp2 = Iast.Member {Iast.exp_member_base = lv_holder;
                                    Iast.exp_member_fields = ["pdata"];
                                    Iast.exp_member_path_id = None;
                                    Iast.exp_member_pos = pos} in
            let exp3 = Iast.Assign {Iast.exp_assign_op = Iast.OpAssign;
                                    Iast.exp_assign_lhs = exp1;
                                    Iast.exp_assign_rhs = exp2;
                                    Iast.exp_assign_path_id = None;
                                    Iast.exp_assign_pos = pos} in
            exp3
        ) addrof_exp_info in
        merge_iast_exp (aux_exps_before @ [call_exp] @ aux_exps_after)
      )
    | Cil.Asm _ ->
        report_error_msg "TRUNG TODO: Handle Cil.Asm later!"
  ) in
  new_exp
  (* let collected_exps = [new_exp] in *)
  (* merge_iast_exp collected_exps     *)

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
      let newexp = Iast.Return {Iast.exp_return_val = retval;
                                Iast.exp_return_path_id = None;
                                Iast.exp_return_pos = pos} in
      newexp
  | Cil.Goto (sref, l) -> report_error_msg "translate_stmt: handle GOTO later!"
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
  | Cil.HipStmtSpec (iast_exp, l) -> iast_exp


and translate_block (blk: Cil.block): Iast.exp =
  let stmts = blk.Cil.bstmts in
  match stmts with
  | [] -> Iast.Empty no_pos
  | [s] -> translate_stmt s
  | _ -> (
      let exps = List.map translate_stmt stmts in
      let blkbody = merge_iast_exp exps in
      let blkpos = translate_location (blk.Cil.bloc) in
      Iast.Block {Iast.exp_block_body = blkbody;
                  Iast.exp_block_jump_label = Iast.NoJumpLabel;
                  Iast.exp_block_local_vars = [];
                  Iast.exp_block_pos = blkpos}
    )


and translate_init (init: Cil.init) (lopt: Cil.location option) : Iast.exp =
  let pos = match lopt with
    | None -> no_pos
    | Some l -> translate_location l in
  match init with
  | Cil.SingleInit exp -> translate_exp exp
  | Cil.CompoundInit (typ, offset_init_list) -> (
      let newtyp = translate_typ typ in
      match newtyp with
      (* translate data structure *)
      | Globals.Named newtyp_name ->
          (* collect init fields and store in a hashtbl *)
          let tbl_fields_init = Hashtbl.create 1 in
          List.iter (fun x ->
            let off, init2 = x in
            let fname = match off with
              | Cil.NoOffset -> report_error_msg "translate_init: handle Cil.NoOffset later!"
              | Cil.Field ((f, _), Cil.NoOffset, _) -> f.Cil.fname
              | Cil.Field ((f, _), (Cil.Field _), _) -> report_error_msg "translate_init: handle Cil.Field later!"
              | Cil.Field ((f, _), (Cil.Index _), _) -> report_error_msg "translate_init: handle Cil.Index later!"
              | Cil.Index _ -> report_error_msg "translate_init: handle Cil.Index later!" in
            let fexp = translate_init init2 lopt in
            Hashtbl.add tbl_fields_init fname fexp;
          ) offset_init_list;
          (* init all fields of *)
          let data_decl = (
            try Hashtbl.find tbl_struct_data_decl newtyp
            with Not_found -> (
              try Hashtbl.find tbl_pointer_data_decl newtyp
              with Not_found ->
                report_error_msg ("translate_init: couldn't find typ - " ^ newtyp_name)
            )
          ) in
          let init_params = List.fold_left (
            fun params field ->
              let ((ftyp, fid), _, _, _) = field in
              let finit = (
                try Hashtbl.find tbl_fields_init fid
                with Not_found -> (
                  match ftyp with
                  | Globals.Int -> Iast.IntLit { Iast.exp_int_lit_val = 0;
                                                 Iast.exp_int_lit_pos = pos }
                  | Globals.Bool -> Iast.BoolLit { Iast.exp_bool_lit_val = true;
                                                   Iast.exp_bool_lit_pos = pos }
                  | Globals.Float -> Iast.FloatLit { Iast.exp_float_lit_val = 0.;
                                                     Iast.exp_float_lit_pos = pos }
                  | Globals.Named _ -> Iast.Null pos
                  | _ -> report_error_msg ("Unexpected typ 3: " ^ (Globals.string_of_typ ftyp))
                )
              ) in
              params @ [finit]
          ) [] data_decl.Iast.data_fields in
          let init_exp = Iast.New { Iast.exp_new_class_name = newtyp_name;
                                    Iast.exp_new_arguments = init_params;
                                    Iast.exp_new_pos = pos } in
          init_exp
      | _ -> report_error_msg ("translate_init: handle other type later - " 
                                ^ (Globals.string_of_typ newtyp))
    )


and translate_global_var (vinfo: Cil.varinfo) (iinfo: Cil.initinfo)
                         (lopt: Cil.location option)
                         : Iast.exp_var_decl =
  let pos = match lopt with None -> no_pos | Some l -> translate_location l in
  let ty = translate_typ vinfo.Cil.vtype in
  let name = vinfo.Cil.vname in
  let decl = (
    match iinfo.Cil.init with
    | None -> [(name, None, pos)]
    | Some init ->
        let init_exp = translate_init init lopt in
        [(name, Some init_exp, pos)]
  ) in
  let vardecl = {Iast.exp_var_decl_type = ty;
                 Iast.exp_var_decl_decls = decl;
                 Iast.exp_var_decl_pos = pos} in
  vardecl


and translate_fundec (fundec: Cil.fundec) (lopt: Cil.location option) : Iast.proc_decl =
  (* reset some local setting *)
  Hashtbl.clear tbl_addrof_lval;
  ls_addr_pointer_vardecl := [];
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
        let translate_one_param (p : string * Cil.typ * Cil.attributes) 
                                : Iast.param = (
          let (name, ty, _) = p in
          let typ = translate_typ ty in
          let newparam = {Iast.param_type = typ;
                          Iast.param_name = name;
                          Iast.param_mod = Iast.NoMod;
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
  let static_specs = fundec.Cil.hipfuncspec in
  let return = translate_funtyp (fheader.Cil.vtype) in
  let args = collect_params fheader in
  let funbody = (
    match fundec.Cil.sbody.Cil.bstmts with
    | [] -> None
    | _ ->
        let slocals = List.map translate_var_decl fundec.Cil.slocals in
        let _ = gather_addrof_info_block fundec.Cil.sbody in
        let sbody = translate_block fundec.Cil.sbody in
        (* collect intermediate information after translating body *) 
        let aux_local_vars = (
          let vars = ref [] in
          List.iter (fun v -> vars := !vars @ [v]) !ls_addr_pointer_vardecl;
          !vars;
        ) in
        let blkbody = merge_iast_exp (slocals @ aux_local_vars @ [sbody]) in
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
    Iast.proc_flags = [] ;
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

and merge_iast_prog (main_prog: Iast.prog_decl) (aux_prog: Iast.prog_decl) 
                    : Iast.prog_decl =
  let newprog : Iast.prog_decl = {
    Iast.prog_data_decls = main_prog.Iast.prog_data_decls
                           @ aux_prog.Iast.prog_data_decls;
    Iast.prog_include_decls = main_prog.Iast.prog_include_decls
                              @ aux_prog.Iast.prog_include_decls;
    Iast.prog_global_var_decls = main_prog.Iast.prog_global_var_decls
                                 @ aux_prog.Iast.prog_global_var_decls;
    Iast.prog_logical_var_decls = main_prog.Iast.prog_logical_var_decls
                                  @ aux_prog.Iast.prog_logical_var_decls;
    Iast.prog_enum_decls = main_prog.Iast.prog_enum_decls
                           @ aux_prog.Iast.prog_enum_decls;
    Iast.prog_view_decls = main_prog.Iast.prog_view_decls
                           @ aux_prog.Iast.prog_view_decls;
    Iast.prog_func_decls = main_prog.Iast.prog_func_decls
                           @ aux_prog.Iast.prog_func_decls;
    Iast.prog_rel_decls = main_prog.Iast.prog_rel_decls
                          @ aux_prog.Iast.prog_rel_decls;
    Iast.prog_rel_ids = main_prog.Iast.prog_rel_ids
                        @ aux_prog.Iast.prog_rel_ids;
    Iast.prog_axiom_decls = main_prog.Iast.prog_axiom_decls
                            @ aux_prog.Iast.prog_axiom_decls;
    Iast.prog_hopred_decls = main_prog.Iast.prog_hopred_decls
                             @ aux_prog.Iast.prog_hopred_decls;
    Iast.prog_proc_decls = main_prog.Iast.prog_proc_decls
                           @ aux_prog.Iast.prog_proc_decls;
    Iast.prog_barrier_decls = main_prog.Iast.prog_barrier_decls
                              @ aux_prog.Iast.prog_barrier_decls;
    Iast.prog_coercion_decls = main_prog.Iast.prog_coercion_decls
                               @ aux_prog.Iast.prog_coercion_decls;
    Iast.prog_hp_decls = main_prog.Iast.prog_hp_decls
                         @ aux_prog.Iast.prog_hp_decls;
    Iast.prog_hp_ids = main_prog.Iast.prog_hp_ids
                       @ aux_prog.Iast.prog_hp_ids;
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
  let axiom_decls : Iast.axiom_decl list ref = ref [] in
  let hopred_decls : Iast.hopred_decl list ref = ref [] in
  let proc_decls : Iast.proc_decl list ref = ref [] in
  let barrier_decls : Iast.barrier_decl list ref = ref [] in
  let coercion_decls : Iast.coercion_decl list ref = ref [] in
  let aux_progs : Iast.prog_decl list ref = ref [] in
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
    | Cil.GHipProgSpec (hipprog, _) ->
        aux_progs := !aux_progs @ [hipprog]
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
  Hashtbl.iter (fun _ data -> data_decls := !data_decls @ [data]) tbl_pointer_data_decl;
  (* create negation & casting procs for data structure *)
  Hashtbl.iter (fun typ _ ->
    if (!need_not_operator_proc) then (
      let neg_proc = create_not_operator_proc typ in
      proc_decls := !proc_decls @ [neg_proc];
    );
    if (!need_pointer_casting_proc) then (
      let cast_procs = (
        match create_pointer_casting_proc typ with
        | None -> []
        | Some proc -> [proc]
      ) in
      proc_decls := !proc_decls @ cast_procs
    )
  ) tbl_pointer_data_decl;
  (* return *)
  let newprog : Iast.prog_decl = {
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
                    ^^ "(see the warnings above).  This may be a bug "
                    ^^ "in CIL.\n")
    )
  );
  let prog = translate_file cil in
  (* return *)
  prog
