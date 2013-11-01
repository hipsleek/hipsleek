open Globals
open Exc.GTable
open Gen.Basic

module IF = Iformula

(* --------------------- *)
(* Global variables      *)
(* --------------------- *)

let tbl_typedef : (string, Cil.typ) Hashtbl.t = Hashtbl.create 1

(* hash table contains Globals.typ structures that are used to represent Cil.typ pointers *)
let tbl_pointer_typ : (Cil.typ, Globals.typ) Hashtbl.t = Hashtbl.create 1

(* hash table contains Iast.data_decl structures that are used to represent pointer types *)
let tbl_data_decl : (Globals.typ, Iast.data_decl) Hashtbl.t = Hashtbl.create 1

(* hash table map lval expressions (in string form) to their address holder generated-pointers *)
let tbl_addrof_info : (string, string) Hashtbl.t = Hashtbl.create 1

(* list of address-represented pointer declaration *)
let aux_local_vardecls : Iast.exp list ref = ref []

(* hashtbl contains all auxiliary procedures, proc_name -> proc_decl *)
let tbl_aux_proc: (string, Iast.proc_decl) Hashtbl.t = Hashtbl.create 1

(* reset all global vars for the next use *)
let reset_global_vars () =
  Hashtbl.clear tbl_pointer_typ;
  Hashtbl.clear tbl_data_decl

(*******************************************************)
(*         string conversion functions for CIL         *)
(*******************************************************)
let string_of_cil_exp (e: Cil.exp) : string =
  Pretty.sprint 10 (Cil.d_exp () e)

let string_of_cil_unop (e: Cil.unop) : string =
  Pretty.sprint 10 (Cil.d_unop () e)

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
  Pretty.sprint 10 (Cil.d_global () g)

let string_of_cil_file (f: Cil.file) : string =
  let globals = f.Cil.globals in
  String.concat "\n\n" (List.map (fun g -> string_of_cil_global g) globals)

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
        let newpos = {Globals.start_pos = posx.Globals.start_pos;
                      Globals.mid_pos = posy.Globals.mid_pos;
                      Globals.end_pos = posy.Globals.end_pos;} in
        Iast.mkSeq x y newpos
      ) hd tl


(* get type *)
let typ_of_cil_lval (lv: Cil.lval) : Cil.typ =
  Cil.typeOfLval lv

let typ_of_cil_exp (e: Cil.exp) : Cil.typ =
  Cil.typeOf e

let rec is_cil_struct_pointer (ty: Cil.typ) : bool = (
  match ty with
  | Cil.TPtr (Cil.TComp (comp, _), _) -> true
  | Cil.TPtr (ty, _) -> is_cil_struct_pointer ty
  | _ -> false
)

(* location  functions *)
let makeLocation (startPos: Lexing.position) (endPos: Lexing.position) : Globals.loc =
  let newloc = {Globals.start_pos = startPos;
                Globals.mid_pos = startPos;
                Globals.end_pos = endPos;} in
  newloc

let startPos (loc: Globals.loc) : Lexing.position =
  loc.Globals.start_pos

let endPos (loc: Globals.loc) : Lexing.position =
  loc.Globals.end_pos

(**********************************************)
(****** create intermediate procedures  *******)
(**********************************************)

let create_void_pointer_casting_proc (typ_name: string) : Iast.proc_decl =
  let proc_name = "cast_void_pointer_to_" ^ typ_name in
  let proc_decl = (
    try
      Hashtbl.find tbl_aux_proc proc_name
    with Not_found -> (
      let data_name, base_data = (
        let re = Str.regexp "\(_star\)" in
        try
          let _ = Str.search_forward re typ_name 0 in
          let dname = Str.global_replace re "^" typ_name in
          let bdata = Str.global_replace re "" typ_name in
          (dname, bdata)
        with Not_found -> (typ_name, typ_name)
      ) in
      let param = (
        match base_data with
        | "int" -> "<_>"
        | "bool" -> "<_>"
        | "float" -> "<_>"
        | "void" -> "<_>"
        | _ -> (
            try 
              let data_decl = Hashtbl.find tbl_data_decl (Globals.Named base_data) in
              match data_decl.Iast.data_fields with
              | []   -> report_error no_pos "create_void_pointer_casting_proc: Invalid data_decl fields"
              | [hd] -> "<_>"
              | hd::tl -> "<" ^ (List.fold_left (fun s _ -> s ^ ", _") "_" tl) ^ ">"
            with Not_found -> report_error no_pos ("create_void_pointer_casting_proc: Unknown data type: " ^ base_data)
          ) 
      ) in
      let cast_proc = (
        typ_name ^ " " ^ proc_name ^ " (void_star p)\n" ^
        "  case { \n" ^
        "    p =  null -> ensures res = null; \n" ^
        "    p != null -> requires p::memLoc<h,s> & h\n" ^ 
        "                 ensures res::" ^ data_name ^ param ^ " * res::memLoc<h,s> & h; \n" ^
        "  }\n"
      ) in
      let pd = Parser.parse_c_aux_proc "void_pointer_casting_proc" cast_proc in
      Hashtbl.add tbl_aux_proc proc_name pd;
      pd
    )
  ) in
  (* return *)
  proc_decl

let create_pointer_to_int_casting_proc (pointer_typ_name: string) : Iast.proc_decl =
  let proc_name = "cast_" ^ pointer_typ_name ^ "_to_int" in
  let proc_decl = (
    try
      Hashtbl.find tbl_aux_proc proc_name
    with Not_found -> (
      let cast_proc = (
        "int " ^ proc_name ^ " (" ^ pointer_typ_name ^ " p)\n" ^
        "  case { \n" ^
        "    p =  null -> ensures res = 0; \n" ^
        "    p != null -> ensures res != 0; \n" ^
        "  }\n"
      ) in
      let pd = Parser.parse_c_aux_proc "pointer_to_int_casting_proc" cast_proc in
      Hashtbl.add tbl_aux_proc proc_name pd;
      pd
    )
  ) in
  (* return *)
  proc_decl

let create_int_to_pointer_casting_proc (pointer_typ_name: string) : Iast.proc_decl =
  let proc_name = "cast_int_to_" ^ pointer_typ_name in
  let proc_decl = (
    try
      Hashtbl.find tbl_aux_proc proc_name
    with Not_found -> (
      let cast_proc = (
        pointer_typ_name ^ " " ^ proc_name ^ " (int p)\n" ^
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

let create_logical_not_proc (typ: Globals.typ) : Iast.proc_decl =
  let typ_name = Globals.string_of_typ typ in
  let proc_name = "not_" ^ typ_name ^ "___" in
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


let create_bool_casting_proc (typ: Globals.typ) : Iast.proc_decl =
  let typ_name = Globals.string_of_typ typ in
  let proc_name = "bool_of_" ^ typ_name ^ "___" in
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

(************************************************************)
(****** collect information about address-of operator *******)
(************************************************************)

let rec gather_addrof_fundec (fd: Cil.fundec) : unit =
  (* reset some local setting *)
  Hashtbl.clear tbl_addrof_info;
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
      let _ = gather_addrof_exp e in
      let _ = gather_addrof_block b1 in
      let _ = gather_addrof_block b2 in
      ()
  | Cil.Switch (_, _, _, l) -> ()
  | Cil.Loop (blk, _, _, stmt_opt1, stmt_opt2) -> (
      let _ = gather_addrof_block blk in
      let _ = (match stmt_opt1 with
        | None -> ()
        | Some s -> gather_addrof_stmt s
      ) in
      let _ = (match stmt_opt2 with
        | None -> ()
        | Some s -> gather_addrof_stmt s
      ) in ()
    )
  | Cil.Block blk -> gather_addrof_block blk
  | Cil.TryFinally (b1, b2, _) ->
      let _ = gather_addrof_block b1 in
      let _ = gather_addrof_block b2 in
      ()
  | Cil.TryExcept (b1, (is, e), b2, _) ->
      let _ = gather_addrof_block b1 in
      let _ = List.iter gather_addrof_instr is in
      let _ = gather_addrof_exp e in
      let _ = gather_addrof_block b2 in
      ()
  | Cil.HipStmt (iast_exp, l) -> ()

and gather_addrof_instr (i: Cil.instr) : unit =
  match i with
  | Cil.Set (_, e, _) -> gather_addrof_exp e
  | Cil.Call (_, e, es, _) ->
      let _ = gather_addrof_exp e in
      let _ = List.iter gather_addrof_exp es in
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
      let _ = gather_addrof_exp e1 in
      let _ = gather_addrof_exp e2 in
      ()
    )
  | Cil.Question (e1, e2, e3, _, _) -> (
      let _ = gather_addrof_exp e1 in
      let _ = gather_addrof_exp e2 in
      let _ = gather_addrof_exp e3 in
      ()
    )
  | Cil.CastE (_, e, _) -> gather_addrof_exp e
  | Cil.AddrOf (lv, l) -> (
      let pos = translate_location l in
      let lv_str = string_of_cil_lval lv in
      let lv_ty = typ_of_cil_lval lv in
      match lv_ty with
      | Cil.TComp _ -> ()
      | _ -> (
          try
            let _ = Hashtbl.find tbl_addrof_info lv_str in ()
          with Not_found -> (
            let refined_ty = (match lv_ty with
              | Cil.TPtr (ty, _) when (is_cil_struct_pointer lv_ty) -> ty      (* pointer to struct goes down 1 level *)
              | _ -> lv_ty
            ) in
            let deref_ty = translate_typ refined_ty pos in
            let (addr_dtyp, addr_dname, addr_ddecl) = (
              try 
                let dtyp = Hashtbl.find tbl_pointer_typ refined_ty in
                let ddecl = Hashtbl.find tbl_data_decl dtyp in
                let dname = (
                  match dtyp with
                  | Globals.Named s -> s
                  | _ -> report_error pos "gather_addrof_exp: unexpected type!"
                ) in
                (dtyp, dname, ddecl)
              with Not_found -> (
                (* create new Globals.typ and Iast.data_decl, then update to a hash table *)
                let ftyp = deref_ty in
                let fname = "deref" in
                let dfields = [((ftyp, fname), no_pos, false, Iast.F_NO_ANN)] in
                let dname = (Globals.string_of_typ ftyp) ^ "_star" in
                let dtyp = Globals.Named dname in
                Hashtbl.add tbl_pointer_typ refined_ty dtyp;
                let ddecl = Iast.mkDataDecl dname dfields "Object" [] false [] in
                Hashtbl.add tbl_data_decl dtyp ddecl;
                (dtyp, dname, ddecl)
              )
            ) in
            (* define new pointer var px that will be used to represent x: {x, &x} --> {*px, px} *)
            let addr_vname = "addr_" ^ lv_str in
            let addr_vdecl = (
              (* create and temporarily initiate a new object *)
              let init_params = [(translate_lval lv)] in
              let init_data = Iast.mkNew addr_dname init_params pos in
              Iast.mkVarDecl addr_dtyp [(addr_vname, Some init_data, pos)] pos
            ) in
            aux_local_vardecls := !aux_local_vardecls @ [addr_vdecl];
            Hashtbl.add tbl_addrof_info lv_str addr_vname;
          )
      )
    )
  | Cil.StartOf (lv, _) -> ()

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

and get_actual_cil_typ (t: Cil.typ) : Cil.typ = (
  let actual_typ = (
    match t with
    | Cil.TNamed (tinfo, _) -> get_actual_cil_typ tinfo.Cil.ttype
    | Cil.TComp (cinfo, _) -> (
	try
          let ty = Hashtbl.find tbl_typedef cinfo.Cil.cname in
          get_actual_cil_typ ty
        with _ -> t
      )
    | _ -> t
  ) in
  actual_typ
)

and translate_typ (t: Cil.typ) pos : Globals.typ =
  let newtype = 
    match t with
    | Cil.TVoid _ -> Globals.Void
    | Cil.TInt (Cil.IBool, _) -> Globals.Bool
    | Cil.TInt _ -> Globals.Int
    | Cil.TFloat _ -> Globals.Float
    | Cil.TPtr (ty, _) -> (
        let actual_ty = get_actual_cil_typ ty in
        (* create a new Globals.typ and a new Iast.data_decl to represent the pointer data structure *)
        let newt = (
          (* find if this pointer was handled before or not *)
          try 
            Hashtbl.find tbl_pointer_typ actual_ty
          with Not_found -> (
            (* create new Globals.typ and Iast.data_decl update to hash tables *)
            let ftyp = translate_typ actual_ty pos in
            let fname = "deref" in
            let dfields = [((ftyp, fname), no_pos, false, Iast.F_NO_ANN)] in
            let dname = (Globals.string_of_typ ftyp) ^ "_star" in
            let dtype = Globals.Named dname in
            Hashtbl.add tbl_pointer_typ actual_ty dtype;
            let ddecl = Iast.mkDataDecl dname dfields "Object" [] false [] in
            Hashtbl.add tbl_data_decl dtype ddecl;
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
       let ty = get_actual_cil_typ t in
       translate_typ ty pos
    | Cil.TComp (comp, _) -> Globals.Named comp.Cil.cname                          (* struct or union type*)
    | Cil.TEnum _ -> report_error pos "TRUNG TODO: handle TEnum later!"
    | Cil.TBuiltin_va_list _ -> report_error pos "TRUNG TODO: handle TBuiltin_va_list later!" in
  (* return *)
  newtype

and translate_var (vinfo: Cil.varinfo) (lopt: Cil.location option) : Iast.exp =
  let pos = match lopt with None -> no_pos | Some l -> translate_location l in
  let name = vinfo.Cil.vname in
  if (String.compare name "null" = 0) then
    (Iast.Null pos)
  else 
    (Iast.mkVar name pos)


and translate_var_decl (vinfo: Cil.varinfo) : Iast.exp =
  let vname = vinfo.Cil.vname in
  let pos = translate_location vinfo.Cil.vdecl in
  let ty = vinfo.Cil.vtype in
  let (new_ty, need_init) = (match ty with
    | Cil.TPtr (ty1, _) when (is_cil_struct_pointer ty) ->
        (translate_typ ty1 pos, false)                 (* heap allocated data *)
    | Cil.TComp _ -> (translate_typ ty pos, true)      (* stack allocated data *)
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
  | Cil.CChr _ -> report_error pos "TRUNG TODO: Handle Cil.CChr later!"
  | Cil.CReal (f, _, _) -> Iast.mkFloatLit f pos
  | Cil.CEnum _ -> report_error pos "TRUNG TODO: Handle Cil.CEnum later!"


(* translate a field of a struct                       *)
(*     return: field type * location * inline property *)
and translate_fieldinfo (field: Cil.fieldinfo) (lopt: Cil.location option) 
                        : (Iast.typed_ident * loc * bool * Iast.data_field_ann) =
  let pos = match lopt with None -> no_pos | Some l -> translate_location l in
  let name = field.Cil.fname in
  let ftyp = field.Cil.ftype in
  match ftyp with
  | Cil.TComp (comp, _) ->
      let ty = Globals.Named comp.Cil.cname in
      ((ty, name), pos, true, Iast.F_NO_ANN)                     (* struct ~~> inline data *)
  | Cil.TPtr (ty, _) ->
      let new_ty = (
        if (is_cil_struct_pointer ftyp) then translate_typ ty pos    (* pointer goes down 1 level *) 
        else translate_typ ftyp pos
      ) in
      ((new_ty, name), pos, false, Iast.F_NO_ANN)
  | _ ->
      let ty = translate_typ ftyp pos in
      ((ty, name), pos, false, Iast.F_NO_ANN)


and translate_compinfo (comp: Cil.compinfo) (lopt: Cil.location option) : unit =
  let name = comp.Cil.cname in
  let fields = List.map (fun x -> translate_fieldinfo x lopt) comp.Cil.cfields in
  let datadecl = Iast.mkDataDecl name fields "Object" [] false [] in
  Hashtbl.add tbl_data_decl (Globals.Named name) datadecl;


and translate_unary_operator (op : Cil.unop) pos : Iast.uni_op =
  match op with
  | Cil.Neg -> Iast.OpUMinus
  | Cil.BNot -> report_error pos "Error!!! Iast doesn't support BNot (bitwise complement) operator!"
  | Cil.LNot -> Iast.OpNot


and translate_binary_operator (op : Cil.binop) pos : Iast.bin_op =
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


and translate_lval (lv: Cil.lval) : Iast.exp =
  let _, _, l = lv in
  let pos = translate_location l in
  let lv_str = string_of_cil_lval lv in
  try 
    let addr_vname = Hashtbl.find tbl_addrof_info lv_str in
    let addr_var = Iast.mkVar addr_vname pos in
    Iast.mkMember addr_var ["deref"] None pos
  with Not_found -> (
    let (lhost, offset, loc) = lv in
    let pos = translate_location loc in
    let rec create_complex_exp (base : Iast.exp) (offset : Cil.offset) 
                               (found_fields : string list) pos
                               : Iast.exp = (
      match offset with
      | Cil.NoOffset -> (
          match found_fields with 
          | [] -> base
          | _ -> Iast.mkMember base found_fields None pos
        )
      | Cil.Field ((field, l1), off, _) ->
          let p = makeLocation (startPos pos) (endPos (translate_location l1)) in
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
          create_complex_exp new_base off [] pos
    ) in
    match lhost with
    | Cil.Var (v, l) ->
        let base = translate_var v (Some l) in
        let newexp = create_complex_exp base offset [] pos in
        newexp
    | Cil.Mem e ->
        (* access to data in pointer variable *)
        let base_typ = typ_of_cil_exp e in
        match base_typ with
        | Cil.TPtr (Cil.TComp _, _) ->
            let base = translate_exp e  in
            create_complex_exp base offset [] pos
        | _ -> (
            let data_base = translate_exp e  in
            let data_fields = ["deref"] in
            let base = Iast.mkMember data_base data_fields None pos in
            create_complex_exp base offset [] pos
          )
  )

and translate_exp (e: Cil.exp) : Iast.exp =
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
        match new_t with
        | Globals.Bool -> Iast.mkUnary o e None pos
        | _ -> (
            let not_proc = create_logical_not_proc new_t in
            let proc_name = not_proc.Iast.proc_name in
            Iast.mkCallNRecv proc_name None [e] None pos
          )
      ) in
      let target_typ = translate_typ ty pos in
      let newexp = Iast.mkCast target_typ unexp pos in 
      newexp
    )
  | Cil.BinOp (op, exp1, exp2, ty, l) ->
      let pos = translate_location l in
      let e1 = translate_exp exp1 in
      let e2 = translate_exp exp2 in
      let o = translate_binary_operator op pos in
      let binexp = Iast.mkBinary o e1 e2 None pos in
      let target_typ = translate_typ ty pos in
      let newexp = Iast.mkCast target_typ binexp pos in 
      newexp
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
        match ity with
        | Cil.TPtr (t, _) when (is_cil_struct_pointer ity) -> translate_typ t pos
        | _ -> translate_typ ity pos
      ) in
      let output_typ = (match ty with
        | Cil.TPtr (ty1, _) when (is_cil_struct_pointer ty) -> translate_typ ty1 pos
        | _ -> translate_typ ty pos
      ) in
      let input_exp = translate_exp exp in
      if (input_typ = output_typ) then
        (* no need casting *)
        input_exp
      else (
        (* do casting *)
        match output_typ, input_typ with
        | Globals.Named otyp_name, Globals.Named ityp_name -> (
            if (ityp_name = "void_star") then (
              let cast_proc = create_void_pointer_casting_proc otyp_name in
              Iast.mkCallNRecv cast_proc.Iast.proc_name None [input_exp] None pos
            )
            else 
              report_error pos ("translate_exp: couldn't cast type 1: " ^ ityp_name ^ " to " ^ otyp_name)
          )
        | Globals.Named otyp_name, Globals.Int -> (
            let cast_proc = create_int_to_pointer_casting_proc otyp_name in
            Iast.mkCallNRecv cast_proc.Iast.proc_name None [input_exp] None pos
          )
        | Globals.Int, Globals.Named ityp_name -> (
            let cast_proc = create_pointer_to_int_casting_proc ityp_name in
            Iast.mkCallNRecv cast_proc.Iast.proc_name None [input_exp] None pos
          )
        | _ -> report_error pos ("translate_exp: couldn't cast type 2: " ^ (Globals.string_of_typ input_typ) 
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
            let addr_vname = Hashtbl.find tbl_addrof_info lv_str in
            Iast.mkVar addr_vname pos
          with Not_found ->
            report_error pos ("translate_exp: addr var of '" ^ lv_str ^ "' is not found.")
        )
    )
  | Cil.StartOf (lv, l) -> translate_lval lv


and translate_instr (instr: Cil.instr) : Iast.exp =
  (* detect address-of operator *)
  match instr with
  | Cil.Set (lv, exp, l) -> (
      let pos = translate_location l in
      let le = translate_lval lv in
      let re = translate_exp exp in
      (Iast.mkAssign Iast.OpAssign le re None pos)
    )
  | Cil.Call (lv_opt, exp, exps, l) -> (
      let pos = translate_location l in
      let fname = match exp with
        | Cil.Const (Cil.CStr s, _) -> s
        | Cil.Lval ((Cil.Var (v, _), _, _), _) -> v.Cil.vname
        | _ -> report_error pos "translate_intstr: invalid callee's name!" in
      let args = List.map (fun x -> translate_exp x) exps in
      let func_call = Iast.mkCallNRecv fname None args None pos in (
        match lv_opt with
        | None -> func_call
        | Some lv ->
            let le = translate_lval lv in
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
        match new_ty with
        | Globals.Bool -> translate_exp exp
        | _ -> (
            let e = translate_exp exp in
            let bool_of_proc = create_bool_casting_proc new_ty in
            let proc_name = bool_of_proc.Iast.proc_name in
            Iast.mkCallNRecv proc_name None [e] None pos
          )
      ) in
      let e1 = translate_block blk1 in
      let e2 = translate_block blk2 in
      let ifexp = Iast.mkCond cond e1 e2 None pos in
      ifexp
  | Cil.Switch (_, _, _, l) ->
      let pos = translate_location l in
      report_error pos "TRUNG TODO: Handle Cil.Switch later!"
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
      (* let p = translate_location l in *)
      (* translate_hip_stmt iast_exp p   *)
      iast_exp

(* and translate_hip_stmt (stmt: Iast.exp) pos : Iast.exp =                                    *)
(*   let rec helper_formula (f: IF.formula): IF.formula = (                                    *)
(*     match f with                                                                            *)
(*     | IF.Base fb ->                                                                         *)
(*         IF.Base { fb with                                                                   *)
(*           IF.formula_base_heap = helper_h_formula fb.IF.formula_base_heap;                  *)
(*           IF.formula_base_pure = helper_pure_formula fb.IF.formula_base_pure;               *)
(*           IF.formula_base_and = List.map helper_one_formula fb.IF.formula_base_and;         *)
(*         }                                                                                   *)
(*     | IF.Exists fe ->                                                                       *)
(*         IF.Exists { fe with                                                                 *)
(*           IF.formula_exists_heap = helper_h_formula fe.formula_exists_heap;                 *)
(*           IF.formula_exists_pure = helper_pure_formula fe.IF.formula_exists_pure;           *)
(*           IF.formula_exists_and = List.map helper_one_formula fe.IF.formula_exists_and;     *)
(*         }                                                                                   *)
(*     | IF.Or fo ->                                                                           *)
(*         IF.Or { fo with                                                                     *)
(*           IF.formula_heap = helper_h_formula fe.formula_heap;                               *)
(*           IF.formula_pure = helper_pure_formula fe.IF.formula_pure;                         *)
(*           IF.formula_delayed = helper_formula fe.IF.formula_delayed;                        *)
(*         }                                                                                   *)
(*   ) in                                                                                      *)
(*   and helper_h_formula (h: IF.h_formula) : IF.h_formula = (                                 *)
(*     match h with                                                                            *)
(*     | IF.Phase hfp ->                                                                       *)
(*         IF.Phase { hfp with                                                                 *)
(*           IF.h_formula_phase_rd = helper_h_formula hfp.IF.h_formula_phase_rd;               *)
(*           IF.h_formula_phase_rw = helper_h_formula hfp.IF.h_formula_phase_rw;               *)
(*         }                                                                                   *)
(*     | IF.Conj hfc ->                                                                        *)
(*         IF.Conj { hfc with                                                                  *)
(*           IF.h_formula_conj_h1 = helper_h_formula hfp.IF.h_formula_conj_h1;                 *)
(*           IF.h_formula_conj_h2 = helper_h_formula hfp.IF.h_formula_conj_h2;                 *)
(*         }                                                                                   *)
(*     | IF.ConjStar hfcs ->                                                                   *)
(*         IF.ConjStar { hfcs with                                                             *)
(*           IF.h_formula_conjstar_h1 = helper_h_formula hfp.IF.h_formula_conjstar_h1;         *)
(*           IF.h_formula_conjstar_h2 = helper_h_formula hfp.IF.h_formula_conjstar_h2;         *)
(*         }                                                                                   *)
(*     | IF.ConjConj hfcc ->                                                                   *)
(*         IF.ConjConj { hfcc with                                                             *)
(*           IF.h_formula_conjconj_h1 = helper_h_formula hfp.IF.h_formula_conjconj_h1;         *)
(*           IF.h_formula_conjconj_h2 = helper_h_formula hfp.IF.h_formula_conjconj_h2;         *)
(*         }                                                                                   *)
(*     | IF.Star hfs ->                                                                        *)
(*         IF.Star { hfs with                                                                  *)
(*           IF.h_formula_star_h1 = helper_h_formula hfp.IF.h_formula_star_h1;                 *)
(*           IF.h_formula_star_h2 = helper_h_formula hfp.IF.h_formula_star_h2;                 *)
(*         }                                                                                   *)
(*     | IF.StarMinus hfsm ->                                                                  *)
(*         IF.StarMinus { hfc with                                                             *)
(*           IF.h_formula_starminus_h1 = helper_h_formula hfp.IF.h_formula_starminus_h1;       *)
(*           IF.h_formula_starminus_h2 = helper_h_formula hfp.IF.h_formula_starminus_h2;       *)
(*         }                                                                                   *)
(*     | IF.HeapNode hfh ->                                                                    *)
(*         IF.HeapNode { hfh with                                                              *)
(*           IF.h_formula_heap_name = H                                                        *)
(*         }                                                                                   *)
(*     | IF.HeapNode2 of h_formula_heap2                                                       *)
(*     | HRel _ | HTrue | HFalse -> h                                                          *)
(*   ) in                                                                                      *)
(* and h_formula_heap = { h_formula_heap_node : (ident * primed);                              *)
(*                        h_formula_heap_name : ident;                                         *)
(*                        h_formula_heap_deref : int;                                          *)
(*                        h_formula_heap_derv : bool;                                          *)
(*                        h_formula_heap_imm : ann;                                            *)
(*                        h_formula_heap_imm_param : ann option list;                          *)
(*                        h_formula_heap_full : bool;                                          *)
(*                        h_formula_heap_with_inv : bool;                                      *)
(*                        h_formula_heap_perm : iperm; (*LDK: optional fractional permission*) *)
(*                        h_formula_heap_arguments : P.exp list;                               *)
(*                        h_formula_heap_pseudo_data : bool;                                   *)
(*                        h_formula_heap_label : formula_label option;                         *)
(*                        h_formula_heap_pos : loc }                                           *)

(* and h_formula_heap2 = { h_formula_heap2_node : (ident * primed);                            *)
(*                         h_formula_heap2_name : ident;                                       *)
(*                         h_formula_heap2_deref : int;                                        *)
(*                         h_formula_heap2_derv : bool;                                        *)
(*                         h_formula_heap2_imm : ann;                                          *)
(*                         h_formula_heap2_imm_param : ann option list;                        *)
(*                         h_formula_heap2_full : bool;                                        *)
(*                         h_formula_heap2_with_inv : bool;                                    *)
(*                         h_formula_heap2_perm : iperm; (*LDK: fractional permission*)        *)
(*                         h_formula_heap2_arguments : (ident * P.exp) list;                   *)
(*                         h_formula_heap2_pseudo_data : bool;                                 *)
(*                         h_formula_heap2_label : formula_label option;                       *)
(*                         h_formula_heap2_pos : loc }                                         *)

(*   match stmt with                                                                           *)
(*   | Iast.Assert assert_e ->                                                                 *)
(*   | Iast.Dprint _ -> stmt                                                                   *)
(*   | _ -> report_error pos ("translate_hip_stmt: unexpected hip statement: "                 *)
(*                            ^ (Iprinter.string_of_exp stmt))                                 *)


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
            try Hashtbl.find tbl_data_decl newtyp
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
  aux_local_vardecls := [];
  let _ = gather_addrof_fundec fundec in
  (* start translating function *)
  let pos = match lopt with None -> no_pos | Some l -> translate_location l in
  let fheader = fundec.Cil.svar in
  let name = fheader.Cil.vname in
  let mingled_name = "" in (* TRUNG TODO: check mingled_name later *)
  let static_specs = fundec.Cil.hipfuncspec in
  let return_typ = ( 
    match fheader.Cil.vtype with
    | Cil.TFun (t, params, _, _) -> translate_typ t pos
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
            | Cil.TComp (comp, _) -> (Globals.Named comp.Cil.cname, Iast.CopyMod)
            | Cil.TPtr (ty1, _) when (is_cil_struct_pointer ty) ->
                (translate_typ ty1 no_pos, Iast.NoMod)
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
        let sbody = translate_block fundec.Cil.sbody in
        let body = merge_iast_exp (slocals @ !aux_local_vardecls @ [sbody]) in
        let pos = translate_location fundec.Cil.sbody.Cil.bloc in
        Some (Iast.mkBlock body Iast.NoJumpLabel [] pos)
  ) in
  let filename = pos.start_pos.Lexing.pos_fname in
	let static_specs1, hp_decls = match static_specs with
	  | Iformula.EList [] ->
		let ss, hps = Iast.genESpec funargs return_typ pos in
		(*let _ = Debug.info_hprint (add_str "ss" !Iformula.print_struc_formula) ss no_pos in *)
		(ss, hps)
	  | _ ->
		static_specs, []
	in
  let newproc : Iast.proc_decl = {
    Iast.proc_name = name;
    Iast.proc_mingled_name = mingled_name;
    Iast.proc_data_decl = None;
    Iast.proc_flags = [] ;
    Iast.proc_hp_decls = hp_decls;
    Iast.proc_constructor = false;
    Iast.proc_args = funargs;
    Iast.proc_source = ""; (* WN : need to change *)
    Iast.proc_return = return_typ;
    Iast.proc_static_specs = static_specs1;
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
  let coercion_decls : Iast.coercion_decl_list list ref = ref [] in
  let aux_progs : Iast.prog_decl list ref = ref [] in
  
  (* reset & init global vars *)
  Hashtbl.reset tbl_pointer_typ;
  Hashtbl.reset tbl_data_decl;
  Hashtbl.reset tbl_aux_proc;
  aux_local_vardecls := [];

  (* begin to translate *)
  let globals = file.Cil.globals in
  (* collect premitive info first *)
  List.iter (fun gl ->
    match gl with
    | Cil.GType (tinfo, _) ->                                   (* collect typedef info *)
        let actual_typ = get_actual_cil_typ tinfo.Cil.ttype in
        Hashtbl.add tbl_typedef tinfo.Cil.tname actual_typ;
    | _ -> ();
  ) globals;
  (* translate the rest *)
  List.iter (fun gl ->
    match gl with
    | Cil.GType (tinfo, _) -> ();
    | Cil.GCompTag (comp, l) -> translate_compinfo comp (Some l)
    | Cil.GCompTagDecl _ ->
        (* let _ = print_endline ("== gl GCompTagDecl = " ^ (string_of_cil_global gl)) in *)
        ()
    | Cil.GEnumTag _ ->
        (* let _ = print_endline ("== gl GEnumTag = " ^ (string_of_cil_global gl)) in *)
        ()
    | Cil.GEnumTagDecl _ ->
        (* let _ = print_endline ("== gl GEnumTagDecl = " ^ (string_of_cil_global gl)) in *)
        ()
    | Cil.GVarDecl (v, l) ->
        (* let _ = print_endline ("== gl GVarDecl = " ^ (string_of_cil_global gl)) in *)
        ()
    | Cil.GVar (v, init, l) ->
        let gvar = translate_global_var v init (Some l) in
        global_var_decls := !global_var_decls @ [gvar];
    | Cil.GFun (fd, l) ->
        let proc = translate_fundec fd (Some l) in
        proc_decls := !proc_decls @ [proc]
    | Cil.GAsm _ ->
        (* let _ = print_endline ("== gl GAsm = " ^ (string_of_cil_global gl)) in *)
        ()
    | Cil.GPragma _ ->
        (* let _ = print_endline ("== gl GPragma = " ^ (string_of_cil_global gl)) in *)
        ()
    | Cil.GText _ ->
        (* let _ = print_endline ("== gl GText = " ^ (string_of_cil_global gl)) in *)
        ()
    | Cil.GHipProgSpec (hipprog, _) ->
        aux_progs := !aux_progs @ [hipprog]
  ) globals;
  let obj_def = {Iast.data_name = "Object";
                 Iast.data_fields = [];
                 Iast.data_pos = no_pos;
                 Iast.data_parent_name = "";
                 Iast.data_invs = [];
                 Iast.data_is_template = false;
                 Iast.data_methods = []} in
  let string_def = {Iast.data_name = "String";
                    Iast.data_pos = no_pos;
                    Iast.data_fields = [];
                    Iast.data_parent_name = "Object";
                    Iast.data_invs = [];
                    Iast.data_is_template = false;
                    Iast.data_methods = []} in
  (* update some global settings *)
  Hashtbl.iter (fun _ data -> data_decls := !data_decls @ [data]) tbl_data_decl;
  (* aux procs *)
  Hashtbl.iter (fun _ p -> proc_decls := !proc_decls @ [p]) tbl_aux_proc;
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
    Iast.prog_hp_decls = List.fold_left (fun r proc ->r@proc.Iast.proc_hp_decls) [] !proc_decls;
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
  (* do the preprocess by GCC first *)
  let prep_filename = filename ^ ".prep" in
  let cmd = "gcc -C -E " ^ filename ^ " -o " ^ prep_filename in
  let _ = print_endline ("GCC Preprocessing...") in
  let _ = print_endline cmd in
  let exit_code = Sys.command cmd in
  if (exit_code != 0) then
    report_error no_pos "GCC Preprocessing failed!";
  (* then use CIL to parse the preprocessed file *)
  let cil = parse_one_file prep_filename in
  if !Cilutil.doCheck then (
    ignore (Errormsg.log "First CIL check\n");
    if not (Check.checkFile [] cil) && !Cilutil.strictChecking then (
      Errormsg.bug ("CIL's internal data structures are inconsistent "
                    ^^ "(see the warnings above).  This may be a bug "
                    ^^ "in CIL.\n")
    )
  );
  if (!Globals.print_cil_input) then (
    print_endline "";
    print_endline ("***********************************");
    print_endline ("********* input cil file **********");
    print_endline (string_of_cil_file cil);
    print_endline ("******** end of cil file **********");
    print_endline "";
  );
  (* finally, translate cil to iast *)
  let prog = translate_file cil in
  (* and clean temp files *)
  let cmd = ("rm " ^ prep_filename) in
  let _ = Sys.command cmd in
  (* return *)
  prog
