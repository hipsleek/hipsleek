open Globals
open Exc.GTable
open Gen.Basic

(* --------------------- *)
(* Global variables      *)
(* --------------------- *)

let tbl_typedef : (string, Cil.typ) Hashtbl.t = Hashtbl.create 1

(* hash table contains Globals.typ structures that are used to represent Cil.typ pointers *)
let tbl_pointer_typ : (Cil.typ, Globals.typ) Hashtbl.t = Hashtbl.create 1

(* hash table contains Iast.data_decl structures that are used to represent pointer types *)
let tbl_pointer_data_decl : (Globals.typ, Iast.data_decl) Hashtbl.t = Hashtbl.create 1

(* hash table contains Iast.data_decl structures that are used to represent struct types *)
let tbl_struct_data_decl : (Globals.typ, Iast.data_decl) Hashtbl.t = Hashtbl.create 1

(* hash table map lval expressions (in string form) to their address holder generated-pointers *)
let tbl_addrof_holder : (string, Iast.exp) Hashtbl.t = Hashtbl.create 1

(* hash table map content of the address holders to expresses they hold *)
let tbl_addrof_data : (string, Iast.exp) Hashtbl.t = Hashtbl.create 1

(* list of address-represented pointer declaration *)
let aux_local_vardecls : Iast.exp list ref = ref []

(* hashtbl contains all auxiliary procedures, proc_name -> proc_decl *)
let tbl_aux_proc: (string, Iast.proc_decl) Hashtbl.t = Hashtbl.create 1

(* reset all global vars for the next use *)
let reset_global_vars () =
  Hashtbl.clear tbl_pointer_typ;
  Hashtbl.clear tbl_pointer_data_decl

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
  let re = Str.regexp "\(__star\)" in
  try (
    let _ = Str.search_forward re typ_name 0 in
    let proc_name = "cast_void_pointer_in_heap_to_" ^ typ_name in
    let proc_decl = (
      try
        Hashtbl.find tbl_aux_proc proc_name
      with Not_found -> (
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
                | []   -> report_error no_pos "create_void_pointer_casting_proc: Invalid data_decl fields"
                | [hd] -> "<_>"
                | hd::tl -> "<" ^ (List.fold_left (fun s _ -> s ^ ", _") "_" tl) ^ ">"
              with Not_found -> report_error no_pos ("create_void_pointer_casting_proc: Unknown data type: " ^ base_data)
            ) 
        ) in
        let cast_proc = (
          typ_name ^ " " ^ proc_name ^ " (void__star p)\n" ^
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
  )
  with Not_found -> report_error no_pos ("create_void_pointer_casting_proc: invalid typ_name")

let create_pointer_to_int_casting_proc (pointer_typ_name: string) : Iast.proc_decl =
  let re = Str.regexp "\(__star\)" in
  try (
    let _ = Str.search_forward re pointer_typ_name 0 in
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
  )
  with Not_found ->
    report_error no_pos ("create_pointer_to_int_casting_proc: invalid typ_name")

let create_int_to_pointer_casting_proc (pointer_typ_name: string) : Iast.proc_decl =
  let re = Str.regexp "\(__star\)" in
  try (
    let _ = Str.search_forward re pointer_typ_name 0 in
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
  )
  with Not_found ->
    report_error no_pos ("create_int_to_pointer_casting_proc: invalid typ_name")

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
          "  case { param =  null -> ensures res;\n" ^
          "         param != null -> ensures !res; }\n"
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

let rec gather_addrof_info_exp (e: Cil.exp) : (Cil.lval * Iast.exp) list =
  let eq_lval (lv1, _) (lv2, _) = (
    let s1 = string_of_cil_lval lv1 in
    let s2 = string_of_cil_lval lv2 in
    s1 = s2
  ) in
  match e with
  | Cil.Const _ -> []
  | Cil.Lval (lv, _) -> []
  | Cil.SizeOf _ -> []
  | Cil.SizeOfE _ -> []
  | Cil.SizeOfStr _ -> []
  | Cil.AlignOf _ -> []
  | Cil.AlignOfE _ -> []
  | Cil.UnOp (_, e1, _, _) -> gather_addrof_info_exp e1
  | Cil.BinOp (_, e1, e2, _, _) -> (
      let r1 = gather_addrof_info_exp e1 in
      let r2 = gather_addrof_info_exp e2 in
      Gen.BList.remove_dups_eq eq_lval (r1 @ r2)
    )
  | Cil.Question (e1, e2, e3, _, _) -> (
      let r1 = gather_addrof_info_exp e1 in
      let r2 = gather_addrof_info_exp e2 in
      let r3 = gather_addrof_info_exp e3 in
      Gen.BList.remove_dups_eq eq_lval (r1 @ r2 @ r3)
    )
  | Cil.CastE (_, e, _) -> gather_addrof_info_exp e
  | Cil.AddrOf (lv, l) -> (
      let pos = translate_location l in
      let lv_str = string_of_cil_lval lv in
      try
        let holder_var = Hashtbl.find tbl_addrof_holder lv_str in
        [(lv, holder_var)]
      with Not_found -> (
        let lv_ty = typ_of_cil_lval lv in
        let pdata_ty = translate_typ lv_ty pos in
        let (datatyp, dataname, datadecl) = (
          try 
            let dtyp = Hashtbl.find tbl_pointer_typ lv_ty in
            let ddecl = Hashtbl.find tbl_pointer_data_decl dtyp in
            let dname = (
              match dtyp with
              | Globals.Named s -> s
              | _ -> report_error pos "gather_addrof_info_exp: unexpected type!"
            ) in
            (dtyp, dname, ddecl)
          with Not_found -> (
            (* create new Globals.typ and Iast.data_decl, then update to a hash table *)
            let ftyp = pdata_ty in
            let fname = "pdata" in
            let dfields = [((ftyp, fname), no_pos, false, Iast.F_NO_ANN)] in
            let dname = (Globals.string_of_typ ftyp) ^ "__star" in
            let dtyp = Globals.Named dname in
            Hashtbl.add tbl_pointer_typ lv_ty dtyp;
            let ddecl = Iast.mkDataDecl dname dfields "Object" [] false [] in
            Hashtbl.add tbl_pointer_data_decl dtyp ddecl;
            (dtyp, dname, ddecl)
          )
        ) in
        (* define new pointer var px that will be used to represent x: {x, &x} --> {*px, px} *)
        let vname = "address__var__" ^ (string_of_int (Hashtbl.length tbl_addrof_holder)) in
        let init_params = (
          match pdata_ty with
          | Globals.Int -> [(Iast.mkIntLit 0 pos)];
          | Globals.Bool -> [(Iast.mkBoolLit true pos)];
          | Globals.Float -> [(Iast.mkFloatLit 0. pos)];
          | Globals.Named _ -> [(Iast.Null pos)];
          | _ -> report_error pos ("Unexpected typ 1: " ^ (Globals.string_of_typ pdata_ty))
        ) in
        let init_data = Iast.mkNew dataname init_params pos in
        let decl = [(vname, Some init_data, pos)] in
        let vardecl = Iast.mkVarDecl datatyp decl pos in
        aux_local_vardecls := !aux_local_vardecls @ [vardecl];
        let holder_var = Iast.mkVar vname pos in
        Hashtbl.add tbl_addrof_holder lv_str holder_var;
        let e2 = Iast.mkMember (Iast.mkVar vname pos) ["pdata"] None pos in
        let e2_str = Iprinter.string_of_exp e2 in
        let lv_exp = translate_lval lv in
        Hashtbl.add tbl_addrof_data e2_str lv_exp;
        [(lv, holder_var)]
      )
    )
  | Cil.StartOf (lv, _) -> []

and gather_addrof_info_exp_list (exps: Cil.exp list) : (Cil.lval * Iast.exp) list =
  let eq_lval (lv1, _) (lv2, _) = (
    let s1 = string_of_cil_lval lv1 in
    let s2 = string_of_cil_lval lv2 in
    s1 = s2
  ) in
  let r = List.concat (List.map gather_addrof_info_exp exps) in
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
            let fname = "pdata" in
            let dfields = [((ftyp, fname), no_pos, false, Iast.F_NO_ANN)] in
            let dname = (Globals.string_of_typ ftyp) ^ "__star" in
            let dtype = Globals.Named dname in
            Hashtbl.add tbl_pointer_typ actual_ty dtype;
            let ddecl = Iast.mkDataDecl dname dfields "Object" [] false [] in
            Hashtbl.add tbl_pointer_data_decl dtype ddecl;
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
  let pos = translate_location vinfo.Cil.vdecl in
  let ty = translate_typ vinfo.Cil.vtype pos in
  let name = vinfo.Cil.vname in
  let newexp = (
    match ty with
    | Globals.Int
    | Globals.Bool
    | Globals.Float
    | Globals.Array _
    | Globals.Named "void__star" -> Iast.mkVarDecl ty [(name, None, pos)] pos
    | Globals.Named typ_name -> (
        (* look for the corresponding data structure *)
        let data_decl = (
          try Hashtbl.find tbl_struct_data_decl ty
          with Not_found -> (
            try Hashtbl.find tbl_pointer_data_decl ty
            with Not_found -> report_error pos ("translate_var_decl: Unknown typ " ^ (Globals.string_of_typ ty))
          )
        ) in
        (* create and temporarily initiate a new object *)
        let init_params = List.fold_left (
          fun params field ->
            let ((ftyp, _), _, _, _) = field in
            let exp = (
              match ftyp with
              | Globals.Int -> Iast.mkIntLit 0 pos
              | Globals.Bool -> Iast.mkBoolLit true pos
              | Globals.Float -> Iast.mkFloatLit 0. pos
              | Globals.Named _ -> Iast.mkNull no_pos
              | _ -> report_error pos ("translate_var_decl: Unexpected typ 1 - " ^ (Globals.string_of_typ ftyp))
            ) in
            params @ [exp]
        ) [] data_decl.Iast.data_fields in
        let init_data = Iast.mkNew typ_name init_params pos in
        Iast.mkVarDecl ty [(name, Some init_data, pos)] pos
      )
    | _ -> report_error pos ("translate_var_decl: Unexpected typ 2 - " ^ (Globals.string_of_typ ty))
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
  match field.Cil.ftype with
  | Cil.TComp (comp, _) ->
      let ty = Globals.Named comp.Cil.cname in
      ((ty, name), pos, false, Iast.F_NO_ANN)
  | _ ->
      let ty = translate_typ field.Cil.ftype pos in
      ((ty, name), pos, false, Iast.F_NO_ANN)


and translate_compinfo (comp: Cil.compinfo) (lopt: Cil.location option) : Iast.data_decl =
  let name = comp.Cil.cname in
  let fields = List.map (fun x -> translate_fieldinfo x lopt) comp.Cil.cfields in
  let datadecl = Iast.mkDataDecl name fields "Object" [] false [] in
  Hashtbl.add tbl_struct_data_decl (Globals.Named name) datadecl;
  datadecl


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
  let (lhost, offset, loc) = lv in
  let pos = translate_location loc in
  let rec create_complex_exp (base : Iast.exp) (offset : Cil.offset) pos : Iast.exp = (
    match offset with
    | Cil.NoOffset -> base
    | Cil.Field ((field, l1), off, _) -> (
        let p = makeLocation (startPos pos) (endPos (translate_location l1)) in
        let b = Iast.mkMember base [field.Cil.fname] None p in
        create_complex_exp b off pos
      )
    | Cil.Index (e, off, _) -> (
        let l1 = loc_of_cil_exp e in
        let p = makeLocation (startPos pos) (endPos (translate_location l1)) in
        let b = Iast.mkArrayAt base [(translate_exp e)] p in
        create_complex_exp b off pos
      )
  ) in
  match lhost with
  | Cil.Var (v, l) -> (
      let base = translate_var v (Some l) in
      let newexp = create_complex_exp base offset pos in
      newexp
    )
  | Cil.Mem e -> (
      (* access to data in pointer variable *)
      let data_base = translate_exp e  in
      let data_fields = ["pdata"] in
      let base = Iast.mkMember data_base data_fields None pos in
      let newexp = create_complex_exp base offset pos in
      newexp
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
      let t = translate_typ (typ_of_cil_exp exp) pos in
      let e = translate_exp exp in
      let unexp = (
        match t with
        | Globals.Bool -> Iast.mkUnary o e None pos
        | _ -> (
            let not_proc = create_logical_not_proc t in
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
      let input_typ = translate_typ (typ_of_cil_exp exp) pos in
      let output_typ = translate_typ ty pos in
      let input_exp = translate_exp exp in
      if (input_typ = output_typ) then
        (* no need casting *)
        input_exp
      else (
        (* do casting *)
        match output_typ, input_typ with
        | Globals.Named otyp_name, Globals.Named ityp_name -> (
            if (ityp_name = "void__star") then (
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
  | Cil.AddrOf (lv, l) ->
      let pos = translate_location l in
      let lv_str = string_of_cil_lval lv in
      let lv_holder = (
        try
          Hashtbl.find tbl_addrof_holder lv_str
        with Not_found ->
          report_error pos ("translate_exp: lval holder of '" ^ lv_str ^ "' is not found.")
      ) in
      lv_holder
  | Cil.StartOf (lv, l) -> translate_lval lv


and translate_instr (instr: Cil.instr) : Iast.exp list =
  (* detect address-of operator *)
  let new_exp = (match instr with
    | Cil.Set (lv, exp, l) -> (
        let pos = translate_location l in
        let addrof_info = gather_addrof_info_exp exp in
        let update_addrof_exps = List.map (
          fun e ->
            let lv, lv_holder = e in
            let exp1 = translate_lval lv in
            let exp2 = Iast.mkMember lv_holder ["pdata"] None pos in
            let exp3 = Iast.mkAssign Iast.OpAssign exp2 exp1 None pos in
            exp3
        ) addrof_info in
        let le = translate_lval lv in
        let re = translate_exp exp in
        let set_exp = Iast.mkAssign Iast.OpAssign le re None pos in
        let aux_addrof_holder_exps = (
          try
            let lv_str = string_of_cil_lval lv in
            let lv_holder = Hashtbl.find tbl_addrof_holder lv_str in
            let e1 = Iast.mkMember lv_holder ["pdata"] None pos in
            let e2 = Iast.mkAssign Iast.OpAssign e1 le None pos in
            [e2]
          with Not_found -> []
        ) in
        (* update addrof_data table *)
        let _ = (
          let continue = ref true in
          let e1 = ref re in
          let e2 = ref le in
          while !continue do
            try
              let e1_data = Iast.mkMember !e1 ["pdata"] None pos in
              e1 := Hashtbl.find tbl_addrof_data (Iprinter.string_of_exp e1_data);
              e2 := Iast.mkMember !e2 ["pdata"] None pos;
              Hashtbl.add tbl_addrof_data (Iprinter.string_of_exp !e2) !e1;
              continue := true;
            with Not_found -> continue := false;
          done;
        ) in
        let aux_addrof_data_exp = (
          match lv with
          | (Cil.Mem _, _, _) -> (
              try
                let e1 = Hashtbl.find tbl_addrof_data (Iprinter.string_of_exp le) in
                let e2 = Iast.mkAssign Iast.OpAssign e1 le None pos in
                [e2]
              with Not_found -> []
            )
          | _ -> []
        ) in
        update_addrof_exps @ [set_exp] @ aux_addrof_holder_exps @ aux_addrof_data_exp
      )
    | Cil.Call (lv_opt, exp, exps, l) -> (
        let pos = translate_location l in
        let _ = gather_addrof_info_exp_list exps in
        let fname = match exp with
          | Cil.Const (Cil.CStr s, _) -> s
          | Cil.Lval ((Cil.Var (v, _), _, _), _) -> v.Cil.vname
          | _ -> report_error pos "translate_intstr: invalid callee's name!" in
        let args = List.map (fun x -> translate_exp x) exps in
        let update_addrof_args_exps_before = ref [] in
        let update_addrof_args_exps_after = ref [] in
        List.iter (
          fun e ->
            let e_data = Iast.mkMember e ["pdata"] None pos in
            try
              let v = Hashtbl.find tbl_addrof_data (Iprinter.string_of_exp e_data) in
              let e1 = Iast.mkAssign Iast.OpAssign e_data v None pos in
              update_addrof_args_exps_before := !update_addrof_args_exps_before @ [e1];
              if (fname <> "free") then ( (* free pointer function *)
                let e2 = Iast.mkAssign Iast.OpAssign v e_data None pos in 
                update_addrof_args_exps_after := !update_addrof_args_exps_after @ [e2];
              );
            with _ -> ()
        ) args;
        let callee = Iast.mkCallNRecv fname None args None pos in
        let newexp = (
          match lv_opt with
          | None -> !update_addrof_args_exps_before @ [callee] @ !update_addrof_args_exps_after
          | Some lv -> (
              (* declare a temp var to store the value return by call *)
              let tmp_var = (
                let vty = translate_typ (typ_of_cil_lval lv) pos in
                let vname = Globals.fresh_name () in
                let vdecl = Iast.mkVarDecl vty [vname, None, pos] pos in
                aux_local_vardecls := !aux_local_vardecls @ [vdecl];
                Iast.mkVar vname pos
              ) in
              let tmp_assign = Iast.mkAssign Iast.OpAssign tmp_var callee None pos in
              let le = translate_lval lv in
              let call_assign = Iast.mkAssign Iast.OpAssign le tmp_var None pos in
              let aux_addrof_holder_exps = ref [] in
              let aux_addrof_data_exp = ref [] in
              if (fname <> "free") then (
                aux_addrof_holder_exps:= (
                  try
                    let lv_str = string_of_cil_lval lv in
                    let lv_holder = Hashtbl.find tbl_addrof_holder lv_str in
                    let e1 = Iast.mkMember lv_holder ["pdata"] None pos in
                    let e2 = Iast.mkAssign Iast.OpAssign e1 le None pos in
                    [e2]
                  with Not_found -> []
                );
                aux_addrof_data_exp := (match lv with
                  | (Cil.Mem _, _, _) -> (
                      try
                        let e1 = Hashtbl.find tbl_addrof_data (Iprinter.string_of_exp le) in
                        let e2 = Iast.mkAssign Iast.OpAssign e1 le None pos in
                        [e2]
                      with Not_found -> []
                    )
                  | _ -> []
                );
              );
              !update_addrof_args_exps_before @ [tmp_assign] @ !update_addrof_args_exps_after
              @ [call_assign] @ !aux_addrof_holder_exps @ !aux_addrof_data_exp
            )
        ) in
        newexp
      )
    | Cil.Asm _ -> []           (* skip translating the ASM... *)
  ) in
  new_exp


and translate_stmt (s: Cil.stmt) : Iast.exp =
  let skind = s.Cil.skind in
  match skind with
  | Cil.Instr instrs ->
      let newexp = (match instrs with
        | [] -> Iast.Empty no_pos
        | [i] -> merge_iast_exp (translate_instr i)
        | _ ->
            let es = List.concat (List.map translate_instr instrs) in
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
      let ty = translate_typ (typ_of_cil_exp exp) pos in
      let cond = (
        match ty with
        | Globals.Bool -> translate_exp exp
        | _ -> (
            let e = translate_exp exp in
            let bool_of_proc = create_bool_casting_proc ty in
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
      let p = translate_location l in
      translate_hip_stmt iast_exp p


and translate_hip_stmt (stmt: Iast.exp) pos : Iast.exp =
  match stmt with
  | Iast.Assert assert_e -> (
      let assert_vars = (
        match assert_e.Iast.exp_assert_asserted_formula with
        | None -> []
        | Some (sf, b) -> Iformula.struc_free_vars true sf
      ) in
      let assume_vars = (
        match assert_e.Iast.exp_assert_assumed_formula with
        | None -> []
        | Some f -> Iformula.all_fv f
      ) in
      let vars = fst (List.split (assert_vars @ assume_vars)) in
      let vars = Gen.BList.remove_dups_eq (=) vars in
      let update_exps = List.fold_left (fun es v ->
        let new_es = (
          try
            let v_holder = Hashtbl.find tbl_addrof_holder v in
            let e1 = Iast.mkMember v_holder ["pdata"] None pos in
            let e2 = Iast.mkVar v pos in
            let e3 = Iast.mkAssign Iast.OpAssign e2 e1 None pos in
            [e3]
          with Not_found -> []
        ) in
        es @ new_es
      ) [] vars in
      merge_iast_exp (update_exps @ [stmt])
    )
  | Iast.Dprint _ -> stmt
  | _ -> report_error pos ("translate_hip_stmt: unexpected hip statement: "
                           ^ (Iprinter.string_of_exp stmt))

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
            try Hashtbl.find tbl_struct_data_decl newtyp
            with Not_found -> (
              try Hashtbl.find tbl_pointer_data_decl newtyp
              with Not_found ->
                report_error pos ("translate_init: couldn't find typ - " ^ newtyp_name)
            )
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
  let ty = translate_typ vinfo.Cil.vtype pos in
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
  Hashtbl.clear tbl_addrof_holder;
  Hashtbl.clear tbl_addrof_data;
  aux_local_vardecls := [];
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
          let typ = translate_typ ty pos in
          let newparam = {Iast.param_type = typ;
                          Iast.param_name = name;
                          Iast.param_mod = Iast.NoMod;
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
	let hp_decls = [] in
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
  let coercion_decls : Iast.coercion_decl_list list ref = ref [] in
  let aux_progs : Iast.prog_decl list ref = ref [] in
  
  (* reset & init global vars *)
  Hashtbl.reset tbl_pointer_typ;
  Hashtbl.reset tbl_pointer_data_decl;
  Hashtbl.reset tbl_struct_data_decl;
  Hashtbl.reset tbl_addrof_holder;
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
    | Cil.GCompTag (comp, l) ->
        let datadecl = translate_compinfo comp (Some l) in
        data_decls := !data_decls @ [datadecl]
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
  Hashtbl.iter (fun _ data -> data_decls := !data_decls @ [data]) tbl_pointer_data_decl;
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
