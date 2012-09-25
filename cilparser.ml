open Globals
open Error

let parse_one_file (fname: string) : Cil.file =
  (* PARSE and convert to CIL *)
  if !Cilutil.printStages then ignore (Errormsg.log "Parsing %s\n" fname);
  let cil = Frontc.parse fname () in
  if (not !Epicenter.doEpicenter) then (
    (* sm: remove unused temps to cut down on gcc warnings  *)
    (* (Stats.time "usedVar" Rmtmps.removeUnusedTemps cil);  *)
    (* (trace "sm" (dprintf "removing unused temporaries\n")); *)
    (Rmtmps.removeUnusedTemps cil)
  );
  (* return *)
  cil

let translate_location (loc: Cil.location) : Globals.loc =
  let pos : Lexing.position = {
    Lexing.pos_fname = loc.Cil.file;
    Lexing.pos_lnum = loc.Cil.line;
    Lexing.pos_bol = 0; (* TRUNG CODE: this should be computed later *)
    Lexing.pos_cnum = loc.Cil.byte;
  } in
  let newloc: Globals.loc = {
    Globals.start_pos = pos;
    Globals.mid_pos = pos; (* TRUNG CODE: this should be computed later *)
    Globals.end_pos = pos; (* TRUNG CODE: this should be computed later *)
  } in
  (* return *)
  newloc

let translate_typ_var (t: Cil.typ) : Globals.typ =
  let newtype = 
    match t with
    | Cil.TVoid _            -> Globals.Void
    | Cil.TInt _             -> Globals.Int 
    | Cil.TFloat _           -> Globals.Float 
    | Cil.TPtr _             -> report_error_msg "TRUNG: handle TPtr later!"  
    | Cil.TArray _           -> report_error_msg "TRUNG: handle TArray later!"
    | Cil.TFun _             -> report_error_msg "Should not appear here. Handle only in translate_typ_fun"
    | Cil.TNamed _           -> report_error_msg "TRUNG: handle TNamed later!"
    | Cil.TComp _            -> report_error_msg "TRUNG: handle TComp later!"
    | Cil.TEnum _            -> report_error_msg "TRUNG: handle TEnum later!"
    | Cil.TBuiltin_va_list _ -> report_error_msg "TRUNG: handle TBuiltin_va_list later!" in
  (* return *)
  newtype

let translate_varinfo (vinfo: Cil.varinfo) (l: Cil.location) : (*Iast.exp_var_decl*) unit =
  let vpos = translate_location vinfo.Cil.vdecl in
  let vtype = translate_typ_var vinfo.Cil.vtype in
  let vdata = [(vinfo.Cil.vname, None, vpos)] in
  (* FOR DEBUG *)
  let _ = print_endline ("  -- var: " ^ (Globals.string_of_typ vtype) ^ " " ^ vinfo.Cil.vname) in ()
  (* RETURN VALUE *)
  (* let newvar  = {Iast.exp_var_decl_type = vtype;  *)
  (*                Iast.exp_var_decl_decls = vdata; *)
  (*                Iast.exp_var_decl_pos = vpos} in *)
  (* newvar                                          *)

let translate_constant (c: Cil.constant) (lopt: Cil.location option) : Iast.exp =
  let pos = match lopt with
            | None -> no_pos
            | Some l -> translate_location l in
  match c with
  | Cil.CInt64 (i64, ikind, _) -> (
      match ikind with
      | Cil.IChar -> report_error_msg "TRUNG: Handle Cil.IChar later!"
      | Cil.ISChar -> report_error_msg "TRUNG: Handle Cil.ISChar later!"
      | Cil.IUChar -> report_error_msg "TRUNG: Handle Cil.IUChar later!"
      | Cil.IBool -> report_error_msg "TRUNG: Handle Cil.IBool later!"
      | Cil.IInt ->
          let i = Int64.to_int i64 in
          let newconstant = Iast.IntLit {Iast.exp_int_lit_val = i; Iast.exp_int_lit_pos = pos} in
          newconstant
      | Cil.IUInt -> report_error_msg "TRUNG: Handle Cil.IUInt later!"
      | Cil.IShort -> report_error_msg "TRUNG: Handle Cil.IShort later!"
      | Cil.IUShort -> report_error_msg "TRUNG: Handle Cil.IUShort later!"
      | Cil.ILong -> report_error_msg "TRUNG: Handle Cil.ILong later!"
      | Cil.IULong -> report_error_msg "TRUNG: Handle Cil.IULong later!"
      | Cil.ILongLong -> report_error_msg "TRUNG: Handle Cil.ILongLong later!"
      | Cil.IULongLong -> report_error_msg "TRUNG: Handle Cil.IULongLong later!"
    )
  | Cil.CStr s -> report_error_msg "TRUNG: Handle Cil.CStr later!"
  | Cil.CWStr _ -> report_error_msg "TRUNG: Handle Cil.CWStr later!"
  | Cil.CChr _ -> report_error_msg "TRUNG: Handle Cil.CChr later!"
  | Cil.CReal (f, fkind, _) -> (
      match fkind with
      | Cil.FFloat ->
          let newconstant = Iast.FloatLit {Iast.exp_float_lit_val = f; Iast.exp_float_lit_pos = pos} in
          newconstant
      | Cil.FDouble -> report_error_msg "TRUNG: Handle Cil.FDouble later!"
      | Cil.FLongDouble -> report_error_msg "TRUNG: Handle Cil.FLongDouble later!"
    )
  | Cil.CEnum _ -> report_error_msg "TRUNG: Handle Cil.CEnum later!"

let translate_exp (e: Cil.exp) (lopt: Cil.location option): Iast.exp =
  match e with
  | Cil.Const c -> translate_constant c lopt
  | Cil.Lval _ -> report_error_msg "TRUNG: Handle Cil.Lval later!"
  | Cil.SizeOf _ -> report_error_msg "TRUNG: Handle Cil.SizeOf later!"
  | Cil.SizeOfE _ -> report_error_msg "TRUNG: Handle Cil.SizeOfE later!"
  | Cil.SizeOfStr _ -> report_error_msg "TRUNG: Handle Cil.SizeOfStr later!"
  | Cil.AlignOf _ -> report_error_msg "TRUNG: Handle Cil.AlignOf later!"
  | Cil.AlignOfE _ -> report_error_msg "TRUNG: Handle Cil.AlignOfE later!"
  | Cil.UnOp _ -> report_error_msg "TRUNG: Handle Cil.UnOp later!"
  | Cil.BinOp _ -> report_error_msg "TRUNG: Handle Cil.BinOp later!"
  | Cil.CastE _ -> report_error_msg "TRUNG: Handle Cil.CastE later!"
  | Cil.AddrOf _ -> report_error_msg "TRUNG: Handle Cil.AddrOf later!"
  | Cil.StartOf _ -> report_error_msg "TRUNG: Handle Cil.StartOf later!"

let translate_offset (off: Cil.offset) =
  match off with
  | Cil.NoOffset _ -> report_error_msg "TRUNG: Handle Cil.NoOffset later!"
  | Cil.Field _ -> report_error_msg "TRUNG: Handle Cil.Field later!"
  | Cil.Index _ -> report_error_msg "TRUNG: Handle Cil.Index later!"

let translate_lhost (lh: Cil.lhost) =
  match lh with
  | Cil.Var _ -> report_error_msg "TRUNG: Handle Cil.Var later!"
  | Cil.Mem _ -> report_error_msg "TRUNG: Handle Cil.Mem later!"

let translate_lval (lv: Cil.lval) = ()

let translate_instr (instr: Cil.instr) : Iast.exp =
  match instr with
  | Cil.Set _ -> report_error_msg "TRUNG: Handle Cil.Set later!"
  | Cil.Call _ -> report_error_msg "TRUNG: Handle Cil.Call later!"
  | Cil.Asm _ -> report_error_msg "TRUNG: Handle Cil.Asm later!"

let rec translate_stmtkind (sk: Cil.stmtkind) (lopt: Cil.location option) : Iast.exp =
  let pos = match lopt with
    | None -> no_pos
    | Some l -> translate_location l in 
  match sk with
  | Cil.Instr instrs -> (
      let newexp = (match instrs with
        | [] -> report_error_msg "ERROR!!! instr list has to have at least 1 instruction"
        | [hd] -> translate_instr hd
        | hd::tl ->
            let e1 = translate_instr hd in
            let es = List.map translate_instr tl in
            List.fold_left (fun x y -> 
              Iast.Seq {Iast.exp_seq_exp1 = x;
                        Iast.exp_seq_exp2 = y;
                        Iast.exp_seq_pos = pos;}
            ) e1 es
      ) in
      newexp
    )
  | Cil.Return (eopt, l) ->
      let pos = translate_location l in
      let retval = match eopt with
        | None -> None
        | Some e -> Some (translate_exp e (Some l)) in
      let newexp = Iast.Return {Iast.exp_return_val = retval;
                                Iast.exp_return_path_id = None;
                                Iast.exp_return_pos = pos} in
      newexp
  | Cil.Goto _ -> report_error_msg "TRUNG: Iast cannot handle Cil.Goto type!"
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
  | Cil.Switch _ -> report_error_msg "TRUNG: Handle Cil.Switch later!"
  | Cil.Loop _ -> report_error_msg "TRUNG: Handle Cil.Loop later!"
  | Cil.Block _ -> report_error_msg "TRUNG: Handle Cil.Block later!"
  | Cil.TryFinally _ -> report_error_msg "TRUNG: Handle Cil.TryFinally later!"
  | Cil.TryExcept _ -> report_error_msg "TRUNG: Handle Cil.TryExcept later!"

let translate_stmt (s: Cil.stmt) (lopt: Cil.location option) : Iast.exp =
  let labels = s.Cil.labels in
  let skind = s.Cil.skind in
  let newskind = translate_stmtkind skind lopt in
  match labels with
  | [] -> newskind
  | [lbl] -> report_error_msg "TRUNG: stmt's label has 1 element. Handle later!"
  | hd::tl -> report_error_msg "TRUNG: stmt's label has >= 2 elements. Handle later!"

let translate_block (blk: Cil.block) : Iast.exp =
  
let translate_fundec (fdec: Cil.fundec) (l: Cil.location): unit (*Iast.proc_decl*) =
  let translate_funtyp (ty: Cil.typ) : Globals.typ = (
    match ty with
    | Cil.TFun (t, params, _, _) -> translate_typ_var t
    | _ -> report_error_msg ("Handle TFun only."
                             ^ "Other types should be passed to translate_typ_var!")
  ) in
  let collect_params (fheader: Cil.varinfo) : Iast.param list = (
    let ftyp = fheader.Cil.vtype in
    let pos = translate_location fheader.Cil.vdecl in
    match ftyp with
    | Cil.TFun (_, p, _, _) -> (
        let params = Cil.argsToList p in
        let translate_one_param (p : string * Cil.typ * Cil.attributes) : Iast.param = (
          let (name, t, attrs) = p in
          let ptyp = translate_typ_var t in
          let is_mod = (
            List.exists (fun attr ->
              let attrparas = match attr with Cil.Attr (_, aps) -> aps in
              List.exists (fun attrpara ->
                match attrpara with
                | Cil.AStar _ -> true
                | _           -> false
              ) attrparas
            ) attrs
          ) in
          let newparam = {Iast.param_type = ptyp;
                          Iast.param_name = name;
                          Iast.param_mod = if is_mod then Iast.RefMod else Iast.NoMod;
                          Iast.param_loc = pos; } in
          newparam
        ) in
        List.map translate_one_param params
      )
    | _ -> report_error_msg "Invalid function header!"
  ) in
  (* let rec collect_stmts (sallstmts: Cil.stmt list) : Iast.exp option = ( *)
    
  (* ) in                                                                   *)
  let fheader = fdec.Cil.svar in
  let proc_name = fheader.Cil.vname in
  let proc_mingled_name = "" in (* TRUNG CODE: check it later *)
  let proc_return = translate_funtyp (fheader.Cil.vtype) in
  let proc_args = collect_params fheader in
  let proc_loc = translate_location l in
  (* FOR DEBUG *)
  let _ = print_endline ("  -- proc: " ^ (Globals.string_of_typ proc_return) ^ " " ^ proc_name ^ "(..)") in ()
  (* RETURN VALUE *)
  (* let proc_iast : Iast.prog_decl = { *)
  (*   Iast.proc_name = proc_name;      *)
  (*   Iast.proc_return = proc_return;  *)
  (*   Iast.proc_file = loc.Cil.file;   *)
  (*   Iast.proc_loc = proc_loc;        *)
  (*   Iast.proc_args = proc_args;      *)
  (* } in                               *)
  (* proc_iast                          *)

let process_one_file (cil: Cil.file) : unit =
  if !Cilutil.doCheck then (
    ignore (Errormsg.log "First CIL check\n");
    if not (Check.checkFile [] cil) && !Cilutil.strictChecking then (
      Errormsg.bug ("CIL's internal data structures are inconsistent "
                    ^^"(see the warnings above).  This may be a bug "
                    ^^"in CIL.\n")
    )
  );
  
  let filename = cil.Cil.fileName in
  let _ = print_endline ("file name = " ^ filename) in
  let globals = cil.Cil.globals in
  List.iter (fun gl ->
    match gl with
    | Cil.GType _ -> print_endline ("== Cil.GType");
    | Cil.GCompTag _ -> print_endline ("== Cil.GCompTag");
    | Cil.GCompTagDecl _ -> print_endline ("== Cil.GCompTagDecl");
    | Cil.GEnumTag _ -> print_endline ("== Cil.GEnumTag");
    | Cil.GEnumTagDecl _ -> print_endline ("== Cil.GEnumTagDecl");
    | Cil.GVarDecl (v, l) ->
        let _ = print_endline ("== Cil.GVarDecl") in 
        translate_varinfo v l
    | Cil.GVar (v, _, l) ->
        let _ = print_endline ("== Cil.GVar") in 
        translate_varinfo v l
    | Cil.GFun (fd, l) -> 
        let _ = print_endline ("== Cil.GFun") in 
        translate_fundec fd l
    | Cil.GAsm _ -> print_endline ("== Cil.GAsm");
    | Cil.GPragma _ -> print_endline ("== Cil.GPragma");
    | Cil.GText _ -> print_endline ("== Cil.GText");
  ) globals