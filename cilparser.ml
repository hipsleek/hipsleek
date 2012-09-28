open Globals
open Error
open Exc.GTable

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


let rec translate_location (loc: Cil.location) : Globals.loc =
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


and translate_typ (t: Cil.typ) : Globals.typ =
  let newtype = 
    match t with
    | Cil.TVoid _            -> Globals.Void
    | Cil.TInt _             -> Globals.Int 
    | Cil.TFloat _           -> Globals.Float 
    | Cil.TPtr _             -> report_error_msg "TRUNG TODO: handle TPtr later!"  
    | Cil.TArray _           -> report_error_msg "TRUNG TODO: handle TArray later!"
    | Cil.TFun _             -> report_error_msg "Should not appear here. Handle only in translate_typ_fun"
    | Cil.TNamed _           -> report_error_msg "TRUNG TODO: handle TNamed later!"
    | Cil.TComp _            -> report_error_msg "TRUNG TODO: handle TComp later!"
    | Cil.TEnum _            -> report_error_msg "TRUNG TODO: handle TEnum later!"
    | Cil.TBuiltin_va_list _ -> report_error_msg "TRUNG TODO: handle TBuiltin_va_list later!" in
  (* return *)
  newtype


and translate_varinfo (vinfo: Cil.varinfo) (l: Cil.location) : (*Iast.exp_var_decl*) unit =
  let vpos = translate_location vinfo.Cil.vdecl in
  let vtype = translate_typ vinfo.Cil.vtype in
  let vdata = [(vinfo.Cil.vname, None, vpos)] in
  (* FOR DEBUG *)
  let _ = print_endline ("  -- var: " ^ (Globals.string_of_typ vtype) ^ " " ^ vinfo.Cil.vname) in ()
  (* RETURN VALUE *)
  (* let newvar  = {Iast.exp_var_decl_type = vtype;  *)
  (*                Iast.exp_var_decl_decls = vdata; *)
  (*                Iast.exp_var_decl_pos = vpos} in *)
  (* newvar                                          *)


and translate_constant (c: Cil.constant) (lopt: Cil.location option) : Iast.exp =
  let pos = match lopt with
            | None -> no_pos
            | Some l -> translate_location l in
  match c with
  | Cil.CInt64 (i64, ikind, _) -> (
      match ikind with
      | Cil.IChar -> report_error_msg "TRUNG TODO: Handle Cil.IChar later!"
      | Cil.ISChar -> report_error_msg "TRUNG TODO: Handle Cil.ISChar later!"
      | Cil.IUChar -> report_error_msg "TRUNG TODO: Handle Cil.IUChar later!"
      | Cil.IBool -> report_error_msg "TRUNG TODO: Handle Cil.IBool later!"
      | Cil.IInt ->
          let i = Int64.to_int i64 in
          let newconstant = Iast.IntLit {Iast.exp_int_lit_val = i; Iast.exp_int_lit_pos = pos} in
          newconstant
      | Cil.IUInt -> report_error_msg "TRUNG TODO: Handle Cil.IUInt later!"
      | Cil.IShort -> report_error_msg "TRUNG TODO: Handle Cil.IShort later!"
      | Cil.IUShort -> report_error_msg "TRUNG TODO: Handle Cil.IUShort later!"
      | Cil.ILong -> report_error_msg "TRUNG TODO: Handle Cil.ILong later!"
      | Cil.IULong -> report_error_msg "TRUNG TODO: Handle Cil.IULong later!"
      | Cil.ILongLong -> report_error_msg "TRUNG TODO: Handle Cil.ILongLong later!"
      | Cil.IULongLong -> report_error_msg "TRUNG TODO: Handle Cil.IULongLong later!"
    )
  | Cil.CStr s -> report_error_msg "TRUNG TODO: Handle Cil.CStr later!"
  | Cil.CWStr _ -> report_error_msg "TRUNG TODO: Handle Cil.CWStr later!"
  | Cil.CChr _ -> report_error_msg "TRUNG TODO: Handle Cil.CChr later!"
  | Cil.CReal (f, fkind, _) -> (
      match fkind with
      | Cil.FFloat ->
          let newconstant = Iast.FloatLit {Iast.exp_float_lit_val = f; Iast.exp_float_lit_pos = pos} in
          newconstant
      | Cil.FDouble -> report_error_msg "TRUNG TODO: Handle Cil.FDouble later!"
      | Cil.FLongDouble -> report_error_msg "TRUNG TODO: Handle Cil.FLongDouble later!"
    )
  | Cil.CEnum _ -> report_error_msg "TRUNG TODO: Handle Cil.CEnum later!"


and translate_unary_operator op =
  match op with
  | Cil.Neg -> Iast.OpUMinus
  | Cil.BNot -> report_error_msg "Error!!! Iast doesn't support BNot (bitwise complement) operator!"
  | Cil.LNot -> Iast.OpNot


and translate_binary_operator op =
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


and translate_exp (e: Cil.exp) (lopt: Cil.location option): Iast.exp =
  let pos = match lopt with None -> no_pos | Some l -> translate_location l in
  match e with
  | Cil.Const c -> translate_constant c lopt
  | Cil.Lval _ -> report_error_msg "TRUNG TODO: Handle Cil.Lval later!"
  | Cil.SizeOf _ -> report_error_msg "Error!!! Iast doesn't support Cil.SizeOf exp"
  | Cil.SizeOfE _ -> report_error_msg "Error!!! Iast doesn't support Cil.SizeOfE exp!"
  | Cil.SizeOfStr _ -> report_error_msg "Error!!! Iast doesn't support Cil.SizeOfStr exp!"
  | Cil.AlignOf _ -> report_error_msg "TRUNG TODO: Handle Cil.AlignOf later!"
  | Cil.AlignOfE _ -> report_error_msg "TRUNG TODO: Handle Cil.AlignOfE later!"
  | Cil.UnOp (op, exp, ty) ->
      let e = translate_exp exp lopt in
      let o = translate_unary_operator op in
      let newexp = Iast.Unary {Iast.exp_unary_op = o;
                               Iast.exp_unary_exp = e;
                               Iast.exp_unary_path_id = None;
                               Iast.exp_unary_pos = pos} in
      newexp
  | Cil.BinOp (op, exp1, exp2, ty) ->
      let e1 = translate_exp exp1 lopt in
      let e2 = translate_exp exp2 lopt in
      let o = translate_binary_operator op in
      let newexp = Iast.Binary {Iast.exp_binary_op = o;
                                Iast.exp_binary_oper1 = e1;
                                Iast.exp_binary_oper2 = e2;
                                Iast.exp_binary_path_id = None;
                                Iast.exp_binary_pos = pos } in
      newexp
  | Cil.CastE (ty, exp) ->
      let t = translate_typ ty in
      let e = translate_exp exp lopt in
      let newexp = Iast.Cast {Iast.exp_cast_target_type = t;
                              Iast.exp_cast_body = e;
                              Iast.exp_cast_pos = pos} in
      newexp
  | Cil.AddrOf _ -> report_error_msg "Error!!! Iast doesn't support Cil.AddrOf exp!"
  | Cil.StartOf _ -> report_error_msg "Error!!! Iast doesn't support Cil.StartOf exp!"


and translate_lval (lv: Cil.lval) (lopt: Cil.location option) : Iast.exp =
  let pos = match lopt with None -> no_pos | Some l -> translate_location l in
  let (lh, off) = lv in
  match (lh, off) with
  | Cil.Var v, Cil.NoOffset ->
      let name = v.Cil.vname in
      let newexp = Iast.Var {Iast.exp_var_name = name;
                             Iast.exp_var_pos = pos} in
      newexp
  | Cil.Var _, _ -> report_error_msg "Error!!! Cil.Var has to have NoOffset!"
  | Cil.Mem exp, Cil.NoOffset -> report_error_msg "TRUNG TODO: Handle (Cil.Mem _, Cil.NoOffset)  later!"
  | Cil.Mem exp, Cil.Index _ ->
      let rec collect_index (off: Cil.offset) : Iast.exp list = (
        match off with
        | Cil.NoOffset -> []
        | Cil.Field _ -> report_error_msg "Error!!! Invalid value! Have to be Cil.NoOffset or Cil.Index!"
        | Cil.Index (e, o) -> [(translate_exp e lopt)] @ (collect_index o)
      ) in
      let e = translate_exp exp lopt in
      let i = collect_index off in
      let newexp = Iast.ArrayAt {Iast.exp_arrayat_array_base = e;
                                 Iast.exp_arrayat_index = i;
                                 Iast.exp_arrayat_pos = pos} in
      newexp
  | Cil.Mem exp, Cil.Field _ ->
      let rec collect_field (off: Cil.offset) : ident list = (
        match off with
        | Cil.NoOffset -> []
        | Cil.Field (f, o) -> [(f.Cil.fname)] @ (collect_field o)
        | Cil.Index _ -> report_error_msg "Error!!! Invalid value! Have to be Cil.NoOffset or Cil.Field!"
      ) in
      let e = translate_exp exp lopt in
      let f = collect_field off in
      let newexp = Iast.Member {Iast.exp_member_base = e;
                                Iast.exp_member_fields = f;
                                Iast.exp_member_path_id = None;
                                Iast.exp_member_pos = pos} in
      newexp


and translate_instr (instr: Cil.instr) : Iast.exp =
  match instr with
  | Cil.Set (lv, exp, l) ->
      let p = translate_location l in
      let le = translate_lval lv (Some l) in
      let re = translate_exp exp (Some l) in
      let newexp = Iast.Assign {Iast.exp_assign_op = Iast.OpAssign;
                                Iast.exp_assign_lhs = le;
                                Iast.exp_assign_rhs = re;
                                Iast.exp_assign_path_id = None;
                                Iast.exp_assign_pos = p} in
      newexp
  | Cil.Call (lv_opt, exp, exps, l) ->
      let p = translate_location l in 
      let fname = match exp with
        | Cil.Const (Cil.CStr s) -> s
        | _ ->  report_error_msg "Error!!! Invalid function name!" in
      let args = List.map (fun x -> translate_exp x (Some l)) exps in
      let newexp = Iast.CallNRecv {Iast.exp_call_nrecv_method = fname;
                                   Iast.exp_call_nrecv_lock = None;
                                   Iast.exp_call_nrecv_arguments = args;
                                   Iast.exp_call_nrecv_path_id = None;
                                   Iast.exp_call_nrecv_pos = p} in
      newexp
  | Cil.Asm _ -> report_error_msg "TRUNG TODO: Handle Cil.Asm later!"


and translate_stmtkind (sk: Cil.stmtkind) (lopt: Cil.location option) : Iast.exp =
  let pos = match lopt with None -> no_pos | Some l -> translate_location l in 
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
  | Cil.Goto _ -> report_error_msg "TRUNG TODO: Iast cannot handle Cil.Goto type!"
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
      let econd = translate_exp exp (Some l) in
      let e1 = translate_block blk1 (Some l) in
      let e2 = translate_block blk2 (Some l) in
      let newexp = Iast.Cond {Iast.exp_cond_condition = econd;
                              Iast.exp_cond_then_arm = e1;
                              Iast.exp_cond_else_arm = e2;
                              Iast.exp_cond_path_id = None;
                              Iast.exp_cond_pos = pos} in
      newexp
  | Cil.Switch _ -> report_error_msg "TRUNG TODO: Handle Cil.Switch later!"
  | Cil.Loop (blk, l, stmt_opt1, stmt_opt2) ->
      let p = translate_location l in
      let cond = Iast.BoolLit {Iast.exp_bool_lit_val = true; Iast.exp_bool_lit_pos = p} in
      let body = translate_block blk (Some l) in
      let newexp = Iast.While {Iast.exp_while_condition = cond;
                               Iast.exp_while_body = body;
                               Iast.exp_while_specs = Iast.mkSpecTrue n_flow pos;
                               Iast.exp_while_jump_label = Iast.NoJumpLabel;
                               Iast.exp_while_path_id = None ;
                               Iast.exp_while_f_name = "";
                               Iast.exp_while_wrappings = None;
                               Iast.exp_while_pos = p} in
      newexp
  | Cil.Block blk -> translate_block blk None
  | Cil.TryFinally (blk1, blk2, l) ->
      let p = translate_location l in
      let e1 = translate_block blk1 (Some l) in
      let e2 = translate_block blk2 (Some l) in
      let newexp = Iast.Try {Iast.exp_try_block = e1;
                             Iast.exp_catch_clauses = [];
                             Iast.exp_finally_clause = [e2];
                             Iast.exp_try_path_id = None;
                             Iast.exp_try_pos = p} in
      newexp
  | Cil.TryExcept (blk1, (instrs, exp), blk2, l) ->
      let p = translate_location l in
      let e1 = translate_block blk1 (Some l) in
      let e2 = translate_block blk2 (Some l) in
      let newexp = Iast.Try {Iast.exp_try_block = e1;
                             (* TRUNG TODO: need to handle the catch_clause with parameter (instrs, exp) *)
                             Iast.exp_catch_clauses = [];
                             Iast.exp_finally_clause = [e2];
                             Iast.exp_try_path_id = None;
                             Iast.exp_try_pos = p} in
      newexp

and translate_stmt (s: Cil.stmt) (lopt: Cil.location option) : Iast.exp =
  let labels = s.Cil.labels in
  let skind = s.Cil.skind in
  let newskind = translate_stmtkind skind lopt in
  match labels with
  | [] -> newskind
  | [lbl] -> report_error_msg "TRUNG TODO: stmt's label has 1 element. Handle later!"
  | hd::tl -> report_error_msg "TRUNG TODO: stmt's label has >= 2 elements. Handle later!"


and translate_block (blk: Cil.block) (lopt: Cil.location option): Iast.exp =
  let stmts = blk.Cil.bstmts in
  match stmts with
  | [] -> report_error_msg "ERROR!!! block has to have at least 1 stmt element."
  | [hd] -> translate_stmt hd lopt
  | hd::tl -> (
      let e1 = translate_stmt hd lopt in
      let exps = List.map (fun x -> translate_stmt x lopt) tl in
      let l = match lopt with None -> no_pos | Some p -> translate_location p in 
      let newexp = List.fold_left (fun x y -> Iast.Seq {Iast.exp_seq_exp1 = x;
                                                        Iast.exp_seq_exp2 = y;
                                                        Iast.exp_seq_pos = l}) e1 exps in
      newexp
    )


and translate_fundec (fdec: Cil.fundec) (l: Cil.location): unit (*Iast.proc_decl*) =
  let translate_funtyp (ty: Cil.typ) : Globals.typ = (
    match ty with
    | Cil.TFun (t, params, _, _) -> translate_typ t
    | _ -> report_error_msg ("Handle TFun only."
                             ^ "Other types should be passed to translate_typ!")
  ) in
  let collect_params (fheader: Cil.varinfo) : Iast.param list = (
    let ftyp = fheader.Cil.vtype in
    let pos = translate_location fheader.Cil.vdecl in
    match ftyp with
    | Cil.TFun (_, p, _, _) -> (
        let params = Cil.argsToList p in
        let translate_one_param (p : string * Cil.typ * Cil.attributes) : Iast.param = (
          let (name, t, attrs) = p in
          let ptyp = translate_typ t in
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