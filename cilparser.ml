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

let translate_var_typ (t: Cil.typ) : Globals.typ =
  let newtype = 
    match t with
    | Cil.TVoid _            -> Globals.Void
    | Cil.TInt _             -> Globals.Int 
    | Cil.TFloat _           -> Globals.Float 
    | Cil.TPtr _             -> report_error_msg "TRUNG: handle TPtr later!"  
    | Cil.TArray _           -> report_error_msg "TRUNG: handle TArray later!"
    | Cil.TFun _             -> report_error_msg "Should not appear here. Handle only in translate_fun_typ"
    | Cil.TNamed _           -> report_error_msg "TRUNG: handle TNamed later!"
    | Cil.TComp _            -> report_error_msg "TRUNG: handle TComp later!"
    | Cil.TEnum _            -> report_error_msg "TRUNG: handle TEnum later!"
    | Cil.TBuiltin_va_list _ -> report_error_msg "TRUNG: handle TBuiltin_va_list later!" in
  (* return *)
  newtype

let translate_fun_typ (ty: Cil.typ) : Globals.typ =
  match ty with
  | Cil.TFun (t, params, _, _) -> translate_var_typ t
  | _ -> report_error_msg ("Only handle TFun here."
                           ^ "Other types should be passed to translate_var_typ!")

let collect_fun_params (fheader: Cil.varinfo) : Iast.param list =
  let ftyp = fheader.Cil.vtype in
  let pos = translate_location fheader.Cil.vdecl in
  match ftyp with
  | Cil.TFun (_, p, _, _) ->
      let params = Cil.argsToList p in
      let translate_one_param (p : string * Cil.typ * Cil.attributes) : Iast.param = (
        let (name, t, attrs) = p in
        let ptyp = translate_var_typ t in
        let is_mod = (
          List.exists (
            fun attr -> (
              let attrparas = match attr with Cil.Attr (_, aps) -> aps in
              List.exists (
                fun attrpara ->
                  match attrpara with
                  | Cil.AStar _ -> true
                  | _           -> false
              ) attrparas
            )
          ) attrs
        ) in
        let newparam = { Iast.param_type = ptyp;
                         Iast.param_name = name;
                         Iast.param_mod = if is_mod then Iast.RefMod else Iast.NoMod;
                         Iast.param_loc = pos; } in
        newparam
      ) in
      (* return *)
      List.map translate_one_param params
  | _ -> report_error_msg "Invalid function header!"

let translate_fundec (fdec: Cil.fundec) (loc: Cil.location): unit (*Iast.proc_decl*) =
  let fheader = fdec.Cil.svar in
  let proc_name = fheader.Cil.vname in
  let proc_mingled_name = "" in (* TRUNG CODE: check it later *)
  let proc_return = translate_fun_typ (fheader.Cil.vtype) in
  let proc_args = collect_fun_params fheader in
  let proc_loc = translate_location loc in
  let 
  let sfun = "proc_name = " ^ proc_name ^ "\n"
             ^ "type = " ^ (Globals.string_of_typ proc_return) ^ "\n" in
  let _ = print_endline sfun in
  (* ()                                 *)
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
  let defaultCilPrinter = new Cil.defaultCilPrinterClass in
  let globals = cil.Cil.globals in
  let _ = print_endline ("globals length = " ^ (string_of_int (List.length globals))) in 
  List.iter (
    fun gl ->
      match gl with
        | Cil.GFun (fd, loc) -> translate_fundec fd loc
        | _          -> print_endline ("== Unknown globals"); 
      (* print *)
      (* let doc = Cil.printGlobal defaultCilPrinter () gl in *)
      (* let s = Pretty.sprint 0 doc in                       *)
      (* print_endline ("++ global " ^ gltype ^ "\n" ^ s)     *)
  ) globals

let print_helper s = 
  print_endline ("helper: " ^ s)

