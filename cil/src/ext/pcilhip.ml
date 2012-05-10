open Cil
open Pretty
module E = Errormsg

let debug = false

(*printer*)
class  hipCilPrinterClass =
  object (self)
    inherit defaultCilPrinterClass as super

    method pGlobal () (g:global) : doc =       (* global (vars, types, etc.) *)
      match g with
      | GVar (vi, io, l) ->
          self#pLineDirective ~forcefile:true l
          ++ text ("global ")
          ++ self#pVDecl () vi
          ++ chr ' '
          ++ (match io.init with
              | None -> nil
              | Some i -> text " = "
                  ++ (let islong = match i with
                                   | CompoundInit (_, il) when List.length il >= 8 -> true
                                   | _ -> false in
                     if islong then line ++ self#pLineDirective l ++ text "  "
                     else nil)
                  ++ (self#pInit () i))
          ++ text ";\n"

      | _ -> super#pGlobal () g

    method private pLvalPrec (contextprec: int) () lv = 
      if getParenthLevel (Lval(lv)) >= contextprec then
        text "(" ++ self#pLval () lv ++ text ")"
      else
        self#pLval () lv

    (*** INSTRUCTIONS ****)
    method pInstr () (i:instr) =       (* imperative instruction *)
      match i with
      | Set(lv,e,l) -> (
          (* Be nice to some special cases *)
          match e with
          | BinOp((PlusA|PlusPI|IndexPI),Lval(lv'),Const(CInt64(one,_,_)),_)
              when Util.equals lv lv' && one = Int64.one && not !printCilAsIs ->
                self#pLineDirective l
                  ++ self#pLvalPrec indexLevel () lv
                  ++ text (" = ")
                  ++ self#pLvalPrec indexLevel () lv
                  ++ text (" + 1" ^ self#getPrintInstrTerminator())

          | BinOp((MinusA|MinusPI),Lval(lv'),
                  Const(CInt64(one,_,_)), _)
              when Util.equals lv lv' && one = Int64.one && not !printCilAsIs ->
                self#pLineDirective l
                  ++ self#pLvalPrec indexLevel () lv
                  ++ text (" = ")
                  ++ self#pLvalPrec indexLevel () lv
                  ++ text (" - 1" ^ self#getPrintInstrTerminator())

          | BinOp((PlusA|PlusPI|IndexPI),Lval(lv'),Const(CInt64(mone,_,_)),_)
              when Util.equals lv lv' && mone = Int64.minus_one && not !printCilAsIs ->
                self#pLineDirective l
                  ++ self#pLvalPrec indexLevel () lv
                  ++ text (" = ")
                  ++ self#pLvalPrec indexLevel () lv
                  ++ text (" - 1" ^ self#getPrintInstrTerminator())
          | _ -> super#pInstr () i
        )

      | _ -> super#pInstr () i

  end (* end class hipCilPrinterClass *)

class hipVisitor = object
  inherit nopCilVisitor

  (* Invoked for each variable declaration.*)
  method vvdec (vinfo : varinfo) =
    DoChildren


  (*Invoked on each variable use. [SkipChildren] or [ChangeTo]*)
  method vvrbl (vinfo : varinfo) =
    
    DoChildren

  (*Function definition.Replaced in place. *)
  method vfunc (f:fundec)=
    DoChildren

  (* Global (vars, types, etc.)  *)
  method vglob (g : Cil.global) =
    
    match g with
    | GVar (vinfo, init, loc) ->
        let _ = print_endline ("global var: " ^ vinfo.vname) in
        (* let new_vinfo = {vinfo with vattr = [Attr ("global", [])] @ vinfo.vattr} in *)
        (* ChangeTo [GVar (new_vinfo, init, loc)]; *)
        ChangeTo [GVar (vinfo, init, loc)];
    (* | GVarDecl (vinfo, p) ->                                     *)
    (*     let _ = print_endline ("global decl: " ^ vinfo.vname) in *)
    (*     let new_vinfo = {vinfo with vname = vinfo.vname} in      *)
    (*     ChangeTo [GVarDecl (new_vinfo, p)];                      *)
      (*
          if vinfo.vglob then ()
            (*add keyword global at the beginning*)
          else ()
          *)
    | GCompTag (cinfo, p) -> print_endline "handle data structures declaration here"; DoChildren
    | _ -> print_endline "not global var declaration, handle later"; DoChildren

  (* method vinst (i: instr) : instr list visitAction =                                   *)
  (*   match i with                                                                       *)
  (*   | Set(lv, e, l) -> begin                                                           *)
  (*       (* Check if we need to log *)                                                  *)
  (*       match lv with                                                                  *)
  (*         (Var(v), off) when not v.vglob -> SkipChildren                               *)
  (*       | _ -> let str = Pretty.sprint 80                                              *)
  (*               (Pretty.dprintf "Write %%p to 0x%%08x at %%s:%%d (%a)\n" d_lval lv)    *)
  (*             in                                                                       *)
  (*             ChangeTo                                                                 *)
  (*             [ Call((None), (Lval(Var(printfFun.svar),NoOffset)),                     *)
  (*                    [ one ;                                                           *)
  (*                      mkString str ; e ; addr_of_lv lv;                               *)
  (*                      mkString l.file;                                                *)
  (*                      integer l.line], locUnknown);                                   *)
  (*             i]                                                                       *)
  (*     end                                                                              *)
  (*   | Call(Some lv, f, args, l) -> begin                                               *)
  (*       (* Check if we need to log *)                                                  *)
  (*       match lv with                                                                  *)
  (*         (Var(v), off) when not v.vglob -> SkipChildren                               *)
  (*       | _ -> let str = Pretty.sprint 80                                              *)
  (*               (Pretty.dprintf "Write retval to 0x%%08x at %%s:%%d (%a)\n" d_lval lv) *)
  (*             in                                                                       *)
  (*             ChangeTo                                                                 *)
  (*             [ Call((None), (Lval(Var(printfFun.svar),NoOffset)),                     *)
  (*                    [ one ;                                                           *)
  (*                      mkString str ; AddrOf lv;                                       *)
  (*                      mkString l.file;                                                *)
  (*                      integer l.line], locUnknown);                                   *)
  (*             i]                                                                       *)
  (*     end                                                                              *)
  (*   | _ -> SkipChildren                                                                *)

end

let hip_transform (f : file) : unit =
  let _ = visitCilFile (new hipVisitor) f in ()
   (*Cil.dumpFile (new hipCilPrinterClass) stdout "output.cil" f*)

let feature : featureDescr = 
  { fd_name = "hip";
    fd_enabled = ref false;
    fd_description = "transform to HIP format";
    fd_extraopt = [];
    fd_doit = hip_transform;
    fd_post_check = true;
  } 
