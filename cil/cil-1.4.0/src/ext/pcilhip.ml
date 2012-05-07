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

    (*** INSTRUCTIONS ****)
    (*method pInstr () (i:instr) =       (* imperative instruction *)
      match i with
      | Set(lv,e,l) -> (
          (* Be nice to some special cases *)
          match e with
          | BinOp((PlusA|PlusPI|IndexPI),Lval(lv'),Const(CInt64(one,_,_)),_)
              when Util.equals lv lv' && one = Int64.one && not !printCilAsIs ->
                self#pLineDirective l
                  ++ self#pLvalPrec indexLevel () lv
                  ++ text (" ++" ^ self#getPrintInstrTerminator())
  
          | BinOp((MinusA|MinusPI),Lval(lv'),
                  Const(CInt64(one,_,_)), _) 
              when Util.equals lv lv' && one = Int64.one && not !printCilAsIs ->
                    self#pLineDirective l
                      ++ self#pLvalPrec indexLevel () lv
                      ++ text (" --" ^ self#getPrintInstrTerminator()) 
  
          | BinOp((PlusA|PlusPI|IndexPI),Lval(lv'),Const(CInt64(mone,_,_)),_)
              when Util.equals lv lv' && mone = Int64.minus_one 
                  && not !printCilAsIs ->
                self#pLineDirective l
                  ++ super#pLvalPrec indexLevel () lv
                  ++ text (" --" ^ self#getPrintInstrTerminator())
  
          | BinOp((PlusA|PlusPI|IndexPI|MinusA|MinusPP|MinusPI|BAnd|BOr|BXor|
            Mult|Div|Mod|Shiftlt|Shiftrt) as bop,
                  Lval(lv'),e,_) when Util.equals lv lv' 
                  && not !printCilAsIs ->
                    self#pLineDirective l
                      ++ self#pLval () lv
                      ++ text " " ++ d_binop () bop
                      ++ text "= "
                      ++ self#pExp () e
                      ++ text (self#getPrintInstrTerminator())
                      
          | _ ->
              self#pLineDirective l
                ++ self#pLval () lv
                ++ text " = "
                ++ self#pExp () e
                ++ text (self#getPrintInstrTerminator())
                
        )
      | _ -> super#pInstr () i *)

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
  method vglob (g : global) =
    let _ = print_endline "global" in
    let _ = 
    match g with
      | GVarDecl (vinfo, p) ->
          print_endline "global variables"
      (*
          if vinfo.vglob then ()
            (*add keyword global at the beginning*)
          else ()
          *)
      | GCompTag (cinfo, p) -> print_endline "handle data structures declaration here"
      | _ -> print_endline "not global var declaration, handle later"
    in
    DoChildren

end

let hip_transform (f : file) : unit =
  let _ = visitCilFile (new hipVisitor) f in ()
  (* Cil.dumpFile (new hipCilPrinterClass) stdout "output.cil" f *)

let feature : featureDescr = 
  { fd_name = "hip";
    fd_enabled = ref false;
    fd_description = "transform to HIP format";
    fd_extraopt = [];
    fd_doit = hip_transform;
    fd_post_check = true;
  } 
