(*
  let $a = <formula>.
  let $b = compose.
  let $c = <formula>.
  
  Nested composition? How to perform the composition and keep the simplified result?
  
  let $a = compose ...
  let $b = compose[x]($a, ...).

  checkentail $a |- $b.
  What problem: not really, just do the composition.
  
  Is it better to keep the mapping as 
  var -> (CF.formula, IF.formula option)

  let $a = <formula>. --> translate with no quantification
  let $b = compose($a, ...) --> compose with no quantification, don't allow $b to be used in consequent position
  
  residue will not be used in consequent position.
*)

open Globals

module I = Iast
module C = Cast
module CF = Cformula
module CP = Cpure
module IF = Iformula
module IP = Ipure

module H = Hashtbl

exception SLEEK_Exception

type command =
  | DataDef of I.data_decl
  | PredDef of I.view_decl
  | FuncDef of I.func_decl
  | RelDef of I.rel_decl (* An Hoa *)
  | HpDef of I.hp_decl
  | AxiomDef of I.axiom_decl (* [4/10/2011] An Hoa *)
  | LemmaDef of I.coercion_decl
  | LetDef of (ident * meta_formula)
  | EntailCheck of (meta_formula * meta_formula)
  | EqCheck of (ident list * meta_formula * meta_formula)
  | BarrierCheck of I.barrier_decl
  | Infer of (ident list * meta_formula * meta_formula)
  | CaptureResidue of ident
  | PrintCmd of print_cmd
  | CmpCmd of (ident list * ident * meta_formula)
  | Time of (bool*string*loc)
  | EmptyCmd 

and print_cmd =
  | PVar of ident
  | PCmd of ident
	  
and meta_formula =
  | MetaVar of ident
  | MetaForm of IF.formula
  | MetaFormCF of CF.formula
  | MetaFormLCF of CF.list_formula
  | MetaEForm of Iformula.struc_formula
  | MetaEFormCF of CF.struc_formula
  | MetaCompose of (ident list * meta_formula * meta_formula)

(*
  The second component is IF.formula and not CF.formula since
  depending on how the formula is used (in negative or positive
  position of an entailment), it will get translated differently.
  Therefore we keep the original version and do the translations
  according to different usage.
*)

type var_table_t = (ident, meta_formula) H.t

let var_tab : var_table_t = H.create 10240

let string_of_command c = match c with
  | DataDef _ -> "DataDef"
  | PredDef _ -> "PredDef" 
  | FuncDef  _ -> "FuncDef"  
  | RelDef  _ -> "RelDef"  
  | HpDef  _ -> "HpDef"  
  | AxiomDef  _ -> "AxiomDef"  
  | LemmaDef  _ -> "LemmaDef"
  | LetDef  _ -> "LetDef"   
  | EntailCheck _ -> "EntailCheck"
  | EqCheck _ -> "EqCheck"
  | BarrierCheck _ -> "BarrierCheck"
  | Infer _ -> "Infer"
  | CaptureResidue _ -> "CaptureResidue"  
  | PrintCmd _ -> "PrintCmd"  
  | CmpCmd _ -> "CmpCmd"  
  | Time _ -> "Time"
  | EmptyCmd -> "EmptyCmd"

let put_var (v : ident) (info : meta_formula) = H.add var_tab v info

let get_var (v : ident) : meta_formula = H.find var_tab v

(* An Hoa : String representation of meta_formula *)
let string_of_meta_formula (mf : meta_formula) = 
	match mf with
  | MetaVar i -> i
  | MetaForm f -> "IFORM:"^Iprinter.string_of_formula f
  | MetaFormCF cf ->  "CFORM:"^Cprinter.string_of_formula cf
  | MetaFormLCF lf -> "" (* TODO Implement *)
  | MetaEForm sf -> "IFORMStruc:"^Iprinter.string_of_struc_formula sf
  | MetaEFormCF sf -> "CFORMStruc:"^Cprinter.string_of_struc_formula sf
  | MetaCompose _ -> "" (* TODO Implement *)

let clear_var_table () = H.clear var_tab

(*
  let get_var (v : ident) : let_body =
  H.find var_tab v
  
  let put_var (v : ident) (body : let_body) =
  H.add var_tab v body
  
  let formula_of_var (v : ident) pos : IF.formula =
  let lbody = get_var v in
  match lbody with
  | LetForm lf -> lf
  | 
*)
