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
  | LemmaDef of I.coercion_decl
  | PureLemmaDef of I.pure_derive
  | LetDef of (ident * meta_formula)
  | EntailCheck of (meta_formula * meta_formula)
  | CaptureResidue of ident
  | PrintCmd of print_cmd
  | Time of (bool*string*loc)
  | PurePredDef of I.pure_pred_decl
  | CheckEntailPure of I.pure_derive
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
  | MetaCompose of (ident list * meta_formula * meta_formula)

(*
  The second component is IF.formula and not CF.formula since
  depending on how the formula is used (in negative or positive
  position of an entailment), it will get translated differently.
  Therefore we keep the original version and do the translations
  according to different usage.
*)

type var_table_t = (ident, meta_formula) H.t

(*create a new hash table named var_tab that has type var_table_t with
 * size 10240*)
let var_tab : var_table_t = H.create 10240

let put_var (v : ident) (info : meta_formula) = H.add var_tab v info

let get_var (v : ident) : meta_formula = H.find var_tab v

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
let rec string_of_string_list li =
  match li with
    |head::tail -> head ^ (string_of_string_list tail)
    |[] -> "\n"

let rec string_of_meta_formula meta =
  match meta with
    |MetaVar id -> "MetaVar " ^ id ^"\n"
    |MetaForm form -> "MetaForm " ^ Iprinter.string_of_formula form ^"\n"
    |MetaFormCF cform -> "MetaFormCF " ^Cprinter.string_of_formula cform ^"\n"
    |MetaEForm struc -> "MetaEForm " ^ Iprinter.string_of_struc_formula struc ^ "\n"
    |MetaCompose (li, meta1, meta2) -> "MetaCompose " ^string_of_string_list li ^ (string_of_meta_formula meta1)^" " ^string_of_meta_formula meta2 ^"\n"
	
let rec string_of_print_cmd p_cmd =
  match p_cmd with
    |PVar id -> "PVar " ^id
    |PCmd id -> "PCmd " ^id

let rec string_of_command cmd = 
  match cmd with
    |DataDef iast_data_decl -> "DataDef "^ (Iprinter.string_of_data_decl iast_data_decl)^"\n"
    |LemmaDef iast_coercion_decl -> "LemmaDef " ^(Iprinter.string_of_coerc_decl iast_coercion_decl) ^"\n"
    |PredDef iast_view_decl -> "PredDef " ^(Iprinter.string_of_view_decl iast_view_decl) ^ "\n"
 (*added Oct 16 2010*)
    | PurePredDef iast_pure_pred_decl -> "PurePredDef " ^(Iprinter.string_of_pure_pred_decl iast_pure_pred_decl) ^ "\n"
    |LetDef (id, meta) -> "LetDef ident:"^id ^"meta: "^string_of_meta_formula meta^"\n"
    |EntailCheck (meta1, meta2) -> "EntailCheck meta1: " ^string_of_meta_formula meta1 ^ " meta2: "^string_of_meta_formula meta2 ^"\n"
    |CaptureResidue id -> "CaptureResidue " ^id^"\n"
    |PrintCmd p_cmd -> "PrintCmd "^string_of_print_cmd p_cmd^"\n"
    |Time (b, str, loc)-> "Time "^string_of_bool b ^ " "^str ^"\n"
    |CheckEntailPure pure -> "CheckEntailPure "^Iprinter.string_of_pure_derive pure^"\n"
    |PureLemmaDef pldef -> "PureLemma " ^ Iprinter.string_of_pure_derive pldef ^ "\n"
    |EmptyCmd -> "EmptyCmd \n"

let rec string_of_command_list cmd_list = 
  match cmd_list with
    |head::tail -> (string_of_command head)^"\n" ^(string_of_command_list tail)
    |[] ->"" 
