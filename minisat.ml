#include "xdebug.cppo"
open VarGen
open Globals
open GlobProver
open Gen.Basic
open Cpure
(* open Rtc_new_stable *)
(* open Rtc_new_algorithm *)
open Rtc_algorithm

module StringSet = Set.Make(String)

(* Global settings *)
let minisat_timeout_limit = 15.0

let test_number = ref 0
let last_test_number = ref 0
let minisat_restart_interval = ref (-1)
let log_all_flag = ref false
let is_minisat_running = ref false
let in_timeout = ref 15.0 (* default timeout is 15 seconds *)
let minisat_call_count: int ref = ref 0
let log_file = open_log_out ("allinput.minisat")
let minisat_input_mode = "file"    (* valid value is: "file" or "stdin" *) 

(*minisat*)
let minisat_path = "/usr/local/bin/minisat"
let minisat_name = "minisat"
let minisat_arg = "-pre"(*"-pre"*)

let minisat_path_crypt = "/home/bachle/improve_rtc_algo/sleekex"
let minisat_name_crypt = "cryptominisat"
let minisat_arg_crypt = "--no-simplify --nosatelite --gaussuntil=3"

let minisat_path2 = (*"/home/bachle/improve_rtc_algo/sleekex/cryptominisat"*)"minisat"
(* let minisat_name2 = (\*"cryptominisat"*\)"minisat22" *)
let minisat_name2 = (*"cryptominisat"*)"minisat"
let minisat_arg2 = ""(*"-pre"*)

let eq_path = "equality_logic"
let eq_name = "equality_logic"
let eq_arg = "equality_logic"
let minisat_input_format = "cnf"   (* valid value is: cnf *)
  (* let number_clauses = ref 1 *)
let number_vars = ref 0
let len=1000
  (* let bcl= ref [] *)
let sat= ref true
let minisat_process = ref {  name = "minisat";
pid = 0;
inchannel = stdin;
outchannel = stdout;
errchannel = stdin 
}
  (***************************************************************
                                                                  TRANSLATE CPURE FORMULA TO PROBLEM IN CNF FORMAT
  **************************************************************)
  (*minisat*)
let de_morgan f=match f with 
  |Not (And(f1,f2,_),l1,l2)-> Or(Not(f1,l1,l2), Not (f2,l1,l2),l1,l2)
  |Not (Or(f1,f2,_,_),l1,l2)-> And(Not(f1,l1,l2),Not(f2,l1,l2),l2)  
  |_->f
let double_negative f= match f with
  |Not (Not(f1,_,_),_,_)->f1
  |_->f
let minisat_cnf_of_spec_var sv = let ident=Cpure.name_of_spec_var sv in ident

let rec minisat_of_exp e0 = match e0 with
  | Null _ -> "null_var"
  | Var (sv, _) -> minisat_cnf_of_spec_var sv
  | IConst (i, _) -> string_of_int i
  | AConst (i, _) -> illegal_format ("eq_logic.eq_logic_of_exp: array, bag or list constraint")
  | Add (a1, a2, _) -> illegal_format ("eq_logic.eq_logic_of_exp: array, bag or list constraint")
  | Subtract (a1, a2, _) -> illegal_format ("eq_logic.eq_logic_of_exp: array, bag or list constraint")
  | Mult (a1, a2, l) -> illegal_format ("eq_logic.eq_logic_of_exp: array, bag or list constraint")
  | Div (a1, a2, l) -> illegal_format ("eq_logic.eq_logic_of_exp: array, bag or list constraint")
  | Max _
  | Min _ -> illegal_format ("eq_logic.eq_logic_of_exp: min/max should not appear here")
  | TypeCast _ -> illegal_format ("eq_logic.eq_logic_of_exp: TypeCast should not appear here")
  | FConst _ -> illegal_format ("eq_logic.eq_logic_of_exp: FConst")
  | Func _ -> "0" (* TODO: Need to handle *)
  | _ -> illegal_format ("eq_logic.eq_logic_of_exp: array, bag or list constraint")


(*-------------------------------Functions are used for generating cnf of CNF formula--------------------*)

(* let addBooleanConst v =                                                                        *)
(* 	let _= print_endline ("length of bcl:"^ string_of_int (List.length !bcl) ) in (*Debug-bach*) *)
(* 	let index= ref 0 in                                                                          *)
(* 				 begin                                                                                 *)
(* 				 for i=0 to (List.length !bcl)-1 do                                                    *)
(*                                      (                                                         *)
(* 				       if v=(List.nth !bcl i) then (index:=i+len)                                      *)
(* 				     )                                                                                 *)
(* 				 done;                                                                                 *)
(* 					if(!index>0) then string_of_int !index                                               *)
(* 					else let _= bcl:= !bcl@[v] in (string_of_int ((List.length !bcl)+len-1))             *)
(* 				 end                                                                                   *)


let  minisat_cnf_of_p_formula (pf : Cpure.p_formula) (allvars:Glabel.t) (ge:G.t) (gd:G.t) =
  match pf with
    | Frm (sv, _)    -> ""
    | LexVar _        -> ""
    | BConst (c, _)   -> (*let _=print_endline ("minisat_cnf_of_p_formula_for_helper BConst EXIT!")  in*) ""
    | XPure _ -> "" (* WN : weakening *)
    | BVar (sv, pos)    -> 
          let _= x_binfo_hp (add_str "minisat_cnf_of_p_formula Bvar" minisat_cnf_of_spec_var) sv pos 
          in ""
    | Lt _            -> ""
    | Lte _           -> ""
    | Gt _            -> ""
    | Gte _           -> ""
    | SubAnn _        -> ""
    | Eq (e1, e2, _)  ->  
          (*Handle here*)let li=minisat_of_exp e1 and ri=minisat_of_exp e2 in
          (* let () = print_endline("minisat of e1: "^li^" minisat of e2: "^ri) in *)
          (* if(li=ri) then                                    *)
          (* 	begin                                           *)
          (* 	let index=addBooleanConst (li) in index         *)
          (* 	end                                             *)
          (* 	else(*add xx to the set of boolean constants *) *)
          let eq_edge=G.E.create li () ri in
          let _= G.add_edge_e ge eq_edge in
          (* let mem=Glabel.mem_edge allvars li ri in *)
          (* let _=if(mem=false)then                  *)
          let _=
	    begin
	      let _=number_vars := !number_vars+1 in 
	      let cx=Glabel.E.create li (ref (string_of_int !number_vars)) ri in 
	      Glabel.add_edge_e allvars cx
	    end
          in	   	
          (*let rtc=new rTC in*) 
          let lr=get_var li ri allvars in 
          lr
    | Neq (e1, e2, _) -> (*Handle here*)let li=minisat_of_exp e1 and ri=minisat_of_exp e2 in
      (* if(li=ri) then (let index=addBooleanConst (li) in ("-"^index))  *)
      (* else(*add xx to the set of boolean constants *)                 *)
      let diseq_edge=G.E.create li () ri in
      let _= G.add_edge_e gd diseq_edge in
      (* let mem=Glabel.mem_edge allvars li ri in *)
      (* let _=if(mem=false)then                  *)
      let _=
	begin
	  let _=number_vars := !number_vars+1 in 
	  let cx=Glabel.E.create li (ref (string_of_int !number_vars)) ri in 
	  Glabel.add_edge_e allvars cx
	end
      in	   	 	
      (*let rtc=new rTC in*) let lr=get_var li ri allvars
      in "-"^lr
    | EqMax _         -> ""
    | EqMin _         -> ""
          (* bag formulas *)
    | BagIn _
    | BagNotIn _
    | BagSub _
    | BagMin _
    | BagMax _        -> ""
          (* list formulas *)
    | ListIn _
    | ListNotIn _
    | ListAllN _
    | ListPerm _
    | RelForm _       -> "" 
    (* | VarPerm _ -> Error.report_no_pattern () *)

let minisat_cnf_of_b_formula (bf : Cpure.b_formula) (allvars:Glabel.t) (ge:G.t) (gd:G.t)=
  
  match bf with
    | (pf, _) -> minisat_cnf_of_p_formula pf allvars ge gd

let  minisat_cnf_of_not_of_p_formula (pf : Cpure.p_formula) (allvars:Glabel.t) (ge:G.t) (gd:G.t) =
  match pf with
    | Frm _ -> ""
    | LexVar _        -> ""
    | BConst (c, _)   -> (*let _=print_endline ("minisat_cnf_of_not_of_p_formula_for_helper BConst EXIT!")  in*) ""
    | BVar (sv, _)    -> (*let _=print_endline ("minisat_cnf_of_not_of_p_formula_for_helper Bvar EXIT!")  in*) ""
    | Lt _            -> ""
    | Lte _           -> ""
    | Gt _            -> ""
    | Gte _           -> ""
    | SubAnn _        -> ""
    | Eq (e1, e2, _)  -> (*Handle here*)let li=minisat_of_exp e1 and ri=minisat_of_exp e2 in
      (* if(li=ri) then                                                                                *)
      (* 	begin                                                                                       *)
      (* 		let index=addBooleanConst (li) in ("-"^index)(*add -xx to the set of boolean constants *) *)
      (* 		end                                                                                       *)
      (* else                                                                                          *)
      let diseq_edge=G.E.create li () ri in
      let _= G.add_edge_e gd diseq_edge in
      (* let mem=Glabel.mem_edge allvars li ri in *)
      (* let _=if(mem=false)then                  *)
      let _=
	begin
	  let _=number_vars := !number_vars+1 in 
	  let cx=Glabel.E.create li (ref (string_of_int !number_vars)) ri in 
	  Glabel.add_edge_e allvars cx
	end
      in	   	 	
      (*let rtc=new rTC in *)let lr=get_var li ri allvars in
      "-"^lr 
    | Neq (e1, e2, _) -> (*Handle here*)let li=minisat_of_exp e1 and ri=minisat_of_exp e2 in
      (* if(li=ri) then (let index=addBooleanConst li in index ) (*add xx to the set of boolean constants *) *)
      (* else                                                                                                *)
      let eq_edge=G.E.create li () ri in
      let _= G.add_edge_e ge eq_edge in
      (* let mem=Glabel.mem_edge allvars li ri in *)
      (* let _=if(mem=false)then                  *)
      let _=
	begin
	  let _=number_vars := !number_vars+1 in 
	  let cx=Glabel.E.create li (ref (string_of_int !number_vars)) ri in 
	  Glabel.add_edge_e allvars cx
	end
      in	   	 	 
      (*let rtc=new rTC in *) let lr=get_var li ri allvars in
      lr 
    | EqMax _         -> ""
    | EqMin _         -> ""
          (* bag formulas *)
    | BagIn _
    | BagNotIn _
    | BagSub _
    | BagMin _
    | BagMax _        -> ""
          (* list formulas *)
    | ListIn _
    | ListNotIn _
    | ListAllN _
    | ListPerm _
    | RelForm _       -> ""
    | XPure _ (* | VarPerm _ *) -> Error.report_no_pattern ()

let minisat_cnf_of_not_of_b_formula (bf : Cpure.b_formula) (allvars:Glabel.t) (ge:G.t) (gd:G.t) =
  match bf with
    | (pf, _) -> minisat_cnf_of_not_of_p_formula pf allvars ge gd


(*----------------------------------Functions are used for generating T-----------------------------------*)


(*---------------------------------------CNF conversion here-----------------------------------*)
let return_pure bf f= match bf with
  | (pf,_)-> match pf with 
      | Eq _ -> f
      | Neq _ -> f
      | Frm _ -> f
      | BConst(a,_)->f (*let _=if(a) then print_endline ("TRUE") else print_endline ("FALSE")  in*)
      | BVar(_,_)->f
      | XPure _ | LexVar _ | Lt _ | Lte _ | Gt _ | Gte _ | SubAnn _ | EqMax _ | EqMin _ | BagIn _ | BagNotIn _ | BagSub _ 
      | BagMin _ | BagMax _ (* | VarPerm _ *) | ListIn _ | ListNotIn _ | ListAllN _ | ListPerm _ | RelForm _ -> Error.report_no_pattern ()

(*For converting to NNF--no need??--*)
let rec minisat_cnf_of_formula f =
  match f with
    | BForm (b, _)         -> (*return_pure b *)f
    | And (f1, f2, l1)      ->   And(minisat_cnf_of_formula f1,minisat_cnf_of_formula f2,l1)  
    | Or (f1, f2, l1, l2)    ->   Or(minisat_cnf_of_formula f1,minisat_cnf_of_formula f2,l1,l2)    
    | Not (BForm(b,_), _, _) -> return_pure b f
    | _ -> minisat_cnf_of_formula (de_morgan (double_negative f));; 

(*let rec cnf_to_string f =                                               *)
(*  match f with                                                          *)
(*  |BForm (b,_)-> minisat_cnf_of_b_formula b                             *)
(*  |Not (f1,_,_)->"-"^cnf_to_string f1                                   *)
(*  |And (f1, f2, _) -> "("^(cnf_to_string f1)^"&"^(cnf_to_string f2)^")" *)
(*  |Or  (f1, f2, _, _)->"("^(cnf_to_string f1)^"v"^(cnf_to_string f2)^")"*)

(* let incr_cls= number_clauses:=1 + !number_clauses *)


(*let rec cnf_to_string_to_file f (map: spec_var list)=                                                           *)
(*  match f with                                                                                                  *)
(*  |BForm (b,_)-> let var=minisat_cnf_of_b_formula b map in check_inmap var map                                  *)
(*  |Not (f1,_,_)->"-"^cnf_to_string_to_file f1 map                                                               *)
(*  |And (f1, f2, _) -> let _= incr_cls in (cnf_to_string_to_file f1 map)^" 0"^"\n"^(cnf_to_string_to_file f2 map)*)
(*  |Or  (f1, f2, _, _)-> (cnf_to_string_to_file f1 map)^" "^(cnf_to_string_to_file f2 map)                       *)

(*For CNF conversion*)
let unsat_in_cnf (bf : Cpure.b_formula) =
  match bf with
    | (pf, _) -> match pf with
	| Neq(e1,e2,_)->let li=minisat_of_exp e1 and ri=minisat_of_exp e2 in
	  let _=if(li=ri) then  let _=print_endline_quiet ("UNSAT CNF") (*Debug-bach*)in sat:=false in ()
	| _->()					
	      
let rec has_and f =
  match f with
    |BForm _ -> false 
    |And(_,_,_)->true
    |Or(f1,f2,_,_) -> if(has_and f1) then true else if (has_and f2) then true else false
    | _->false

and is_cnf_old2 f = 
  match f with
    | BForm _ -> true
    | Or (f1,f2,_,_)-> if(has_and f1) then false  else if (has_and f2) then false else true
    | And (BForm(b,_),f2,_)->let _=unsat_in_cnf b in if(!sat=true) then is_cnf f2 else true
    | And (f1,BForm(b,_),_)->let _=unsat_in_cnf b in if(!sat=true) then is_cnf f1 else true
    | And (f1,f2,_)-> if(is_cnf f1) then is_cnf f2 else false
    | AndList _ | Not _ |  Forall _ | Exists _ -> Error.report_no_pattern ()

and is_cnf_old1 f = (*Should use heuristic in CNF*)
  match f with
    | BForm _ -> true
    | Or (f1,f2,_,_)-> if(has_and f1) then false  else if (has_and f2) then false else true
    | And (BForm(b,_),f2,_)->is_cnf f2 
    | And (f1,BForm(b,_),_)->is_cnf f1 
    | And (f1,f2,_)-> if(is_cnf f1) then is_cnf f2 else false
    | AndList _ | Not _ | Forall _ | Exists _ -> Error.report_no_pattern()

and is_cnf f = (*Should use heuristic in CNF*)
  match f with
    | BForm _ -> true
    | Or (f1,f2,_,_)-> if(has_and f1) then false  else if (has_and f2) then false else true
    | And (BForm(b,_),f2,_)->is_cnf f2 
    | And (f1,BForm(b,_),_)->is_cnf f1 
    | And (f1,f2,_)-> if(is_cnf f1) then is_cnf f2 else false
    | _->	 let _=print_endline_quiet ("CNF conv here: "^Cprinter.string_of_pure_formula f) in true

(* distributive law 1 - (f & k) v (g & h) -> (f v g) & (f v h) & (k v g) & (k v h) *)
let dist_1 f = 
  match f with (*using heuristic for the first one*)
    | Or(f1, And(f2, f3,_),l1,l2) -> Or (f1,f3,l1,l2)(*And(Or(f1, f2,l1,l2), Or(f1, f3,l1,l2),l2)*) (*The main here- when using slicing*)
          (*| Or(And(f1, f2,_), And(f3, f4,_),l1,l2) ->And(And(Or(f1, f3,l1,l2), Or(f1, f4,l1,l2),l2), And(Or(f2, f3,l1,l2), Or(f2, f4,l1,l2),l2),l2)*)
    | Or(And(f2, f3,_), f1,l1,l2) -> And(Or(f1, f2,l1,l2), Or(f1, f3,l1,l2),l2)
    | _ -> f

let dist_no_slicing f = 
  match f with 
    | Or(f1, And(f2, f3,_),l1,l2) -> And(Or(f1, f2,l1,l2), Or(f1, f3,l1,l2),l2) (*The main here- when using slicing*)
	  (*| Or(And(f1, f2,_), And(f3, f4,_),l1,l2) ->And(And(Or(f1, f3,l1,l2), Or(f1, f4,l1,l2),l2), And(Or(f2, f3,l1,l2), Or(f2, f4,l1,l2),l2),l2)*)
    | Or(And(f2, f3,_), f1,l1,l2) -> And(Or(f1, f2,l1,l2), Or(f1, f3,l1,l2),l2)
    | _ -> f


let rec nnf_to_xxx f rule =
  let nf = match f with  
      BForm (b,_) -> return_pure b f 
    | Not (f1,l1,l2) -> Not ((nnf_to_xxx f1 rule),l1,l2)
    | And (f1, f2,l1) -> And (nnf_to_xxx f1 rule, nnf_to_xxx f2 rule,l1)
    | Or (f1, f2,l1,l2) -> Or (nnf_to_xxx f1 rule, nnf_to_xxx f2 rule,l1,l2)
    | Exists (_,f1,_,_) -> nnf_to_xxx f1 rule
	(* let _=print_endline ("CNF form: "^Cprinter.string_of_pure_formula f1) in let _= print_endline ("[minisat.ml exit 0] Please use the option '--enable-slicing'") in exit 0 *)
        (* | Exists _ ->  *)
    | AndList _ | Forall _ -> Error.report_no_pattern()
  in
  rule nf

let nnf_to_cnf f= nnf_to_xxx f dist_1 

let nnf_to_cnf_no_slicing f=	nnf_to_xxx f dist_no_slicing
  (*let to_cnf f = nnf_to_cnf (minisat_cnf_of_formula f)*)

(*The old CNF conversion*)
let rec to_cnf f =
  let res= (*Debug-bach*)
    let cnf_form=(nnf_to_cnf_no_slicing f) in
    if(is_cnf cnf_form) then cnf_form  else to_cnf cnf_form(*(to_cnf cnf_form)*)
  in
  let _=print_endline_quiet ("CNF form: "^Cprinter.string_of_pure_formula res) in
  res

let to_cnf_no_slicing f=
  let _=print_endline_quiet ("Orig: "^Cprinter.string_of_pure_formula f) in
  let nnf= minisat_cnf_of_formula f in 
  let _=print_endline_quiet ("NNF here: "^Cprinter.string_of_pure_formula nnf) in
  to_cnf nnf
      
(*The no need CNF conversion adapt to slicing, we just need the distributive law*)		
      
(* let minisat_cnf_of_formula f = *)
(*   Debug.no_1 "minisat_of_formula" Cprinter.string_of_pure_formula pr_id minisat_cnf_of_formula f *)
      
(*bach-minisat*)

(*************************************************************)
(* Check whether minisat can handle the expression, formula... *)
let rec can_minisat_handle_expression (exp: Cpure.exp) : bool =
  match exp with
    | Cpure.Null _         -> false
    | Cpure.Var _          -> false
    | Cpure.IConst _       -> false
    | Cpure.FConst _       -> false
    | Cpure.AConst _       -> false
  | Cpure.NegInfConst _ 
  | Cpure.InfConst _  -> false
          (* arithmetic expressions *)
    | Cpure.Add _
    | Cpure.Subtract _
    | Cpure.Mult _
    | Cpure.Div _
    | Cpure.Max _
    | Cpure.Min _
    | Cpure.TypeCast _     -> false
          (* bag expressions *)
    | Cpure.Bag _
    | Cpure.BagUnion _
    | Cpure.BagIntersect _
    | Cpure.BagDiff _      -> false
          (* list expressions *)
    | Cpure.List _
    | Cpure.ListCons _
    | Cpure.ListHead _
    | Cpure.ListTail _
    | Cpure.ListLength _
    | Cpure.ListAppend _
    | Cpure.ListReverse _  -> false
          (* array expressions *)
    | Cpure.ArrayAt _      -> false
    | Cpure.Func _ ->  false 
    | Cpure.Template _ -> false
    | Cpure.Level _ 
    | Cpure.Tsconst _ -> Error.report_no_pattern()
    | Cpure.Tup2 _ -> Error.report_no_pattern()
    | Cpure.Bptriple _ -> Error.report_no_pattern()


and can_minisat_handle_p_formula (pf : Cpure.p_formula) : bool =
  match pf with
    | Frm _               -> false
    | LexVar _             -> false
    | BConst (a,_)         ->  true (*true*)
    | BVar _               -> false (*true*)
    | Lt _                 -> false
    | Lte _                -> false
    | Gt _                 -> false
    | Gte _                -> false
    | SubAnn (ex1, ex2, _) -> false
    | Eq (ex1, ex2, _)     -> true
    | Neq (ex1, ex2, _)    -> true
    | EqMax _              -> false
    | EqMin _              -> false
          (* bag formulars *)
    | BagIn _
    | BagNotIn _
    | BagSub _
    | BagMin _
    | BagMax _             -> false
          (* list formulas *)
    | ListIn _
    | ListNotIn _
    | ListAllN _
    | ListPerm _
    | RelForm _            -> false
    | XPure _ (* | VarPerm _ *) -> Error.report_no_pattern()

and can_minisat_handle_b_formula (bf : Cpure.b_formula) : bool =
  match bf with
    | (pf, _) -> can_minisat_handle_p_formula pf

and can_minisat_handle_formula (f: Cpure.formula) : bool =
  match f with
    | BForm (bf, _)       -> can_minisat_handle_b_formula bf
    | And (f1, f2, _)     -> (can_minisat_handle_formula f1) && (can_minisat_handle_formula f2)
    | Or (f1, f2, _, _)   -> (can_minisat_handle_formula f1) && (can_minisat_handle_formula f2)
    | Not (f, _, _)       -> can_minisat_handle_formula f
    | Forall (_, f, _, _) -> can_minisat_handle_formula f
    | Exists (_, f, _, _) -> can_minisat_handle_formula f
    | AndList _ -> Error.report_no_pattern()

(***************************************************************
                                                                INTERACTION
**************************************************************)

let rec collect_output (chn: in_channel)  : (string * bool) =
  try
    let line = input_line chn in
    (* let () = print_endline ("  -- output: " ^ line) in *)
    if line = "SATISFIABLE" then
      (line, true)
    else if (line = "c SAT")	then
      ("SATISFIABLE",true) 
    else
      collect_output chn 
  with 
    | End_of_file ->  ("", false)

(* read the output stream of minisat prover, return (conclusion * reason)    *)
(* TODO: this function need to be optimized                                *)
let get_prover_result (output : string) :bool =
  if !Globals.print_original_solver_output then
    begin
      print_endline_quiet "MINISAT OUTPUT";
      print_endline_quiet "--------------";
      print_endline_quiet output;
      print_endline_quiet "--------------";
    end;
  let validity =
    if (output="SATISFIABLE") then
      (*			let _=print_endline output in*)
      true
    else
      (*			let _=print_endline output in*)
      false in 
  validity

(* output:  - prover_output 
   - the running status of prover: true if running, otherwise false *)
let get_answer (chn: in_channel) : (bool * bool)=
  let (output, running_state) = collect_output chn  in
  let
        validity_result = get_prover_result output;
  in
  (validity_result, running_state)  

let remove_file filename =
  try Sys.remove filename;
  with e -> ignore e

let set_process (proc: prover_process_t) =
  minisat_process := proc

let start () =
  if not !is_minisat_running then (
      print_endline_quiet ("Starting minisat... \n");
      last_test_number := !test_number;
      let prelude () = () in
      if (minisat_input_format = "cnf") then (
          Procutils.PrvComms.start !log_all_flag log_file (minisat_name, minisat_path, [|minisat_arg|]) set_process prelude;
          is_minisat_running := true;
      )
  )

(* stop minisat system *)
let stop () =
  if !is_minisat_running then (
      let num_tasks = !test_number - !last_test_number in
      print_string_if !Globals.enable_count_stats ("\nStop minisat... " ^ (string_of_int !minisat_call_count) ^ " invocations "); flush stdout;
      let () = Procutils.PrvComms.stop !log_all_flag log_file !minisat_process num_tasks Sys.sigkill (fun () -> ()) in
      is_minisat_running := false;
  )

(* restart Omega system *)
let restart reason =
  if !is_minisat_running then (
      let () = print_string_if !Globals.enable_count_stats (reason ^ " Restarting minisat after ... " ^ (string_of_int !minisat_call_count) ^ " invocations ") in
      Procutils.PrvComms.restart !log_all_flag log_file reason "minisat" start stop
  )
  else (
      let () = print_string_if !Globals.enable_count_stats (reason ^ " not restarting minisat ... " ^ (string_of_int !minisat_call_count) ^ " invocations ") in ()
  )
    
(* Runs the specified prover and returns output *)
let check_problem_through_file (input: string) (timeout: float) : bool =
  (* debug *)
  (* let () = print_endline "** In function minisat.check_problem" in *)
  let file_suffix = "bach_eq_minisat" in
  let infile =(file_suffix) ^ ".cnf" in
  (* let () = print_endline ("-- input: " ^ input^"\n") in  *)
  if !Globals.print_original_solver_input then
    begin
      print_endline_quiet "MINISAT INPUT";
      print_endline_quiet "--------------";
      print_endline_quiet input;
      print_endline_quiet "--------------";
    end;
  let out_stream = open_out infile in
  output_string out_stream input;
  close_out out_stream;
  let minisat_result="minisatres.txt" in
  let set_process proc = minisat_process := proc in
  let fnc () =
    if (minisat_input_format = "cnf") then ( 
	(* let tstartlog = Gen.Profiling.get_time () in	 *)
	(* let ch = Unix.open_process_in "/usr/local/bin/ minisat22 bach_eq_minisat.cnf" in  *)
	(* let ch = Unix.execvp "/usr/local/bin/minisat22" [|"minisat22";"bach_eq_minisat.cnf"|]  in  *)
        Procutils.PrvComms.start false stdout (minisat_name2, minisat_path2, [|minisat_arg2;infile;minisat_result|]) set_process (fun () -> ());
	(* let status = Unix.close_process_in ch in *)
	minisat_call_count := !minisat_call_count + 1;
        let (prover_output, running_state) = get_answer !minisat_process.inchannel in
        is_minisat_running := running_state;
	(* let tstoplog = Gen.Profilingminisat_cnf_of_formula.get_time () in                                            *)
	(* let _= Globals.minisat_time_T := !Globals.minisat_time_T +. (tstoplog -. tstartlog) in *)
        prover_output;
	
    )
    else illegal_format "[minisat.ml] The value of minisat_input_format is invalid!" in
  let res = 
    try
      let res = Procutils.PrvComms.maybe_raise_timeout fnc () timeout in
      res
    with _ -> ((* exception : return the safe result to ensure soundness *)
        print_backtrace_quiet ();
        print_endline_quiet ("WARNING: Restarting prover due to timeout");
        Unix.kill !minisat_process.pid 9;
        ignore (Unix.waitpid [] !minisat_process.pid);
        false
    )
  in
  let (*tstartlog*)_ = Gen.Profiling.get_time () in
  let () = Procutils.PrvComms.stop false stdout !minisat_process 0 9 (fun () -> ()) in
  let (*tstoplog*)_ = Gen.Profiling.get_time () in
  (* let _= Globals.minisat_time_T := !Globals.minisat_time_T +. (tstoplog -. tstartlog) in *)
  remove_file infile;
  res
      

let check_problem_through_file (input: string) (timeout: float) : bool =
  Debug.no_1 "check_problem_through_file (minisat)"
      (fun s -> s) string_of_bool
      (fun f -> check_problem_through_file f timeout) input

(***************************************************************
                                                                GENERATE CNF INPUT FOR IMPLICATION / SATISFIABILITY CHECKING
**************************************************************)
(* minisat: output for cnf format *)
let rtc_generate_B (f:Cpure.formula) =
  let ge=G.create() and gd=G.create() and gr_e=Glabel.create() in (*ge is eq graph and gd is diseq graph*)
  (*let () = print_endline("INSIDE rtc_generate_B, f=="^Cprinter.string_of_pure_formula f) in*)
  let rec cnf_to_string_to_file f = (*Aiming to get ge and gd and cnf string of the given CNF formula*)                                                           
    match f with
      |BForm (b,_)->  minisat_cnf_of_b_formula b gr_e ge gd 
      |And (f1, f2, _) ->cnf_to_string_to_file f1 ^" 0"^"\n"^ cnf_to_string_to_file f2
      |Or  (f1, f2, _, _)->cnf_to_string_to_file f1 ^" "^ cnf_to_string_to_file f2
      |Not ((BForm(b,_)),_,_)-> minisat_cnf_of_not_of_b_formula b gr_e ge gd
      | _-> 
            
            let _= 
              x_tinfo_hp (add_str "imply Final Formula :"  Cprinter.string_of_pure_formula) f no_pos
            in ""
  in
  let cnf_str =cnf_to_string_to_file f in
  (cnf_str,ge,gd,gr_e)

let get_cnf_from_cache ge gd gr_e=
  let testRTC= new rTC in
  let cache= testRTC#rtc_v2 ge gd gr_e !number_vars in
  cache

let to_minisat_cnf (ante: Cpure.formula)  =
  (*let () = "** In function Spass.to_minisat_cnf" in*)
  (*let _=print_endline ("imply Final Formula :" ^ (Cprinter.string_of_pure_formula ante))in*)
  (*let () = read_line() in*)
  (*let _=print_endline ("CNF Formula :" ^ (Cprinter.string_of_pure_formula (to_cnf ante)))in*)
  (* let () = print_endline("INSIDE to_minisat_cnf"^Cprinter.string_of_pure_formula ante) in *)
  let _= number_vars := 0  in
  (* let _=Gen.Profiling.push_time("stat_CNF_ori_conversion") in *)
  (* let ante_cnf=to_cnf ante in(*convert the given formula in to CNF here*) *)
  let cnf_ante=nnf_to_cnf ante
  in
  (* let _=print_endline ("To minisat cnf :" ^ (Cprinter.string_of_pure_formula cnf_ante))in *)
  match ante with
    | BForm ((BConst (a,_),_),_)-> 
          let () = print_endline_quiet ("BForm:\n ") in 
          if (a) 
          then (false,"t",G.create(),G.create(),Glabel.create()) 
          else (false,"f",G.create(),G.create(),Glabel.create())
    |	_ ->
            (* let () = print_endline ("other\n") in  *)
	    (* let _=Gen.Profiling.pop_time("stat_CNF_ori_conversion") in *)
            (*			let _=print_endline "sat true" in*)
	    (* let _=Gen.Profiling.push_time("stat_CNF_generation_of_B") in *)
	    let (ante_str,ge,gd,gr_e)=rtc_generate_B cnf_ante in
            let () = Debug.ninfo_hprint (add_str "ante_str == " pr_id) ante_str no_pos in
	    (*start generating cnf for the given CNF formula*)
	    let temp= if(ante_str <> "0" && ante_str <> "") then (ante_str^" 0") else "p cnf 0 0" in
	    let final_res= temp(*result*)^"\n" in
	    (* let _=Gen.Profiling.pop_time("stat_CNF_generation_of_B") in  *)
	    (true,final_res,ge,gd,gr_e)
		
(*bach*) 
(***************************************************************
                                                                GENERATE CNF INPUT FOR IMPLICATION / SATISFIABILITY CHECKING
**************************************************************)


(**************************************************************
                                                               MAIN INTERFACE : CHECKING IMPLICATION AND SATISFIABILITY
*************************************************************)

(**
   * Test for satisfiability
   * We also consider unknown is the same as sat
*)
(* minisat *)
let minisat_is_sat (f : Cpure.formula) (sat_no : string) timeout : bool =
  (* to check sat of f, minisat check the validity of negative(f) or (f => None) *)
  (* let tstartlog = Gen.Profiling.get_time () in *)
  (* let () = print_endline ("here"^Cprinter.string_of_pure_formula f ) in *)
  let (flag,minisat_input,ge,gd,gr_e) = to_minisat_cnf f in
  (* let tstoplog = Gen.Profiling.get_time () in                                                          *)
  (* let _= Globals.minisat_time_cnf_conv := !Globals.minisat_time_cnf_conv +. (tstoplog -. tstartlog) in *)
  if(flag = false ) then
    begin
      
      if(minisat_input = "t") then true
      else 
         
        if(minisat_input = "f") then false
	else false
    end
  else 
    (* let validity =                                                     *)
    (*   (* if ((List.length !bcl)>0 ) then *)                            *)
    (* 		(* let _=Gen.Profiling.push_time("stat_check_sat_1") in *)     *)
    (*    let res=check_problem_through_file minisat_input timeout in res *)
    (* 		(* let _=Gen.Profiling.pop_time("stat_check_sat_1") in res *)  *)
    (* 	(* else true *)                                                  *)
    (* in                    check_problem_through_file                                             *)
    (* if(validity=false) then                                            *)
    (* let _= print_endline "check sat1" in *)                      
    (* 		validity                                                       *)
    (* else                                                               *)
    (*			let _= print_endline "check sat2" in*)
    (* let _=Gen.Profiling.push_time("stat_generation_of_T") in *)
    (* let tstartlog = Gen.Profiling.get_time () in *)
    (* let _= print_endline ("ori cnf form: "^minisat_input) in *)
    (* let tstartlog = Gen.Profiling.get_time () in *)
    let cnf_T = get_cnf_from_cache ge gd gr_e in
    (*let () = print_endline("get_cnf_from_cache "^cnf_T^"\n") in *)
    (* let tstoplog = Gen.Profiling.get_time () in *)
    (* let _= Globals.minisat_time_BCC := !Globals.minisat_time_BCC +. (tstoplog -. tstartlog) in  *)
    (* let tstoplog = Gen.Profiling.get_time () in *)
    (* let _= Globals.minisat_time_T := !Globals.minisat_time_T +. (tstoplog -. tstartlog) in  *)
    (* let _=Gen.Profiling.pop_time("stat_generation_of_T") in *)
    (* let _=Gen.Profiling.push_time("stat_check_sat_2") in *)
    let all_input=if(cnf_T <> "") then cnf_T^minisat_input else minisat_input in
    (*let () = print_endline("cnf_T:"^cnf_T^" minisat_input:"^minisat_input^"\n") in*)
    (* let _=print_endline ("All input: \n"^all_input) in *)
    (* let tstartlog = Gen.Profiling.get_time () in *)
    (* let () = print_endline("all_input: "^all_input^"\n") in  *)
    let res= check_problem_through_file (all_input) timeout in 
    (* let tstoplog = Gen.Profiling.get_time () in *)
    (* let _= Globals.minisat_time_T := !Globals.minisat_time_T +. (tstoplog -. tstartlog) in *)
    res
	(* let _=Gen.Profiling.pop_time("stat_check_sat_2") in res *)

(* minisat *)
let minisat_is_sat (f : Cpure.formula) (sat_no : string) : bool =
  minisat_is_sat f sat_no minisat_timeout_limit

(* minisat *)
let minisat_is_sat (f : Cpure.formula) (sat_no : string) : bool =
  let pr = Cprinter.string_of_pure_formula in
  let result = Debug.no_1 "minisat_is_sat" pr string_of_bool (fun _ -> minisat_is_sat f sat_no) f in
  (* let omega_result = Omega.is_sat f sat_no in
     let () = print_endline ("-- minisat_is_sat result: " ^ (if result then "TRUE" else "FALSE")) in
     let () = print_endline ("-- Omega.is_sat result: " ^ (if omega_result then "TRUE" else "FALSE")) in *)
  result

(* see imply *)
let is_sat (f: Cpure.formula) (sat_no: string) : bool =
  (* debug *)
  (* let () = print_endline "** In function minisat.is_sat: " in *)
  minisat_is_sat f sat_no 

let is_sat_with_check (pe : Cpure.formula) sat_no : bool option =
  Cpure.do_with_check "" (fun x -> is_sat x sat_no) pe

(* let is_sat f sat_no = Debug.loop_2_no "is_sat" (!print_pure) (fun x->x) *)
(* string_of_bool is_sat f sat_no                                          *)

let is_sat (pe : Cpure.formula) (sat_no: string) : bool =
  (* let () = print_endline "** In function minisat.is_sat: " in *)
  try
    is_sat pe sat_no;
  with Illegal_Prover_Format s -> (
      print_endline_quiet ("\nWARNING : Illegal_Prover_Format for :" ^ s);
      print_endline_quiet ("Apply minisat.is_sat on formula :" ^ (Cprinter.string_of_pure_formula pe));
      flush stdout;
      failwith s
  )

(**
   * Test for validity
   * To check the implication P -> Q, we check the satisfiability of
   * P /\ not Q
   * If it is satisfiable, then the original implication is false.
   * If it is unsatisfiable, the original implication is true.
   * We also consider unknown is the same as sat
*)
      
let imply (ante: Cpure.formula) (conseq: Cpure.formula) (timeout: float) : bool =
  (*let () = print_endline "** In function minisat.imply:" in *)
  (*  let _=List.map (fun x-> print_endline (minisat_cnf_of_spec_var x)) all in*)
  let cons= (mkNot_s conseq) in
  let imply_f= mkAnd ante cons no_pos  in
  (* x_tinfo_pp "hello\n" no_pos; *)
  let res =is_sat imply_f ""
  in 	
  (*		let _=if(res) then print_endline ("SAT") else print_endline ("UNSAT") in *)
  if(res) then false else true
    
let imply (ante : Cpure.formula) (conseq : Cpure.formula) (timeout: float) : bool =
  (* let () = print_endline "** In function minisat.imply:" in *)
  try
    let result = imply ante conseq timeout in
    (*bach-test*)
    result
        
  with Illegal_Prover_Format s -> (
      print_endline_quiet ("\nWARNING : Illegal_Prover_Format for :" ^ s);
      print_endline_quiet ("Apply minisat.imply on ante Formula :" ^ (Cprinter.string_of_pure_formula ante));
      print_endline_quiet ("and conseq Formula :" ^ (Cprinter.string_of_pure_formula conseq));
      flush stdout;
      failwith s
  )

let imply (ante : Cpure.formula) (conseq : Cpure.formula) (timeout: float) : bool =
  (* let () = pint_endline "** In function minisat.imply:" in *)
  let pr = Cprinter.string_of_pure_formula in
  Debug.no_2(* _loop *) "minisat.imply" (add_str "ante" pr) (add_str "conseq" pr) string_of_bool
      (fun _ _ -> imply ante conseq timeout) ante conseq

let imply_with_check (ante : Cpure.formula) (conseq : Cpure.formula) (imp_no : string) (timeout: float) : bool option =
  (* let () = print_endline "** In function minisat.imply_with_check:" in *)
  Cpure.do_with_check2 "" (fun a c -> imply a c timeout) ante conseq
      (**
         * To be implemented
      *)

let simplify (f: Cpure.formula) : Cpure.formula =
  (* debug *)
  (* let () = print_endline "** In function minisat.simplify" in *)
  try (Omega.simplify f) with _ -> f

let simplify (pe : Cpure.formula) : Cpure.formula =
  match (Cpure.do_with_check "" simplify pe) with
    | None -> pe
    | Some f -> f

let hull (f: Cpure.formula) : Cpure.formula = f

let pairwisecheck (f: Cpure.formula): Cpure.formula = f

