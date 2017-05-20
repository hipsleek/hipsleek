#include "xdebug.cppo"

module CP = Cpure
open GlobProver
open Gen


let set_prover_type () = Others.last_tp_used # set Others.CHR
    
let log_chr_formula = ref false
let chr_log = ref stdout
let chr_log_file = "allinput.chr"
let _valid = true
let _invalid = false
let _sat = true
let _unsat = false

let out_chan = ref stdout
let in_chan = ref stdin
let err_chan = ref stdin

let chr_cmd = "orderchr"

let halt = "halt."

type sat = SAT | UNSAT | UNK

let string_of_sat sat = 
  match sat with
  | SAT -> "SAT"
  | UNSAT -> "UNSAT"
  | UNK -> "UNKNOWN"

let set_log_file () : unit =
  log_chr_formula := true;
  chr_log := open_log_out chr_log_file

let log_text_to_chr_file (str : string) : unit =
  if !log_chr_formula then
    begin
      output_string !chr_log str
    end

let rec chr_of_spec_var (sv : CP.spec_var) = match sv with
  | CP.SpecVar (_, v, p) -> (String.capitalize v) ^ (if CP.is_primed sv then Oclexer.primed_str else "")

let rec chr_of_exp exp = match exp with
  | CP.Null _ -> "0"
  | CP.Var (sv, _) -> chr_of_spec_var sv
  | CP.IConst (iconst, _) -> string_of_int iconst 
  | _ -> ""

and chr_of_b_formula b =
  let (pf,_) = b in
  match pf with
  | CP.BConst (c, _) -> string_of_bool c
  | CP.BVar (sv, _)  -> (chr_of_spec_var sv)
  | CP.Eq (a1, a2, _)  -> (chr_of_exp a1) ^ "=" ^ (chr_of_exp a2)
  | CP.Neq (a1, a2, _) -> (chr_of_exp a1) ^ "\\=" ^ (chr_of_exp a2)
  | CP.RelForm (r, args, l) -> 
    (* assumes the relations are already declared (maybe in prelude?) *)
    (Cprinter.string_of_spec_var r) ^ "(" ^ (String.concat "," (List.map chr_of_exp args)) ^ ")"
    (* Cprinter.string_of_b_formula b *)
  | _ -> ""

and chr_of_formula f = match f with
  | CP.BForm (b,_) -> 
    begin
      match (fst CP.drop_lexvar_ops) (fst b) with
      | None -> "(" ^ (chr_of_b_formula b) ^ ")"
      | Some f -> chr_of_formula f
    end
  | CP.And (p1, p2, _) -> "" ^ (chr_of_formula p1) ^ "," ^ (chr_of_formula p2) ^ ""
  | CP.Or (p1, p2,_, _) -> "(" ^ (chr_of_formula p1) ^ ";" ^ (chr_of_formula p2) ^ ")"
  | CP.Not (p,_, _) -> "(snot(" ^ (chr_of_formula p) ^ "))"
  | _ -> ""

(* all formulae that shall be sent to CHR process have to be transformed in CHR input language *)
let prepare_formula_for_chr (f : CP.formula) : string =
  chr_of_formula f

let prepare_formula_for_chr (f : CP.formula) : string =
  Debug.no_1 "prepare_formula_for_chr" Cprinter.string_of_pure_formula (fun x-> x) prepare_formula_for_chr f

(* send a query to CHR and receive result -> true/false/unknown *)
let send_query (query : string) : sat =
  let () = output_string !out_chan query in
  let () = flush !out_chan in
  let result =
    try  
      let result = input_line !in_chan in
      let () = y_tinfo_pp ("\n############\n CHR result: "^result^"\n############\n") in
      match result with
      | "false" -> UNSAT
      | "true"  -> SAT
      | _       -> let () = y_winfo_pp ("WARNING (CHR) : "^result) in SAT
    with _ ->
      let () = y_binfo_pp ("\n############ NO CHR result ############\n") in
      SAT  in
   result

let send_query (query : string) : sat =
  Debug.no_1 "CHR.send_query" pr_string string_of_sat (fun _ -> send_query query) query

(* valid(A |- C)  ~~> unsat( not(A |- C) ) ~~> unsat( A/\not(C) ) *)
let imply (ante : CP.formula) (conseq : CP.formula) (imp_no : string) : bool =
  let () = set_prover_type () in
  let ante_chr = prepare_formula_for_chr ante in
  let conseq_chr = prepare_formula_for_chr conseq in
  let query = (ante_chr ^ ",snot((" ^ conseq_chr ^  ")).\n") in
  let result = x_add_1 send_query query in
  match result with
  | SAT   -> _invalid
  | UNSAT -> _valid
  | UNK   -> _invalid
    
let imply (ante : CP.formula) (conseq : CP.formula) (imp_no : string) : bool =
  let pr = Cprinter.string_of_pure_formula in
  Debug.no_2 "CHR.imply" pr pr string_of_bool (fun _ _ -> imply ante conseq imp_no) ante conseq
  
(* valid(A |- C)  ~~> unsat( not(A |- C) ) ~~> unsat( A/\not(C) ) *)
let is_sat (form : CP.formula) (sat_no : string) : bool =
  let () = set_prover_type () in
  let formula_chr = prepare_formula_for_chr form in
  let query = formula_chr ^ ".\n" in
  let result = x_add_1 send_query query in
  match result with
  | SAT   -> _sat
  | UNSAT -> _unsat
  | UNK   -> _sat
    
let is_sat (form : CP.formula) (sat_no : string) : bool =
  let pr = Cprinter.string_of_pure_formula in
  Debug.no_1 "CHR.is_sat" pr string_of_bool (fun _ -> is_sat form sat_no) form
    
let start () =
  print_string_quiet "\nStarting CHR... \n"; flush stdout;
  let args = [| chr_cmd |] in
  let inchn, outchn, errchn, npid = Procutils.open_process_full chr_cmd args in
  in_chan := inchn;
  out_chan := outchn;
  err_chan := errchn

let stop () = 
  output_string !out_chan halt

