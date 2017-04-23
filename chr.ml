#include "xdebug.cppo"

module CP = Cpure
open GlobProver


let set_prover_type () = Others.last_tp_used # set Others.CHR
    
let log_chr_formula = ref false
let chr_log = ref stdout
let chr_log_file = "allinput.chr"

(* this file is only needed until until we resolve the interactive chr *)
let infilename = !tmp_files_path ^ "input.chr." ^ (string_of_int (Unix.getpid ()))

let set_log_file () : unit =
  log_chr_formula := true;
  chr_log := open_log_out chr_log_file

let log_text_to_chr_file (str : string) : unit =
  if !log_chr_formula then
    begin
      output_string !chr_log str
    end

let output_to_chr_file str =
  let chr_infile = open_out infilename in
  let () = output_string chr_infile str in
  flush chr_infile

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
  | CP.BVar (sv, _) ->
    let () = y_binfo_pp "Andreea: why is a BVar translated to sv > 0 ?" in
    (chr_of_spec_var sv) (* ^ " > 0"  *)
  | CP.Eq (a1, a2, _) -> (chr_of_exp a1) ^ "=" ^ (chr_of_exp a2)
  | CP.Neq (a1, a2, _) -> (chr_of_exp a1) ^ "\\=" ^ (chr_of_exp a2)
  | CP.RelForm (r, args, l) -> 
    (* assumes the relations are already declared (maybe in prelude?) *)
    Cprinter.string_of_b_formula b
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
  | CP.Not (p,_, _) -> "(not (" ^ (chr_of_formula p) ^ "))"
    (* begin *)
    (*   match p with *)
    (*   | CP.BForm ((CP.BVar (bv, _), _), _) -> (chr_of_spec_var bv) ^ " <= 0" *)
    (*   | _ -> "(not (" ^ (chr_of_formula p) ^ "))" *)
    (* end *)
  | _ -> ""


(* all formulae that shall be sent to CHR process have to be transformed in CHR input language *)
let prepare_formula_for_chr (f : CP.formula) : string =
  chr_of_formula f

let prepare_formula_for_chr (f : CP.formula) : string =
  Debug.no_1 "prepare_formula_for_chr" Cprinter.string_of_pure_formula (fun x-> x) prepare_formula_for_chr f
  
let imply (ante : CP.formula) (conseq : CP.formula) (imp_no : string) : bool =
  let () = set_prover_type () in
  let ante_chr = prepare_formula_for_chr ante in
  let conseq_chr = prepare_formula_for_chr conseq in
  let () = log_text_to_chr_file (ante_chr ^ ", not(" ^ conseq_chr ^  ").\n") in
  let () = output_to_chr_file (ante_chr ^ ", not(" ^ conseq_chr ^  ").\n") in
  (* TODO elena: replace the relative path for the script *)
  let cmd = "../../../../chr/run_simple_pl.sh" in
  let args = [| cmd; infilename |] in
  (* TODO elena: modify the script such that it expects the command instead of a file *)
  (* let args = [| cmd; (ante_chr ^ ", not(" ^ conseq_chr ^  ").\n") |] in *)
  let inchn, outchn, errchn, npid = Procutils.open_process_full cmd args in
  let result = input_line inchn in
  if result = "false." then
    true
  else 
    false

let imply (ante : CP.formula) (conseq : CP.formula) (imp_no : string) : bool =
  let pr = Cprinter.string_of_pure_formula in
  Debug.no_2 "CHR.imply" pr pr string_of_bool (fun _ _ -> imply ante conseq imp_no) ante conseq
  
