#include "xdebug.cppo"

module CP = Cpure
open GlobProver


let set_prover_type () = Others.last_tp_used # set Others.CHR
    
let log_chr_formula = ref false
let chr_log = ref stdout

let rec chr_of_spec_var (sv : CP.spec_var) = match sv with
  | CP.SpecVar (_, v, p) -> v ^ (if CP.is_primed sv then Oclexer.primed_str else "")

let rec chr_of_exp exp = match exp with
  | CP.Null _ -> "0"
  | CP.Var (sv, _) -> chr_of_spec_var sv
  | CP.IConst (iconst, _) -> string_of_int iconst 
  | _ -> ""

and chr_of_b_formula b =
  let (pf,_) = b in
  match pf with
  | CP.BConst (c, _) -> string_of_bool c
  | CP.BVar (sv, _) -> (chr_of_spec_var sv) ^ " > 0"
  | CP.Eq (a1, a2, _) -> (chr_of_exp a1) ^ " = " ^ (chr_of_exp a2)
  | CP.Neq (a1, a2, _) -> (chr_of_exp a1) ^ " \\= " ^ (chr_of_exp a2)
  | _ -> ""

and chr_of_formula f = match f with
  | CP.BForm (b,_) -> 
    begin
      match (fst CP.drop_complex_ops) (fst b) with
      | None -> "(" ^ (chr_of_b_formula b) ^ ")"
      | Some f -> chr_of_formula f
    end
  | CP.And (p1, p2, _) -> "(" ^ (chr_of_formula p1) ^ " , " ^ (chr_of_formula p2) ^ ")"
  | CP.Or (p1, p2,_, _) -> "(" ^ (chr_of_formula p1) ^ " ; " ^ (chr_of_formula p2) ^ ")"
  | CP.Not (p,_, _) ->
    begin
      match p with
      | CP.BForm ((CP.BVar (bv, _), _), _) -> (chr_of_spec_var bv) ^ " <= 0"
      | _ -> "(not (" ^ (chr_of_formula p) ^ "))"
    end
  | _ -> ""

let set_log_file () : unit =
  log_chr_formula := true;
  chr_log := open_log_out "allinput.chr"

let log_text_to_chr_file (str : string) : unit =
  if !log_chr_formula then
    begin
      output_string !chr_log str
    end


(*all formulae that shall be sent to CHR process have to be transformed in CHR input language *)
let prepare_formula_for_chr (f : CP.formula) : string =
  chr_of_formula f 

(*
is_sat (f : CPure.formula) : bool =
  let chr_form = prepare_formula_for_chr f in
  let () = (log_text_to_chr_file ("%%% Res: TODO \n\n"); flush !chr_log)
  
*)

