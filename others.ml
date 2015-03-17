#include "xdebug.cppo"
open VarGen
open Globals
open Gen

class proving_type =
object
  inherit [string] store "None" (fun x -> x)
     (* method string_of_string : string = match lc with *)
     (*   | None -> "None" *)
     (*   | Some l -> l *)
end;;

type proving_kind = 
	  PK_Sat_Warning
	| PK_Pred_Check_Inv 
	| PK_Compute_Base_Case
	| PK_Trans_Proc
	| PK_Check_Specs
	| PK_Verify_Lemma
	| PK_Lemma_Norm
	| PK_Lemma_Prop
	| PK_Term_Dec
	| PK_Term_Bnd
	| PK_Sleek_Entail of int
	| PK_Early_Contra_Detect
	| PK_Contra_Detect_Pure
	| PK_Cast
	| PK_If_Stmt
	| PK_Pre_Oblg
	| PK_Post_Oblg
        | PK_Pred_Split
	| PK_Assign_Stmt
	| PK_Assert
	| PK_Assert_Assume
	| PK_BIND
	| PK_PRE
	| PK_PRE_REC
	| PK_POST
        | PK_SA_EQUIV
	| PK_Unknown


let string_of_proving_kind pk =
  match pk with
    | PK_Sat_Warning -> "Sat_Warning"
    | PK_Pred_Check_Inv -> "Pred_Check_Inv"
    | PK_Compute_Base_Case-> "Compute_Base_Case"
    | PK_Trans_Proc -> "Trans_Proc"
    | PK_Check_Specs -> "Check_Specs"
    | PK_Verify_Lemma -> "Verify_Lemma"
    | PK_Lemma_Norm -> "Lemma_Norm"
    | PK_Lemma_Prop -> "Lemma_Prop"
    | PK_Term_Dec -> "Term_Dec"
    | PK_Term_Bnd -> "Term_Bnd"
    | PK_Sleek_Entail(n) -> "Sleek_Entail("^(string_of_int n)^")"
    | PK_Early_Contra_Detect -> "Early_Contra_Detect"
    | PK_Contra_Detect_Pure -> "Contra_Detect_Pure"
    | PK_Cast -> "Cast"
    | PK_If_Stmt -> "If_Stmt"
    | PK_Assign_Stmt -> "Assign_Stmt"
    | PK_Assert -> "Assert"
    | PK_Assert_Assume -> "Assert/Assume"
    | PK_BIND -> "BIND"
    | PK_PRE -> "PRE"
    | PK_PRE_REC -> "PRE_REC"
    | PK_POST -> "POST"
    | PK_SA_EQUIV -> "PK_SA_EQUIV"
    | PK_Pre_Oblg -> "PRE-OBLIGATION"
    | PK_Post_Oblg -> "POST-OBLIGATION"
    | PK_Pred_Split -> "PK_Pred_Split"
    | PK_Unknown -> "UNKNOWN"

let sleek_kind = new Gen.stack_pr string_of_proving_kind (==)

let proving_kind = new Gen.stack_noexc PK_Unknown string_of_proving_kind (==)

let find_impt ls =
  let rec aux ls = match ls with
    | [] -> PK_Unknown
    | [x] -> x
    | x::xs -> (match x with
        | PK_Sleek_Entail(_)
        | PK_Assert | PK_Assert_Assume | PK_BIND 
        | PK_PRE | PK_PRE_REC | PK_POST -> x
        | _ -> aux xs
      ) 
  in aux ls

let find_impt_proving_kind () =
  let stk = proving_kind # get_stk in
  find_impt stk

let proving_info () = 
  if(proving_kind # is_avail) then
    (
	let temp= if(explain_mode # is_avail) then "FAILURE EXPLAINATION" else proving_kind # string_of in
      	if (post_pos # is_avail) 
        then ("Proving Infor spec:"^(post_pos#string_of_pos) ^" loc:"^(proving_loc#string_of_pos)^" kind::"^temp)
        else 
          let loc_info = 
            if (proving_loc # is_avail) then " loc:"^(proving_loc#string_of_pos)
            else " loc: NONE" 
          in ("Proving Infor spec:"^(post_pos#string_of_pos) ^loc_info^" kind::"^temp)
    )
  else "..no proving kind.."(*"who called is_sat,imply,simplify to be displayed later..."*)


let wrap_proving_kind (tk) exec_function args =
  (* let str = string_of_proving_kind tk in *)
  (* if (!sleek_logging_txt || !proof_logging_txt) then *)
  begin
    (* let m = proving_kind # get_stk in *)
    let () = proving_kind # push tk in
    try 
      let res = exec_function args in
      let () =  proving_kind # pop in
      (* let () = proving_kind # set_stk m in *)
      res
    with _ as e ->
        begin
          let () = proving_kind # pop in
          (* let () = proving_kind # set_stk m in *)
          raise e
        end
  end
  (* else 	 *)
  (*   let res = exec_function args  *)
  (*   in res *)
 
(* let wrap_proving_kind (str : string) exec_function args = *)
(*   Debug.no_1 "wrap_proving_kind" pr_id pr_none  *)
(*       (fun _ -> wrap_proving_kind str exec_function args) str *)

(* let post_pos = ref no_pos *)
(* let set_post_pos p = post_pos := p *)

type tp_type =
  | OmegaCalc
  | CvcLite
  | Cvc3
  | CO (* CVC3 then Omega combination *)
  | Isabelle
  | Mona
  | MonaH
  | OM
  | OI
  | SetMONA
  | CM (* CVC3 then MONA *)
  | Coq
  | Z3
  | Z3N
  | OCRed
  | Redlog
  | Mathematica
  | RM (* Redlog and Mona *)
  | PARAHIP (* Redlog, Z3 and Mona *) (*This option is used on ParaHIP website*)
  | ZM (* Z3 and Mona *)
  | OZ (* Omega and Z3 *)
  | AUTO (* Omega, Z3, Mona, Coq *)
  | DP (*ineq prover for proof slicing experim*)
  | SPASS
  | MINISAT
  | LOG (* Using previous results instead of invoking the actual provers *)

let string_of_prover prover = match prover with
	| OmegaCalc -> "OMEGA CALCULATOR"
	| CvcLite -> "CVC Lite"
	| Cvc3 -> "CVC3"
	| CO  -> "CO"
	| Isabelle -> "ISABELLE"
	| Mona -> "MONA"
	| MonaH -> "MonaH"
	| OM -> "OM"
	| OI -> "OI"
	| SetMONA -> "SetMONA"
	| CM  -> "CM"
	| Coq -> "COQ"
	| Z3 -> "Z3"
        | Z3N -> "Z3N"
	| OCRed -> "OC and REDLOG"
	| Redlog -> "REDLOG (REDUCE LOGIC)"
	| RM -> "Redlog, Mona"
        | Mathematica -> "Mathematica"
	| PARAHIP -> "Redlog, Mona, z3" (*This option is used on ParaHIP website*)
	| ZM -> "Z3, Mona"
	| OZ -> "Omega, z3"
	| AUTO -> "AUTO - omega, z3, mona, coq"
	| DP -> "Disequality Solver"
	| SPASS -> "SPASS"
	| MINISAT -> "MINISAT"
	| LOG -> "LOG"

let last_tp_used = new VarGen.store LOG string_of_prover

let last_proof_string = new VarGen.store "no proof" pr_id

let last_proof_result = new VarGen.store "no result" pr_id

(* 
   this is meant to record the last commands in the
   different category encounterd by sleek/hip; but it
   should perhaps be integrated with the logging command
   option to avoid duplication?
*)
