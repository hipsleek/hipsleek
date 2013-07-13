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
	| PK_Term_Dec
	| PK_Term_Bnd
	| PK_Sleek_Entail of int
	| PK_Early_Contra_Detect
	| PK_Contra_Detect_Pure
	| PK_Cast
	| PK_If_Stmt
	| PK_Pre_Oblg
	| PK_Post_Oblg
	| PK_Assign_Stmt
	| PK_Assert
	| PK_BIND
	| PK_PRE
	| PK_POST

let string_of_proving_kind pk =
  match pk with
    | PK_Sat_Warning -> "Sat_Warning"
    | PK_Pred_Check_Inv -> "Pred_Check_Inv"
    | PK_Compute_Base_Case-> "Compute_Base_Case"
    | PK_Trans_Proc -> "Trans_Proc"
    | PK_Check_Specs -> "Check_Specs"
    | PK_Verify_Lemma -> "Verify_Lemma"
    | PK_Lemma_Norm -> "Lemma_Norm"
    | PK_Term_Dec -> "Term_Dec"
    | PK_Term_Bnd -> "Term_Bnd"
    | PK_Sleek_Entail(n) -> "Sleek_Entail("^(string_of_int n)^")"
    | PK_Early_Contra_Detect -> "Early_Contra_Detect"
    | PK_Contra_Detect_Pure -> "Contra_Detect_Pure"
    | PK_Cast -> "Cast"
    | PK_If_Stmt -> "If_Stmt"
    | PK_Assign_Stmt -> "Assign_Stmt"
    | PK_Assert -> "Assert"
    | PK_BIND -> "BIND"
    | PK_PRE -> "PRE"
    | PK_POST -> "POST"
    | PK_Pre_Oblg -> "PRE-OBLIGATION"
    | PK_Post_Oblg -> "POST-OBLIGATION"

let sleek_kind = new Gen.stack_pr string_of_proving_kind (==)

let proving_kind = new Gen.stack_pr string_of_proving_kind (==)

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
    let m = proving_kind # get_stk in
    let _ = proving_kind # push tk in
    try 
      let res = exec_function args in
      let _ =  proving_kind # pop
      in res
    with _ as e ->
        begin
          proving_kind # set_stk m;
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

