open Cformula
open Prooftracer
open Globals


let mkFailCtx_may ?(conseq=None) ln s estate pos =
  let conseq = match conseq with
    | None -> (formula_of_heap HFalse pos)
    | Some f -> f in
  (* let fail_ctx = mkFailContext mem_leak estate_orig1 conseq None pos in *)
  let err_msg = ln^s in
  mkFailCtx_in (Basic_Reason (mkFailContext err_msg estate conseq None pos, 
                                  mk_failure_may ln Globals.sl_error, estate.es_trace)) 
    ((convert_to_may_es estate), err_msg, Failure_May err_msg) 
    (mk_cex true)

let mkFailCtx_must ln s estate pos =
  let err_msg = s in
  mkFailCtx_in (Basic_Reason (mkFailContext err_msg estate (formula_of_heap HFalse pos) None pos, 
                                  mk_failure_must ln Globals.sl_error, estate.es_trace)) ((convert_to_must_es estate), err_msg, Failure_Must err_msg) (mk_cex true)
