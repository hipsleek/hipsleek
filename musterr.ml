(*for must/may errors*)

open Globals
open Gen
open Exc.GTable
open Perm
open Cformula

module Err = Error
module CP = Cpure
module MCP = Mcpure


(* context functions *)
(*type formula_cache_no = int
  
type formula_cache_no_list = formula_cache_no list*)
type formula_trace = string list

type list_formula_trace = formula_trace list

type entail_state = {
  es_formula : formula; (* can be any formula ; 
    !!!!!  make sure that for each change to this formula the es_cache_no_list is update apropriatedly*)
  es_heap : h_formula; (* consumed nodes *)
  es_pure : (MCP.mix_formula * (branch_label * CP.formula) list);
  es_evars : CP.spec_var list;
  (*used by lemmas*)
  es_ivars : CP.spec_var list; (* ivars are the variables to be instantiated (for the universal lemma application)  *)
  (* es_expl_vars : CP.spec_var list; (\* vars to be explicit instantiated *\) *)
  es_ante_evars : CP.spec_var list;
  (* es_must_match : bool; *)
  (*used by late instantiation*)
  es_gen_expl_vars: CP.spec_var list; 
  es_gen_impl_vars: CP.spec_var list; 
  es_unsat_flag : bool; (* true - unsat already performed; false - requires unsat test *)
  es_pp_subst : (CP.spec_var * CP.spec_var) list;
  es_arith_subst : (CP.spec_var * CP.exp) list;
  es_success_pts : (formula_label * formula_label)  list  ;(* successful pt from conseq *)
  es_residue_pts : formula_label  list  ;(* residue pts from antecedent *)
  es_id      : int              ; (* unique +ve id *)
  es_orig_ante   : formula        ;  (* original antecedent formula *) 
  es_orig_conseq : struc_formula ;
  es_path_label : path_trace;
  es_prior_steps : steps; (* prior steps in reverse order *)
  (*es_cache_no_list : formula_cache_no_list;*)
  es_var_measures : CP.exp list;
  es_var_label : int option;
  es_var_ctx_lhs : CP.formula;
  es_var_ctx_rhs : CP.formula;
  es_var_subst : (CP.spec_var * CP.spec_var * ident) list;
  es_var_loc : loc;
  (* for immutability *)
(* INPUT : this is an alias set for the RHS conseq *)
(* to be used by matching strategy for imm *)
  es_rhs_eqset : (CP.spec_var * CP.spec_var) list;
(*  es_frame : (h_formula * int) list; *)
  es_cont : h_formula list;
  es_crt_holes : (h_formula * int) list;
  es_hole_stk : ((h_formula * int) list) list;
  es_aux_xpure_1 : MCP.mix_formula;
(* below are being used as OUTPUTS *)
  es_subst :  (CP.spec_var list *  CP.spec_var list) (* from * to *); 
  es_aux_conseq : CP.formula;
  es_imm_pure_stk : MCP.mix_formula list;
  es_must_error : (string * fail_type) option;
  (* es_must_error : string option *)
  es_trace : formula_trace; (*LDK: to keep track of past operations: match,fold...*)
  es_is_normalizing : bool (*normalizing process*)
}

and context = 
  | Ctx of entail_state
  | OCtx of (context * context) (* disjunctive context *)
      (*| FailCtx of (fail_context list)*)

and steps = string list

(*      MAY

 VALID       MUST

        BOT
*)

and failure_kind =
  | Failure_May of string
  | Failure_Must of string
  | Failure_Bot of string
  | Failure_Valid

and fail_explaining = {
  fe_kind: failure_kind; (*may/must*)
  fe_name: string;
  fe_locs: loc list;
  (* fe_explain: string;  *)
    (* string explaining must failure *)
  (*  fe_sugg = struc_formula *)
}

and fail_context = {
  fc_prior_steps : steps; (* prior steps in reverse order *)
  fc_message : string;          (* error message *)
  fc_current_lhs : entail_state;     (* LHS context with success points *)
  fc_orig_conseq : struc_formula;     (* RHS conseq at the point of failure *)
  fc_failure_pts : formula_label list;     (* failure points in conseq *) 
  fc_current_conseq : formula;
}  
    
and fail_type =
  | Basic_Reason of (fail_context * fail_explaining)
  | Trivial_Reason of fail_explaining
  | Or_Reason of (fail_type * fail_type)
  | And_Reason of (fail_type * fail_type)
  | Union_Reason of (fail_type * fail_type)
  | ContinuationErr of fail_context    
  | Or_Continuation of (fail_type * fail_type)


(* Fail | List of Successes *)
and list_context = 
  | FailCtx of fail_type 
  | SuccCtx of context list
      
and branch_fail = path_trace * fail_type

and branch_ctx =  path_trace * context

(* disjunction of state with failures and partial success *)
(* a state is successful if it has empty branch_fail *)
and partial_context = (branch_fail list) * (branch_ctx list)  
    (* disjunct of failures and success *)

(* successful partial states that have escaped through exceptions *)
and esc_stack = ((control_path_id_strict * branch_ctx list) list)

and failesc_context = (branch_fail list) * esc_stack * (branch_ctx list)

(* conjunct of context in the form of /\(f1|f2 ..s1|s2|s3) *)
and list_partial_context = partial_context list

and list_failesc_context = failesc_context list
    (* conjunct of contexts *)

and list_failesc_context_tag = failesc_context Gen.Stackable.tag_list

let print_list_context_short = ref(fun (c:list_context) -> "printer not initialized")
let print_context_list_short = ref(fun (c:context list) -> "printer not initialized")
let print_context_short = ref(fun (c:context) -> "printer not initialized")
let print_entail_state = ref(fun (c:entail_state) -> "printer not initialized")
let print_list_partial_context = ref(fun (c:list_partial_context) -> "printer not initialized")
let print_list_failesc_context = ref(fun (c:list_failesc_context) -> "printer not initialized")
(* let print_flow = ref(fun (c:nflow) -> "printer not initialized") *)
let print_esc_stack = ref(fun (c:esc_stack) -> "printer not initialized")
let print_failesc_context = ref(fun (c:failesc_context) -> "printer not initialized")
let print_failure_kind_full = ref(fun (c:failure_kind) -> "printer not initialized")
let print_fail_type = ref(fun (c:fail_type) -> "printer not initialized")

let rec empty_es flowt pos =
	let x = mkTrue flowt pos in
{
  es_formula = x;
  es_heap = HTrue;
  es_pure = (MCP.mkMTrue pos , []);
  es_evars = [];
  (* es_must_match = false; *)
  es_ivars = [];
  (* es_expl_vars = []; *)
  es_ante_evars = [];
  es_gen_expl_vars = [];
  es_gen_impl_vars = [];
  es_pp_subst = [];
  es_unsat_flag = true;
  es_arith_subst = [];
  es_success_pts = [];
  es_residue_pts  = [];
  es_id = 0 ;
  es_orig_ante = x;
  es_orig_conseq = [mkETrue flowt pos] ;
  es_rhs_eqset = [];
  es_path_label  =[];
  es_prior_steps  = [];
  es_var_measures = [];
  es_var_label = None;
  es_var_ctx_lhs = CP.mkTrue pos;
  es_var_ctx_rhs = CP.mkTrue pos;
  es_var_subst = [];
   es_var_loc = no_pos;
  (*es_cache_no_list = [];*)
  es_cont = [];
  es_crt_holes = [];
  es_hole_stk = [];
  es_aux_xpure_1 = MCP.mkMTrue pos;
  es_subst = ([], []);
  es_aux_conseq = CP.mkTrue pos;
   es_imm_pure_stk = [];
  es_must_error = None;
  es_trace = [];
  es_is_normalizing = false;
}


let is_one_context (c:context) =
  match c with
    | Ctx _ -> true
    | OCtx _ -> false

let is_cont t = 
  match t with
    | ContinuationErr _ -> true
    | Or_Continuation _ -> true
    | _ -> false

let isFailCtx cl = match cl with 
	| FailCtx _ -> true
	| SuccCtx _ -> false

let isFailCtx cl = 
  Gen.Debug.no_1 "isFailCtx" 
      !print_list_context_short string_of_bool isFailCtx cl

let get_must_error_from_ctx cs = 
  match cs with 
    | [Ctx es] -> (match es.es_must_error with
        | None -> None
        | Some (msg,_) -> Some msg)
    | _ -> None

let get_bot_status_from_ctx cs=
  match cs with
    | [Ctx es] ->
        ( match formula_is_eq_flow es.es_formula false_flow_int with
          | true -> Some ""
          | false -> None
        )
    | _ -> None

let rec set_must_error_from_one_ctx ctx msg ft=
  match ctx with
    | Ctx es ->
        begin
            let instance_ft=
              (
                  match ft with
                    | Basic_Reason (fc, fe) ->
                        let instance_fc = {fc with fc_current_lhs = es;
                            fc_message = msg;
                            fc_prior_steps = es.es_prior_steps
                                          }
                        in Basic_Reason (instance_fc, fe)
                    | _ -> report_error no_pos "Cformula.set_must_error_from_one_ctx: should be basic reason here"
              )
            in
            Ctx {es with  es_formula = substitute_flow_into_f  !error_flow_int es.es_formula;
                es_must_error = Some (msg,instance_ft)}
        end
    | OCtx (ctx1, ctx2) -> OCtx (set_must_error_from_one_ctx ctx1 msg ft, set_must_error_from_one_ctx ctx2 msg ft)

let rec set_must_error_from_ctx cs msg ft=
  match cs with
    | [] -> []
    | es::ls -> (set_must_error_from_one_ctx es msg ft):: (set_must_error_from_ctx ls msg ft)

let isFailCtx_gen cl = match cl with
	| FailCtx _ -> true
	| SuccCtx cs -> (get_must_error_from_ctx cs) !=None
    (* | _ -> false *)

let mk_failure_bot_raw msg = Failure_Bot msg

let mk_failure_must_raw msg = Failure_Must msg

let mk_failure_may_raw msg = Failure_May msg

let mk_failure_may msg name = {fe_kind = Failure_May msg;fe_name = name ;fe_locs=[]}

let mk_failure_must msg name = {fe_kind = mk_failure_must_raw msg;fe_name = name ;fe_locs=[]}

let mk_failure_bot msg = {fe_kind = mk_failure_bot_raw msg;fe_name = "" ;fe_locs=[]}

let mkAnd_Reason (ft1:fail_type option) (ft2:fail_type option): fail_type option=
  match ft1, ft2 with
    | None, ft2 -> ft2
    | _ , None -> ft1
    | Some ft1, Some ft2 -> Some (And_Reason (ft1, ft2))

let comb_must m1 m2 = "["^m1^","^m2^"]"

let is_must_failure_fe (f:fail_explaining) =
  match f.fe_kind with
    | Failure_Must _ -> true
    | _ -> false

let rec is_must_failure_ft (f:fail_type) =
  match f with
    | Basic_Reason (_,fe) -> is_must_failure_fe fe
    | Or_Reason (f1,f2) -> (is_must_failure_ft f1) && (is_must_failure_ft f2)
    | And_Reason (f1,f2) -> (is_must_failure_ft f1) || (is_must_failure_ft f2)
    | Union_Reason (f1,f2) -> (is_must_failure_ft f1) || (is_must_failure_ft f2)
    | _ -> false

let is_must_failure (f:list_context) =
  match f with
    | FailCtx f -> is_must_failure_ft f
    | _ -> false

let get_must_failure_fe (f:fail_explaining) =
  match f.fe_kind with
    | Failure_Must m -> Some m
    | _ -> None

let comb_or m1 m2 = match m1,m2 with
  | Some m1, Some m2 -> Some ("or["^m1^","^m2^"]")
  | _, _ -> None

let comb_and m1 m2 = match m1,m2 with
  | Some m1, Some m2 -> Some ("and["^m1^","^m2^"]")
  | Some m1, None -> Some (m1)
  | None, Some m2 -> Some (m2)
  | _, _ -> None

let rec context_is_eq_flow (f:context) (ff)  : bool=
  match f with
    | Ctx es -> formula_is_eq_flow es.es_formula ff
    | OCtx (c1,c2) -> (context_is_eq_flow c1 ff) && (context_is_eq_flow c2 ff)

let list_context_is_eq_flow (f:list_context) (ff)  : bool=
  match f with
    | FailCtx _ -> false
    | SuccCtx ls -> List.for_all (fun f -> context_is_eq_flow f ff) ls

let get_failure_fe (f:fail_explaining) = f.fe_kind

(*gen_land*)
let gen_land (m1,n1,e1) (m2,n2,e2) = match m1,m2 with
  | Failure_Bot _, _ -> m1, n1, e1
      (*report_error no_pos "Failure_None not expected in gen_and"*)
  | _, Failure_Bot _ -> m2, n2, e2
      (*report_error no_pos "Failure_None not expected in gen_and"*)
  | Failure_May m1, Failure_May m2 -> (Failure_May ("land["^m1^","^m2^"]"),n1,None)
  | Failure_May m1, _ -> m2, n2, e2
  | _ , Failure_May m2 -> m1,n1, e1
  | Failure_Must m1, Failure_Must m2 ->
       if (n1==sl_error) then (Failure_Must m2, n2, e2)
       else if (n2==sl_error) then (Failure_Must m1, n1, e1)
       else Failure_Must ("land["^m1^","^m2^"]"), n1, e1 (*combine state here?*)
  | Failure_Must m1, Failure_Valid -> Failure_May ("land["^m1^",Valid]"), n1, None (*combine state here?*)
  | Failure_Valid, x  -> (m2, n2, e2)

(*gen_rand*)
let gen_rand_x (m1,n1,e1) (m2,n2,e2) = match m1,m2 with
  | Failure_Bot m, _ -> Failure_Bot m, n1,e1
      (*report_error no_pos "Failure_None not expected in gen_and"*)
  | _, Failure_Bot m -> Failure_Bot m, n2, e2
      (*report_error no_pos "Failure_None not expected in gen_and"*)
  | Failure_Must m1, Failure_Must m2 ->
      if (n1=sl_error) then (Failure_Must m2, n2, e2)
      else if (n2= sl_error) then (Failure_Must m1, n1, e1)
      else Failure_Must ("rand["^m1^","^m2^"]"), n1, e1 (*combine state here?*)
  | Failure_Must m, _ -> Failure_Must m, n1, e1
  | _, Failure_Must m -> Failure_Must m, n2, e2
  | Failure_May m1, Failure_May m2 -> (Failure_May ("rand["^m1^","^m2^"]"),n1,None)
  | Failure_May m, _ -> Failure_May m,n1,None
  | _, Failure_May m -> Failure_May m,n2,None
  | Failure_Valid, x  -> (m2,n2,e2)
  (* | x, Failure_Valid -> x *)

let gen_rand (m1,n1,e1) (m2,n2,e2)=
  let pr (m, n , e) = (!print_failure_kind_full m) ^ ", name: " ^ n in
  let pr1 (m, n, e) = let tmp = (!print_failure_kind_full m) ^ ", name: " ^ n in
                       match e with
                         | None -> tmp
                         | Some f -> tmp ^ "\n" ^ (!print_entail_state f)
  in
  Gen.Debug.no_2 "gen_rand" pr pr pr1 (fun x y -> gen_rand_x x y) (m1,n1,e1) (m2,n2,e2)

(* state to be refined to accurate one for must-bug *)
(*gen_lor*)
let gen_lor_x (m1,n1,e1) (m2,n2,e2) : (failure_kind * string * (entail_state option)) = match m1,m2 with
  | Failure_Bot m1,  Failure_Bot m2 ->  Failure_Bot ("lor["^m1^","^m2^"]"), n1, e1 (*combine state here?*)
(* report_error no_pos "Failure_None not expected in gen_or" *)
  | Failure_Bot _, _ ->  m2, n2,e2
      (* report_error no_pos "Failure_None not expected in gen_or" *)
  | _, Failure_Bot _ -> m1,n1,e1
      (*report_error no_pos "Failure_None not expected in gen_or"*)
  | Failure_May m1, Failure_May m2 -> Failure_May ("lor["^m1^","^m2^"]"),n1, None
  | Failure_May m, _ -> Failure_May m, n1,None
  | _, Failure_May m -> Failure_May m,n2,None
  | Failure_Must m1, Failure_Must m2 ->
      if (n1=sl_error) then (Failure_Must m2, n2, e2)
      else if (n2= sl_error) then (Failure_Must m1, n1, e1)
      else (Failure_Must ("lor["^m1^","^m2^"]"), n1, e1)
  | Failure_Must m, Failure_Valid -> (Failure_May ("lor["^m^",valid]"),n1,None)
  | Failure_Valid, Failure_Must m -> (Failure_May ("lor["^m^",valid]"),n2,None)
  (* | _, Failure_Must m -> Failure_May ("or["^m^",unknown]") *)
  (* | Failure_Must m,_ -> Failure_May ("or["^m^",unknown]") *)
  | Failure_Valid, x  -> (m2,n2,e2)
  (* | x, Failure_Valid -> x *)

let gen_lor (m1,n1,e1) (m2,n2,e2)=
  let pr (m, n , e) = (!print_failure_kind_full m) ^ ", name: " ^ n in
  let pr1 (m, n, e) = let tmp = (!print_failure_kind_full m) ^ ", name: " ^ n in
                       match e with
                         | None -> tmp
                         | Some f -> tmp ^ "\n" ^ (!print_entail_state f)
  in
  Gen.Debug.no_2 "gen_lor" pr pr pr1 (fun x y -> gen_lor_x x y) (m1,n1,e1) (m2,n2,e2)


(*gen_ror*)
(*
  - m: failure_kind (must/may/bot/valid)
  - n: name of failure (logical/separation entailment). should reduce separation entailment
  - e: current entailment
*)
let gen_ror_x (m1, n1, e1) (m2, n2, e2) = match m1,m2 with
  | Failure_Bot m1,  Failure_Bot m2 ->  Failure_Bot ("ror["^m1^","^m2^"]"), n1,e1 (*combine state here?*)
  | Failure_Bot _, x -> m1,n1,e1 (* (m2,e2) *)
  | x, Failure_Bot _ -> m2,n2,e2 (*(m1,e1)*)
  | Failure_Valid, _ -> (Failure_Valid,"",None)
  | _, Failure_Valid -> (Failure_Valid,"",None)
  | Failure_Must m1, Failure_Must m2 ->
      if (n1=sl_error && e2 != None) then (Failure_Must m2, n2, e2)
      else if (n2 =sl_error && e1 != None) then(Failure_Must m1, n1, e1)
      else (Failure_Must ("ror["^m1^","^m2^"]"),n1, e1)
  | Failure_May m1, Failure_May m2 -> (Failure_May ("ror["^m1^","^m2^"]"),n1,None)
  | Failure_May _,  _ -> (m1,n1,e1)
  | _, Failure_May _ -> (m2,n2,e2)

let gen_ror (m1,n1,e1) (m2,n2,e2)=
  let pr (m, n , e) = (!print_failure_kind_full m) ^ ", name: " ^ n in
  let pr1 (m, n, e) = let tmp = (!print_failure_kind_full m) ^ ", name: " ^ n in
                       match e with
                         | None -> tmp
                         | Some f -> tmp ^ "\n" ^ (!print_entail_state f)
  in
  Gen.Debug.no_2 "gen_ror" pr pr pr1 (fun x y -> gen_ror_x x y) (m1,n1,e1) (m2,n2,e2)


let rec get_failure_es_ft_x (ft:fail_type) : (failure_kind * (entail_state option)) =
  let rec helper ft = 
  match ft with
    | Basic_Reason (fc,fe) ->
        (*let _= print_endline ("fe_name: " ^ fe.fe_name) in*)
        let f = get_failure_fe fe in
        if (is_must_failure_fe fe) then (f,  fe.fe_name, Some fc.fc_current_lhs)
        else (f,fe.fe_name, None)
    | Or_Reason (f1,f2) -> gen_lor (helper f1) (helper f2)
    | And_Reason (f1,f2) -> gen_rand (helper f1) (helper f2)
    | Union_Reason (f1,f2) -> gen_ror (helper f1) (helper f2)
    | ContinuationErr _ -> (Failure_May "Continuation_Err", "Continuation", None)
    | Or_Continuation (f1,f2) -> gen_lor (helper f1) (helper f2)
    (* report_error no_pos "get_must_failure : or continuation encountered" *)
    | Trivial_Reason fe -> (fe.fe_kind, fe.fe_name, None)
  in
  let (f, _, oes) = helper ft in (f, oes)


let get_failure_es_ft (ft:fail_type) : (failure_kind * (entail_state option)) =
  let pr1 (m, e) = let tmp = (!print_failure_kind_full m) in
                       match e with
                         | None -> tmp
                         | Some f -> tmp ^ "\n" ^ (!print_entail_state f)
  in
  Gen.Debug.no_1 "get_failure_es_ft" !print_fail_type pr1 (fun x -> get_failure_es_ft_x x) ft

let get_failure_ft (ft:fail_type) : (failure_kind) =
  fst (get_failure_es_ft ft)

let get_must_failure_ft f =
  match (get_failure_ft f) with
    | Failure_Must m -> Some m
    | _ -> None

let get_bot_status_ft f =
  match (get_failure_ft f) with
    | Failure_Bot m -> Some m
    | _ -> None

let get_may_failure_fe (f:fail_explaining) =
  match f.fe_kind with
    | Failure_May m | Failure_Must m -> Some m 
    | Failure_Valid -> Some "proven valid here"
    | Failure_Bot _ -> None


let get_may_failure_ft f =
  match (get_failure_ft f) with
    | Failure_Must m -> Some ("must:"^m)
    | Failure_May m -> Some (m)
    | Failure_Valid -> Some ("Failure_Valid")
    | Failure_Bot m -> Some ("Failure_None"^m)

let get_may_failure (f:list_context) =
  match f with
    | FailCtx ft -> 
          let m = (get_may_failure_ft ft) in
          (match m with
            | Some s -> m
            | None -> 
                  let _ = print_flush (!print_list_context_short f) 
                  in report_error no_pos "Should be a may failure here")
    | _ -> None

(* returns Some es if it is a must failure *)
let rec get_must_es_from_ft ft = 
  match ft with
    | Basic_Reason (fc,fe) -> 
          if is_must_failure_fe fe then Some fc.fc_current_lhs
          else None
    | Or_Reason (f1,f2) -> 
          let r1=(get_must_es_from_ft f1) in
          let r2=(get_must_es_from_ft f2) in
          (match r1,r2 with
            | Some _,Some _ -> r1
            | _, _ -> None)
    | And_Reason (f1,f2) | Union_Reason (f1,f2) -> 
          let r1=(get_must_es_from_ft f1) in
          let r2=(get_must_es_from_ft f2) in
          (match r1,r2 with
            | Some _, _ -> r1
            | None, Some _ -> r2
            | None, None -> None)
    | _ -> None

let get_must_es_msg_ft ft =
  let msg,es = get_failure_es_ft ft in
  (* let es = get_must_es_from_ft ft in *)
  (* let msg = get_must_failure_ft ft in *)
  match es,msg with
    | Some es, Failure_Must msg -> Some (es,msg)
    | None, Failure_Must msg -> Some (empty_es ( mkTrueFlow ()) no_pos,msg) (*may be Trivial fail*)
    (*report_error no_pos "INCONSISTENCY with get_must_es_msg_ft"*)
    | _, _ -> None

let get_must_failure (ft:list_context) =
  match ft with
    | FailCtx f -> get_must_failure_ft f
          (* (try get_must_failure_ft f *)
          (* with a ->   *)
          (*     let _ = print_flush (!print_list_context_short ft) in *)
          (*     raise a) *)
	| SuccCtx cs -> get_must_error_from_ctx cs
    (* | _ -> None *)

let get_bot_status (ft:list_context) =
  match ft with
    | FailCtx f -> get_bot_status_ft f
	| SuccCtx cs -> get_bot_status_from_ctx cs

let extract_failure_msg rs=
 if not !Globals.disable_failure_explaining then
   match get_must_failure rs with
     | Some s -> "(must) cause:"^s
     | _ -> (match get_may_failure rs with
           | Some s -> "(may) cause:"^s
           | None -> "INCONSISTENCY : expected failure but success instead"
     )
 else ""


let is_may_failure_fe (f:fail_explaining) = (get_may_failure_fe f) != None

let rec is_may_failure_ft (f:fail_type) = (get_may_failure_ft f) != None

let is_may_failure (f:list_context) = (get_may_failure f) != None

let is_bot_status (f:list_context) = (get_bot_status f) != None

let convert_must_failure_4_fail_type  (s:string) (ft:fail_type) : context option =
     match (get_must_es_msg_ft ft) with
          | Some (es,msg) -> Some (Ctx {es with es_must_error = Some (s^msg,ft) } )
          | _ ->  None

let convert_must_failure_to_value_orig (l:list_context) : list_context =
  match l with
    | FailCtx ft ->
          (* (match (get_must_es_msg_ft ft) with *)
          (*   | Some (es,msg) -> SuccCtx [Ctx {es with es_must_error = Some (msg,ft) } ]  *)
          (*   | _ ->  l) *)
          (match (convert_must_failure_4_fail_type "" ft) with
            | Some ctx -> SuccCtx [ctx]
            | None -> l)
    | SuccCtx _ -> l

let convert_must_failure_to_value_orig (l:list_context) : list_context =
 let pr = !print_list_context_short in
  Gen.Debug.no_1 "convert_must_failure_to_value_orig" pr pr
  (fun _ -> convert_must_failure_to_value_orig l) l

(* let add_must_err (s:string) (fme:branch_ctx list) (e:esc_stack) : esc_stack = *)
(*   ((-1,"Must Err @"^s),fme) :: e *)

let add_must_err_to_pc (s:string) (fme:branch_ctx list) (e:branch_ctx list) : branch_ctx list =
  fme @ e

let convert_must_failure_4_branch_type  (s:string) ((pt,ft):branch_fail) : branch_ctx option =
  match (convert_must_failure_4_fail_type s ft) with
    | Some b -> Some (pt,b)
    | None -> None

let convert_must_failure_4_branch_fail_list  (s:string) (fl:branch_fail list) : (branch_ctx list * branch_fail list) =
  List.fold_left (fun (must_l,may_l) bf ->
      match (convert_must_failure_4_branch_type s bf) with
        | Some r -> (r::must_l, may_l)
        | None -> (must_l, bf::may_l)) ([],[]) fl

let convert_must_failure_4_failesc_context (s:string) ((fl,e,bl):failesc_context) : failesc_context =
  let (fme,fl) = convert_must_failure_4_branch_fail_list s fl in
  (fl,e,add_must_err_to_pc s fme bl)

let convert_must_failure_4_list_failesc_context (s:string) (l:list_failesc_context) : list_failesc_context =
  List.map (convert_must_failure_4_failesc_context s) l


let fold_context (f:'t -> entail_state -> 't) (a:'t) (c:context) : 't =
  let rec helper a c = match c with
    | Ctx es -> f a es
    | OCtx (c1,c2) -> helper (helper a c1) c2 in
  helper a c


let consistent_entail_state (es:entail_state) : bool = consistent_formula es.es_formula

let consistent_context (c:context) : bool =
  fold_context (fun a es -> (consistent_entail_state es) && a) true c

let must_consistent_context (s:string) l : unit =
  if !consistency_checking then
    let b = consistent_context l in
    if b then  print_endline ("\nSuccessfully Tested Consistency at "^s)
    else report_error no_pos ("ERROR at "^s^": context inconsistent")

let consistent_branch_ctx ((_,c):branch_ctx) : bool = consistent_context c

let consistent_esc_stack (ls:esc_stack) : bool =
  List.for_all (fun (_,b_ls) -> List.for_all consistent_branch_ctx b_ls) ls

let consistent_failesc_context ((_,es,b_ls):failesc_context) : bool =
  let b1 = List.for_all (consistent_branch_ctx) b_ls in
  let b2 = consistent_esc_stack es in
  b1 && b2

let consistent_list_failesc_context (l:list_failesc_context) : bool =
   List.for_all (consistent_failesc_context) l

let must_consistent_list_failesc_context (s:string) l : unit =
  if !consistency_checking then
    let b = consistent_list_failesc_context l in
    if b then  print_endline ("\nSuccessfully Tested Consistency at "^s)
    else report_error no_pos ("ERROR: "^s^" list_failesc context inconsistent")

let isAnyFalseCtx (ctx:context) : bool = match ctx with
  | Ctx es -> isAnyConstFalse es.es_formula
  | _ -> false

let isAnyFalseBranchCtx (ctx:branch_ctx) : bool = match ctx with
  | _,Ctx es -> isAnyConstFalse es.es_formula
  | _ -> false

let isAnyFalsePartialCtx (fc,sc) = (fc=[]) &&
  List.for_all (fun (_,s) -> isAnyFalseCtx s) sc

let isAnyFalseFailescCtx (fc,ec,sc) = (fc=[]) &&
  List.for_all (fun (_,s) -> isAnyFalseCtx s) sc

let isAnyFalseListCtx ctx = match ctx with
  | SuccCtx lc ->List.exists isAnyFalseCtx lc
  | FailCtx _ -> false

let isStrictTrueCtx ctx = match ctx with
  | Ctx es -> isStrictConstTrue es.es_formula
  | _ -> false

let isAnyTrueCtx ctx = match ctx with
  | Ctx es -> isAnyConstTrue es.es_formula
  | _ -> false

let rec allFalseCtx ctx = match ctx with
	| Ctx es -> isAnyFalseCtx ctx
	| OCtx (c1,c2) -> (allFalseCtx c1) && (allFalseCtx c2)


let es_simplify (e1:entail_state):entail_state =
  let hfv0 = h_fv e1.es_heap in
  let pusher f vl =
    if (vl==[]) then (f,[])
      else
        let h, p , fl , br , t  = split_components f in
        let hfv = (h_fv h)@hfv0 in
        let brfv = br_fv br [] in
        let rv1 = Gen.BList.difference_eq (CP.eq_spec_var) vl hfv in
        let rvp,rvb = Gen.BList.diff_split_eq (CP.eq_spec_var) rv1 brfv in
        if (rv1==[]) then (f,[])
        else
          let rp =
            if (rvp==[]) then p
          else MCP.memo_pure_push_exists rvp p in
          (mkExists rvb h rp t fl br no_pos, [])  in

  let formula_simplify f aev= match f with
    | Exists e ->
      let vl = e.formula_exists_qvars @ aev in
      pusher f vl
    | Base _ -> pusher f aev
    | Or c-> Err.report_error { Err.error_loc = no_pos; Err.error_text ="unexpected Or formula in es_simplify"} in
  let nf, naev = formula_simplify e1.es_formula e1.es_ante_evars in
  {e1 with es_formula = nf; es_ante_evars =naev}


let es_simplify e1 =
  let pr  = !print_entail_state in
  Gen.Debug.no_1 "es_simplify" pr pr es_simplify e1

let mkOCtx ctx1 ctx2 pos =
  if isAnyFalseCtx ctx1 then ctx2
  else if isAnyFalseCtx ctx2 then ctx1
  else OCtx (ctx1,ctx2)

let or_context c1 c2 = mkOCtx c1 c2 no_pos

let rec context_simplify (c:context):context  = match c with
  | Ctx e -> Ctx ((*es_simplify*) e)
  | OCtx (c1,c2) -> mkOCtx (context_simplify c1) (context_simplify c2) no_pos

let context_list_simplify (l:context list):context list = List.map context_simplify l

let list_context_simplify (l : list_context) : list_context = match l with
  | FailCtx _-> l
  | SuccCtx sc -> SuccCtx (List.map context_simplify sc)


let failesc_context_simplify ((l,a,cs) : failesc_context) : failesc_context =
  let cs = List.filter (fun x -> not(isAnyFalseBranchCtx x)) cs in
  let newcs = List.map (fun (p,c) -> (p,context_simplify c)) cs in
  (l,a,newcs)

let list_failesc_context_simplify (l : list_failesc_context) : list_failesc_context =
  List.map failesc_context_simplify l

let list_failesc_context_simplify (l : list_failesc_context) : list_failesc_context =
  let pr = !print_list_failesc_context in
  Gen.Debug.no_1 "list_failesc_context_simplify" pr pr list_failesc_context_simplify l


let mk_empty_frame () : (h_formula * int ) =
  let hole_id = fresh_int () in
    (Hole(hole_id), hole_id)

let mk_not_a_failure =
  Basic_Reason (
      {
          fc_prior_steps = []; fc_message = "Success";
          fc_current_lhs =  empty_es (mkTrueFlow ()) no_pos;
          fc_orig_conseq =  [mkETrue  (mkTrueFlow ()) no_pos];
          fc_failure_pts = [];
          fc_current_conseq = mkTrue (mkTrueFlow ()) no_pos},
      {
          fe_kind = Failure_Valid;
          fe_name = "" ;fe_locs=[]
      }
  )

let invert ls =
  let foo es =
    let fc_template = {
		fc_message = "INCONSISTENCY : expected failure but success instead";
		fc_current_lhs  =  empty_es (mkTrueFlow ()) no_pos;
		fc_prior_steps = [];
		fc_orig_conseq  = es.es_orig_conseq;
		fc_current_conseq = mkTrue (mkTrueFlow()) no_pos;
		fc_failure_pts =  []
    } in
    (Basic_Reason (fc_template,
                   mk_failure_must "INCONSISTENCY : expected failure but success instead" ""))
  in
  let goo es ff = formula_subst_flow es.es_formula ff in
  let errmsg = "Expecting Failure but Success instead" in
  match ls with
  | [] -> []
  | [Ctx es] -> (match es.es_must_error with
      | None -> [Ctx {es with es_must_error = Some ("1 "^errmsg,foo es); es_formula = goo es (mkErrorFlow())}]
      | Some _ -> [Ctx {es with es_must_error = None; es_formula = goo es (mkNormalFlow())}])
  | (Ctx es)::_ -> [Ctx {es with es_must_error = Some ("2 "^errmsg,foo es); es_formula = goo es (mkErrorFlow())}]
  | _ -> report_error no_pos "not sure how to invert_outcome"

let invert_outcome (l:list_context) : list_context =
  match l with
  | FailCtx ft -> l
  | SuccCtx ls -> SuccCtx (invert ls)

let empty_ctx flowt pos = Ctx (empty_es flowt pos)

let false_ctx flowt pos =
	let x = mkFalse flowt pos in
	Ctx ({(empty_es flowt pos) with es_formula = x ; es_orig_ante = x; })

let false_ctx_with_orig_ante f flowt pos =
	let x = mkFalse flowt pos in
	Ctx ({(empty_es flowt pos) with es_formula = x ; es_orig_ante = f; })

let false_es flowt pos =
  let x =  mkFalse flowt pos in
    {(empty_es flowt pos) with es_formula = x;}

and true_ctx flowt pos = Ctx (empty_es flowt pos)

let mkFalse_branch_ctx = ([],false_ctx mkFalseFlow no_pos)

let rec contains_immutable_ctx (ctx : context) : bool =
  match ctx with
    | Ctx(es) -> contains_immutable es.es_formula
    | OCtx(c1, c2) -> (contains_immutable_ctx c1) or (contains_immutable_ctx c2)

let or_context_list (cl10 : context list) (cl20 : context list) : context list =
  let rec helper cl1 = match cl1 with
	| c1 :: rest ->
		let tmp1 = helper rest in
		let tmp2 = List.map (or_context c1) cl20 in
		  tmp2 @ tmp1
	| [] -> []
  in
	if Gen.is_empty cl20 then
	  []
	else helper cl10

let or_context_list cl10 cl20 =
  let pr = !print_context_list_short in
  Gen.Debug.no_2 "or_context_list" pr pr pr (fun _ _ -> or_context_list cl10 cl20) cl10 cl20

let mkFailContext msg estate conseq pid pos = {
  fc_prior_steps = estate.es_prior_steps ;
  fc_message = msg ;
  fc_current_lhs = estate;
  fc_orig_conseq = estate.es_orig_conseq;
  fc_failure_pts = (match pid with | Some s-> [s] | _ -> []);
  fc_current_conseq = conseq;
}
let mkFailCtx_in (ft:fail_type) = FailCtx ft

let mk_fail_partial_context_label (ft:fail_type) (lab:path_trace) : (partial_context) = ([(lab,ft)], [])

(* let mk_partial_context (c:context) : (partial_context) = ([], [ ([], c) ] )  *)

let mk_partial_context (c:context) (lab:path_trace) : (partial_context) = ([], [ (lab, c) ] )
let mk_failesc_context (c:context) (lab:path_trace) esc : (failesc_context) = ([], esc,[ (lab, c) ] )

let rec is_empty_esc_stack (e:esc_stack) : bool = match e with
  | [] -> false
  | (_,[])::t -> is_empty_esc_stack t
  | (_,h::t)::_ -> true

let colapse_esc_stack (e:esc_stack) : branch_ctx list = List.fold_left (fun a (_,c)-> a@c) [] e

let push_esc_elem  (e:esc_stack) (b:branch_ctx list): esc_stack =
  match b with
  | [] -> e
  | _ ->
    match e with
    | [] -> [((0,""),b)]
    | (lbl,h)::t-> (lbl,b@h)::t

let push_esc_level (e:esc_stack) lbl : esc_stack = (lbl,[])::e

let pop_esc_level (e:esc_stack) lbl : (esc_stack * branch_ctx list) = match e with
  | (lbl,s)::t -> (t,s)
  | _ -> Error.report_error {Err.error_loc = no_pos;
              Err.error_text = "error in popping exception contexts \n"}

let rec merge_success s1 s2 = match s1,s2 with
    | [],xs | xs,[] -> xs
        (* List.filter (fun (l,_) -> not (List.mem l pt_fail_list)) xs *)
    | (l1,b1)::z1,(l2,b2)::z2 ->
	if path_trace_eq l1 l2 then
	  let res = merge_success z1 z2 in
	    ((l1,or_context b1 b2)::res)
	else if path_trace_lt l1 l2 then
	  let res = merge_success z1 s2 in
	    (l1,b1)::res
	else let res = merge_success s1 z2 in
	  (l2,b2)::res

let pop_esc_level_list (l:list_failesc_context) lbl : list_failesc_context =
  List.map (fun (fl,el,sl)->
    let ne,el = pop_esc_level el lbl in
    (fl,ne, merge_success el sl)) l

let mk_list_partial_context_label (c:list_context) (lab:path_trace): (list_partial_context) =
  match c with
    | FailCtx fr ->  [( [(lab,fr)] ,[])]
    | SuccCtx cl -> List.map (fun c -> mk_partial_context c lab) cl

let mk_list_partial_context (c:list_context) : (list_partial_context) =
  mk_list_partial_context_label c []



let repl_label_list_partial_context (lab:path_trace) (cl:list_partial_context) : list_partial_context
    = List.map (fun (fl,sl) -> (fl, List.map (fun (_,c) -> (lab,c)) sl)) cl

(*context set union*)
let list_context_union_x c1 c2 =
  let simplify x = (* context_list_simplify *) x in
match c1,c2 with
  | FailCtx t1 ,FailCtx t2 -> (*FailCtx (Or_Reason (t1,t2))*)
      if ((is_cont t1) && not(is_cont t2))
      then FailCtx(t1)
      else
	if ((is_cont t2) && not(is_cont t1))
	then FailCtx(t2)
	else
	  if (is_cont t1) && (is_cont t2) then
	    FailCtx (Or_Continuation (t1,t2))
	  else
	    FailCtx (Union_Reason (t1,t2))  (* for UNION, we need to priorities MAY bug *)
	     (*FailCtx (And_Reason (t1,t2))   *)
  | FailCtx t1 ,SuccCtx t2 -> SuccCtx (simplify t2)
  | SuccCtx t1 ,FailCtx t2 -> SuccCtx (simplify t1)
  | SuccCtx t1 ,SuccCtx t2 -> SuccCtx (simplify(t1@t2))

let list_context_union c1 c2 =
  let pr = !print_list_context_short in
  Gen.Debug.no_2_opt (fun _ -> not(isFailCtx c1 ||  isFailCtx c2) )  "list_context_union"
      pr pr pr
      list_context_union_x c1 c2

let rec union_context_left c_l = match (List.length c_l) with
  | 0 ->  Err.report_error {Err.error_loc = no_pos;
              Err.error_text = "folding empty context list \n"}
  | 1 -> (List.hd c_l)
  | _ ->  List.fold_left list_context_union (List.hd c_l) (List.tl c_l)

and fold_context_left_x c_l = union_context_left c_l

 (*list_context or*)
and get_explaining t =
  match t with
  | Basic_Reason (f, fe) -> Some fe
  | Trivial_Reason _ -> None
  | Or_Reason _ -> None
  | Union_Reason _ -> None
  | And_Reason (_,_) -> None
  | ContinuationErr _ -> None
  | Or_Continuation _ -> None

and isMustFail fc = is_must_failure_ft fc

and isMayFail fc = is_may_failure_ft fc

and isMustFailCtx cl = match cl with
  | FailCtx fc -> isMustFail fc
  | SuccCtx _ -> false

and isMayFailCtx cl = match cl with
  | FailCtx fc -> isMayFail fc
  | SuccCtx _ -> false

and fold_context_left c_l =
  let pr = !print_list_context_short in
  let pr1 x = String.concat "\n" (List.map !print_list_context_short x) in
  Gen.Debug.no_1 "fold_context_left" pr1 pr fold_context_left_x c_l

(* Fail U Succ --> Succ *)
(* Fail m1 U Fail m2 --> And m1 m2 *)
(* Fail or Succ --> Fail *)
(* Fail m1 or Fail m2 --> Or m1 m2 *)
  (*list_context or*)

and or_list_context_x c1 c2 = match c1,c2 with
     | FailCtx t1 ,FailCtx t2 -> FailCtx (Or_Reason (t1,t2))
     | FailCtx t1 ,SuccCtx t2 ->
         let t = mk_not_a_failure in
        FailCtx (Or_Reason (t1,t))
     | SuccCtx t1 ,FailCtx t2 ->
         let t = mk_not_a_failure in
        FailCtx (Or_Reason (t,t2))
     | SuccCtx t1 ,SuccCtx t2 -> SuccCtx (or_context_list t1 t2)

and and_list_context c1 c2= match c1,c2 with
  | FailCtx t1 ,FailCtx t2 -> FailCtx (And_Reason (t1,t2))
  | FailCtx t1 ,SuccCtx t2 ->
         c1
  | SuccCtx t1 ,FailCtx t2 ->
      c2
  | SuccCtx t1 ,SuccCtx t2 -> SuccCtx (or_context_list t1 t2)

and or_list_context c1 c2 =
  let pr = !print_list_context_short in
  Gen.Debug.no_2 "or_list_context" pr pr pr or_list_context_x c1 c2

(* can remove redundancy here? *)
let isFailPartialCtx (fs,ss) =
  if (Gen.is_empty fs) then false else true

let isFailFailescCtx (fs,es,ss) =
  if (Gen.is_empty fs) then false else true
(* if (Gen.is_empty ss)&&(Gen.is_empty (colapse_esc_stack es)) then true else false *)

let isFailListPartialCtx cl =
  List.for_all isFailPartialCtx cl

let isFailListFailescCtx cl =
  List.for_all isFailFailescCtx cl

let isSuccessPartialCtx (fs,ss) =
if (Gen.is_empty fs) then true else false

let isSuccessFailescCtx (fs,_,_) =
if (Gen.is_empty fs) then true else false

let isSuccessListPartialCtx cl =
  cl==[] || List.exists isSuccessPartialCtx cl

let isSuccessListPartialCtx cl =
  let pr = !print_list_partial_context in
  Gen.Debug.no_1 "isSuccessListPartialCtx" pr string_of_bool isSuccessListPartialCtx cl

let isSuccessListFailescCtx cl =
  cl==[] || List.exists isSuccessFailescCtx cl

let isSuccessListFailescCtx cl =
  (* let cl = list_failesc_context_simplify cl in *)
  let pr = !print_list_failesc_context in
  Gen.Debug.no_1 "isSuccessListFailescCtx" pr string_of_bool isSuccessListFailescCtx cl

let isNonFalseListPartialCtx cl =
 List.exists (fun (_,ss)-> ((List.length ss) >0) && not (List.for_all (fun (_,c) -> isAnyFalseCtx c) ss )) cl

let isNonFalseListFailescCtx cl =
 List.exists (fun (_,el,ss)->
  let ess = (colapse_esc_stack el)@ss in
  ((List.length ess) >0) && not (List.for_all (fun (_,c) -> isAnyFalseCtx c) ess )) cl

(*********************************************************************)
let keep_failure_failesc_context ((c,es,sc): failesc_context) : failesc_context =
  (c,[],[])

let keep_failure_list_failesc_context (lc: list_failesc_context) : list_failesc_context =
  List.map ( keep_failure_failesc_context) lc

let keep_failure_partial_context ((c,es): partial_context) : partial_context =
  (c,[])

(*used by string_of_failure_list_partial_context*)
let keep_failure_list_partial_context (lc: list_partial_context) : list_partial_context =
  List.map ( keep_failure_partial_context) lc

(*********************************************************************)
(* this should be applied to merging also and be improved *)
let count_false (sl:branch_ctx list) = List.fold_left (fun cnt (_,oc) -> if (isAnyFalseCtx oc) then cnt+1 else cnt) 0 sl

(* let remove_dupl_false (sl:branch_ctx list) =  *)
(*   let nf = count_false sl in *)
(*     if (nf=0) then sl *)
(*     else let n = List.length sl in *)
(*       if (nf=n) then [List.hd(sl)] *)
(*       else (List.filter (fun (_,oc) -> not (isAnyFalseCtx oc) ) sl) *)

(***************************************************************************************)
(*remove v=v from formula*)
let remove_dupl_conj_estate (estate:entail_state) : entail_state =
  let mix_f,rest = estate.es_pure in
  let mix_f1 = Cformula.remove_dupl_conj_eq_mix_formula mix_f in
  {estate with es_pure=mix_f1,rest}

(*used by Solver.combine_list_failesc_context_and_unsat_now*)
let remove_dupl_false (sl:branch_ctx list) =
  let nl = (List.filter (fun (_,oc) -> not (isAnyFalseCtx oc) ) sl) in
  if nl==[] then
    if (sl==[]) then []
    else [List.hd(sl)]
  else nl

let isFalseBranchCtxL (ss:branch_ctx list) =
   (ss!=[]) && (List.for_all (fun (_,c) -> isAnyFalseCtx c) ss )

let remove_dupl_false (sl:branch_ctx list) =
  let pr n = string_of_int(List.length n) in
  Gen.Debug.no_1 "remove_dupl_false" pr pr remove_dupl_false sl

let remove_dupl_false_pc (fl,sl) = (fl,remove_dupl_false sl)

let remove_dupl_false_fe (fl,ec,sl) = (fl,ec,remove_dupl_false sl)

let remove_dupl_false_pc_list (fs_list:list_partial_context) =
  let ns = List.filter (fun (fl,sl) -> not(fl==[] && isFalseBranchCtxL sl)) fs_list in
  if ns==[] then [List.hd fs_list]
  else ns

(*ext*)
let remove_dupl_false_fe_list (fs_list:list_failesc_context) =
  let ns = List.filter (fun (fl,_,sl) -> not(fl==[] && isFalseBranchCtxL sl)) fs_list in
  if ns==[] then [List.hd fs_list]
  else ns

(***************************************************************************************)
let rank (t:partial_context):float = match t with
  | ( [] ,[] ) -> Err.report_error {Err.error_loc = no_pos;  Err.error_text = " rank: recieved an empty partial_context\n"}
  | ( [] , _ ) -> 1.
  | ( _  ,[] ) -> 0.
  | ( l1 , l2) ->
    let fn,sn =float (List.length(l1)), float(List.length(l2)) in
    sn /.(fn +. sn)

let list_partial_context_union (l1:list_partial_context) (l2:list_partial_context):list_partial_context = remove_dupl_false_pc_list (l1 @ l2)

let list_failesc_context_union (l1:list_failesc_context) (l2:list_failesc_context):list_failesc_context = remove_dupl_false_fe_list (l1 @ l2)

let list_partial_context_union (l1:list_partial_context) (l2:list_partial_context):list_partial_context =
  let pr x = string_of_int(List.length x) in
  Gen.Debug.no_2 "list_partial_context_union" pr pr pr list_partial_context_union l1 l2

let list_failesc_context_union (l1:list_failesc_context) (l2:list_failesc_context):list_failesc_context =
  let pr x = string_of_int(List.length x) in
  Gen.Debug.no_2 "list_failesc_context_union" pr pr pr list_failesc_context_union l1 l2


let select n l =
  if n<=0 then l
    else (Gen.BList.take n l) @(List.filter (fun c-> (rank c)==1.) (Gen.BList.drop n l))

let list_partial_context_union_n (l1:list_partial_context) (l2:list_partial_context) n :list_partial_context =
    select n  (List.sort (fun a1 a2 -> truncate (((rank a2)-.(rank a1))*.1000.)) (l1 @ l2))

let rec merge_fail (f1:branch_fail list) (f2:branch_fail list) : (branch_fail list * path_trace list) =
  match f1,f2 with
    | [],xs -> xs, (List.map (fun (p,_)->p) xs)
    | xs,[] -> xs, (List.map (fun (p,_)->p) xs)
    | (l1,b1)::z1,(l2,b2)::z2 ->
	if path_trace_eq l1 l2 then
	  let res,pt = merge_fail z1 z2 in
      (* let fe = {fe_kind = Failure_None} in *)
	  ((l1,Or_Reason (b1,b2))::res, l1::pt)
	else if path_trace_lt l1 l2 then
	  let res,pt = merge_fail z1 f2 in
	    ((l1,b1)::res, l1::pt)
	else let res,pt = merge_fail f1 z2 in
	  ((l2,b2)::res, l2::pt)

let merge_partial_context_or ((f1,s1):partial_context) ((f2,s2):partial_context) : partial_context =
  let s1 = remove_dupl_false s1 in
  let s2 = remove_dupl_false s2 in
  let (res_f,pt_fail_list) = merge_fail f1 f2 in
  let res_s = merge_success s1 s2 in
    (* print_string ("\nBefore :"^(Cprinter.summary_partial_context (f1,s1))); *)
    (* print_string ("\nBefore :"^(Cprinter.summary_partial_context (f2,s2))); *)
    (* print_string ("\nAfter :"^(Cprinter.summary_partial_context (res_f,res_s))); *)
    (res_f,res_s)

(***************************************************************************************)
(*
type: esc_stack ->
  esc_stack -> (control_path_id_strict * branch_ctx list) list

*)
let rec merge_esc f e1 e2 =
  match e1,e2 with
    | [],[] -> []
    | (l1,b1)::z1,(l2,b2)::z2 ->
          let flag = not ((fst l1)==(fst l2)) in
          (if flag then
            print_endline ("WARNING MISMATCH at merge_esc:\n"^(!print_esc_stack e1)^"\n"^(!print_esc_stack e2)))
          ; (l1,merge_success b1 b2)::(merge_esc f z1 z2)
              (* if not ((fst l1)==(fst l2)) then  *)
              (*   Err.report_error {Err.error_loc = no_pos;  Err.error_text = "malfunction in merge failesc context lbl mismatch\n"} *)
    | _ ->
          print_string ("stack e1: "^ (f e1)^":"^" stack e2: "^(f e2)^":"^"\n");
          Err.report_error {Err.error_loc = no_pos;  Err.error_text = "mismatched number in merge_esc methd \n"}

let merge_esc f e1 e2 =
  let pr1 x = "#"^(!print_esc_stack x)^"#" in
  Gen.Debug.no_2 "merge_esc" pr1 pr1 pr_no (fun _ _ -> merge_esc f e1 e2) e1 e2

(***************************************************************************************)

let merge_failesc_context_or f ((f1,e1,s1):failesc_context) ((f2,e2,s2):failesc_context) : failesc_context =
  let s1 = remove_dupl_false s1 in
  let s2 = remove_dupl_false s2 in
  let (res_f,pt_fail_list) = merge_fail f1 f2 in
  let res_s = merge_success s1 s2 in
  (* WN[((0,""),[])] : this should be added at the beginning of each proc, and not here *)
  (* let e1 = match e1 with | [] -> [((0,""),[])] | _-> e1 in *)
  (* let e2 = match e2 with | [] -> [((0,""),[])] | _-> e2 in *)
  let res_e = merge_esc f e1 e2 in
  (* print_string ("\nBefore :"^(Cprinter.summary_partial_context (f1,s1))); *)
  (* print_string ("\nBefore :"^(Cprinter.summary_partial_context (f2,s2))); *)
  (* print_string ("\nAfter :"^(Cprinter.summary_partial_context (res_f,res_s))); *)
  (res_f,res_e,res_s)

let merge_failesc_context_or f (((f1,e1,s1):failesc_context) as x1) (((f2,e2,s2):failesc_context) as x2) : failesc_context =
  let pr = !print_failesc_context in
  Gen.Debug.no_2 "merge_failesc_context_or" pr pr pr
      (fun _ _ -> merge_failesc_context_or f (x1) (x2)) x1 x2


let simple_or pc1 pc2 =  ( (fst pc1)@(fst pc2),  remove_dupl_false ((snd pc1)@(snd pc2)) )

let list_partial_context_or_naive (l1:list_partial_context) (l2:list_partial_context) : list_partial_context =
  List.concat (List.map (fun pc1-> (List.map (simple_or pc1) l2)) l1)
  (* List.concat (List.map (fun pc1-> (List.map (merge_partial_context_or pc1) l2)) l1) *)

let list_partial_context_or (l1:list_partial_context) (l2:list_partial_context) : list_partial_context =
  (* List.concat (List.map (fun pc1-> (List.map (simple_or pc1) l2)) l1) *)
  List.concat (List.map (fun pc1-> (List.map (fun pc2 -> remove_dupl_false_pc (merge_partial_context_or pc1 pc2)) l2)) l1)

let list_partial_context_or (l1:list_partial_context) (l2:list_partial_context) : list_partial_context =
  let pr x = string_of_int (List.length x) in
  Gen.Debug.loop_2_no "list_partial_context_or" pr pr pr list_partial_context_or l1 l2

let list_failesc_context_or f (l1:list_failesc_context) (l2:list_failesc_context) : list_failesc_context =
  List.concat (List.map (fun pc1-> (List.map (fun pc2 -> remove_dupl_false_fe (merge_failesc_context_or f pc1 pc2)) l2)) l1)

let list_failesc_context_or f (l1:list_failesc_context) (l2:list_failesc_context) : list_failesc_context =
  let pr = !print_list_failesc_context in
  Gen.Debug.no_2 "list_failesc_context_or"
      pr pr pr
      (fun _ _ -> list_failesc_context_or f l1 l2) l1 l2

let add_cond_label_partial_context (c_pid: control_path_id_strict) (c_opt: path_label) ((fl,sl):partial_context) =
  let sl_1 = List.map (fun (pt,ctx) -> (((c_pid,c_opt)::pt),ctx) ) sl in
    (fl,sl_1)

let add_cond_label_failesc_context (c_pid: control_path_id_strict) (c_opt: path_label) ((fl,esc,sl):failesc_context) =
  let sl_1 = List.map (fun (pt,ctx) -> (((c_pid,c_opt)::pt),ctx) ) sl in
    (fl,esc,sl_1)


let add_cond_label_list_partial_context (c_pid: control_path_id) (c_opt: path_label) (lpc:list_partial_context) =
match c_pid with
  | None -> (print_string "empty c_pid here"; lpc)
  | Some pid -> List.map (add_cond_label_partial_context pid c_opt) lpc

let add_cond_label_list_failesc_context (c_pid: control_path_id) (c_opt: path_label) (lpc:list_failesc_context) =
match c_pid with
  | None -> (print_string "empty c_pid here"; lpc)
  | Some pid -> List.map (add_cond_label_failesc_context pid c_opt) lpc

let rec build_context ctx f pos = match f with
  | Base _ | Exists _ ->
	  let es = estate_of_context ctx pos in
		Ctx ({es with es_formula = f;es_unsat_flag =false})
  | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = _}) ->
	  let c1 = build_context ctx f1 pos in
	  let c2 = build_context ctx f2 pos in
		or_context c1 c2


(* 09.05.2008 ---*)
and set_context_formula (ctx : context) (f : formula) : context = match ctx with
  | Ctx es -> begin
	  match f with
		| Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) ->
			let cf1 = set_context_formula ctx f1 in
			let cf2 = set_context_formula ctx f2 in
			  mkOCtx  cf1 cf2 pos
		| _ -> Ctx {es with es_formula = f;es_unsat_flag =false;}
	end
  | OCtx (c1, c2) ->
	  let nc1 = set_context_formula c1 f in
	  let nc2 = set_context_formula c2 f in
		mkOCtx nc1 nc2 (pos_of_formula f)

and moving_ivars_to_evars (estate:entail_state) (anode:h_formula) : entail_state =
    let arg_vars = h_fv anode in
    let (removed_ivars,remaining_ivars) = List.partition (fun v -> CP.mem v arg_vars) estate.es_ivars in
    {estate with es_evars = estate.es_evars@removed_ivars; es_ivars = remaining_ivars; }

and set_estate f (es: entail_state) : entail_state =
	f es

and set_context f (ctx : context) : context = match ctx with
  | Ctx (es) -> Ctx(set_estate f es)
  | OCtx (ctx1, ctx2) -> mkOCtx (set_context f ctx1)  (set_context f ctx2) no_pos

and set_list_context f (ctx : list_context) : list_context = match ctx with
  | FailCtx f -> ctx
  | SuccCtx l -> let nl = List.map (set_context f) l in SuccCtx nl

and estate_of_context (ctx : context) (pos : loc) = match ctx with
  | Ctx es -> es
  | _ -> Err.report_error {Err.error_loc = pos;
						   Err.error_text = "estate_of_context: disjunctive or fail context"}

and flow_formula_of_ctx (ctx : context) (pos : loc) = match ctx with
  | Ctx es -> flow_formula_of_formula es.es_formula
  | _ -> Err.report_error {Err.error_loc = pos;
						   Err.error_text = "flow_of_context: disjunctive or fail context"}

and set_flow_in_ctx_override (c:context) (f:flow_formula) :context = match c with
	| Ctx c1-> Ctx {c1 with es_formula = set_flow_in_formula_override f c1.es_formula}
	| OCtx (c1,c2) -> OCtx ((set_flow_in_ctx_override c1 f),(set_flow_in_ctx_override c2 f))

and change_flow_ctx from_fl to_fl ctx_list =
	let rec helper c = match c with
		| Ctx c -> Ctx {c with es_formula = substitute_flow_in_f to_fl from_fl c.es_formula;}
		| OCtx (c1,c2)-> OCtx ((helper c1), (helper c2)) in
	List.map helper ctx_list

and change_flow_into_ctx to_fl ctx =
  match ctx with
	| Ctx c -> Ctx {c with es_formula = substitute_flow_into_f to_fl c.es_formula;}
	| OCtx (c1,c2)-> OCtx ((change_flow_into_ctx to_fl c1), (change_flow_into_ctx to_fl c2))

and change_flow_into_ctx_list to_fl ctx_list =
	List.map (change_flow_into_ctx to_fl) ctx_list

and convert_must_failure_to_value (l:list_context) ante_flow conseq (bug_verified:bool): list_context =
  match l with
  | FailCtx ft ->
        (match (get_must_es_msg_ft ft) with
          | Some (es,msg) ->
              begin
                  match bug_verified with
                    | true ->
                        (*change flow to the flow at the beginning*)
                        let new_ctx_lst = change_flow_into_ctx_list ante_flow [Ctx es] in
                        SuccCtx new_ctx_lst
                    | false ->
                        (*update es_must_error*)
                        SuccCtx [Ctx {es with es_must_error = Some (msg,ft) } ]
              end
          | _ ->  l)
  | SuccCtx ctx_lst -> if not bug_verified then l else
        begin
            let fc_template = {
		        fc_message = "INCONSISTENCY : expected failure but success instead";
		        fc_current_lhs  =  empty_es (mkTrueFlow ()) no_pos;
		        fc_prior_steps = [];
		        fc_orig_conseq  = conseq;
		        fc_current_conseq = mkTrue (mkTrueFlow()) no_pos;
		        fc_failure_pts =  []} in
            let ft_template = (Basic_Reason (fc_template,
                                             mk_failure_must "INCONSISTENCY : expected failure but success instead" "")) in
            let new_ctx_lst = set_must_error_from_ctx ctx_lst "INCONSISTENCY : expected failure but success instead"
              ft_template in
            SuccCtx new_ctx_lst
        end

(*23.10.2008*)
and compose_context_formula_x (ctx : context) (phi : formula) (x : CP.spec_var list) flow_tr (pos : loc) : context = match ctx with
  | Ctx es -> begin
	  match phi with
		| Or ({formula_or_f1 = phi1; formula_or_f2 =  phi2; formula_or_pos = _}) ->
			let new_c1 = compose_context_formula_x ctx phi1 x flow_tr pos in
			let new_c2 = compose_context_formula_x ctx phi2 x flow_tr pos in
			let res = (mkOCtx new_c1 new_c2 pos ) in
			  res
		| _ -> Ctx {es with es_formula = compose_formula es.es_formula phi x flow_tr pos; es_unsat_flag =false;}
	end
  | OCtx (c1, c2) ->
	  let new_c1 = compose_context_formula_x c1 phi x flow_tr pos in
	  let new_c2 = compose_context_formula_x c2 phi x flow_tr pos in
	  let res = (mkOCtx new_c1 new_c2 pos) in
		res

and compose_context_formula (ctx : context) (phi : formula) (x : CP.spec_var list) flow_tr (pos : loc) : context =
  let pr1 = !print_context_short in
  let pr2 = !print_formula in
  let pr3 = !print_svl in
  Gen.Debug.no_3 "compose_context_formula" pr1 pr2 pr3 pr1 (fun _ _ _ -> compose_context_formula_x ctx phi x flow_tr pos) ctx phi x

(*TODO: expand simplify_context to normalize by flow type *)
and simplify_context (ctx:context):context =
	if (allFalseCtx ctx) then (false_ctx (mkFalseFlow) no_pos)
								else  ctx

and normalize_es (f : formula) (pos : loc) (result_is_sat:bool) (es : entail_state): context =
	Ctx {es with es_formula = normalize 3 es.es_formula f pos; es_unsat_flag = es.es_unsat_flag&&result_is_sat}

and normalize_es_combine (f : formula) (result_is_sat:bool)(pos : loc) (es : entail_state): context =
  (* let _ = print_string ("\nCformula.ml: normalize_es_combine") in *)
	Ctx {es with es_formula = normalize_combine es.es_formula f pos; es_unsat_flag = es.es_unsat_flag&&result_is_sat;}

and combine_and (f1:formula) (f2:MCP.mix_formula) :formula*bool = match f1 with
	| Or ({formula_or_f1 = o11; formula_or_f2 = o12; formula_or_pos = pos}) ->
	 print_string ("malfunction: inner or has not been converted to a CtxOr!");
      Error.report_error {
		Error.error_loc = pos;
		Error.error_text = ("malfunction: inner or has not been converted to a CtxOr!") }
	| Base ({ formula_base_pure = p;} as b) ->
			let r1,r2 = (combine_and_pure f1 p f2) in
			(Base{b with formula_base_pure = r1;}, r2)
	| Exists ({formula_exists_qvars = evars;
			   formula_exists_pure = p ;} as b) ->
			if (List.length (Gen.BList.intersect_eq (=) (MCP.mfv f2) evars))=0 then
				let r1,r2 = combine_and_pure f1 p f2 in
				(Exists {b with formula_exists_pure = r1;},r2)
				else
					let rf1 = rename_bound_vars f1 in
					(combine_and rf1 f2)

and normalize_no_rename_context_formula (ctx : context) (p : MCP.mix_formula) : context =
	let rec push_pure (f:formula):formula = match f with
		| Base b-> Base {b with formula_base_pure = MCP.merge_mems p b.formula_base_pure true;}
		| Exists b -> Exists {b with formula_exists_pure = MCP.merge_mems p b.formula_exists_pure true;}
		| Or b -> Or {
			formula_or_f1 = push_pure b.formula_or_f1;
			formula_or_f2 = push_pure b.formula_or_f2;
			formula_or_pos = b.formula_or_pos
		}
    in
    match ctx with
      | Ctx es -> Ctx {es with es_formula = push_pure es.es_formula;es_unsat_flag  =false;}
      | OCtx (c1, c2) ->
	      let nc1 = normalize_no_rename_context_formula c1 p in
	      let nc2 = normalize_no_rename_context_formula c2 p in
	      let res = mkOCtx nc1 nc2 no_pos in
		  res

(* -- 17.05.2008 *)
and normalize_clash_es (f : formula) (pos : loc) (result_is_sat:bool)(es:entail_state): context =
  (* let _ = print_string ("\nCformula.ml: normalize_clash_es") in *)
  match f with
	| Or ({formula_or_f1 = phi1; formula_or_f2 =  phi2; formula_or_pos = _}) ->
		let new_c1 = normalize_clash_es phi1 pos result_is_sat es in
		let new_c2 = normalize_clash_es phi2 pos result_is_sat es in
		let res = (mkOCtx new_c1 new_c2 pos) in
		res
	| _ -> Ctx {es with es_formula = normalize_only_clash_rename es.es_formula f pos; es_unsat_flag =es.es_unsat_flag&&result_is_sat}

(* 17.05.2008 -- *)
(***************************************************************************************)
(*add es_pure into residue*)
and formula_of_context ctx0 = match ctx0 with
  | OCtx (c1, c2) ->
	  let f1 = formula_of_context c1 in
	  let f2 = formula_of_context c2 in
		mkOr f1 f2 no_pos
  | Ctx es -> 
      let mix_f,_ = es.es_pure in
      add_mix_formula_to_formula mix_f es.es_formula

(*add es_pure into residue*)
and formula_trace_of_context ctx0 = match ctx0 with
  | OCtx (c1, c2) ->
	  let f1,trace1 = formula_trace_of_context c1 in
	  let f2,trace2  = formula_trace_of_context c2 in
	  let f = mkOr f1 f2 no_pos in
      let trace = trace1@["||OR||"]@trace2 in
      (f,trace)
  | Ctx es ->
      let mix_f,_ = es.es_pure in
      let f = add_mix_formula_to_formula mix_f es.es_formula in
      let trace = es.es_trace in
      (f,trace)

(* -- added 16.05.2008 *)
and formula_of_list_context (ctx : list_context) : formula =  match ctx with
  | FailCtx _ -> mkTrue (mkTrueFlow()) no_pos
  | SuccCtx ls -> List.fold_left (fun a c-> mkOr (formula_of_context c) a no_pos)
          (mkFalse (mkTrueFlow ()) no_pos) ls

(* 16.05.2008 -- *)
and list_formula_of_list_context (ctx : list_context) : list_formula =  match ctx with
  | FailCtx _ -> []
  | SuccCtx ls -> List.map (formula_of_context) ls

and list_formula_trace_of_list_context (ctx : list_context) : (formula*formula_trace) list =  match ctx with
  | FailCtx _ -> []
  | SuccCtx ls -> List.map (formula_trace_of_context) ls

(* filter out partial failure first *)
and list_formula_of_list_partial_context (ls : list_partial_context) : list_formula =
  let ls = List.filter (fun (f,s) -> Gen.is_empty f) ls in
  List.map (formula_of_partial_context) ls

(* assumes that all are successes, may need to filter *)
and list_formula_of_list_failesc_context (ls : list_failesc_context) : list_formula =
  let ls = List.filter (fun (f,es,s) -> Gen.is_empty f) ls in
  List.map (formula_of_failesc_context) ls

and formula_of_list_partial_context (ls : list_partial_context) : formula =
  List.fold_left (fun a c-> mkOr (formula_of_partial_context c) a no_pos)
          (mkFalse (mkTrueFlow ()) no_pos) ls

and formula_of_list_failesc_context (ls : list_failesc_context) : formula =
  List.fold_left (fun a c-> mkOr (formula_of_failesc_context c) a no_pos)
          (mkFalse (mkTrueFlow ()) no_pos) ls

(* below ignored the escaping state! *)
and formula_of_failesc_context ((_,_,sl) : failesc_context) : formula =
  List.fold_left (fun a (_,c)-> mkOr (formula_of_context c) a no_pos)
          (mkFalse (mkTrueFlow ()) no_pos) sl

and formula_of_partial_context ((fl,sl) : partial_context) : formula =
  List.fold_left (fun a (_,c)-> mkOr (formula_of_context c) a no_pos)
          (mkFalse (mkTrueFlow ()) no_pos) sl

(***************************************************************************************)
and disj_count_ctx (ctx0 : context) = match ctx0 with
  | OCtx (c1, c2) ->
	  let t1 = disj_count_ctx c1 in
	  let t2 = disj_count_ctx c2 in
		1 + t1 + t2
  | Ctx es -> disj_count es.es_formula

and count_or c = match c with
			| Ctx _ -> 1
			| OCtx (c1,c2) -> (count_or c1)+(count_or c2)

let rec set_flow_in_context_override f_f ctx = match ctx with
	| Ctx es -> Ctx {es with es_formula = (set_flow_in_formula_override f_f es.es_formula)}
	| OCtx (c1,c2) -> OCtx ((set_flow_in_context_override f_f c1),(set_flow_in_context_override f_f c2))


(*************************************SPLIT*************************************************)
and find_false_ctx ctx pos =
  match ctx with
   | FailCtx _ -> ()
   | SuccCtx ctx ->
	if (List.exists isAnyFalseCtx ctx) then
    false_ctx_line_list := Gen.BList.remove_dups_eq (=) (pos::!false_ctx_line_list) else ()

and find_false_list_failesc_ctx (ctx:list_failesc_context) pos =
    if (List.exists isAnyFalseFailescCtx ctx) then
      false_ctx_line_list := Gen.BList.remove_dups_eq (=) (pos::!false_ctx_line_list)
    else ()

and set_unsat_flag (ctx:context) (nf:bool):context = match ctx with
| OCtx(c1,c2)-> OCtx ((set_unsat_flag c1 nf),(set_unsat_flag c2 nf))
| Ctx c-> Ctx {c with es_unsat_flag = nf}

and set_es_evars (c:context)(v:Cpure.spec_var list):context = match c with
	| OCtx (c1,c2)-> OCtx ((set_es_evars c1 v),(set_es_evars c2 v))
	| Ctx e -> Ctx {e with es_evars = v}

(* start label - can be simplified *)
let get_start_label ctx = match ctx with
  | FailCtx _ -> ""
  | SuccCtx sl ->
    let rec helper c= match c with
      | Ctx e -> if (List.length e.es_path_label)==0 then "" else snd(fst (Gen.BList.list_last e.es_path_label))
      | OCtx (c1,c2) -> helper c1 in
	helper (List.hd sl)

let get_start_partial_label (ctx:list_partial_context) =
  let rec helper c= match c with
    | Ctx e -> if (List.length e.es_path_label)==0 then "" else snd(fst (Gen.BList.list_last e.es_path_label))
    | OCtx (c1,c2) -> helper c1 in
  let pc = List.hd ctx in
    if (rank pc) < 1. then ""
    else let (_,ls) = pc in
      helper (snd (List.hd ls))

(***************************************************************************************)
let rec transform_context f (c:context):context =
	match c with
	| Ctx e ->
        (f e)
	| OCtx (c1,c2) ->
        mkOCtx (transform_context f c1)(transform_context f c2) no_pos

let trans_context (c: context) (arg: 'a)
        (f: 'a -> context -> (context * 'b) option)
        (f_arg: 'a -> context -> 'a)
        (f_comb: 'b list -> 'b)
        : (context * 'b) =
  let rec trans_c (c: context) (arg: 'a) : (context * 'b) =
    let r = f arg c in
    match r with
    | Some c1 -> c1
    | None ->
        let new_arg = f_arg arg c in
        match c with
        | Ctx _ -> (c, f_comb [])
        | OCtx (c1, c2) ->
            let nc1, v1 = trans_c c1 new_arg in
            let nc2, v2 = trans_c c2 new_arg in
            (mkOCtx nc1 nc2 no_pos, f_comb [v1; v2])
  in
  trans_c c arg

let rec transform_fail_ctx f (c:fail_type) : fail_type =
  match c with
    | Trivial_Reason _ -> c
    | Basic_Reason (br,fe) -> Basic_Reason ((f br), fe)
    | ContinuationErr br -> ContinuationErr (f br)
    | Or_Reason (ft1,ft2) -> Or_Reason ((transform_fail_ctx f ft1),(transform_fail_ctx f ft2))
    | Union_Reason (ft1,ft2) -> Union_Reason ((transform_fail_ctx f ft1),(transform_fail_ctx f ft2))
    | Or_Continuation (ft1,ft2) -> Or_Continuation ((transform_fail_ctx f ft1),(transform_fail_ctx f ft2))
    | And_Reason (ft1,ft2) -> And_Reason ((transform_fail_ctx f ft1),(transform_fail_ctx f ft2))

let transform_list_context f (c:list_context):list_context =
  let f_c,f_f = f in
  match c with
    | FailCtx fc -> FailCtx (transform_fail_ctx f_f fc)
    | SuccCtx sc -> SuccCtx ((List.map (transform_context f_c)) sc)

let transform_partial_context f ((fail_c, succ_c):partial_context) : partial_context =
  let f_c,f_f = f in
  let f_res = List.map (fun (lbl, f_t) -> (lbl, transform_fail_ctx f_f f_t )) fail_c in
  let s_res = List.map (fun (lbl, ctx) -> (lbl, transform_context f_c ctx) ) succ_c in
    (f_res,s_res)


let transform_failesc_context f ((fail_c,esc_c, succ_c):failesc_context): failesc_context =
  let ff,fe,fs = f in
  let rf = List.map (fun (lbl, ctx) -> (lbl, transform_fail_ctx ff ctx) ) fail_c in
  let re = fe esc_c in
  let rs = List.map (fun (lbl, ctx) -> (lbl, transform_context fs ctx) ) succ_c in
  (rf, re,rs)

let transform_list_partial_context f (c:list_partial_context):list_partial_context =
  List.map (transform_partial_context f) c

let transform_list_failesc_context f (c:list_failesc_context): list_failesc_context =
  List.map (transform_failesc_context f) c

  (*use with care, it destroyes the information about exception stacks , preferably do not use except in check specs*)
let list_failesc_to_partial (c:list_failesc_context): list_partial_context =
	List.map (fun (fl,el,sl) -> (fl,(colapse_esc_stack el)@sl)) c


let rec fold_fail_context f (c:fail_type) =
  (*let f_br,f_or,f_and = f in*)
  match c with
    | Trivial_Reason _ -> f c []
    | Basic_Reason br -> f c []
    | ContinuationErr br -> f c []
    | Or_Reason (ft1,ft2) | Union_Reason (ft1,ft2) -> f c [(fold_fail_context f ft1);(fold_fail_context f ft2)]
    | Or_Continuation (ft1,ft2) -> f c [(fold_fail_context f ft1);(fold_fail_context f ft2)]
    | And_Reason (ft1,ft2) -> f c [(fold_fail_context f ft1);(fold_fail_context f ft2)]

(***************************************************************************************)

and pop_expl_impl_context (expvars : CP.spec_var list) (impvars : CP.spec_var list) (ctx : list_context)  : list_context =
  transform_list_context ((fun es -> Ctx{es with
				es_gen_expl_vars = Gen.BList.difference_eq CP.eq_spec_var es.es_gen_expl_vars expvars;
				es_gen_impl_vars = Gen.BList.difference_eq CP.eq_spec_var es.es_gen_impl_vars impvars;
				es_evars = Gen.BList.difference_eq (=) es.es_evars expvars;
				}), fun c->c) ctx

and push_exists_list_context (qvars : CP.spec_var list) (ctx : list_context) : list_context =
  transform_list_context ((fun es -> Ctx{es with es_formula = push_exists qvars es.es_formula}),(fun c->c)) ctx


and push_exists_list_partial_context (qvars : CP.spec_var list) (ctx : list_partial_context) : list_partial_context =
  transform_list_partial_context ((fun es -> Ctx{es with es_formula = push_exists qvars es.es_formula}),(fun c->c)) ctx

and push_exists_list_failesc_context (qvars : CP.spec_var list) (ctx : list_failesc_context) : list_failesc_context =
  transform_list_failesc_context (idf,idf,(fun es -> Ctx{es with es_formula = push_exists qvars es.es_formula})) ctx

and push_exists_context (qvars : CP.spec_var list) (ctx : context) : context =
  transform_context (fun es -> Ctx{es with es_formula = push_exists qvars es.es_formula}) ctx

and push_expl_impl_context (expvars : CP.spec_var list) (impvars : CP.spec_var list) (ctx : context)  : context =
 transform_context (fun es -> Ctx{es with
				es_gen_expl_vars = es.es_gen_expl_vars @ expvars;
				es_gen_impl_vars = es.es_gen_impl_vars @ impvars;
				(*es_evars = es.es_evars@ expvars;*)}) ctx

and impl_to_expl es vl : entail_state =
  let im, il = List.partition (fun c-> List.mem c vl) es.es_gen_impl_vars in
  {es with
    es_gen_expl_vars = es.es_gen_expl_vars @ im;
    es_gen_impl_vars = il;}


and pop_exists_context (qvars : CP.spec_var list) (ctx : list_context) : list_context =
transform_list_context ((fun es -> Ctx{es with es_formula = pop_exists qvars es.es_formula}),(fun c->c)) ctx

and pop_exists_estate (qvars : CP.spec_var list) (es : entail_state) : entail_state =
	let new_es = {es with
		es_evars = (List.filter (fun x -> not (List.exists (fun y -> (CP.eq_spec_var x y)) qvars)) es.es_evars);
		es_formula = pop_exists qvars es.es_formula
	}
	in new_es


 (* add a list of existential vars, evars, to each context in the list ctx *)
and add_exist_vars_to_ctx_list (ctx : list_context) (evars	: CP.spec_var list) : list_context =
  transform_list_context ((fun es-> Ctx{es with es_formula = (add_quantifiers evars es.es_formula)}),(fun c->c)) ctx

(***************************************************************************************)
and change_ret_flow_ctx ctx_list =
  transform_list_context ((fun es -> Ctx{es with es_formula = substitute_flow_in_f !norm_flow_int !ret_flow_int es.es_formula;})
    ,(fun c->c)) ctx_list

and change_ret_flow_partial_ctx ctx_list =
  transform_list_partial_context ((fun es -> Ctx{es with es_formula = substitute_flow_in_f !norm_flow_int !ret_flow_int es.es_formula;})
    ,(fun c->c)) ctx_list

and change_ret_flow_failesc_ctx ctx_list =
  transform_list_failesc_context
    (idf,idf,(fun es -> Ctx{es with es_formula = substitute_flow_in_f !norm_flow_int !ret_flow_int es.es_formula;})) ctx_list

(***************************************************************************************)
let add_path_id ctx (pi1,pi2) = match pi1 with
	| None -> ctx
	| Some s ->
    let fct e = Ctx{e with es_path_label = (s,pi2)::e.es_path_label} in
    transform_context fct ctx

let add_path_id_ctx_list c (pi1,pi2)  = match pi1 with
	| None -> c
	| Some s ->
    let fct e = Ctx{e with es_path_label = (s,pi2)::e.es_path_label} in
    transform_list_context (fct,(fun c-> c)) c

let add_path_id_ctx_partial_list (c:list_partial_context) (pi1,pi2) : list_partial_context =
  match pi1 with
    | None -> c
    | Some s ->
	let fct e = Ctx{e with es_path_label = (s,pi2)::e.es_path_label} in
	  transform_list_partial_context (fct,(fun c-> c)) c

let add_path_id_ctx_failesc_list (c:list_failesc_context) (pi1,pi2) : list_failesc_context =
  match pi1 with
    | None -> c
    | Some s ->
	let fct e = Ctx{e with es_path_label = (s,pi2)::e.es_path_label} in
	  transform_list_failesc_context (idf,idf,fct) c

(***************************************************************************************)
let normalize_max_renaming_list_partial_context f pos b ctx =
    if !max_renaming then transform_list_partial_context ((normalize_es f pos b),(fun c->c)) ctx
      else transform_list_partial_context ((normalize_clash_es f pos b),(fun c->c)) ctx
let normalize_max_renaming_list_failesc_context f pos b ctx =
    if !max_renaming then transform_list_failesc_context (idf,idf,(normalize_es f pos b)) ctx
      else transform_list_failesc_context (idf,idf,(normalize_clash_es f pos b)) ctx
let normalize_max_renaming_list_failesc_context f pos b ctx =
  Gen.Profiling.do_2 "normalize_max_renaming_list_failesc_context" (normalize_max_renaming_list_failesc_context f pos) b ctx

let normalize_max_renaming f pos b ctx =
  if !max_renaming then transform_list_context ((normalize_es f pos b),(fun c->c)) ctx
  else transform_list_context ((normalize_clash_es f pos b),(fun c->c)) ctx

let normalize_max_renaming_s f pos b ctx =
  if !max_renaming then transform_context (normalize_es f pos b) ctx
  else transform_context (normalize_clash_es f pos b) ctx

(***************************************************************************************)

(*
  to be used in the type-checker. After every entailment, the history of consumed nodes
  must be cleared.
*)
let clear_entailment_history_es (es :entail_state) :context =
  Ctx {(empty_es (mkTrueFlow ()) no_pos) with
	es_formula = es.es_formula;
	es_path_label = es.es_path_label;
	es_prior_steps = es.es_prior_steps;
	es_var_measures = es.es_var_measures;
	es_var_label = es.es_var_label;
	es_var_ctx_lhs = es.es_var_ctx_lhs(*;
	es_var_ctx_rhs = es.es_var_ctx_rhs;
	es_var_subst = es.es_var_subst*)
  }
let clear_entailment_history (ctx : context) : context =
  transform_context clear_entailment_history_es ctx

let clear_entailment_history_list (ctx : list_context) : list_context =
  transform_list_context (clear_entailment_history_es,(fun c->c)) ctx

let clear_entailment_history_partial_list (ctx : list_partial_context) : list_partial_context =
  transform_list_partial_context (clear_entailment_history_es,(fun c->c)) ctx

let clear_entailment_history_failesc_list (ctx : list_failesc_context) : list_failesc_context =
  transform_list_failesc_context (idf,idf,clear_entailment_history_es) ctx

let fold_partial_context_left_or (c_l:(list_partial_context list)) = match (List.length c_l) with
  | 0 ->  Err.report_error {Err.error_loc = no_pos;
              Err.error_text = "folding or empty partial context list \n"}
  | 1 -> (List.hd c_l)
  | _ -> List.fold_left (fun a c->  list_partial_context_or a c)
      (List.hd c_l) (List.tl c_l)

let fold_partial_context_left_union (c_l:(list_partial_context list)) = match (List.length c_l) with
  | 0 ->  Err.report_error {Err.error_loc = no_pos;
              Err.error_text = "folding union empty partial context list \n"}
  | 1 -> (List.hd c_l)
  | _ -> List.fold_left (fun a c->  list_partial_context_union a c) (List.hd c_l) (List.tl c_l)

(***************************************************************************************)
(* convert entail state to ctx with nf flow and quantify eres
   variable *)
(* need also a binding to catch handler's bound var *)
let conv_elim_res (cvar:typed_ident option)  (c:entail_state)
    (elim_ex_fn: context -> context) =
  let res_typ, b_rez = get_exc_result_type c.es_formula in
  let ctx = (Ctx {c with es_formula =
      (substitute_flow_into_f !norm_flow_int c.es_formula) } )  in
  match cvar with
    | None -> ctx
    | Some (cvt,cvn) ->
        if not(b_rez) then ctx
        else begin
      	  let vsv_f = formula_of_pure_N (CP.mkEqVar (CP.SpecVar (res_typ, cvn, Primed)) (CP.mkeRes res_typ) no_pos) no_pos in
      	  let ctx1 = normalize_max_renaming_s vsv_f no_pos true ctx in
      	  let ctx1 = push_exists_context [CP.mkeRes res_typ] ctx1 in
      	  if !elim_exists then elim_ex_fn ctx1 else  ctx1
        end

let conv_elim_res (cvar:typed_ident option)  (c:entail_state)
    (elim_ex_fn: context -> context) =
  let pr1 = pr_option (pr_pair string_of_typ pr_id) in
  let pr2 = !print_entail_state in
  Gen.Debug.no_2 "conv_elim_res" pr1 pr2 !print_context_short
      (fun _ _ -> conv_elim_res cvar c elim_ex_fn) cvar c

(* convert entail state to ctx with nf flow *)
let conv (c:entail_state) (nf(* :nflow *)) = (Ctx {c
with es_formula =
(substitute_flow_into_f nf c.es_formula) } )

let conv_lst (c:entail_state) (nf_lst(*: nflow list *)) =
  match nf_lst with
    | [] -> None
    | x::xs -> Some (List.fold_left (fun acc_ctx y -> mkOCtx (conv c y) acc_ctx no_pos) (conv c x)  xs)

(***************************************************************************************)
let rec splitter (c:context)
    (nf(* :nflow *)) (cvar:typed_ident option)  (elim_ex_fn: context -> context)
    (* : (context option, context option) (\* caught under nf flow, escaped from nf flow*\)   *)
    =
  let rec helper c =
    match c with
      | Ctx b ->
	      let ff =(flow_formula_of_ctx c no_pos) in
	      if (subsume_flow nf ff.formula_flow_interval) then  (Some
            (conv_elim_res cvar b elim_ex_fn),None) (* change caught item to normal flow *)
	      else if not(overlapping nf ff.formula_flow_interval) then (None,Some c)
          else (* let t_caught = intersect_flow nf
                  ff.formula_flow_interval in *)
	        let t_escape_lst = subtract_flow_list ff.formula_flow_interval nf in
            (Some (conv_elim_res cvar b elim_ex_fn), (* change caught item to normal flow *)
	        conv_lst b t_escape_lst)
      | OCtx (b1,b2) ->
	      let (r11,r12) = helper b1 in
	      let (r21,r22) = helper b2 in
	      let r1 = match (r11,r21) with
	        | None, None -> None
	        | Some c, None -> Some c
	        | None, Some c -> Some c
	        | Some c1, Some c2 -> Some (mkOCtx c1 c2 no_pos)	in
	      let r2 = match (r12,r22) with
	        | None, None -> None
	        | Some c, None -> Some c
	        | None, Some c -> Some c
	        | Some c1, Some c2 -> Some (mkOCtx c1 c2 no_pos) in
	      (r1,r2) in
  helper c

let splitter_wrapper p c nf cvar elim_ex_fn fn_esc =
	let r_caught,r_esc = splitter c nf cvar elim_ex_fn in
	match (r_esc,r_caught) with
	| None, None -> Err.report_error {Err.error_loc = no_pos;
								Err.error_text = "Split can not return both empty contexts\n"}
    | Some cl,None -> ([(p,fn_esc cl)],[])
	| None, Some c -> ([],[(p,c)])
	| Some cl,Some c ->  ([(p,fn_esc cl)],[(p,c)])

(* fn transforms context to list of partial context *)
(* fn_esc is being applied to context that escapes; for try-catch construct it may add (pid,0) label to it *)

let splitter_failesc_context  (nf(* :nflow *)) (cvar:typed_ident option) (fn_esc:context -> context)
	(elim_ex_fn: context -> context) (pl :list_failesc_context) : list_failesc_context =
   List.map (fun (fl,el,sl)->
						let r = List.map (fun (p,c)-> splitter_wrapper p c nf cvar elim_ex_fn fn_esc ) sl in
						let re,rs = List.split r in
						(fl,push_esc_elem el (List.concat re),(List.concat rs))) pl

let splitter_failesc_context  (nf(* :nflow *)) (cvar:typed_ident option) (fn_esc:context -> context)
	(elim_ex_fn: context -> context) (pl :list_failesc_context) : list_failesc_context =
  let pr = !print_list_failesc_context in
  let pr2 = !print_flow in
  Gen.Debug.no_2 "splitter_failesc_context" pr2 pr pr (fun _ _ -> splitter_failesc_context nf cvar fn_esc elim_ex_fn pl) nf pl

let splitter_partial_context  (nf(* :nflow *)) (cvar:typed_ident option)
    (fn:  path_trace -> context ->  list_partial_context) (fn_esc:context -> context)
	(elim_ex_fn: context -> context) ((fl,sl):partial_context) : list_partial_context =

  let r = List.map (fun (l,c)->
	let r1,r2 = splitter c nf cvar elim_ex_fn in
	let r1 = match r1 with
	  | Some c-> Some (fn l c )  (* CF.SuccCtx[(CF.simplify_context c)] *)
	  | None -> None in
	match (r1,r2) with
	  | None, None -> Err.report_error {Err.error_loc = no_pos;
		Err.error_text = "Split can not return both empty contexts\n"}
	  | Some cl,None -> cl
	  | None, Some c -> [mk_partial_context   (fn_esc c) l]
	  | Some cl,Some c ->  list_partial_context_or cl  [(mk_partial_context (fn_esc c) l)]
	) sl
  in
   list_partial_context_or [ (fl, []) ] (fold_partial_context_left_or r)

(***************************************************************************************)
(*used by solver.fold_op_x*)
let add_to_steps (ss:steps) (s:string) = s::ss

let get_prior_steps (c:context) =
  match c with
    | Ctx es -> es.es_prior_steps
    | OCtx _ -> print_string "Warning : OCtx with get_prior_steps \n"; [] ;;

let add_to_context (c:context) (s:string) =
  (* set_context (fun es -> {es with es_prior_steps = add_to_steps es.es_prior_steps s;}) c *)
  match c with
    | Ctx es -> Ctx {es with es_prior_steps = add_to_steps es.es_prior_steps s; }
    | OCtx _ ->
      (* let _ = print_endline (!print_context_short c) in *)
      set_context (fun es -> {es with es_prior_steps = add_to_steps es.es_prior_steps s;}) c
;;

let add_to_context_num i (c:context) (s:string) =
  let pr x = match x with Ctx _ -> "Ctx" | OCtx _ -> "OCtx" in
  Gen.Debug.no_1_num i "add_to_context" pr pr_no (fun _ -> add_to_context c s) c

let add_to_estate (es:entail_state) (s:string) =
  {es with es_prior_steps = s::es.es_prior_steps; }

(*used by solver. process_one_x*)
let overwrite_estate_with_steps (es:entail_state) (ss:steps) =
  {es with es_prior_steps = ss; }

let add_to_estate_with_steps (es:entail_state) (ss:steps) =
  {es with es_prior_steps = ss@es.es_prior_steps; }

let rec add_post post f = List.map (fun c-> match c with
  | EBase b ->
      let fec = if (List.length b.formula_ext_continuation)>0 then
                  add_post post b.formula_ext_continuation
                else
                  let (svs,pf,(i_lbl,s_lbl)) = post in
                  [EAssume (svs,pf,(fresh_formula_label s_lbl))] in
    EBase{b with formula_ext_continuation = fec}
  | ECase b ->
      let fcb1 = List.map (fun (c1,c2)->
          if (List.length c2)>0 then
          (c1,(add_post post c2))
        else
          let (svs,pf,(i_lbl,s_lbl)) = post in
          (c1,[EAssume (svs,pf,(fresh_formula_label s_lbl))])) b.formula_case_branches  in
      ECase {b with formula_case_branches  = fcb1;}
  | EAssume _ -> Err.report_error {Err.error_loc = no_pos; Err.error_text = "add post found an existing post\n"}
  | EVariance b ->
	  let fec = if (List.length b.formula_var_continuation)>0 then
                  add_post post b.formula_var_continuation
                else
                  let (svs,pf,(i_lbl,s_lbl)) = post in
                  [EAssume (svs,pf,(fresh_formula_label s_lbl))] in
		EVariance {b with formula_var_continuation = fec}
) f

(***************************************************************************************)
and add_to_aux_conseq lctx to_aux_conseq pos =
  match lctx with
    | FailCtx _ -> lctx
    | SuccCtx cl ->
      let new_cl = List.map (fun c ->
      (transform_context
    	(fun es ->
    		Ctx{es with
    		    (* add to the aux conseq *)
    		    es_aux_conseq = CP.mkAnd es.es_aux_conseq to_aux_conseq pos;
    		})) c) cl
      in SuccCtx(new_cl)

and add_to_subst lctx r_subst l_subst =
  match lctx with
    | FailCtx _ -> lctx
    | SuccCtx cl ->
      let new_cl = List.map (fun c ->
      (transform_context
    	(fun es ->
    		Ctx{es with
    		    (* add to the substitution list *)
		    es_subst = ((fst es.es_subst)@r_subst, (snd es.es_subst)@l_subst);
    		})) c) cl
      in SuccCtx(new_cl)

(***************************************************************************************)
let reset_original_es x = {x with es_formula = (Cformula.reset_original x.es_formula)}

let reset_original_list_partial_context (f : list_partial_context) : list_partial_context =
  let f1 x = Ctx (reset_original_es x) in
  transform_list_partial_context (f1,(fun c->c)) f

(***************************************************************************************)
let extr_lhs_b (es:entail_state) =
  let e = es.es_formula in
  let h1, p1, fl1, br1, t1 = split_components e in
  let b1 = { formula_base_heap = h1;
  formula_base_pure = p1;
  formula_base_type = t1;
  formula_base_branches = br1;
  formula_base_flow = fl1;
  formula_base_label = None;
  formula_base_pos = no_pos } in
  b1

(***************************************************************************************)
(** An Hoa : SECTION SIMPLIFY FORMULAE AND CONTEXT **)
let rec simplify_list_failesc_context (ctx : list_failesc_context) (bv : CP.spec_var list) =
	List.map (fun x -> simplify_failesc_context x bv) ctx

and simplify_failesc_context (ctx : failesc_context) (bv : CP.spec_var list) =
	match ctx with
		| (brfaillist,escstk,brctxlist) ->
			let newbrctxlist = List.map (fun x -> simplify_branch_context x bv) brctxlist in
				(brfaillist,escstk,newbrctxlist)

and simplify_branch_context (brctx : branch_ctx) (bv : CP.spec_var list) =
	match brctx with
		| (pathtrc, ctx) ->
			let newctx = simplify_context ctx bv in
				(pathtrc, newctx)

and simplify_context (ctx : context) (bv : CP.spec_var list) =
	match ctx with
		| Ctx ({ es_formula = esformula;
				  es_heap = esheap;
				  es_pure = espure;
				  es_evars = esevars;
				  es_ivars = esivars;
				  es_ante_evars = esanteevars;
				  es_gen_expl_vars = esgenexplvars;
				  es_gen_impl_vars = esgenimplvars;
				  es_unsat_flag = esunsatflag;
				  es_pp_subst = esppsubst;
				  es_arith_subst = esarithsubst;
				  es_success_pts = essuccesspts;
				  es_residue_pts = esresiduepts;
				  es_id = esid;
				  es_orig_ante   = esorigante;
				  es_orig_conseq = esorigconseq;
				  es_path_label = espathlabel;
				  es_prior_steps = espriorsteps;
				  es_var_measures = esvarmeasures;
				  es_var_label = esvarlabel;
				  es_var_ctx_lhs = esvarctxlhs;
				  es_var_ctx_rhs = esvarctxrhs;
				  es_var_subst = esvarsubst;
				  es_rhs_eqset = esrhseqset;
				  es_cont = escont;
				  es_crt_holes = escrtholes;
				  es_hole_stk = esholestk;
				  es_aux_xpure_1 = esauxxpure1;
				  es_subst = essubst;
				  es_aux_conseq = esauxconseq;
					} as es) ->
						let sesfml = simplify_formula esformula bv in
							Ctx { es with es_formula = sesfml }
		| OCtx (ctx1, ctx2) ->
					OCtx (simplify_context ctx1 bv, simplify_context ctx2 bv)

