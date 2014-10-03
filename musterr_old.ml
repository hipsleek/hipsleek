(*
 1. this file provides interfaces and implementations for
   - must/may errors
2. IMPORTANT (AVOID REDUNDANT): before implement new method, please go through
  interfaces and UNUSED module to check whether your need is there.
*)

open Globals
open Gen
open Exc.GTable
open Perm
open Cformula


module Err = Error
module CP = Cpure
module MCP = Mcpure

(*
module ME_COM=
struct

end;;
(*******************************************************************************)
open ME_COM
*)
(************USED BY LOCAL MODULES*****************************************)
module EMLocal=
 struct
(*local used only, pretty printer, pointers of CPrinter*)
let print_list_context_short = ref(fun (c:list_context) -> "printer not initialized")
let print_context_list_short = ref(fun (c:context list) -> "printer not initialized")
let print_context_short = ref(fun (c:context) -> "printer not initialized")
let print_entail_state = ref(fun (c: entail_state) -> "printer not initialized")
let print_list_partial_context = ref(fun (c:list_partial_context) -> "printer not initialized")
let print_list_failesc_context = ref(fun (c:list_failesc_context) -> "printer not initialized")
(* let print_flow = ref(fun (c:nflow) -> "printer not initialized") *)
let print_esc_stack = ref(fun (c:esc_stack) -> "printer not initialized")
let print_failesc_context = ref(fun (c:failesc_context) -> "printer not initialized")
let print_failure_kind_full = ref(fun (c:failure_kind) -> "printer not initialized")
let print_fail_type = ref(fun (c:fail_type) -> "printer not initialized")


(*********************************************************************************)
(*must/may*)
   let is_cont t =
     match t with
       | ContinuationErr _ -> true
       | Or_Continuation _ -> true
       | _ -> false

  let rec transform_fail_ctx f (c:fail_type) : fail_type =
    match c with
      | Trivial_Reason _ -> c
      | Basic_Reason (br,fe) -> Basic_Reason ((f br), fe)
      | ContinuationErr br -> ContinuationErr (f br)
      | Or_Reason (ft1,ft2) -> Or_Reason ((transform_fail_ctx f ft1),(transform_fail_ctx f ft2))
      | Union_Reason (ft1,ft2) -> Union_Reason ((transform_fail_ctx f ft1),(transform_fail_ctx f ft2))
      | Or_Continuation (ft1,ft2) -> Or_Continuation ((transform_fail_ctx f ft1),(transform_fail_ctx f ft2))
      | And_Reason (ft1,ft2) -> And_Reason ((transform_fail_ctx f ft1),(transform_fail_ctx f ft2))

 end;;
open EMLocal

(********************INTERFACE of MUST/MAY*********************)
module type IMUST_MAY =
 sig
   (*list context, contect + must/may operators*)
   val or_list_context: list_context -> list_context -> list_context
   val and_list_context: list_context -> list_context -> list_context
   val union_list_context: list_context -> list_context -> list_context
     (*Use union_list_context to compose*)
   val fold_context_left: list_context list -> list_context

(*construction/destruction*)
   val mkFailCtx_in: fail_type -> list_context
   val mkFailContext: string -> entail_state ->
     Cformula.formula -> Globals.formula_label option -> (*pos: can remove*) 'a -> fail_context
(*msg -> failure*)
   val mk_failure_must_raw: string -> failure_kind
   val mk_failure_may_raw: string -> failure_kind
(*msg -> fail_type -> failure*)
   val mk_failure_must: string -> string -> fail_explaining
   val mk_failure_may: string -> string -> fail_explaining

   val mkAnd_Reason: fail_type option -> fail_type option -> fail_type option

(*get*)
   val get_must_error_from_ctx: context list -> string option
   val get_must_failure: list_context -> string option
   val get_may_failure: list_context -> string option
(*SLEEK: check failure ctx+ extract err msg*)
(*todo: HIP?*)
   val isFailCtx_gen: list_context -> bool

(*transform*)
   val convert_must_failure_to_value_orig: list_context -> list_context
   val convert_must_failure_4_failesc_context: string -> failesc_context -> failesc_context
   val convert_must_failure_4_list_failesc_context: string -> list_failesc_context -> list_failesc_context
   val invert_outcome: list_context -> list_context

(*LOCAL USED ONLY*)
   val is_must_failure_fe: fail_explaining -> bool
   val get_failure_ft: fail_type -> failure_kind
   val get_may_failure_ft: fail_type -> string option
   val get_must_es_msg_ft: fail_type -> (entail_state * string) option
 end;;
(******************END of INTERFACE of MUST/MAY******************)

(********************IMPLEMENTATION of MUST/MAY*********************)
module MME: IMUST_MAY=
struct
  (*list context, contect + must/may operators*)
(* Fail U Succ --> Succ *)
(* Fail m1 U Fail m2 --> And m1 m2 *)
(* Fail or Succ --> Fail *)
(* Fail m1 or Fail m2 --> Or m1 m2 *)
  (*list_context or*)
  let rec or_list_context_x c1 c2 = match c1,c2 with
    | FailCtx t1 ,FailCtx t2 -> FailCtx (Or_Reason (t1,t2))
    | FailCtx t1 ,SuccCtx t2 ->
        let t = mk_not_a_failure in
        FailCtx (Or_Reason (t1,t))
    | SuccCtx t1 ,FailCtx t2 ->
        let t = mk_not_a_failure in
        FailCtx (Or_Reason (t,t2))
    | SuccCtx t1 ,SuccCtx t2 -> SuccCtx (mk_or_2list_of_context t1 t2)

    and mk_not_a_failure =
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

(*l1 \/ l2 = {OCtx(c1, c2) | c1 \in l1 and c2 \in ;2 } *)
  and mk_or_2list_of_context_x (cl10 : context list) (cl20 : context list) : context list =
    let rec helper cl1 = match cl1 with
	  | c1 :: rest ->
		  let tmp1 = helper rest in
		  let tmp2 = List.map (fun c2 -> mk_OCtx c1 c2 no_pos) cl20 in
		  tmp2 @ tmp1
	  | [] -> []
    in
	if Gen.is_empty cl20 then
	  []
	else helper cl10

  and mk_or_2list_of_context cl10 cl20 =
    let pr = !print_context_list_short in
    Debug.no_2 "or_context_list" pr pr pr (fun _ _ -> mk_or_2list_of_context_x cl10 cl20) cl10 cl20

  and or_list_context c1 c2 =
    let pr = !print_list_context_short in
    Debug.no_2 "or_list_context" pr pr pr or_list_context_x c1 c2

  (*todo: sth is wrong here, why mk_or_2list_of_context?*)
  let and_list_context c1 c2= match c1,c2 with
    | FailCtx t1 ,FailCtx t2 -> FailCtx (And_Reason (t1,t2))
    | FailCtx t1 ,SuccCtx t2 -> c1
    | SuccCtx t1 ,FailCtx t2 -> c2
    | SuccCtx t1 ,SuccCtx t2 -> SuccCtx (mk_or_2list_of_context t1 t2)

(*context set union*)
  let rec union_list_context_x c1 c2 =
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

  and union_list_context c1 c2 =
    let pr = !print_list_context_short in
    Debug.no_2_opt (fun _ -> not(isFailCtx c1 ||  isFailCtx c2) )  "union_list_context"
        pr pr pr
        union_list_context_x c1 c2

  and is_cont t =
    match t with
      | ContinuationErr _ -> true
      | Or_Continuation _ -> true
      | _ -> false

  let rec fold_context_left_x c_l = union_context_left c_l

  and fold_context_left c_l =
    let pr = !print_list_context_short in
    let pr1 x = String.concat "\n" (List.map !print_list_context_short x) in
    Debug.no_1 "fold_context_left" pr1 pr fold_context_left_x c_l

  and union_context_left c_l = match (List.length c_l) with
    | 0 ->  Err.report_error {Err.error_loc = no_pos;
                              Err.error_text = "folding empty context list \n"}
    | 1 -> (List.hd c_l)
    | _ ->  List.fold_left union_list_context (List.hd c_l) (List.tl c_l)
(*construction/destruction*)
  let mkFailCtx_in (ft:fail_type) = FailCtx ft

let mkFailContext msg estate conseq pid pos = {
      fc_prior_steps = estate.es_prior_steps ;
      fc_message = msg ;
      fc_current_lhs = estate;
      fc_orig_conseq = estate.es_orig_conseq;
      fc_failure_pts = (match pid with | Some s-> [s] | _ -> []);
      fc_current_conseq = conseq;
  }

(*not in used*)
  let mk_failure_bot_raw msg = Failure_Bot msg

  let mk_failure_must_raw msg = Failure_Must msg

  let mk_failure_may_raw msg = Failure_May msg

(*not in used*)
  let mk_failure_bot msg = {fe_kind = mk_failure_bot_raw msg;fe_name = "" ;fe_locs=[]}

  let mk_failure_may msg name = {fe_kind = Failure_May msg;fe_name = name ;fe_locs=[]}

  let mk_failure_must msg name = {fe_kind = mk_failure_must_raw msg;fe_name = name ;fe_locs=[]}

(*will be local when check_must_may move here*)
  let mkAnd_Reason (ft1:fail_type option) (ft2:fail_type option): fail_type option=
    match ft1, ft2 with
      | None, ft2 -> ft2
      | _ , None -> ft1
      | Some ft1, Some ft2 -> Some (And_Reason (ft1, ft2))

(*get*)
  let get_must_error_from_ctx cs =
    match cs with
      | [Ctx es] -> (match es.es_must_error with
            | None -> None
            | Some (msg,_) -> Some msg)
      | _ -> None

  let rec get_must_failure (ft:list_context) =
    match ft with
      | FailCtx f -> get_must_failure_ft f
   	  | SuccCtx cs -> get_must_error_from_ctx cs

  and get_failure_ft (ft:fail_type) : (failure_kind) =
    fst (get_failure_es_ft ft)

  and get_must_failure_ft f =
    match (get_failure_ft f) with
      | Failure_Must m -> Some m
      | _ -> None

  and get_failure_es_ft (ft:fail_type) : (failure_kind * (entail_state option)) =
    let pr1 (m, e) = let tmp = (!print_failure_kind_full m) in
                     match e with
                       | None -> tmp
                       | Some f -> tmp ^ "\n" ^ (!print_entail_state f)
    in
    Debug.no_1 "get_failure_es_ft" !print_fail_type pr1 (fun x -> get_failure_es_ft_x x) ft

  and get_failure_es_ft_x (ft:fail_type) : (failure_kind * (entail_state option)) =
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

  and is_must_failure_fe (f:fail_explaining) =
    match f.fe_kind with
      | Failure_Must _ -> true
      | _ -> false

  and get_failure_fe (f:fail_explaining) = f.fe_kind

(*gen_land*)
  and gen_land (m1,n1,e1) (m2,n2,e2) = match m1,m2 with
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
  and gen_rand_x (m1,n1,e1) (m2,n2,e2) = match m1,m2 with
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

  and gen_rand (m1,n1,e1) (m2,n2,e2)=
    let pr (m, n , e) = (!print_failure_kind_full m) ^ ", name: " ^ n in
    let pr1 (m, n, e) =
      let tmp = (!print_failure_kind_full m) ^ ", name: " ^ n in
      match e with
        | None -> tmp
        | Some f -> tmp ^ "\n" ^ (!print_entail_state f)
    in
    Debug.no_2 "gen_rand" pr pr pr1 (fun x y -> gen_rand_x x y) (m1,n1,e1) (m2,n2,e2)

(* state to be refined to accurate one for must-bug *)
(*gen_lor*)
  and gen_lor_x (m1,n1,e1) (m2,n2,e2) : (failure_kind * string * (entail_state option)) = match m1,m2 with
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

  and gen_lor (m1,n1,e1) (m2,n2,e2)=
    let pr (m, n , e) = (!print_failure_kind_full m) ^ ", name: " ^ n in
    let pr1 (m, n, e) =
      let tmp = (!print_failure_kind_full m) ^ ", name: " ^ n in
      match e with
        | None -> tmp
        | Some f -> tmp ^ "\n" ^ (!print_entail_state f)
    in
    Debug.no_2 "gen_lor" pr pr pr1 (fun x y -> gen_lor_x x y) (m1,n1,e1) (m2,n2,e2)

(*gen_ror*)
(*
  - m: failure_kind (must/may/bot/valid)
  - n: name of failure (logical/separation entailment). should reduce separation entailment
  - e: current entailment
*)
  and gen_ror_x (m1, n1, e1) (m2, n2, e2) = match m1,m2 with
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

  and gen_ror (m1,n1,e1) (m2,n2,e2)=
    let pr (m, n , e) = (!print_failure_kind_full m) ^ ", name: " ^ n in
    let pr1 (m, n, e) =
      let tmp = (!print_failure_kind_full m) ^ ", name: " ^ n in
      match e with
        | None -> tmp
        | Some f -> tmp ^ "\n" ^ (!print_entail_state f)
    in
    Debug.no_2 "gen_ror" pr pr pr1 (fun x y -> gen_ror_x x y) (m1,n1,e1) (m2,n2,e2)

  let rec get_may_failure (f:list_context) =
    match f with
      | FailCtx ft ->
          let m = (get_may_failure_ft ft) in
          (match m with
            | Some s -> m
            | None ->
                let _ = print_flush (!print_list_context_short f)
                in report_error no_pos "Should be a may failure here")
      | _ -> None

  and get_may_failure_ft f =
    match (get_failure_ft f) with
      | Failure_Must m -> Some ("must:"^m)
      | Failure_May m -> Some (m)
      | Failure_Valid -> Some ("Failure_Valid")
      | Failure_Bot m -> Some ("Failure_Bot"^m)

(*SLEEK: check failure ctx+ extract err msg*)
(*todo: HIP?*)
  let isFailCtx_gen cl = match cl with
	| FailCtx _ -> true
	| SuccCtx cs -> (get_must_error_from_ctx cs) !=None
 (* | _ -> false *)

(*transform*)
  let rec convert_must_failure_to_value_orig_x (l:list_context) : list_context =
    match l with
      | FailCtx ft ->
          (match (convert_must_failure_4_fail_type "" ft) with
            | Some ctx -> SuccCtx [ctx]
            | None -> l)
      | SuccCtx _ -> l

  and convert_must_failure_to_value_orig (l:list_context): list_context =
     let pr = !print_list_context_short in
     Debug.no_1 "convert_must_failure_to_value_orig" pr pr
         (fun _ -> convert_must_failure_to_value_orig_x l) l

  and convert_must_failure_4_fail_type  (s:string) (ft:fail_type) : context option =
    match (get_must_es_msg_ft ft) with
      | Some (es,msg) -> Some (Ctx {es with es_must_error = Some (s^msg,ft) } )
      | _ ->  None

  and get_must_es_msg_ft ft =
    let msg,es = get_failure_es_ft ft in
    match es,msg with
      | Some es, Failure_Must msg -> Some (es,msg)
      | None, Failure_Must msg -> Some (empty_es ( mkTrueFlow ()) no_pos,msg) (*may be Trivial fail*)
      | _, _ -> None

  let rec convert_must_failure_4_failesc_context (s:string) ((fl,e,bl):failesc_context) : failesc_context =
    let (fme,fl) = convert_must_failure_4_branch_fail_list s fl in
    (fl,e,add_must_err_to_pc s fme bl)

  and add_must_err_to_pc (s:string) (fme:branch_ctx list) (e:branch_ctx list) : branch_ctx list =
    fme @ e

  and convert_must_failure_4_branch_fail_list  (s:string) (fl:branch_fail list) : (branch_ctx list * branch_fail list) =
    List.fold_left (fun (must_l,may_l) bf ->
        match (convert_must_failure_4_branch_type s bf) with
          | Some r -> (r::must_l, may_l)
          | None -> (must_l, bf::may_l)) ([],[]) fl

  and convert_must_failure_4_branch_type  (s:string) ((pt,ft):branch_fail) : branch_ctx option =
    match (convert_must_failure_4_fail_type s ft) with
      | Some b -> Some (pt,b)
      | None -> None

  let convert_must_failure_4_list_failesc_context (s:string) (l:list_failesc_context) : list_failesc_context =
    List.map (convert_must_failure_4_failesc_context s) l

  let rec invert_outcome (l:list_context) : list_context =
  match l with
  | FailCtx ft -> l
  | SuccCtx ls -> SuccCtx (invert ls)

  and invert ls =
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

end;;
(******************END of IMPLEMENTATION of MUST/MAY******************)
open MME

(*********UNUSED MODULE: All methods are obsolete and should be removed******************)
module MUSTERR_UNUSED=
 struct
(*********************************************************************************)
(*unsed must/may*)
   let rec get_bot_status_ft f =
     match (get_failure_ft f) with
       | Failure_Bot m -> Some m
       | _ -> None

   and get_bot_status (ft:list_context) =
     match ft with
       | FailCtx f -> get_bot_status_ft f
	   | SuccCtx cs -> get_bot_status_from_ctx cs

   and get_bot_status_from_ctx cs=
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

   let comb_must m1 m2 = "["^m1^","^m2^"]"

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

   let get_may_failure_fe (f:fail_explaining) =
     match f.fe_kind with
       | Failure_May m | Failure_Must m -> Some m 
       | Failure_Valid -> Some "proven valid here"
       | Failure_Bot _ -> None

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

   let rec get_explaining t =
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
(* unused
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
		        fc_current_lhs  =  ES.empty_es (mkTrueFlow ()) no_pos;
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
*)
   let rec fold_fail_context f (c:fail_type) =
  (*let f_br,f_or,f_and = f in*)
     match c with
       | Trivial_Reason _ -> f c []
       | Basic_Reason br -> f c []
       | ContinuationErr br -> f c []
       | Or_Reason (ft1,ft2) | Union_Reason (ft1,ft2) -> f c [(fold_fail_context f ft1);(fold_fail_context f ft2)]
       | Or_Continuation (ft1,ft2) -> f c [(fold_fail_context f ft1);(fold_fail_context f ft2)]
       | And_Reason (ft1,ft2) -> f c [(fold_fail_context f ft1);(fold_fail_context f ft2)]
 end;;
(********************END of IMPLEMENTATION of UNSED*********************)
