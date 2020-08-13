#include "xdebug.cppo"
open VarGen
open Globals
open VarGen
open Others
open GlobProver
open Stat_global
open Gen.Basic
open Printf
open Cprinter

module CP = Cpure
module CF = Cformula

type proof_type =
  | PT_IMPLY_TOP of (CP.formula * CP.formula)
  | PT_IMPLY of (CP.formula * CP.formula)
  | PT_SAT  of CP.formula
  | PT_SIMPLIFY of CP.formula
  | PT_HULL of CP.formula
  | PT_PAIRWISE of CP.formula

type proof_res =
  | PR_BOOL of bool
  | PR_FORMULA of CP.formula
  | PR_exception (* translation problem? *)
  | PR_timeout (* include timeout? *)

(* superceded by Others.last_tp_used *)
(* let called_prover = ref "" *)

type proof_log = {
  log_id : int; (* TODO: Should change to integer for performance *)
  (* log_other_properties : string list; (\* TODO: Should change to integer for performance *\) *)
  log_loc : loc;
  log_sleek_no : int;
  log_proving_kind : Others.proving_kind;
  log_prover : Others.tp_type;
  log_type : proof_type;
  log_proof_string : string;
  log_proof_result : string;
  log_time : float;
  log_timeout : bool;
  log_cache : bool;
  log_res : proof_res;
}

(* type sleek_proving_kind = *)
(* 	| POST *)
(* 	| PRE *)
(* 	| BINDING *)
(*  | ASSERTION *)

type sleek_log_entry = {
  sleek_proving_id :int;
  sleek_src_no : int;
  sleek_parent_no : int;
  sleek_proving_pos: loc;
  sleek_proving_classic_flag: bool;
  sleek_proving_avoid: bool;
  sleek_proving_caller : string;
  sleek_proving_aob: string;
  sleek_proving_hec: int;
  sleek_proving_kind : string;
  (* sleek_proving_kind; *)
  sleek_proving_ante: CF.formula;
  sleek_proving_conseq: CF.formula;
  sleek_proving_c_heap: CF.h_formula;
  sleek_proving_evars: CP.spec_var list;
  sleek_proving_impl_vars: CP.spec_var list;
  sleek_proving_infer_vars: CP.spec_var list;
  sleek_proving_infer_type: infer_type option;
  sleek_proving_tntrel_ass: Tid.tntrel list;
  sleek_proving_hprel_ass: CF.hprel list;
  sleek_proving_rel_ass: CP.infer_rel_type list;
  (* TODO:WN:HVar *)
  sleek_ho_vars_map: ( CP.spec_var * CF.formula) list; (* map: HVar -> its formula *)
  sleek_time : float;
  sleek_timeout : bool;
  sleek_proving_res : CF.list_context option;
}

(* let string_of_sleek_proving_kind t= *)
(* match t with *)
(*   | POST -> "POST" *)
(*   | PRE -> "PRE" *)
(*   | BINDING -> "BINDING" *)
(*   | ASSERTION -> "ASSERTION" *)

let num_sat = ref 1

let string_of_sleek_proving_kind ()
  = proving_kind#string_of

let string_of_top_proving_kind ()
  = string_of_proving_kind (proving_kind#top_no_exc)

let string_of_impt_proving_kind ()
  = string_of_proving_kind (Others.find_impt_proving_kind ())


let string_of_log_type lt =
  match lt with
  |PT_IMPLY_TOP (ante, conseq) ->
    "ImplyTOP: ante:" ^(string_of_pure_formula ante) ^"\n\t     conseqTOP: "
    ^(string_of_pure_formula conseq)
  |PT_IMPLY (ante, conseq) ->
    let clean_str =
      if !print_clean_flag then
        let ante,conseq = CleanUp.cleanUpPureFormulas ante conseq in
        "\n   clean ante:"^(Cprinter.string_of_pure_formula ante)^
        "\n\t clean conseq:"^(Cprinter.string_of_pure_formula conseq)
      else "" in
    "Imply: ante:" ^(string_of_pure_formula ante) ^"\n\t     conseq: " ^(string_of_pure_formula conseq)^clean_str
  |PT_SAT f->
    let clean_str =
      if !print_clean_flag then
        "\n clean Sat: "^(Cprinter.string_of_pure_formula (fst (CleanUp.cleanUpPureFormulas f (Cpure.mkTrue no_pos))))
      else "" in
    "Sat: "^(string_of_pure_formula f)^clean_str
  |PT_SIMPLIFY f ->
    let clean_str =
      if !print_clean_flag then
        "\n clean Simplify: "^(Cprinter.string_of_pure_formula (fst (CleanUp.cleanUpPureFormulas f (Cpure.mkTrue no_pos))))
      else "" in
    "Simplify: "^(string_of_pure_formula f)^clean_str
  |PT_HULL f ->
    let clean_str =
      if !print_clean_flag then
        "\n clean Hull: "^(Cprinter.string_of_pure_formula (fst (CleanUp.cleanUpPureFormulas f (Cpure.mkTrue no_pos))))
      else "" in
    "Hull: "^(string_of_pure_formula f)^clean_str
  |PT_PAIRWISE f ->
    let clean_str =
      if !print_clean_flag then
        "\n clean PairWise: "^(Cprinter.string_of_pure_formula (fst (CleanUp.cleanUpPureFormulas f (Cpure.mkTrue no_pos))))
      else "" in
    "PairWise: "^(string_of_pure_formula f)^clean_str

let last_proof_command = new store (PT_SAT (CP.mkTrue no_pos)) (string_of_log_type )

let pr_f = Cprinter.string_of_formula

(* let last_sleek_command = new store None (pr_option (pr_pair pr_f pr_f)) *)

let string_of_log_res lt r =
  match r with
  |PR_BOOL b ->
    (match lt with
     | PT_SAT(_) -> if b then "SAT" else "UNSAT"
     | _ -> string_of_bool b )
  |PR_FORMULA f ->
    let clean_str =
      if !print_clean_flag then
        "\n clean res: "^(Cprinter.string_of_pure_formula (fst (CleanUp.cleanUpPureFormulas f (Cpure.mkTrue no_pos))))
      else "" in
    (string_of_pure_formula f)^clean_str
  |PR_exception -> "exception thrown"
  |PR_timeout -> "timeout detected"

let pr_proof_log_entry e =
  fmt_open_box 1;
  fmt_string ("\n id: " ^ (string_of_int e.log_id)^"<"^(string_of_int e.log_sleek_no));
  if e.log_cache then fmt_string ("; prover : CACHED ")
  else fmt_string ("; prover: " ^ (string_of_prover e.log_prover));
  let x = if e.log_timeout then "(TIMEOUT)" else "" in
  if e.log_time > !time_limit_large then fmt_string ("; TIME: "^ (string_of_float e.log_time)^x);
  fmt_string ("; loc: "^(string_of_loc e.log_loc));
  fmt_string ("; kind: "^(Others.string_of_proving_kind e.log_proving_kind));
  (* fmt_string ("; "^((pr_list pr_id) e.log_other_properties)); *)
  if !Globals.log_proof_details then fmt_string ("\n raw proof:" ^ e.log_proof_string);
  if !Globals.log_proof_details then fmt_string (" raw result:" ^ e.log_proof_result);
  fmt_string ("\n " ^ (string_of_log_type e.log_type));
  fmt_string ("\n res: "^(string_of_log_res e.log_type e.log_res));
  fmt_string ("\n --------------------");
  fmt_close()

let string_of_proof_log_entry e= Cprinter.poly_string_of_pr pr_proof_log_entry e

let pr_sleek_log_entry e =
  fmt_open_box 1;
  fmt_string("\n");
  (if (e.sleek_proving_avoid) then
     fmt_string ("HIDE! ")
  );
  let src = e.sleek_src_no in
  let par_id = e.sleek_parent_no in
  let rest = if src!=3 then " src:"^(string_of_int src) else "" in
  let rest = if par_id>=(0) then "<:"^(string_of_int par_id)^rest else rest in
  fmt_string ("id: " ^ (string_of_int e.sleek_proving_id)^rest);
  fmt_string ("; caller: " ^ (e.sleek_proving_caller));
  fmt_string ("; line: " ^ (Globals.line_number_of_pos e.sleek_proving_pos)) ;
  let x = if e.sleek_timeout then "(TIMEOUT)" else "" in
  if e.sleek_time > 0.5 then fmt_string ("; TIME: " ^ (string_of_float e.sleek_time)^x);
  fmt_string ("; classic: " ^ (string_of_bool e.sleek_proving_classic_flag)) ;
  fmt_string ("; kind: " ^ (e.sleek_proving_kind)) ;
  fmt_string ("; hec_num: " ^ (string_of_int e.sleek_proving_hec)) ;
  fmt_string ("; evars: " ^ (Cprinter.string_of_spec_var_list e.sleek_proving_evars)) ;
  fmt_string ("; impl_vars: " ^ (Cprinter.string_of_spec_var_list e.sleek_proving_impl_vars)) ;
  fmt_string ("; infer_vars: " ^ (Cprinter.string_of_infer_list (opt_to_list e.sleek_proving_infer_type) e.sleek_proving_infer_vars)) ;
  fmt_string ("; c_heap:" ^ (Cprinter.string_of_h_formula e.sleek_proving_c_heap)) ;
  fmt_string ("; others: " ^ (e.sleek_proving_aob));
  fmt_string "\n checkentail";
  let f = Cfout.tidy_print e.sleek_proving_ante in
  fmt_string (Cprinter.string_of_formula f);
  (* if (!Globals.print_en_tidy) *)
  (* then fmt_string (Cprinter.string_of_formula (Cfout.shorten_formula e.sleek_proving_ante)) *)
  (* else fmt_string (Cprinter.string_of_formula e.sleek_proving_ante); *)
  fmt_string "\n |- ";
  (* WN -> Long : won't we get inconsistent vars *)
  let f = Cfout.tidy_print e.sleek_proving_conseq in
  fmt_string (Cprinter.string_of_formula f);
  (* if (!Globals.print_en_tidy) *)
  (* then fmt_string (Cprinter.string_of_formula (Cfout.shorten_formula e.sleek_proving_conseq)) *)
  (* else fmt_string (Cprinter.string_of_formula e.sleek_proving_conseq); *)
  fmt_string ". \n";
  (if !print_clean_flag then
     let ante,conseq = CleanUp.cleanUpFormulas e.sleek_proving_ante e.sleek_proving_conseq in
     fmt_string ("\n clean checkentail"^(Cprinter.string_of_formula ante)^"\n |- "^(Cprinter.string_of_formula conseq)^". \n")
   else ());
  (match e.sleek_proving_tntrel_ass with
   | [] -> ()
   | _  -> let pr = pr_list_ln string_of_tntrel in
     fmt_string ("tntrel_ass: " ^ (pr e.sleek_proving_tntrel_ass)^"\n")
  );
  (match e.sleek_proving_hprel_ass with
   | [] -> ()
   | _  -> let pr = pr_list_ln Cprinter.string_of_hprel_short in
     fmt_string ("hprel_ass: " ^ (pr e.sleek_proving_hprel_ass)^"\n")
  );
  (match e.sleek_proving_rel_ass with
   | [] -> ()
   | _  -> let pr = pr_list_ln CP.string_of_infer_rel in
     fmt_string ("pure rel_ass: " ^ (pr e.sleek_proving_rel_ass)^"\n")
  );
  (match e.sleek_ho_vars_map with
   | [] -> fmt_string ("ho_vars: nothing?\n");
   | _  -> let pr = pr_list_ln (pr_pair CP.string_of_spec_var Cprinter.string_of_formula) in
     fmt_string ("ho_vars: " ^ (pr e.sleek_ho_vars_map)^"\n")
  );
  match e.sleek_proving_res with
  | Some r -> fmt_string  ("res: " ^ (Cprinter.string_of_list_context_short r))
  | None -> fmt_string ("res : EXCEPTION");
    fmt_close()

let string_of_sleek_log_entry e = Cprinter.poly_string_of_pr pr_sleek_log_entry e

let sleek_tidy_formula f =
  (* if (!Globals.print_en_tidy)                                              *)
  (* then fmt_string (Cprinter.sleek_of_formula (Cformula.shorten_formula f)) *)
  (* else fmt_string (Cprinter.sleek_of_formula f)                            *)
  fmt_string (Cprinter.sleek_of_formula f)

let slk_sleek_log_entry prog e =
  let frm, expected = match e.sleek_proving_res with
    | None -> None, "Fail"
    | Some res ->
      let r = CF.formula_of_list_context res in
      let hole_matching, expected = match res with
        | CF.FailCtx _ -> [], "Fail"
        | CF.SuccCtx ls -> (List.concat (List.map CF.collect_hole ls)), "Valid"
      in
      let hole_matching = List.map (fun (h, i) -> (i, h)) hole_matching in
      Some (CF.restore_hole_formula r hole_matching), expected
  in
  let conseq =
    if !Globals.sleek_gen_vc then e.sleek_proving_conseq
    else (* !Globals.sleek_gen_vc_exact *)
      match frm with
      | None -> e.sleek_proving_conseq
      | Some r ->
        let conseq = e.sleek_proving_conseq in
        let comb_conseq = CF.mkStar_combine conseq r
            CF.Flow_combine (CF.pos_of_formula conseq) in
        let ante_fv = CF.fv e.sleek_proving_ante in
        (* let cons_fv = CF.fv conseq in *)
        let comb_cons_fv = CF.fv comb_conseq in
        let ex_vars = Gen.BList.difference_eq CP.eq_spec_var comb_cons_fv ante_fv in
        (* let ex_vars = Gen.BList.difference_eq CP.eq_spec_var ex_vars cons_fv in *)
        CF.push_exists ex_vars comb_conseq
  in
  let tidy_ante,tidy_conseq = Cfout.rearrange_entailment prog e.sleek_proving_ante conseq in
  fmt_open_box 1;
  fmt_string("\n");
  let src = e.sleek_src_no in
  let par_id = e.sleek_parent_no in
  let rest = if src!=3 then " src:"^(string_of_int src) else "" in
  let rest = if par_id>=(0) then "<:"^(string_of_int par_id)^rest else rest in
  fmt_string ("// id: " ^ (string_of_int e.sleek_proving_id)^rest);
  fmt_string ("; line: " ^ (Globals.line_number_of_pos e.sleek_proving_pos));
  fmt_string ("; kind: " ^ (e.sleek_proving_kind));
  fmt_string (if !Globals.sleek_gen_vc_exact then "\n checkentail_exact" else "\n checkentail");
  sleek_tidy_formula tidy_ante (* e.sleek_proving_ante *);
  fmt_string "\n |- ";
  sleek_tidy_formula tidy_conseq (* conseq *);
  fmt_string ".\n";
  fmt_string ("expect " ^ expected ^ ".");
  (if !print_clean_flag then
     let ante, conseq = CleanUp.cleanUpFormulas e.sleek_proving_ante conseq in
     fmt_string ("\n clean checkentail" ^ (Cprinter.sleek_of_formula ante)
                 ^ "\n |- " ^ (Cprinter.sleek_of_formula conseq)^".\n")
   else ());
  fmt_close()

let sleek_of_sleek_log_entry prog e = Cprinter.poly_string_of_pr (slk_sleek_log_entry prog) e

class last_commands =
  object (self)
    val mutable last_proof = None (* simplify?,prover? sat? *)
    val mutable last_proof_fail = None (* with timeout/exception *)
    (* val mutable last_imply_fail = None (\* prover, failure *\) *)
    val mutable last_sleek = None
    val mutable last_sleek_fail = None
    val mutable last_is_sleek = false
    val mutable sleek_no = -1
    val mutable mona_cnt = 0
    val mutable z3_cnt = 0
    val mutable oc_cnt = 0
    val mutable cache_cnt = 0
    val sleek_stk = new Gen.stack_noexc "sleek_stk" (-1,-1) (fun (a,_) -> string_of_int a) (fun (a,_) (b,_) -> a==b)
    (* method set_sleek_num no = sleek_no <- no *)
    method get_sleek_no_only = fst(sleek_stk # top_no_exc)
    method get_proof_num =
      match last_proof with
      | None -> 0
      | Some n -> n.log_id
    method count_prover e pt =
      if (e.log_cache) then cache_cnt <- cache_cnt+1
      else
        begin
          match pt with
          | OmegaCalc -> oc_cnt <- oc_cnt+1
          | Mona -> mona_cnt <- mona_cnt+1
          | Z3 -> z3_cnt <- z3_cnt+1
          | _ -> ()
        end
    method set entry =
      let () = last_is_sleek <- false in
      let cmd = entry.log_type in
      let ans = Some entry in
      let () = last_proof <- ans in
      let res = entry.log_res in
      self # count_prover entry entry.log_prover;
      let () = match res with
        | PR_exception | PR_timeout ->
          begin
            last_proof_fail <- ans;
            set_last_sleek_fail ()
          end

        | _ -> () in
      let () = match cmd with
        | PT_IMPLY _ ->
          (match res with
           | PR_BOOL true  -> ()
           | _ -> if not(entry.log_cache) then
               begin
                 last_proof_fail <-ans;
                 set_last_sleek_fail ()
               end
          )
        | _ -> ()
      in ()
    method start_sleek src =
      begin
        (* let (parent,_) = sleek_stk # top_no_exc in *)
        sleek_no <- sleek_no+1;
        Globals.sleek_proof_no := sleek_no;
        sleek_stk # push (sleek_no,src);
        (* let pr = string_of_int in *)
        (* print_endline ((add_str "Start (no,src,parent)" (pr_triple pr pr pr)) (sleek_no,src,parent)); *)
        sleek_no
      end
    method get_sleek_no =
      (* returns cur sleek no & its parent *)
      begin
        let (cur,src) = sleek_stk # top_no_exc in
        (if sleek_stk # is_empty
         then (print_endline_quiet "ERROR : get_sleek_no on empty sleek_stk")
         else sleek_stk # pop);
        (cur,src,fst(sleek_stk # top_no_exc))
      end
    method set_sleek entry =
      let () = last_is_sleek <- true in
      let cmd = Some entry in
      let () = last_sleek <- cmd in
      let res = entry.sleek_proving_res in
      match res with
      | Some res ->
        let f = if (* (!Globals.enable_error_as_exc || CF.is_en_error_exc_ctx_list res) && *) not (CF.is_dis_error_exc_ctx_list res) then CF.isFailCtx_gen else CF.isFailCtx in
        if (* CF.isFailCtx *) f (res) then
          last_sleek_fail <- cmd
      | None -> last_sleek_fail <- cmd
    method dumping no =
      if  !proof_logging_txt && !is_hip_running (*|| !sleek_logging_txt *) then
        begin
          match last_proof_fail with
          | Some e ->
            let () = Debug.info_zprint  (lazy  ("dumping for "^no)) no_pos in
            Debug.info_hprint string_of_proof_log_entry e no_pos
          | _ -> Debug.info_pprint ("Cannot find imply proof failure for "^no) no_pos
        end;
      if !sleek_logging_txt && !is_hip_running then
        match last_sleek_fail with
        | Some e ->
          let () = Debug.info_zprint  (lazy  ("dumping for "^no)) no_pos in
          Debug.info_hprint string_of_sleek_log_entry e no_pos
        | _ -> Debug.info_pprint ("Cannot find sleek failure for "^no) no_pos
    (* print_endline ("!!!! WARNING : last sleek log " ^ (pr_id no)); *)
    method dump_prover_cnt =
      let print_cnt info cnt =
        if cnt>0 then
          Debug.info_hprint (add_str info string_of_int) cnt no_pos
      in
      begin
        print_cnt "Number of MONA calls" mona_cnt;
        print_cnt "Number of Omega calls" oc_cnt;
        print_cnt "Number of Z3 calls" z3_cnt;
        print_cnt "Number of Cache calls" cache_cnt;
        print_endline_quiet ""
      end

  end;;

let last_cmd = new last_commands

let sleek_counter= ref 0

(* this part is not properly maintained *)
(* to create a hash_table from proof_stk *)
(* also to read a hastbl from file *)
let proof_log_tbl : (string, proof_log) Hashtbl.t = Hashtbl.create 700

let add_proof_tbl pno plog =
  if !Globals.proof_logging then
    Hashtbl.add proof_log_tbl pno plog

let sleek_log_stk : sleek_log_entry  Gen.stack_filter
  = new Gen.stack_filter "sleek_log_stk" string_of_sleek_log_entry (==) (fun e -> not(e.sleek_proving_avoid))

(* let sleek_proving_kind = ref (POST : sleek_proving_kind) *)
let sleek_proving_id = ref (0 : int)

(* let current_hprel_ass = ref ([] : CF.hprel list) *)
let current_infer_rel_stk : CP.infer_rel_type Gen.stack_pr = new Gen.stack_pr "current-infer-rel-stk"
  CP.string_of_infer_rel (==)

let current_hprel_ass_stk : CF.hprel  Gen.stack_pr
  = new Gen.stack_pr "current_hprel_ass_stk" Cprinter.string_of_hprel_short (==)

let current_tntrel_ass_stk : Tid.tntrel Gen.stack_pr =
  new Gen.stack_pr "current_tntrel_ass_stk" string_of_tntrel (==)

(* let get_sleek_proving_id () = *)
(*   let r = !sleek_proving_id in *)
(*   let () = Globals.add_count sleek_proving_id in *)
(*   r *)

(* let proof_log_list  = ref [] (\*For printing to text file with the original order of proof execution*\) *)
let proof_log_stk : proof_log  Gen.stack_filter
  = new Gen.stack_filter "proof_log_stk" string_of_proof_log_entry (fun e1 e2 -> e1.log_id==e2.log_id) (fun e -> true)
(* 	if (proving_kind # string_of)<>"TRANS_PROC" then *)
(* true) *)
(*     log_proving_kind : Others.proving_kind; *)

(* not(Others.proving_kind # top_no_exc == PK_Trans_Proc)) *)

(* let proof_gt5_log_list = ref [] (\*Logging proofs require more than 5 secs to be proved*\) *)

(* let update_sleek_proving_kind k= let () = sleek_proving_kind:= k in () *)

(* TODO : add result into the log printing *)
(* wrong order number indicates recursive invocations *)
let add_sleek_logging (es_opt:Cformula.entail_state option) timeout_flag stime infer_type infer_vars classic_flag caller avoid hec slk_no ante conseq
    consumed_heap evars impl_vars (result) pos=
  (* let () = Debug.info_zprint  (lazy  ("avoid: "^(string_of_bool avoid))) no_pos in *)
  (* let () = x_binfo_hp (add_str "es_opt" (pr_option Cprinter.string_of_entail_state)) es_opt no_pos in *)
  (* es_infer_obj: Globals.inf_obj; *)
  if !Globals.sleek_logging_txt then
    let result = match result with
      | Some c ->
        begin
          match c with
          | CF.FailCtx (_,c,cex) ->
            if cex.CF.cex_processed_mark then Some (CF.SuccCtx [c])
            else result
          | _ -> result
        end
      | _ -> None in
    (* let () = Debug.info_pprint "logging .." no_pos in *)
    let (stk_slk_no,src,slk_parent_no) = last_cmd # get_sleek_no in
    let (ho_vars_map,str,hp_rels) = match es_opt with
      | None ->
        let () = y_winfo_hp (add_str "sleekno(no entail-state?)" string_of_int) slk_no in
        ([],"",[]);
      | Some es -> (es.es_ho_vars_map, " es_infer_obj: "^(es.es_infer_obj # string_of)
                   ,if slk_parent_no>=0 then es.es_infer_hp_rel # get_stk_recent
                    else es.es_infer_hp_rel # get_stk_recent_reset) in
    let str = str^" globals: "^(Globals.infer_const_obj # string_of) in
    if slk_no != stk_slk_no then print_endline_quiet ("LOGGING ERROR : inconsistent slk_no problem "
                                                      ^(string_of_int slk_no)^" "^((add_str "stk" string_of_int) stk_slk_no));
    let sleek_log_entry = {
      (* sleek_proving_id = get_sleek_proving_id (); *)
      sleek_src_no = src; (* where sleek cmd was created *)
      sleek_parent_no = slk_parent_no;
      sleek_proving_id = slk_no;
      sleek_proving_caller = caller;
      sleek_proving_aob = str;
      sleek_proving_avoid = not !Globals.sleek_log_all && avoid;
      sleek_proving_classic_flag = classic_flag;
      sleek_proving_hec = hec;
      sleek_proving_pos = pos;
      (* sleek_proving_kind = string_of_top_proving_kind (); *)
      sleek_proving_kind = string_of_impt_proving_kind ();
      (* !sleek_proving_kind; *)
      sleek_proving_ante = ante;
      sleek_proving_conseq = conseq;
      sleek_proving_tntrel_ass = current_tntrel_ass_stk # get_stk;
      sleek_proving_hprel_ass = hp_rels (* current_hprel_ass_stk # get_stk *);
      sleek_proving_rel_ass = current_infer_rel_stk # get_stk;
      sleek_proving_c_heap = consumed_heap;
      sleek_proving_evars = evars;
      sleek_proving_impl_vars = impl_vars;
      sleek_proving_infer_vars = infer_vars;
      sleek_proving_infer_type = infer_type;
      sleek_ho_vars_map = ho_vars_map;
      sleek_time = stime;
      sleek_timeout = timeout_flag;
      sleek_proving_res = result;
    }
    in
    let () =  x_dinfo_pp (string_of_sleek_log_entry sleek_log_entry) no_pos in
    let () = last_cmd # set_sleek sleek_log_entry in
    let () = sleek_log_stk # push sleek_log_entry in
    (if not(avoid) then
       begin
         current_tntrel_ass_stk # reset;
         current_hprel_ass_stk # reset;
         current_infer_rel_stk # reset
       end)
  ; ()
  else
    ()

let add_sleek_logging es_opt timeout_flag stime infer_type infer_vars classic_flag caller avoid hec slk_no ante conseq
    consumed_heap evars impl_vars (result) pos=
  let pr = Cprinter.string_of_formula in
  Debug.no_4 "add_sleek_logging"
    string_of_bool string_of_int
    pr pr pr_none
    (fun _ _ _ _ -> add_sleek_logging es_opt timeout_flag stime infer_type infer_vars classic_flag caller avoid hec slk_no ante conseq
        consumed_heap evars impl_vars (result) pos) avoid slk_no ante conseq

let find_bool_proof_res pno =
  try
    let log = Hashtbl.find proof_log_tbl pno in
    match log.log_res with
    | PR_BOOL r -> r
    | _ -> report_error no_pos "Fatal error with Proof Logging: Unexpected result."
  with _ -> report_error no_pos "Fatal error with Proof Logging. Do remember to enable proof logging before using LOG."

let find_formula_proof_res pno =
  try
    let log = Hashtbl.find proof_log_tbl pno in
    match log.log_res with
    | PR_FORMULA r -> r
    | _ -> report_error no_pos "Fatal error with Proof Logging: Unexpected result."
  with _ -> report_error no_pos "Fatal error with Proof Logging. Do remember to enable proof logging before using LOG."

let proof_log_to_file src_files =
  let out_chn =
    (try Unix.mkdir "logs" 0o750 with _ -> ());
    open_out ("logs/proof_log_" ^ (Globals.norm_file_name (List.hd src_files))) in
  output_value out_chn proof_log_tbl

let file_to_proof_log  src_files =
  try
    let in_chn = open_in ("logs/proof_log_" ^ (Globals.norm_file_name (List.hd src_files))) in
    let tbl = input_value in_chn in
    Hashtbl.iter (fun k log -> Hashtbl.add proof_log_tbl k log) tbl
  with _ -> report_error no_pos "File of proof logging cannot be opened."

(* let log_append_properties (ls: string ) = (\*For append more properties to log, currently not used*\) *)
(* 	try *)
(* 	 let tl= List.nth !proof_log_list ((List.length !proof_log_list) -1) in *)
(* 	 let tlog=Hashtbl.find proof_log_tbl tl in *)
(* 	 let _= tlog.log_other_properties <- tlog.log_other_properties @ [ls] in *)
(* 	 print_endline (ls) *)
(*   with _-> () *)

(*TO DO: check unique pno??*)
let add_proof_logging timeout_flag (cache_status:bool) old_no pno tp ptype time res =
  (* let () = Debug.info_pprint "inside add_proof_log" no_pos in *)
  if (* !Globals.proof_logging || *) !Globals.proof_logging_txt
  (* || !Globals.sleek_logging_txt *) then
    (* let _= print_endline ("logging :"^pno^" "^proving_info () ^"\n"^trace_info ()) in *)
    let tstartlog = Gen.Profiling.get_time () in
    let plog = {
      log_id = pno;
      log_loc = proving_loc # get;
      log_sleek_no = last_cmd # get_sleek_no_only;
      log_proving_kind = proving_kind # top_no_exc;
      (* log_other_properties = [proving_info ()]@[trace_info ()]; *)
      (* log_old_id = old_no; *)
      log_prover = Others.last_tp_used # get;
      log_type = ptype;
      log_time = time;
      log_proof_string = Others.last_proof_string # get_rm;
      log_proof_result = Others.last_proof_result # get_rm;
      log_timeout = timeout_flag;
      log_cache = cache_status;
      log_res = res; } in
    let () = last_cmd # set plog in
    proof_log_stk # push plog;
    (* let pno_str = string_of_int pno in *)
    (* let () = add_proof_tbl pno_str plog in *)
    let () =  x_dinfo_pp (string_of_proof_log_entry plog) no_pos in
    (* let () = try *)
    (*   (\* let _= BatString.find (Sys.argv.(0)) "hip" in *\) *)
    (*   if (proving_kind # string_of)<>"TRANS_PROC" then *)
    (*     begin  *)
    (*       proof_log_stk # push plog; *)
    (*     end		 *)
    (* with _-> *)
    (*     if(!Globals.proof_logging_txt) then *)
    (*       try *)
    (*         let temp=(proving_kind # string_of) in *)
    (*         let () = *)
    (*           if !Globals.log_filter *)
    (*           then BatString.find temp "SLEEK_ENT" *)
    (*           else 0 in *)
    (*         begin  *)
    (*   	proof_log_stk # push pno; *)
    (*         end		 	 *)
    (*       with _->()	 *)
    (* in *)
    let tstoplog = Gen.Profiling.get_time () in
    let _= Globals.proof_logging_time := !Globals.proof_logging_time +. (tstoplog -. tstartlog) in ()
    (* let _=print_endline ("log time: "^(string_of_float (tstoplog))^" and "^(string_of_float (tstartlog))) in ()	  *)
  else ()

let proof_log_to_text_file fname (src_files) =
  if !Globals.proof_logging_txt (* || !Globals.sleek_logging_txt *)
  then
    begin
      let lgs = (List.rev (proof_log_stk # get_stk)) in
      let () = Debug.info_zprint  (lazy  ("Number of log entries "^(string_of_int (List.length lgs)))) no_pos in
      Debug.info_zprint  (lazy  ("Logging "^fname^"\n")) no_pos;
      let tstartlog = Gen.Profiling.get_time () in
      let oc =
        (try Unix.mkdir "logs" 0o750 with _ -> ());
        let with_option = if !Globals.en_slc_ps then "eps" else "no_eps" in
        open_out ("logs/"^with_option^"_proof_log_" ^ (Globals.norm_file_name (List.hd src_files)) ^".txt") in
      let string_of_log_type lt =
        match lt with
        |PT_IMPLY (ante, conseq) |PT_IMPLY_TOP (ante, conseq)
          -> "Imply: ante:" ^(string_of_pure_formula ante) ^"\n\t     conseq: " ^(string_of_pure_formula conseq)
        |PT_SAT f-> "Sat: "^(string_of_pure_formula f)
        | PT_SIMPLIFY f -> "Simplify: "^(string_of_pure_formula f)
        |PT_HULL f -> "Hull: "^(string_of_pure_formula f)
        |PT_PAIRWISE f -> "PairWise: "^(string_of_pure_formula f)
      in
      (* let helper log = *)
      (*   "\n--------------\n"^ *)
      (*       (\* List.fold_left (fun a c->a^c) "" log.log_other_properties^ *\) *)
      (*       (\* "\nid: "^log.log_id^ *\) *)
      (*       "\nProver: "^ *)
      (*       (if log.log_cache then "CACHED"  *)
      (*       else (string_of_prover log.log_prover))^ *)
      (*       "\nType: "^(string_of_log_type log.log_type)^ *)
      (*       (\* "\nTime: "^(string_of_float(log.log_time))^ *\) *)
      (*       "\nResult: "^(string_of_log_res log.log_type log.log_res)^"\n"  *)
      (* in *)
      (* with *)
      (*            |PR_BOOL b -> string_of_bool b *)
      (*            |PR_FORMULA f -> string_of_pure_formula f)^"\n" in *)
      (* let () = proof_log_stk # string_of_reverse in *)
      let _= List.map
          (fun log ->
             (* let log=Hashtbl.find proof_log_tbl (string_of_int ix) in *)
             if log.log_proving_kind != PK_Trans_Proc then
               begin
                 let str = ((* helper *) string_of_proof_log_entry log) in
                 fprintf oc "%s" str;
                 if !Globals.dump_proof then printf "%s" str;
               end
          ) lgs in
      let () = last_cmd # dump_prover_cnt in
      let tstoplog = Gen.Profiling.get_time () in
      let _= Globals.proof_logging_time := !Globals.proof_logging_time +. (tstoplog -. tstartlog) in
      close_out oc
    end
  else ()

let proof_log_to_text_file fname (src_files) =
  Debug.no_1 "proof_log_to_text_file" pr_id pr_none (fun _ -> proof_log_to_text_file fname src_files) fname

(* let z3_proofs_list_to_file fz3name (src_files) = *)
(*   if !Globals.proof_logging_txt || !Globals.sleek_logging_txt then *)
(*     let () = Debug.info_zprint  (lazy  ("Logging "^fz3name^"\n")) no_pos in *)
(*     let tstartlog = Gen.Profiling.get_time () in *)
(*     let oc =  *)
(*       (try Unix.mkdir "logs" 0o750 with _ -> ()); *)
(*       (\* let with_option= if(!Globals.do_slicing) then "slice" else "noslice" in *\) *)
(*       let with_option = if(!Globals.en_slc_ps) then "eps" else "no_eps" in *)
(*       let with_option= with_option^"_"^if(!Globals.split_rhs_flag) then "rhs" else "norhs" in *)
(*       let with_option= with_option^"_"^if(not !Globals.elim_exists_ff) then "noee" else "ee" in *)
(*       open_out ("logs/"^with_option^"_"^(Globals.norm_file_name (List.hd src_files)) ^".z3") in *)
(*     let _= List.map (fun ix-> let _=fprintf oc "%s" ix in ()) !z3_proof_log_list in *)
(*     let tstoplog = Gen.Profiling.get_time () in *)
(*     let _= Globals.proof_logging_time := !Globals.proof_logging_time +. (tstoplog -. tstartlog) in  *)
(*     close_out oc; *)
(*   else ()	 *)


(* let proof_greater_5secs_to_file (src_files) = *)
(* 	if !Globals.proof_logging_txt then *)
(* 		let tstartlog = Gen.Profiling.get_time () in *)
(* 		let oc =  *)
(* 		(try Unix.mkdir "logs" 0o750 with _ -> ()); *)
(* 		(\* let with_option= if(!Globals.do_slicing) then "slice" else "noslice" in *\) *)
(* 		let with_option = if(!Globals.en_slc_ps) then "eps" else "no_eps" in *)
(* 		let with_option= with_option^"_"^if(!Globals.split_rhs_flag) then "rhs" else "norhs" in *)
(*     let with_option= with_option^"_"^if(not !Globals.elim_exists_ff) then "noee" else "ee" in *)
(* 		open_out ("logs/greater_5sec_"^with_option^"_"^(Globals.norm_file_name (List.hd src_files)) ^".log5") in *)
(* 		let _= List.map (fun ix-> let _=fprintf oc "%s" ix in ()) !proof_gt5_log_list in *)
(* 		let tstoplog = Gen.Profiling.get_time () in *)
(* 	  let _= Globals.proof_logging_time := !Globals.proof_logging_time +. (tstoplog -. tstartlog) in  *)
(* 		close_out oc; *)
(* 	else ()	 *)

let wrap_calculate_time exec_func src_file args =
  (* if !Globals.proof_logging_txt then  *)
  let _= sleek_counter := !sleek_counter +1 in
  let tstartlog = Gen.Profiling.get_time () in
  let () = exec_func args in
  let tstoplog = Gen.Profiling.get_time () in
  (* let period = (tstoplog -. tstartlog) in *)
  ()
(* if (period> 0.7) then *)
(*   proof_gt5_log_list :=   *)
(*       (!proof_gt5_log_list@[(Globals.norm_file_name (List.hd src_file))^"-check-entail-num-"^string_of_int !sleek_counter^"--Time--"^string_of_float (period)^"\n"]) *)
(* else exec_func args *)

(* let sleek_z3_proofs_list_to_file source_files =                                                    *)
(* 	if !Globals.proof_logging_txt then                                                               *)
(* 		let tstartlog = Gen.Profiling.get_time () in                                                   *)
(* 		let oc =                                                                                       *)
(* 		(try Unix.mkdir "logs" 0o750 with _ -> ());                                                    *)
(* 		let with_option= if(!Globals.do_slicing) then "sleek_slice" else "sleek_noslice" in            *)
(* 		(* let with_option= with_option^"_"^if(!Globals.split_rhs_flag) then "rhs" else "norhs" in *)  *)
(* 		open_out ("logs/"^with_option^(Globals.norm_file_name (List.hd source_files)) ^".z3") in       *)
(* 		let _= List.map (fun ix-> let _=fprintf oc "%s" ix in ()) !z3_proof_log_list in                *)
(* 		let tstoplog = Gen.Profiling.get_time () in                                                    *)
(* 	  let _= Globals.proof_logging_time := !Globals.proof_logging_time +. (tstoplog -. tstartlog) in *)
(* 		close_out oc;                                                                                  *)
(* 	else ()                                                                                          *)

let sleek_log_to_text_file slfn (src_files) =
  (* let tstartlog = Gen.Profiling.get_time () in *)
  let lgs = sleek_log_stk # len in
  let () = Debug.info_zprint  (lazy  ("Number of sleek log entries "^(string_of_int (lgs)))) no_pos in
  Debug.info_zprint  (lazy  ("Logging "^slfn^"\n")) no_pos;
  (* let fn = "logs/sleek_log_" ^ (Globals.norm_file_name (List.hd src_files)) ^".txt" in *)
  let fn = slfn in
  let oc =
    (try Unix.mkdir "logs" 0o750 with _ -> ());
    (* let with_option = if !Globals.en_slc_ps then "eps" else "no_eps" in *)
    open_out fn
  in
  let ls = sleek_log_stk # get_stk in
  let ls =
    if (!Globals.sleek_log_filter)
    then List.filter (fun e -> not(e.sleek_proving_avoid)) ls
    else ls
  in
  let ls = List.sort (fun e1 e2 -> compare e1.sleek_proving_id e2.sleek_proving_id) ls in
  let str = String.concat "\n" (List.map string_of_sleek_log_entry ls) in
  let _= fprintf oc "%s" str in
  if !Globals.dump_sleek_proof then printf "%s" str;
  (* let tstoplog = Gen.Profiling.get_time () in *)
  (* let _= Globals.proof_logging_time := !Globals.proof_logging_time +. (tstoplog -. tstartlog) in  *)
  close_out oc

let sleek_log_to_sleek_file slfn src_files prog prim_names =
  (* let tstartlog = Gen.Profiling.get_time () in *)
  let lgs = if !Globals.sleek_gen_sat then CF.sat_stk # len else sleek_log_stk # len in
  let () = Debug.info_zprint  (lazy  ("Number of sleek log entries "^(string_of_int (lgs)))) no_pos in
  Debug.info_zprint  (lazy  ("Logging "^slfn^"\n")) no_pos;
  (* let fn = "logs/sleek_log_" ^ (Globals.norm_file_name (List.hd src_files)) ^".txt" in *)
  let fn = slfn in
  let oc =
    (try Unix.mkdir "logs" 0o750 with _ -> ());
    (* let with_option = if !Globals.en_slc_ps then "eps" else "no_eps" in *)
    open_out fn
  in
  let ls = sleek_log_stk # get_stk in
  let ls =
    if (!Globals.sleek_log_filter)
    then List.filter (fun e -> not(e.sleek_proving_avoid)) ls
    else ls
  in
  let ls = List.sort (fun e1 e2 -> compare e1.sleek_proving_id e2.sleek_proving_id) ls in
  let str_data = String.concat "\n" (List.map Cprinter.sleek_of_data_decl
                                       (List.filter (fun d -> not (Gen.BList.mem_eq (=) d.Cast.data_name prim_names)) prog.Cast.prog_data_decls)) in
  let str_view = String.concat "\n" (List.map Cprinter.sleek_of_view_decl
                                       (List.filter (fun v -> not (Gen.BList.mem_eq (=) v.Cast.view_name prim_names)) prog.Cast.prog_view_decls)) in
  let str_lem =
    let lem = (Lem_store.all_lemma # get_left_coercion) @ (Lem_store.all_lemma # get_right_coercion) in
    if lem = [] then ""
    else "/*\n" ^ (Cprinter.string_of_coerc_decl_list lem) ^ "\n*/"
  in
  let str_ent =
    if !Globals.sleek_gen_sat then
      let formula_list = CF.sat_stk # get_stk in
      String.concat "\n" (List.map (fun f ->
          let str1 = "// id " ^ (string_of_int !num_sat) ^ "\n" in
          let str2 = "checksat " ^ (Cprinter.sleek_of_formula f) ^ ".\n" in
          str1 ^ str2
      ) formula_list)
    else String.concat "\n" (List.map (sleek_of_sleek_log_entry prog) ls)
  in
  let str = str_data ^ "\n" ^ str_view ^ "\n" ^ str_lem ^ "\n" ^ str_ent in
  let _= fprintf oc "%s" str in
  if !Globals.dump_sleek_proof then printf "%s" str;
  (* let tstoplog = Gen.Profiling.get_time () in *)
  (* let _= Globals.proof_logging_time := !Globals.proof_logging_time +. (tstoplog -. tstartlog) in  *)
  close_out oc

let sleek_log_to_text_file2 (src_files) =
  (* let () = print_endline "sleek_log_2" in *)
  let fn = "logs/sleek_log_" ^ (Globals.norm_file_name (List.hd src_files)) ^".txt" in
  let pr = pr_list pr_id in
  Debug.no_1 "sleek_log_to_text_file" pr pr_none (sleek_log_to_text_file fn) (src_files)

let process_proof_logging src_files prog prim_names =
  (* Debug.info_zprint  (lazy  ("process_proof_logging\n")) no_pos; *)
  if !Globals.proof_logging_txt (* || !Globals.proof_logging_txt || !Globals.sleek_logging_txt *) then
    begin
      let tstartlog = Gen.Profiling.get_time () in
      let _= proof_log_to_file src_files in
      let with_option = if(!Globals.en_slc_ps) then "eps" else "no_eps" in
      let fname = "logs/"^with_option^"_proof_log_" ^ (Globals.norm_file_name (List.hd src_files)) ^".txt"  in
      (* let fz3name= ("logs/"^with_option^"_z3_proof_log_"^ (Globals.norm_file_name (List.hd src_files)) ^".txt") in *)
      let slfn = "logs/sleek_log_" ^ (Globals.norm_file_name (List.hd src_files)) ^".txt" in
      let slkfn = "logs/sleek_log_" ^ (Globals.norm_file_name (List.hd src_files)) ^".slk" in
      (* let _=  *)
      (*   (\* if (!Globals.sleek_logging_txt || !Globals.proof_logging_txt)  *\) *)
      (*   (\* then  *\) *)
      (*     begin *)
      (*       proof_log_to_text_file fname src_files *)
      (*       (\* z3_proofs_list_to_file fz3name src_files *\) *)
      (*     end *)
      (*   (\* else try Sys.remove fname  *\) *)
      (*   (\*   (\\* ("logs/proof_log_" ^ (Globals.norm_file_name (List.hd src_files))^".txt") *\\) *\) *)
      (*   (\* with _ -> () *\) *)
      (* in *)
      proof_log_to_text_file fname src_files;
      let _= if (!Globals.sleek_logging_txt)
        then
          begin
            sleek_log_to_text_file slfn src_files;
          end
        else try Sys.remove slfn
          (* ("logs/proof_log_" ^ (Globals.norm_file_name (List.hd src_files))^".txt") *)
          with _ -> ()
      in
      let () = if (!Globals.sleek_gen_vc || !Globals.sleek_gen_vc_exact || !Globals.sleek_gen_sat)
        then
          begin
            sleek_log_to_sleek_file slkfn src_files prog prim_names;
          end
        else try Sys.remove slkfn
          (* ("logs/proof_log_" ^ (Globals.norm_file_name (List.hd src_files))^".txt") *)
          with _ -> ()
      in
      let tstoplog = Gen.Profiling.get_time () in
      let _= Globals.proof_logging_time := !Globals.proof_logging_time +. (tstoplog -. tstartlog) in ()
      (* let _=print_endline ("Time for logging: "^(string_of_float (!Globals.proof_logging_time))) in    () *)
    end
  else ()

let process_proof_logging src_files prog prim_names =
  let pr = pr_list pr_id in
  Debug.no_1 "process_proof_logging" pr pr_none
    (fun _ -> process_proof_logging src_files prog prim_names) src_files


(* let add_sleek_log_entry e= *)
(*   if !Globals.sleek_logging_txt then *)
(*     sleek_log_stk # push e *)
(*   else () *)



(* let process_sleek_logging ()= *)
(*   if !Globals.sleek_logging_txt then *)
(*     (\* let () = print_endline "" in *\) *)
(*     (\* let () = print_endline "*************************************" in *\) *)
(*     (\* let () = print_endline "*******sleek logging ********" in *\) *)
(*     (\* let () = print_endline "*************************************" in *\) *)
(*     (\* let () = print_endline (sleek_log_stk # string_of) in *\) *)
(*     (\* let () = print_endline "*************************************" in () *\) *)
(*     let () = sleek_log_to_text_file src_files in *)
(*     () *)
(*   else *)
(*     () *)

let report_error_dump e =
  last_cmd # dumping "report_error_dump";
  (* print_endline "Last SLEEK FAILURE:"; *)
  (* last_sleek_command # dump; *)
  (* print_endline "Last PURE PROOF FAILURE:"; *)
  (* last_proof_command # dump; *)
  Error.report_error e
