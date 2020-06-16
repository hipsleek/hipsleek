#include "xdebug.cppo"
open Gen
open VarGen

(* let no_pos = no_pos *)
let report_error = Gen.report_error

module Ts = Tree_shares.Ts
module CP = Cpure

(*module Sv:Share_prover.SV =
  struct
  	type t = CP.spec_var
  	let cnt = ref 1
  	let eq = CP.eq_spec_var
  	(*type t_spec = CP.spec_var
  	let rconv v = v
  	let conv v = v
  	let string_of_s v1 = CP.string_of_spec_var v1
  	let get_name_s v = CP.string_of_spec_var v
  	*)
    let string_of v1 = CP.string_of_spec_var v1
  	let rename s a =  match s with CP.SpecVar(t,_,p)-> CP.SpecVar(t,a,p)
    let get_name v = CP.string_of_spec_var v
  	let var_of v = CP.SpecVar(Globals.Tree_sh,v,Unprimed)
    let fresh_var v = cnt:=!cnt+1; rename v ("__ts_fv_"^(string_of_int !cnt))
  end*)



module Ss_proc_Z3:Share_prover.SAT_SLV = functor (Sv:Share_prover.SV) ->
struct
  type t_var = Sv.t
  type nz_cons = t_var list list
  type p_var = (*include Gen.EQ_TYPE with type t=v*)
    | PVar of t_var
    | C_top
  type eq_syst = (t_var*t_var*p_var) list

  let stringofTvar = Sv.string_of
  let stringofPvar v = match v with | C_top -> "T" | PVar v -> Sv.string_of v

  let mkTop () = C_top
  let mkVar v = PVar v
  let getVar v = match v with | C_top -> None | PVar v -> Some v

  let string_of_eq (v1,v2,v3) = (Sv.string_of v1)^" * "^(Sv.string_of v2)^" = "^(match v3 with | PVar v3 ->  Sv.string_of v3 | _ -> " true")
  let string_of_eq_l l = String.concat "\n" (List.map string_of_eq l)

  let to_sv v = CP.SpecVar(Globals.Bool,Sv.string_of v,Unprimed)

  let mkBfv v = CP.BForm ((CP.BVar (to_sv v,no_pos),None),None)

  let f_of_eqs eqs = List.fold_left (fun a (e1,e2,e3)->
      let bf1,bf2 = mkBfv e1, mkBfv e2 in
      let f_eq =  match e3 with
        | PVar v3->
          let bf3 = mkBfv v3 in
          let f1 = CP.And (bf3, CP.And (bf2, CP.Not (bf1,None,no_pos),no_pos), no_pos) in
          let f2 = CP.And (bf3, CP.And (bf1, CP.Not (bf2,None,no_pos),no_pos), no_pos) in
          let f3 = CP.Or (CP.Not (bf2,None,no_pos), CP.Not (bf1,None,no_pos), None, no_pos) in
          let r = CP.Or (f1,f2,None,no_pos) in
          CP.And(r,f3,no_pos)
        | C_top ->
          let f1 = CP.And (bf2, CP.Not (bf1,None,no_pos),no_pos) in
          let f2 = CP.And (bf1, CP.Not (bf2,None,no_pos),no_pos) in
          CP.Or (f1,f2,None,no_pos) in
      CP.mkAnd a f_eq no_pos) (CP.mkTrue no_pos) eqs

  let check_nz_sat f_eq f_nz_l =
    let f_tot = List.fold_left (fun a c-> CP.mkAnd a c no_pos) f_eq f_nz_l in
    if Smtsolver.is_sat f_tot "0" then true
    else List.for_all (fun c-> Smtsolver.is_sat (CP.mkAnd f_eq c no_pos) "1") f_nz_l

  let call_sat non_zeros eqs =
    let f = f_of_eqs eqs in
    let f_nz_l = List.map (List.fold_left (fun a c-> CP.mkOr a (mkBfv c) None no_pos) (CP.mkTrue no_pos))  non_zeros in
    Gen.Profiling.inc_counter ("pm_s") ;
    Gen.Profiling.do_1 "tms" (check_nz_sat f) f_nz_l

  let call_sat non_zeros eqs =
    (*		let nzs = String.concat "," (List.map (fun l-> "{"^(String.concat "," (List.map Sv.string_of l))^"}") non_zeros) in
      		let eqss = string_of_eq_l eqs in
      		Debug.devel_print ("Z3 SAT: "^nzs^"\n"^eqss^"\n");*)
    let r = call_sat non_zeros eqs in
    (*		Debug.devel_print ("r: "^(string_of_bool r)^"\n");*) r

  (*t_var list -> nz_cons -> eq_syst -> t_var list -> nz_cons -> eq_syst -> (t_var*bool) list -> (t_var*t_var) list-> bool*)
  let call_imply (a_ev:t_var list) a_nz_cons a_l_eqs (c_ev:t_var list) c_nz_cons c_l_eqs c_const_vars c_subst_vars  =
    let ante_eq_f = f_of_eqs a_l_eqs in
    let ante_nz_l = List.map (List.fold_left (fun a c-> CP.mkOr a (mkBfv c) None no_pos) (CP.mkTrue no_pos))  a_nz_cons in
    if not (check_nz_sat ante_eq_f ante_nz_l) then true
    else
      let ante_tot = CP.mkExists (List.map to_sv a_ev) (List.fold_left (fun a c-> CP.mkAnd a c no_pos) ante_eq_f ante_nz_l) None no_pos in
      let conseq_tot =
        let conseq_eq_f = f_of_eqs c_l_eqs in
        let conseq_nz_f = List.fold_left (fun a c->
            let r = List.fold_left (fun a c-> CP.mkOr a (mkBfv c) None no_pos) (CP.mkTrue no_pos) c in
            CP.And (a,r,no_pos)) conseq_eq_f  c_nz_cons in
        let vc_f = List.fold_left (fun a (v,c)->
            let r = if c then mkBfv v else CP.Not (mkBfv v, None, no_pos) in
            CP.And (r,a,no_pos)) conseq_nz_f  c_const_vars in
        let ve_f = List.fold_left (fun a (v1,v2)->
            let f1 = CP.Or (CP.Not (mkBfv v1, None, no_pos),mkBfv v2, None, no_pos) in
            let f2 = CP.Or (CP.Not (mkBfv v2, None, no_pos),mkBfv v1, None, no_pos) in
            CP.And (CP.And (f1,f2,no_pos),a,no_pos)) vc_f c_subst_vars in
        CP.mkExists (List.map to_sv c_ev) ve_f None no_pos in
      (*let () = Debug.devel_print ("share prover: call_imply ante:  "^ (Cprinter.string_of_pure_formula ante_tot))in
        			let () = Debug.devel_print ("share prover: call_imply conseq:  "^ (Cprinter.string_of_pure_formula conseq_tot))in*)
      Gen.Profiling.inc_counter ("pm_i") ;
      Gen.Profiling.do_1 "tmi" (fun c-> Smtsolver.imply ante_tot c 0.) conseq_tot

  let call_imply (a_ev:t_var list) a_nz_cons a_l_eqs c_ev c_nz_cons c_l_eqs c_const_vars c_subst_vars  =
    (*let nzsf l = String.concat "," (List.map (fun l-> "{"^(String.concat "," (List.map Sv.string_of l))^"}") l) in
      			let consl = Gen.Basic.pr_list (Gen.Basic.pr_pair Sv.string_of string_of_bool) c_const_vars in
      			let cvel = Gen.Basic.pr_list (Gen.Basic.pr_pair Sv.string_of Sv.string_of) c_subst_vars in
      			let anzs = nzsf a_nz_cons in
      			let cnzs = nzsf c_nz_cons in
      			let aeqss = string_of_eq_l a_l_eqs in
      			let ceqss = string_of_eq_l c_l_eqs in
      			Debug.devel_print ("Imply ante: "^anzs^";\n"^aeqss^";\n");
      			Debug.devel_print ("Imply conseq: "^cnzs^";\n"^cvel^";\n"^consl^";\n"^ceqss^";\n")s;*)
    let r = call_imply a_ev a_nz_cons a_l_eqs c_ev c_nz_cons c_l_eqs c_const_vars c_subst_vars in
    (*Debug.devel_print ("r: "^(string_of_bool r));*) r
end;;


(************************************************************************************)

module Ss_minisat_proc:Share_prover.SAT_SLV = functor (Sv:Share_prover.SV) ->
struct
  type t_var = Sv.t
  type nz_cons = t_var list list
  type p_var = (*include Gen.EQ_TYPE with type t=v*)
    | PVar of t_var
    | C_top
  type eq_syst = (t_var*t_var*p_var) list

  let stringofTvar = Sv.string_of
  let stringofPvar v = match v with | C_top -> "T" | PVar v -> Sv.string_of v

  let mkTop () = C_top
  let mkVar v = PVar v
  let getVar v = match v with | C_top -> None | PVar v -> Some v

  let string_of_eq (v1,v2,v3) = (Sv.string_of v1)^" * "^(Sv.string_of v2)^" = "^(match v3 with | PVar v3 ->  Sv.string_of v3 | _ -> " true")
  let string_of_eq_l l = String.concat "\n" (List.map string_of_eq l)

  (**********minisat interface **********)



  (* Global settings *)
  let minisat_timeout_limit = 15.0


  let test_number = ref 0
  let last_test_number = ref 0
  let minisat_restart_interval = ref (-1)
  let log_all_flag = ref false
  let is_minisat_running = ref false
  let in_timeout = ref 15.0 (* default timeout is 15 seconds *)
  let minisat_call_count: int ref = ref 0
  (*let log_file = open_out ("allinput22.minisat")*)
  let minisat_input_mode = "file"    (* valid value is: "file" or "stdin" *)

  (*minisat*)
  let minisat_path = try FileUtil.which "minisat" with Not_found -> ""
  let minisat_name = "minisat"
  let minisat_arg = "-pre"
  let minisat_input_format = "cnf"   (* valid value is: cnf *)
  let number_clauses = ref 1
  let number_var = ref 0
  let minisat_process = ref {    GlobProver.name = "minisat";
                                 GlobProver.pid = 0;
                                 GlobProver.inchannel = stdin;
                                 GlobProver.outchannel = stdout;
                                 GlobProver.errchannel = stdin
                            }

  (***************************************************************
     INTERACTION
   **************************************************************)

  let rec collect_output (chn: in_channel)  : (string * bool) =
    try
      let line = input_line chn in
      if line = "SATISFIABLE" then
        (line, true)
      else
        collect_output chn
    with
    | End_of_file ->  ("", false)

  let get_prover_result (output : string) :bool =
    let validity =
      if (output="SATISFIABLE") then
        true
      else
        false in
    validity
  (* output:  - prover_output 									- the running status of prover: true if running, otherwise false *)
  let get_answer (chn: in_channel) : (bool * bool)=
    let (output, running_state) = collect_output chn  in
    let
      validity_result = get_prover_result output;						   in
    (validity_result, running_state)
  let remove_file filename =
    try Sys.remove filename;
    with e -> ignore e
  let set_process proc =
    minisat_process := proc
  let start () =
    if not !is_minisat_running then (
      print_endline_quiet ("Starting Minisat... \n");
      last_test_number := !test_number;
      if (minisat_input_format = "cnf") then (
        Procutils.PrvComms.start false stdout (minisat_name, minisat_path, [|minisat_arg|]) set_process (fun () -> ());
        is_minisat_running := true;
      )
    )
  (* stop minisat system *)
  let stop () =
    if !is_minisat_running then (
      let num_tasks = !test_number - !last_test_number in
      print_string ("\nStop Minisat... " ^ (string_of_int !minisat_call_count) ^ " invocations "); flush stdout;
      Procutils.PrvComms.stop false stdout !minisat_process num_tasks Sys.sigkill (fun ()->());
      is_minisat_running := false;
    )
  (* restart Omega system *)
  let restart reason =
    if !is_minisat_running then (
      let () = print_string (reason ^ " Restarting minisat after ... " ^ (string_of_int !minisat_call_count) ^ " invocations ") in
      Procutils.PrvComms.restart false stdout reason "minisat" start stop
    )
    else (
      let () = print_string (reason ^ " not restarting minisat ... " ^ (string_of_int !minisat_call_count) ^ " invocations ") in ()
    )

  (* Runs the specified prover and returns output *)
  let check_problem_through_file (input: string) (timeout: float) : bool =
    (* debug *)
    (* let () = print_endline "** In function minisat.check_problem" in *)
    let file_suffix = Random.int 1000000 in
    let infile = "/tmp/in" ^ (string_of_int file_suffix) ^ ".cnf" in
    (*let () = print_endline ("-- input: \n" ^ input) in*)
    let out_stream = open_out infile in
    output_string out_stream input;
    close_out out_stream;
    let minisat_result="minisatres.txt" in
    let set_process proc = minisat_process := proc in
    let fnc () =
      if (minisat_input_format = "cnf") then (
        Procutils.PrvComms.start false stdout (minisat_name, minisat_path, [|minisat_arg;infile;minisat_result|]) set_process (fun ()->());
        minisat_call_count := !minisat_call_count + 1;
        let (prover_output, running_state) = get_answer !minisat_process.GlobProver.inchannel in
        is_minisat_running := running_state;
        prover_output;
      )
      else failwith "[minisat.ml] The value of minisat_input_format is invalid!" in
    let res =
      try
        let fail_with_timeout () = restart ("[minisat]Timeout when checking sat!" ^ (string_of_float timeout)); false in
        let res = Procutils.PrvComms.maybe_raise_and_catch_timeout fnc () timeout fail_with_timeout in
        res
      with _ -> ((* exception : return the safe result to ensure soundness *)
          Printexc.print_backtrace stdout;
          print_endline_quiet ("WARNING: Restarting prover due to timeout");
          Unix.kill !minisat_process.GlobProver.pid 9;
          ignore (Unix.waitpid [] !minisat_process.GlobProver.pid);
          false
        ) in
    let () = Procutils.PrvComms.stop false stdout !minisat_process 0 9 (fun () -> ()) in
    remove_file infile;
    res



  (**************************************************************
     MAIN INTERFACE : CHECKING IMPLICATION AND SATISFIABILITY
   *************************************************************)

  (*******************zzzzzzzzzzzzzz****************)

  (*generate the CNF *)
  let cnf_to_string var_cnt f : string =
    let fct l = String.concat " " (List.map (fun (c,b)-> if b then string_of_int c else ("-"^(string_of_int c))) l) in
    "p cnf "^(string_of_int var_cnt)^" "^ (string_of_int (List.length f))^"\n"^
    (String.concat " 0\n" (List.map fct f))^" 0\n"


  let xor sv1 sv2 sv3 = [ [(sv1, false);(sv2,false)];				(*~v1 | ~v2      *)
                          [(sv1,true);(sv2,true);(sv3,false)]; 	    (* v1 | v2 | ~v3 *)
                          [(sv1,false);(sv2,true);(sv3,true)]; 	    (* ~v1| v2 | v3  *)
                          [(sv1,true);(sv2,false);(sv3,true)]] 	 	(* v1 | ~v2| v3  *)

  let xorc sv1 sv2 = [[(sv1, true);(sv2,true)];[(sv1, false);(sv2,false)]]

  let trans_vv sv1 sv2 = [[(sv1, true);(sv2,false)];[(sv1, false);(sv2,true)]]

  let negVar v f = List.map (List.map (fun (c,b)-> if c=v then c,not b else c,b)) f

  let rec tauto_x l = match l with
    | [] -> false
    | (c,b)::t-> (List.exists (fun (v,b1)-> c=v && b<>b1) t) || (tauto_x t)

  let tauto l =
    (*print_string ("tauto: "^(string_of_int (List.length l))^"\n"); flush stdout;*)
    let r = tauto_x l in
    (*print_string ("tauto: "^(string_of_bool r)^"\n"); flush stdout;*)
    r

  let neg_f f =
    let f = List.map (List.map (fun (c,b)-> c,not b)) f in
    if f=[] then f
    else List.fold_left (fun a c->
        let r = List.concat (List.map (fun c-> List.map (fun d-> c::d) a) c) in
        List.filter (fun c->not (tauto c)) r) (List.map (fun c-> [c]) (List.hd f)) (List.tl f)


  let mkOr f1 f2 =
    let l = List.map (fun l -> List.map (fun l2 -> l@l2) f2) f1 in
    List.filter (fun c-> not (tauto c)) (List.concat l)

  let mkExists vl f =
    (*let fv = List.fold_left (fun a c-> a@ (List.map fst c)) [] f in
      				let vl = List.filter (fun c-> List.mem c fv) vl in*)
    (*let () = print_string "here1a\n"; flush stdout in		*)
    let r = List.fold_left (fun f v->
        let l1, l2 = List.partition (fun c-> List.exists (fun (c,_)->  v=c) c) f in
        if l1=[] then f
        else
          let nl1 = negVar v l1 in
          let l1 = mkOr l1 nl1 in
          l1@l2) f vl  in
    (*let () = print_string "here1b\n"; flush stdout in		*)
    r


  let call_imply (a_ev:t_var list) (a_nz_cons:nz_cons) (a_l_eqs:eq_syst) (c_ev:t_var list) (c_nz_cons:nz_cons) (c_l_eqs:eq_syst) (c_const_vars:(t_var*bool) list) (c_subst_vars:(t_var*t_var) list):bool  =
    let ht = Hashtbl.create 20 in
    let tp = ref 0 in
    let get_var v = let v = Sv.string_of v in try Hashtbl.find ht v  with | Not_found -> (tp:= !tp+1; Hashtbl.add ht v !tp;!tp) in
    let trans_eq (v1,v2,c) = match c with
      | C_top -> xorc (get_var v1) (get_var v2)
      | PVar v3-> xor (get_var v1) (get_var v2) (get_var v3) in
    let ante_f =
      let nz = List.map (List.map (fun c-> get_var c, true)) a_nz_cons in   (*conj of disj*)
      let eqs = List.map trans_eq a_l_eqs in
      let a_ev = List.map get_var a_ev in
      mkExists a_ev (List.concat (nz::eqs)) in
    let conseq_f =
      let c_ev = List.map get_var c_ev in
      let nz = List.map (List.map (fun c-> get_var c, true)) c_nz_cons in   (*conj of disj*)
      let eqs = List.map trans_eq  c_l_eqs in
      let c_subst = List.map (fun (v1,v2) -> trans_vv (get_var v1)(get_var v2)) c_subst_vars in
      let c_const = List.map (fun (v,b) -> [[(get_var v, b)]]) c_const_vars in
      let r = List.concat (nz::eqs@c_subst@c_const) in
      let r = List.map (List.filter (fun (c,_)-> not (List.mem c c_ev))) (neg_f r) in
      List.filter (fun c-> c<>[]) r in
    let all_f = ante_f@conseq_f in
    if all_f<>[] then
      not ( if !Globals.perm_prof then
              (Gen.Profiling.inc_counter ("pm_i") ;
               Gen.Profiling.do_1 "tm_i" (check_problem_through_file (cnf_to_string !tp (ante_f@conseq_f))) 0.)
            else check_problem_through_file (cnf_to_string !tp (ante_f@conseq_f)) 0.)
    else true

  let call_imply  (a_ev:t_var list) (a_nz_cons:nz_cons) (a_l_eqs:eq_syst)
      (c_ev:t_var list) (c_nz_cons:nz_cons) (c_l_eqs:eq_syst) (c_const_vars:(t_var*bool) list) (c_subst_vars:(t_var*t_var) list):bool  =
    (*let nzsf l = String.concat "," (List.map (fun l-> "{"^(String.concat "," (List.map Sv.string_of l))^"}") l) in
      					let consl = Gen.Basic.pr_list (Gen.Basic.pr_pair Sv.string_of string_of_bool) c_const_vars in
      					let cvel = Gen.Basic.pr_list (Gen.Basic.pr_pair Sv.string_of Sv.string_of) c_subst_vars in
      					let anzs = nzsf a_nz_cons in
      					let cnzs = nzsf c_nz_cons in
      					let aeqss = string_of_eq_l a_l_eqs in
      					let ceqss = string_of_eq_l c_l_eqs in
      				    print_string ("Imply ante: nz: "^anzs^";\n ex: "^(Gen.Basic.pr_list Sv.string_of a_ev)^";\n eqs: "^aeqss^";\n");
      					print_string ("Imply conseq: nz: "^cnzs^";\n ex: "^(Gen.Basic.pr_list Sv.string_of c_ev)^";\n veq: "^cvel^";\n cons: "^consl^";\n eqs: "^ceqss^";\n");*)
    let r = call_imply a_ev a_nz_cons a_l_eqs c_ev c_nz_cons c_l_eqs c_const_vars c_subst_vars in
    (*print_string ("r: "^(string_of_bool r)); *)
    r


  let call_sat non_zeros eqs =
    let ht = Hashtbl.create 20 in
    let tp = ref 0 in
    let get_var v = let v = Sv.string_of v in try Hashtbl.find ht v  with | Not_found ->
        (tp:= !tp+1;
         (*print_string (v^" "^(string_of_int !tp)^"\n");*)						Hashtbl.add ht v !tp;!tp) in
    let input =
      let nz = List.map (List.map (fun c-> get_var c, true)) non_zeros in   (*conj of disj*)
      let eqs = List.map ( fun (v1,v2,c)->
          let sv1 = get_var v1 in
          let sv2 = get_var v2 in
          match c with
          | C_top -> xorc sv1 sv2
          | PVar v3-> xor sv1 sv2 (get_var v3) ) eqs in
      List.concat (nz::eqs) in
    if input<> [] then
      let input_str = cnf_to_string !tp input in
      (*print_string (input_str^"\n");*)
      if !Globals.perm_prof then (
        Gen.Profiling.inc_counter ("pm_s") ;
        Gen.Profiling.do_1 "tm_s" (check_problem_through_file input_str) minisat_timeout_limit)
      else check_problem_through_file input_str minisat_timeout_limit
    else true


  let call_sat non_zeros eqs =
    (*let nzs = String.concat "," (List.map (fun l-> "{"^(String.concat "," (List.map Sv.string_of l))^"}") non_zeros) in
      				let eqss = string_of_eq_l eqs in
      				print_string ("MINISAT SAT: "^nzs^"\n"^eqss^"\n");*)
    let r = call_sat non_zeros eqs in
    (*print_string ("r: "^(string_of_bool r)^"\n");*) r

end;;





(*module SSV = Share_prover.Sv*)
module Solver_byt = Share_prover.Dfrac_s_solver(Ts)(Share_prover.Sv)(Ss_proc_Z3)
module Solver_minisat = Share_prover.Dfrac_s_solver(Ts)(Share_prover.Sv)(Ss_minisat_proc)
(*to switch to z3 as library change solver from solver_byt to Solver_nat*)
(*module Solver_nat = Shares_z3_lib.Solver*)
module Solver= Solver_minisat


let tr_var v= CP.string_of_spec_var v
let sv_eq = Share_prover.Sv.eq

let mkVperm v = Solver.Vperm (tr_var v)
let mkCperm t = Solver.Cperm t


let rec simpl fl =
  List.fold_left (fun (ve,vc,j) e->
      match e with
      | CP.Eq (e1,e2,_) ->
        (match (e1,e2) with
         | CP.Tsconst (t1,_), CP.Tsconst (t2,_) -> if Ts.eq t2 t1 then ve,vc,j
           else raise Solver.Unsat_exception
         | CP.Var (v1,_),CP.Var (v2,_) ->
           if CP.eq_spec_var v1 v2 then ve,vc,j
           else (tr_var v1, tr_var v2)::ve,vc,j
         | CP.Var (v,_),CP.Tsconst t
         | CP.Tsconst t, CP.Var (v,_) -> ve,(tr_var v,fst t)::vc,j
         | CP.Add(e1,e2,_),CP.Tsconst (t,_)
         | CP.Tsconst (t,_),CP.Add(e1,e2,_) ->
           (match e1,e2 with
            | CP.Var (v1,_), CP.Var (v2,_) -> ve,vc,(mkVperm v1, mkVperm v2, mkCperm t)::j
            | CP.Tsconst (t1,_), CP.Tsconst (t2,_) ->
              if (Ts.can_join t1 t2)&& Ts.eq t (Ts.join t1 t2) then ve,vc,j
              else raise Solver.Unsat_exception
            | CP.Var (v1,_), CP.Tsconst (t1,_)
            | CP.Tsconst (t1,_), CP.Var (v1,_) ->
              if Ts.eq t t1 then raise Solver.Unsat_exception
              else if Ts.contains t t1 then ve,(tr_var v1,Ts.subtract t t1)::vc,j
              else raise Solver.Unsat_exception
            | _,_ -> report_error no_pos "unexpected share formula1")
         | CP.Add(e1,e2,_),CP.Var (v,_)
         | CP.Var (v,_),CP.Add(e1,e2,_) ->
           (match e1,e2 with
            | CP.Var (v1,_), CP.Var (v2,_) -> ve,vc,(mkVperm v1, mkVperm v2, mkVperm v)::j
            | _,_ ->
              let rec l_adds f = match f with
                | CP.Tsconst (t,_) -> [],[t]
                | CP.Var (v,_) -> [v],[]
                | CP.Add (e1,e2,_)->
                  let v1,c1 = l_adds e1 in
                  let v2,c2 = l_adds e2 in
                  v1@v2,c1@c2
                | _ -> report_error no_pos "unexpected share formula4" in
              let (vars, consts) = l_adds (CP.Add (e1,e2,no_pos))  in
              if (List.length vars>1)||(consts==[]) then report_error no_pos ("unexpected share formula2: "^(Cprinter.string_of_b_formula (e,None)))
              else
                let c = List.fold_left (fun a c-> if (Ts.can_join a c) then Ts.join a c else raise Solver.Unsat_exception) (List.hd consts) (List.tl consts) in
                if vars=[] then ve,(tr_var v,c)::vc,j
                else ve,vc,(mkCperm c, mkVperm (List.hd vars), mkVperm v)::j)
         | _,_ -> report_error no_pos ("unexpected share formula3 "^(Cprinter.string_of_b_formula (e,None))))
      | _ -> report_error no_pos "unexpected non_equality") ([],[],[]) fl

let simpl fl =
  let pr1 = pr_list (fun c-> !CP.print_b_formula (c,None)) in
  let pe = pr_list (pr_pair (fun c->c) (fun c->c)) in
  let pc = pr_list (pr_pair (fun c->c) Ts.string_of) in
  let pre1 e = match e with | Solver.Vperm t-> t | Solver.Cperm t-> Ts.string_of t in
  let peq = pr_list (pr_triple pre1 pre1 pre1) in
  let pr2 = pr_triple pe pc peq in
  Debug.no_1(* _loop *) "simpl" pr1 pr2 simpl fl

let fv_eq_syst acc l =
  let f c = match c with | Solver.Vperm v-> [v] | Solver.Cperm _ -> [] in
  List.fold_left (fun a (e1,e2,e3)-> a@(f e1)@(f e2)@(f e3)) acc l

let sleek_sat_wrapper ((evs,f):CP.spec_var list * CP.p_formula list):bool =
  try
    let ve,vc,le = simpl f in
    let vc = (Perm.PERM_const.full_perm_name, Ts.top)::vc in
    let lv1 = List.fold_left (fun a (v1,v2)-> v1::v2::a) [] ve in
    let lv2 = List.fold_left (fun a (v,_)-> v::a) lv1 vc in
    let eqs = {
      Solver.eqs_ex = List.map tr_var evs ;
      Solver.eqs_nzv = Gen.BList.remove_dups_eq sv_eq (fv_eq_syst lv2 le);
      Solver.eqs_vc = vc;
      Solver.eqs_ve = ve;
      Solver.eqs_eql = le;} in
    Solver.is_sat eqs
  with | Solver.Unsat_exception -> false


let sleek_sat_wrapper (aevs,f) =
  let pr = pr_pair !CP.print_svl (pr_list (fun c-> !CP.print_b_formula (c,None))) in
  Debug.no_1(* _loop *) "sleek_sat_wrapper" pr string_of_bool sleek_sat_wrapper (aevs,f)

let sleek_imply_wrapper (aevs,ante) (cevs,conseq) =
  try
    let aevs =
      let afv = List.fold_left (fun a c-> a@ (CP.bfv (c,None))) [] ante in
      Gen.BList.intersect_eq CP.eq_spec_var aevs afv in
    let cevs =
      let cfv = List.fold_left (fun a c-> a@ (CP.bfv (c,None))) [] conseq in
      Gen.BList.intersect_eq CP.eq_spec_var cevs cfv in
    let ave,avc,ale = simpl ante in
    let avc = (Perm.PERM_const.full_perm_name, Ts.top)::avc in
    let alv = fv_eq_syst (List.fold_left (fun a (v,_)-> v::a) (List.fold_left (fun a (v1,v2)-> v1::v2::a) [] ave) avc) ale in
    let aeqs = {
      Solver.eqs_ex = List.map tr_var aevs ;
      Solver.eqs_nzv = Gen.BList.remove_dups_eq sv_eq alv;
      Solver.eqs_vc = avc;
      Solver.eqs_ve = ave;
      Solver.eqs_eql = ale;} in
    try
      let cve,cvc,cle = simpl conseq in
      let clv = fv_eq_syst (List.fold_left (fun a (v,_)-> v::a) (List.fold_left (fun a (v1,v2)-> v1::v2::a) [] cve) cvc) cle in
      let ceqs = {
        Solver.eqs_ex = List.map tr_var cevs ;
        Solver.eqs_nzv = Gen.BList.remove_dups_eq sv_eq clv;
        Solver.eqs_vc = cvc;
        Solver.eqs_ve = cve;
        Solver.eqs_eql = cle;} in
      Solver.imply aeqs ceqs
    with | Solver.Unsat_exception -> not (Solver.is_sat aeqs)
    with | Solver.Unsat_exception -> true

let sleek_imply_wrapper (aevs,ante) (cevs,conseq) =
  let pr = pr_pair !CP.print_svl (pr_list (fun c-> !CP.print_b_formula (c,None))) in
  Debug.no_2(* _loop *) "sleek_imply_wrapper" pr pr string_of_bool sleek_imply_wrapper (aevs,ante) (cevs,conseq)
