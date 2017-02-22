(* The following has just been copied straight from Cris's implementation,
   lines 1-9 of share_prove_w2.ml *)
#include "xdebug.cppo"
open Gen
open VarGen

(* let no_pos = no_pos *)
let report_error = Gen.report_error

module Ts = Tree_shares.Ts
module CP = Cpure
(* End copied *)

(* *********************** Begin new material *************************** *)
module CSE = Coq_solver_extract

module type SV =
sig 
  type t
  (*type t_spec*)
  (*val conv: t-> t_spec
    val rconv: t_spec -> t*)
  val eq: t->t->bool
  (* NEW *)
  val lt: t->t->bool
  val le: t->t->bool
  (* end NEW *)
  val string_of : t->string
  (*val string_of_s : t_spec->string*)
  val rename : t -> string -> t
  val get_name : t -> string
  (*val get_name_s : t_spec -> string*)
  val fresh_var : t -> t
  val var_of : string -> t
end

module Shim_SV (SV : SV) : CSE.SV with type t = SV.t =
struct
  type t = SV.t
  let t_eq_dec = SV.eq
  let t_ord = CSE.Build_Ord
  let t_lt_dec = SV.lt
  let t_leq_dec = SV.le
end

(* This is not very elegant but it gets the job done. *)
module Shim_solver = functor (SV : SV)->
struct
    type t_var = SV.t
    type const_sh = Tree_shares.Ts.t_sh
    type const_eq = t_var*const_sh
    type var_eq = t_var*t_var
    type frac_perm = 
      | Vperm of t_var 
      | Cperm of const_sh
    type eq = frac_perm * frac_perm * frac_perm
    type eq_syst = {
        eqs_ex : t_var list; 
        eqs_nzv : t_var list;
        eqs_vc : const_eq list;
        eqs_ve : var_eq list;
        eqs_eql : eq list;
   }

   (* None of these are raised by the certified solver, but they are expected to be in the module *)
   exception Unsat_exception
   exception Unsat_conseq of bool
    
   module CSV : CSE.SV with type t = SV.t = Shim_SV(SV)
   module CES = CSE.Equation_system(CSV)(CSE.Share_Domain)

   let rec tshare_hs2coq (s : Tree_shares.Ts.stree) : CSE.Share.coq_ShareTree =
      match s with
       | Tree_shares.Ts.Leaf b -> CSE.Share.Leaf b
       | Tree_shares.Ts.Node(s1, s2) -> CSE.Share.Node(tshare_hs2coq s1,tshare_hs2coq s2)

(*
    let rec tshare_coq2hs (s : CSE.Share.coq_ShareTree) : Tree_shares.Ts.stree = 
      match s with
       | CSE.Share.Leaf b -> Tree_shares.Ts.Leaf b
       | CSE.Share.Node(s1, s2) -> Tree_shares.Ts.Node(tshare_coq2hs s1,tshare_coq2hs s2)
*)
    
   let const_eq2Cequality (c : const_eq) : CES.equality =
     match c with (var,csh) ->
       (* let () = print_string ("CES.Vobject " ^ (SV.string_of var) ^ ";" ^ "CSE.Cobject " ^ (Tree_shares.Ts.string_of_tree_share csh) ^ "\n") in  *)
       (CSE.Vobject var, CSE.Cobject (tshare_hs2coq csh))

   let var_eq2Cequality (e : var_eq) : CES.equality =
     match e with (var1, var2) ->
       (* let () = print_string ("CES.Vobject " ^ (SV.string_of var2) ^ ";" ^ "CSE.Vobject " ^ (SV.string_of var2) ^ "\n") in  *)
       (CSE.Vobject var1, CSE.Vobject var2)
   
   let frac_perm2Ccoq_object (f : frac_perm) : CES.coq_object =
     match f with Vperm v -> CSE.Vobject v | Cperm c -> CSE.Cobject (tshare_hs2coq c)
     
   let eq2Cequation (e : eq) : CES.equation =
     match e with (fp1, fp2, fp3) -> ((frac_perm2Ccoq_object fp1, frac_perm2Ccoq_object fp2), frac_perm2Ccoq_object fp3)
   
   (* ~(v + 0 = 0) *)
   let nz2Cnequation (v : t_var) : CES.nequation =
     (* let () = print_string ("CSE.Vobject " (SV.string_of v)  ^ "\n") in *)
     (((CSE.Vobject v, CSE.Cobject (CSE.Share.Leaf false)), CSE.Cobject (CSE.Share.Leaf false)), ())
   
   let eq_syst2Csat_equation_system (eqs : eq_syst) : CES.sat_equation_system =
     {CES.sat_equalities = (List.map const_eq2Cequality (eqs.eqs_vc)) @ (List.map var_eq2Cequality (eqs.eqs_ve));
      CES.sat_equations = List.map eq2Cequation (eqs.eqs_eql);
      CES.sat_nequations = List.map nz2Cnequation (eqs.eqs_nzv) }
   
   let eq_syst2Cimpl_equation_system (eqs : eq_syst) : CES.impl_equation_system =
     let result = 
     {CES.impl_exvars = eqs.eqs_ex;
      CES.impl_equalities = (List.map const_eq2Cequality (eqs.eqs_vc)) @ (List.map var_eq2Cequality (eqs.eqs_ve));
      CES.impl_equations = List.map eq2Cequation (eqs.eqs_eql);
      CES.impl_nequations = List.map nz2Cnequation (eqs.eqs_nzv) }
     in
     let impl_exvars = result.impl_exvars in
     let impl_equalities = result.impl_equalities in
     (* let () = print_string ("impl_exvars: " ^ (List.fold_left (fun x y -> x ^ " " ^ (SV.string_of y)) "" impl_exvars) ^ "\n") in *)
     (* let impl_equlaities_str = List.fold_left (fun x y -> *)
     (*     let (CSE.Vobject var1, CSE.Cobject var2) = y in *)
     (*     x ^ " " ^ "(" ^ (SV.string_of var1) ^ "," ^ (Tree_shares.Ts.string_of_tree_share var2) ^ ")" ) "" impl_equalities in *)
  
     result
   
   module CBF = CSE.Bool_formula(CSV)
   module CBS = CSE.BF_solver(CSV)(CBF)
   module CSolver = CSE.Solver_with_partition(CSV)(CES)(CBF)(CBS)

   let counting (eq_syst:eq_syst) =
     let eqs_ex = eq_syst.eqs_ex in
     let eqs_nzv = eq_syst.eqs_nzv in
     let eqs_vc = eq_syst.eqs_vc in
     let eqs_ve = eq_syst.eqs_ve in
     let eqs_eql = eq_syst.eqs_eql in
     let () = Globals.total_vars_shim := !Globals.total_vars_shim + (List.length eqs_ex) + (List.length eqs_nzv) + (List.length eqs_vc) + 2 *(List.length eqs_ve) in
     let () = Globals.total_bot_top_shim := !Globals.total_bot_top_shim + 2 * (List.length eqs_nzv) in
     let () = Globals.total_constants_shim := !Globals.total_constants_shim + 2 * (List.length eqs_nzv) + (List.length eqs_vc) in
     let () = List.iter (fun (a,b) -> match b with
         | Tree_shares.Ts.Leaf true -> Globals.total_bot_top_shim := !Globals.total_bot_top_shim + 1
         | Tree_shares.Ts.Leaf false -> Globals.total_bot_top_shim := !Globals.total_bot_top_shim + 1
         | _ -> ()
       ) eqs_vc in
     let count_one x = match x with
       | Vperm var -> Globals.total_vars_shim := !Globals.total_vars_shim + 1
       | Cperm perm ->
         let () =  Globals.total_constants_shim := !Globals.total_constants_shim +  1 in
         (match perm with
         | Tree_shares.Ts.Leaf true -> Globals.total_bot_top_shim := !Globals.total_bot_top_shim + 1
         | Tree_shares.Ts.Leaf false -> Globals.total_bot_top_shim := !Globals.total_bot_top_shim + 1
         | _ -> ()
         )
     in
     let () = List.iter (fun (a,b,c) ->
       let () = count_one a in
       let () = count_one b in
       let () = count_one c in
       ()
     ) eqs_eql in
     ()
   
   let is_sat (eqs : eq_syst) : bool =
     CSolver.coq_SATsolver (eq_syst2Csat_equation_system eqs)
   
   let imply (a_sys : eq_syst) (c_sys : eq_syst) : bool =
     let a_sys_res = eq_syst2Cimpl_equation_system a_sys in
     let c_sys_res = eq_syst2Cimpl_equation_system c_sys in
     let res = CSolver.coq_IMPLsolver (a_sys_res, c_sys_res) in
     (* let () = print_string ("res: " ^ (string_of_bool res) ^ "\n") in *)
     res

   let str_frac_perm perm = match perm with
     | Vperm x -> SV.string_of x
     | Cperm y -> Tree_shares.Ts.string_of_tree_share y

   let str_eq_syst (eq_syst:eq_syst) : string =
     let eqs_ex = eq_syst.eqs_ex in
     let eqs_nzv = eq_syst.eqs_nzv in
     let eqs_vc = eq_syst.eqs_vc in
     let eqs_ve = eq_syst.eqs_ve in
     let eqs_eql = eq_syst.eqs_eql in
     let eqs_ex_str = List.fold_left (fun x y -> x ^ " " ^ (SV.string_of y)) "" eqs_ex in
     let eqs_nzv_str = List.fold_left (fun x y -> x ^ " " ^ (SV.string_of y)) "" eqs_nzv in
     let eqs_vc_str = List.fold_left (fun x y -> x ^ " " ^ "(" ^ (SV.string_of (fst y)) ^ "," ^ (Tree_shares.Ts.string_of_tree_share (snd y)) ^ ")" ) "" eqs_vc in
     let eqs_ve_str = List.fold_left (fun x y -> x ^ " " ^ "(" ^ (SV.string_of (fst y)) ^ "," ^ (SV.string_of (snd y)) ^ ")") "" eqs_ve in
     let eqs_eql_str = List.fold_left (fun x y ->
         let (a,b,c) = y in
         x ^ " " ^ (str_frac_perm a) ^ " " ^ (str_frac_perm b) ^ " " ^ (str_frac_perm c)) "" eqs_eql in
     "eqs_ex: " ^ eqs_ex_str ^ ";\n" ^
     "eqs_nzv: "^ eqs_nzv_str ^ ";\n" ^
     "eqs_vc: " ^ eqs_vc_str ^ ";\n" ^
     "eqs_ve:" ^ eqs_ve_str ^ ";\n" ^
     "eqs_eql: " ^ eqs_eql_str ^ "\n"


end

(* concrete SV *)
module Sv = 
struct
  type t=string
  (*type t_spec = string
    	let conv v=v
    	let rconv v=v*)
  let cnt = ref 1
  let eq v1 v2 = (String.compare v1 v2) = 0
  (* NEW *)
  let lt v1 v2 = (String.compare v1 v2) < 0
  let le v1 v2 = (String.compare v1 v2) <= 0
  (* end NEW *)
  let string_of v1 = v1
  (*let string_of_s v1 = v1
    	let get_name_s v = v*)
  let rename _ s = s
  let get_name v = v	
  let var_of v = v
  let fresh_var _ = cnt:=!cnt+1; "ts_fv_"^(string_of_int !cnt)    
end

module Solver = Shim_solver(Sv)
(* *********************** End new material *************************** *)

(* Everything above compiles without any trouble, except for the header from Cris's implementation. *)

(* The following has just been copied straight from Cris's implementation,
   lines 431-550 of share_prove_w2.ml *)
let tr_var v= CP.string_of_spec_var v
let sv_eq = Sv.eq

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
    let () = Solver.counting eqs in
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
    (* let () = print_string (Solver.str_eq_syst aeqs) in *)
    try
      let cve,cvc,cle = simpl conseq in
      let clv = fv_eq_syst (List.fold_left (fun a (v,_)-> v::a) (List.fold_left (fun a (v1,v2)-> v1::v2::a) [] cve) cvc) cle in
      let ceqs = {
        Solver.eqs_ex = List.map tr_var cevs ;
        Solver.eqs_nzv = Gen.BList.remove_dups_eq sv_eq clv;
        Solver.eqs_vc = cvc;
        Solver.eqs_ve = cve;
        Solver.eqs_eql = cle;} in
      (* let () = print_string (Solver.str_eq_syst ceqs) in *)
      let () = Solver.counting aeqs in
      let () = Solver.counting ceqs in
      Solver.imply aeqs ceqs
    with | Solver.Unsat_exception ->
      (* let () = print_string "second case \n" in *)
      not (Solver.is_sat aeqs)
  with | Solver.Unsat_exception ->
    (* let () = print_string "third case \n" in *)
    true

let sleek_imply_wrapper (aevs,ante) (cevs,conseq) =
  let pr = pr_pair !CP.print_svl (pr_list (fun c-> !CP.print_b_formula (c,None))) in
  Debug.no_2(* _loop *) "sleek_imply_wrapper" pr pr string_of_bool sleek_imply_wrapper (aevs,ante) (cevs,conseq)
