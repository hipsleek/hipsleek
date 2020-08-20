#include "xdebug.cppo"
(*
  15-06-2006
*)

open Globals
open VarGen
open Gen
open GlobProver
(* open Cpure *)
module CP = Cpure

let set_prover_type () = Others.last_tp_used # set Others.Mona
let set_proof_string str = Others.last_proof_string # set str
let set_proof_result str = Others.last_proof_result # set str

let is_mona_running = ref false
(* let channels = ref (stdin, stdout, stdin) *)
let last_test_number = ref 0
let test_number = ref 0
(* let mona_cycle = ref 10000 *)
let mona_cycle = ref 90
(* default timeout is 10 seconds *)
(* let mona_timeout = ref 5.0 *)
let mona_timeout = ref 10.0
let max_BUF_SIZE = 16384

let result_file_name = "res"
let log_all_flag = ref false
let log_all = open_log_out "allinput.mona"


let automaton_completed = ref false
let sat_optimize = ref false
let mona_pred_file = "mona_predicates.mona"
let mona_pred_file_alternative_path = "/usr/local/lib/"

(* let mona_prog = if !Globals.web_compile_flag then "/usr/local/bin/mona_inter" else "mona_inter" *)
let mona_prog = try FileUtil.which "mona_inter" with Not_found -> ""

let process = ref {name = "mona"; pid = 0;  inchannel = stdin; outchannel = stdout; errchannel = stdin}

let string_of_hashtbl tab = Hashtbl.fold
    (fun c1 c2 a ->
       a^"; ("^(Cprinter.string_of_spec_var c1)^" "^
       (string_of_int c2) ^")") tab ""

(* pretty printing for primitive types *)
let rec mona_of_typ t = match t with
  | Bool          -> "int"
  | Tree_sh 	  -> "int"
  | Float         -> 
    (* "float"	(\* Can I really receive float? What do I do then? I don't have float in Mona. *\) *)
    Error.report_error {Error.error_loc = no_pos; 
                        Error.error_text = "float type not supported for mona"}
  | Int           -> "int"
  | INFInt        -> "int"
  | AnnT          -> "AnnT"
  | RelT _        -> "RelT"
  | FuncT _       -> "FuncT"
  | UtT b        -> "UtT("^(string_of_bool b)^")"
  | HpT           -> "HpT"
  | Void          -> "void" 	(* same as for float *)
  | BagT i		  -> "("^(mona_of_typ i)^") set"
  | TVar i        -> "TVar["^(string_of_int i)^"]"
  | UNK |FORM | Tup2 _         ->
    Error.report_error {Error.error_loc = no_pos; 
                        Error.error_text = ("unexpected type for mona: "^(string_of_typ t))}
  | List t        -> "("^(mona_of_typ t)^") list"	(* lists are not supported *)
  | NUM | Named _ | Array _ (* | SLTyp *) ->
    Error.report_error {Error.error_loc = no_pos; 
                        Error.error_text = "array and named type not supported for mona"}
  | Pointer _ ->
    Error.report_error {Error.error_loc = no_pos; 
                        Error.error_text = "pointer type not supported for mona"}
  | Bptyp ->
    Error.report_error {Error.error_loc = no_pos; 
                        Error.error_text = "Bptyp type not supported for mona"}

(*------------------------------------------*)
let rec mkEq l = match l with
  | e :: [] -> CP.BForm(e,None)
  | e :: rest -> CP.And(CP.BForm(e,None), (mkEq rest), no_pos)
  | _ -> assert false

let rec mkEx l f = match l with
  | [] -> f
  | sv :: rest -> mkEx rest (CP.Exists(sv, f, None, no_pos))

(*

  ALG for deciding between 1st-order and 2nd-order variables
  I  -  generate constraints which can have any of the below forms
        1. var1 = var2 
        2. var = const, where const can be 
              1 --> 1st order (var1), 
              2 --> 2nd order (var2)
              0 --> unknown
  II  - verify if the generated constraints are satisfiable
  III - solve the constraints
*)

type order_atom =
  | MO_Var of CP.spec_var * int
  | MO_EQ of CP.spec_var * CP.spec_var
  (* | MO_True *)
(* | MO_False *)

let is_mo_var ord_atom =
  match ord_atom with
  | MO_Var _ -> true
  | MO_EQ  _ -> false

let eq_order_atom a1 a2 =
  match a1, a2 with
  | MO_Var (sv1,o1), MO_Var (sv2,o2)   -> (CP.eq_spec_var sv1 sv2) && (o1 = o2)
  | MO_EQ (sv11,sv12), MO_EQ (sv21,sv22) -> (CP.eq_spec_var sv11 sv12) && (CP.eq_spec_var sv21 sv22)
  | _ -> false

let order_atom_contains_var ord_atom sv =
  match ord_atom with
  | MO_Var (v, _)   ->  CP.eq_spec_var sv v
  | MO_EQ  (v1, v2) -> (CP.eq_spec_var sv v1) || (CP.eq_spec_var sv v2)

let get_lhs_order_atom ord_atom =
  match ord_atom with
  | MO_Var (v, _) 
  | MO_EQ  (v, _) -> v

let get_mo_vars ord_atom =
  match ord_atom with
  | MO_EQ (v1, v2) -> (v1, v2)
  | MO_Var  _       -> failwith ("[mona.ml] should only call det_mo_vars on mo_eq")

let is_first_order_atom_constraint ord_atom =
  match ord_atom with
  | MO_Var (_, i)   ->  i == 1
  | MO_EQ  _ -> false

let is_unk_order_atom_constraint ord_atom =
  match ord_atom with
  | MO_Var (_, i)   ->  i == 0
  | MO_EQ  _ -> false

let string_of_order_atom a =
  match a with
  | MO_Var(sv,i) -> ((CP.string_of_spec_var sv) ^ "=" ^ (string_of_int i))
  | MO_EQ(sv1,sv2) -> ((CP.string_of_spec_var sv1) ^ "=" ^ (CP.string_of_spec_var sv2 ))

let mkMO_Var sv (order: int option) =
  match order with
  | Some i -> [MO_Var(sv,i)]
  | None   -> []

let same_order_lst aux el (* (order: int option) *) =
  let (rr,cc) as result = 
    List.fold_left (fun (r2,c2) b -> 
        let (r1,c1,_) = aux b in
        match r1,r2 with
        | (None,_) -> (r2,c1@c2) 
        | (_,None) -> (r1,c1@c2) 
        | (Some v1,Some v2) ->  
          (* let new_c = mkMO_Var v1 order in *)
          (r1, MO_EQ(v1,v2)::(* new_c@ *)c1@c2) 
      ) (None,[]) el in
  result

(* let force_order_lst_opt aux el order = *)
(*   same_order_lst aux el (Some order) *)

let force_order_lst aux el order =
  let (rr,cc) as result = same_order_lst aux el in
  match rr with
  | None -> result
  | Some v -> (rr, MO_Var(v,order)::cc)

let compute_order_exp (f:CP.exp) : (CP.spec_var option) * order_atom list * int = 
  (* (None,[]) *)
  let rec aux e = match e with
    | CP.Var(sv, l) -> (Some sv,[], 0)
    | CP.Subtract (e1, e2, _) 
    | CP.Mult(e1, e2, _)
    | CP.Div(e1, e2, _)
    | CP.Max(e1, e2, _)
    | CP.Min(e1, e2, _) 
    | CP.Add (e1, e2, _) ->  let (r,c) = force_order_lst aux [e1;e2] 0 in (r, c, 0) (* should return r so that the 
                                                                                       result of the operation would have teh same type as the operands *)
    | CP.Bag(el, _) 
      -> let (r,c) = force_order_lst aux el 1 in (None, c, 2)
    | CP.BagUnion(el, _) 
    | CP.BagIntersect(el, _) -> let (r,c) =  force_order_lst aux el 2 in (None, c, 2)
    | CP.BagDiff(e1, e2, _) -> let (r,c) =  force_order_lst aux [e1;e2] 2 in (None, c, 2)
    | CP.ListCons _
    | CP.List _
    | CP.ListAppend _
    | CP.ListHead _
    | CP.ListTail _
    | CP.ListLength _
    | CP.ListReverse _ -> failwith ("Lists are not supported in Mona")
    | CP.ArrayAt _ -> failwith ("Mona does not handle arrays!")
    | _ -> (None, [],0)                   (* null and iconst *)
  in aux f


let force_order_exp (f:CP.exp) order : (CP.spec_var option) * order_atom list * int = 
  let (r, c, exp_ord) as result = compute_order_exp f in
  match r with
  | None -> result
  | Some v -> 
    if not(order == 0) then (r,MO_Var(v,order)::c, exp_ord)
    else (r,c, exp_ord)

let force_eq_exp (f:CP.exp) (sv: CP.spec_var option) : (CP.spec_var option) * order_atom list * int = 
  let (r, c, exp_ord) as result = compute_order_exp f in
  match r, sv with
  | Some v, Some sv -> (r,MO_EQ(v,sv)::c, exp_ord)
  | _ -> result

let compute_order_b_formula (bf:CP.b_formula) : order_atom list = 
  let (pf,_) = bf in
  match pf with
  | CP.BagNotIn(sv1, e1, _)
  | CP.BagIn(sv1, e1, _) ->
    let (_,cl,_) = force_order_exp e1 2 in
    MO_Var(sv1,1)::cl
  | CP.BagMax(sv1, sv2, _) 
  | CP.BagMin(sv1, sv2, _) ->
    MO_Var(sv1,1)::[MO_Var(sv2,2)]
  | CP.BagSub(e1, e2, _) -> 
    let (r2, c2, _) = force_order_exp e2 2 in
    let (_, c1, _) = force_eq_exp e1 r2 in
    c1@c2
  | CP.ListIn _
  | CP.ListNotIn _
  | CP.ListAllN _
  | CP.ListPerm _ -> failwith ("Lists are not supported in Mona")
  | CP.Lt(e1, e2, _)
  | CP.Lte(e1, e2, _) 
  | CP.SubAnn(e1, e2, _ )
  | CP.Gt(e1, e2, _)
  | CP.Gte(e1, e2, _)  
  | CP.Eq(e1, e2, _)
  | CP.Neq(e1, e2, _) -> 
    let (r2, c2, ord) = compute_order_exp e2 in
    let (_, c1, _) = if (ord != 0) then force_order_exp e1 ord 
      else force_eq_exp e1 r2 in
    c1@c2
  | CP.EqMax(e1, e2, e3, _)
  | CP.EqMin(e1, e2, e3, _) -> 
    let (r2, c2, ord2) = compute_order_exp e2 in
    let (r1, c1, ord1) = if not(ord2 == 0) then force_order_exp e1 ord2 
      else force_eq_exp e1 r2 in
    let ord = if (ord1 <= ord2) then ord2 else ord1 in
    let (r3, c3, _) = if not(ord == 0) then force_order_exp e3 ord 
      else force_eq_exp e3 r1 in
    c1@c2@c3
  | CP.BVar(sv1, l1) ->  
    [MO_Var(sv1,2)]
  | CP.BConst(b, loc) -> []
  | CP.RelForm (_ , el, _) -> List.flatten (List.map (fun e -> let (_,c,_) = compute_order_exp e in c) el)
  | _ -> failwith ("compute_order_b_formula not supporting :" ^(Cprinter.string_of_b_formula bf))


let compute_order_formula_x (f:CP.formula) : order_atom list = 
  let rec aux f =
    match f with
    | CP.And(f1, f2, _)
    | CP.Or(f1, f2, _,_) -> (aux f1)@(aux f2)
    | CP.Forall(_, f1, _,_)
    | CP.Exists(_, f1, _,_)
    | CP.Not(f1, _,_) -> (aux f1)
    | CP.AndList b -> List.concat (List.map (fun (_,e) -> aux e) b)
    | CP.BForm(bf,_) -> (compute_order_b_formula bf)
  in aux f

let compute_order_formula (f:CP.formula) : order_atom list = 
  let pr_out = pr_list string_of_order_atom in
  Debug.no_1 "compute_order_formula" pr_none pr_out compute_order_formula_x f

let get_order var1_lst var2_lst sv =
  if (List.exists (CP.eq_spec_var sv) var1_lst) then 1 (* 1st order *)
  else if (List.exists (CP.eq_spec_var sv) var2_lst) then 2 (* 2nd order *)
  else 0                                                    (* unknown *)

let replace_known var1_lst var2_lst unk_lst (c:order_atom): order_atom = 
  match c with
  | MO_Var _ -> c (*should not reach this*)
  | MO_EQ  (sv1, sv2) -> 
    if (List.exists (CP.eq_spec_var sv1) unk_lst ) then 
      if (List.exists (CP.eq_spec_var sv2) unk_lst ) then c
      else 
        let order = get_order var1_lst var2_lst sv2 in
        MO_Var (sv1, order)
    else
      let order = get_order var1_lst var2_lst sv1 in
      MO_Var (sv2, order)

(* 
   @deprecated
   1. separate the constraints into two differnet lists: list1 for "var = const" constraints and list2 for "var = var"
   2. compute the lists containing 1st order and 2nd order vars, respectively (from list1)
   3. compute the list containing unknown order vars 
   4. if the new list of unknown order vars did not change ===> fix-point;
       otherwise go to step 5
   5. remove redundand constraints from list2 (known order var = known order var)
   6. update list2 so that known order variables are replaced by their numeric order in all their occurances in list2
   7. repeat step 1-4
 *)

let solve_constraints_x (cons: order_atom list) (sv_lst: CP.spec_var list)=
  (* let unk_no = List.length sv_lst in *)

  let rec aux var1_lst var2_lst unk_lst cons =
    let cons = Gen.BList.remove_dups_eq eq_order_atom cons in 
    let mo_var_constr, eq_var_constr = List.partition is_mo_var cons in
    let var1_constr, var2_constr = List.partition is_first_order_atom_constraint mo_var_constr in 
    let var1_lst0 = List.map get_lhs_order_atom var1_constr in
    let var1_lst = var1_lst@var1_lst0 in
    (* let pr = pr_list string_of_order_atom in *)
    (* let () = x_tinfo_hp (add_str "cons" pr) cons no_pos in *)
    (* let () = x_tinfo_hp (add_str "mo_var_constr" pr) mo_var_constr no_pos in *)
    (* let () = x_tinfo_hp (add_str "var1_constr" pr) var1_constr no_pos in *)
    (* let pr = pr_list Cprinter.string_of_spec_var in *)
    (* let () = x_tinfo_hp (add_str "var1_lst" pr) var1_lst no_pos in *)
    let var2_lst0 = List.map get_lhs_order_atom var2_constr in
    let var2_lst = var2_lst@var2_lst0 in
    let new_unk_lst = Gen.BList.difference_eq CP.eq_spec_var unk_lst (var1_lst@var2_lst) in
    if (List.length new_unk_lst =  List.length unk_lst) then 
      (var1_lst, var2_lst, unk_lst)
    else
      (* filter redundant constraints *)
      let eq_var_constr = List.filter (fun c -> List.exists (order_atom_contains_var c) new_unk_lst) eq_var_constr in
      let new_constr = List.map (replace_known var1_lst var2_lst new_unk_lst) eq_var_constr in
      aux var1_lst var2_lst new_unk_lst new_constr
  in
  aux [] [] sv_lst cons

let solve_constraints (cons: order_atom list) (sv_lst: CP.spec_var list)=
  let pr_1 = pr_list string_of_order_atom in
  let pr_2 = pr_list Cprinter.string_of_spec_var in
  let pr_out = pr_triple pr_2 pr_2 pr_2 in
  Debug.no_2 "solve_constraints" pr_1 pr_2 pr_out solve_constraints_x cons sv_lst 

let mkConstraint (constr: order_atom): CP.formula =
  let l,r = 
    match constr with
    | MO_Var (sv,order) -> CP.Var(sv,no_pos), CP.IConst(order, no_pos)
    | MO_EQ  (sv1,sv2)  -> CP.Var(sv1,no_pos), CP.Var(sv2,no_pos) in
  CP.BForm ((CP.Eq(l,r,no_pos),None), None)

(* let mkConstrLabel (constr: order_atom) =  *)
(*   let bf = mkConstraint constr in *)
(*   (LO.unlabelled, bf)  *)

let is_intersect_non_empty lst1 lst2 = 
  not(Gen.is_empty (Gen.BList.intersect_eq CP.eq_spec_var lst1 lst2)) 

let sat_constraints_x cons = 
  let mo_var_constr, eq_var_constr = List.partition is_mo_var cons in
  let eq_var_constr = List.map get_mo_vars eq_var_constr in
  let emap = CP.EMapSV.build_eset eq_var_constr in
  let epart = CP.EMapSV.partition emap in 
  let var1_constr, var2_constr = List.partition is_first_order_atom_constraint mo_var_constr in 
  let var1_lst = List.map get_lhs_order_atom var1_constr in
  let var2_lst = List.map get_lhs_order_atom var2_constr in
  let not_sat = List.exists (fun elist ->  is_intersect_non_empty elist var1_lst  &&  is_intersect_non_empty elist var2_lst) epart in
  if (not_sat) then 
    (not_sat, var1_lst, var2_lst)
  else
    let var1_lst, var2_lst = List.fold_left (fun (l1,l2) elist -> 
        if (is_intersect_non_empty elist l1) then (l1@elist,l2)
        else if (is_intersect_non_empty elist l2) then (l1, elist@l2)
        else (l1,l2)
      ) (var1_lst, var2_lst) epart in 
    (not(not_sat), var1_lst, var2_lst)

let sat_constraints (cons: order_atom list)=
  let pr_1 = pr_list string_of_order_atom in
  let pr_2 = pr_list Cprinter.string_of_spec_var in
  let pr_out = pr_triple string_of_bool pr_2 pr_2 in
  Debug.no_1 "sat_constraints" pr_1 pr_out sat_constraints_x cons


let new_order_formula_x (f:CP.formula) : (CP.spec_var list * CP.spec_var list * CP.spec_var list) =
  let cl = compute_order_formula f in
  let cl = List.filter (fun c -> not (is_unk_order_atom_constraint c)) cl in (* filter out constraints like MO_Var(v,0) *)
  let all_vars = CP.all_vars f in
  (* let constr = CP.join_conjunctions (List.map mkConstraint cl) in *)
  (* let sat = Timelog.logtime_wrapper "mona-om" (Omega.is_sat constr) "mona constraints" in  *)  
  let (sat, l1, l2) = sat_constraints cl in
  if (not sat) then
    failwith ("[mona.ml:new_order_formula] mona translation failure")
  else
    let lunk =  Gen.BList.difference_eq CP.eq_spec_var all_vars (l1@l2) in
    (* let l1,l2,lunk = solve_constraints cl all_vars in *)
    let l2 = l2@lunk in             (* consider unknown vars as 2nd order vars *)
    (l1,l2,lunk)

let new_order_formula (f:CP.formula) : (CP.spec_var list * CP.spec_var list * CP.spec_var list) =
  let pr_out = pr_list Cprinter.string_of_spec_var in
  Debug.no_1 "new_order_formula" pr_none (pr_triple pr_out pr_out pr_out) new_order_formula_x f
(*

  PREPROCESSING:

  - In monadic 2nd order logic, first-order variables denote natural numbers, which can be compared and subjected to addition with only constants (not other vars). 
  - Consequently, for non monadic formulae, we use the set representation, e.g. the addition a1 = a2 + a3 is written as plus(a2, a3, a1).

  - The preprocessing will substitute the non monadic formulae by a fresh var, and add a new constraint.
  Ex: a2+a3 are substituted by a fresh_var and a new constraint fresh_var=a2+a3 is added. 

*)

(* 
   Preprocessing expressions 
*)
let rec preprocess_exp (e0 : CP.exp) : (CP.exp * CP.formula * CP.spec_var list) = 
  let reconstr_2arg a1 a2 f l =
    let (e1, constr1, ev1) = preprocess_exp a1 in
    let (e2, constr2, ev2) = preprocess_exp a2 in
    ((f e1 e2 l), (CP.mkAnd constr1 constr2 l), ev1@ev2)
  in   
  match e0 with
  | CP.Add(CP.Var(CP.SpecVar(t1, _, _), l1), CP.Var(CP.SpecVar(_, _, _), _), l3) 
  | CP.Add(CP.IConst(_, _), CP.Var(CP.SpecVar(t1, _, _), l1) , l3)
  | CP.Add( CP.Var(CP.SpecVar(t1, _, _), l1), CP.IConst(_, _), l3) ->
    let tmp = fresh_var_name (string_of_typ t1) l3.start_pos.Lexing.pos_lnum in
    let new_evar = CP.SpecVar(t1, tmp, Unprimed) in
    let additional_constr = CP.BForm((CP.Eq(CP.Var(new_evar, no_pos), e0, l3), None), None) in
    (CP.Var(new_evar, l3), additional_constr, [new_evar])
  | CP.Subtract(CP.Var(CP.SpecVar(t1, id1, p1), l1), CP.Var(CP.SpecVar(t2, id2, p2), l2), l3) ->
    let tmp = fresh_var_name (string_of_typ t1) l3.start_pos.Lexing.pos_lnum in
    let new_evar = CP.SpecVar(t1, tmp, Unprimed) in
    let additional_constr = CP.BForm((CP.Eq(CP.Var(new_evar, no_pos), CP.Add(CP.Var(CP.SpecVar(t1, tmp, p1), l1), CP.Var(CP.SpecVar(t2, id2, p2), l2), l3), l3), None), None) in
    (CP.Var(new_evar, l3), additional_constr, [new_evar])
  | CP.Subtract( CP.Var(CP.SpecVar(t2, id2, p2), l2), CP.IConst(i1, l1), l3) ->
    let tmp = fresh_var_name (string_of_typ t2) l3.start_pos.Lexing.pos_lnum in
    let new_evar = CP.SpecVar(t2, tmp, Unprimed) in
    let additional_constr = CP.BForm((CP.Eq(CP.Var(new_evar, no_pos), CP.Add(CP.IConst(i1, l1), CP.Var(CP.SpecVar(t2, tmp, p2), l2), l3), l3), None), None) in
    (CP.Var(new_evar, l3), additional_constr, [new_evar])
  | CP.Subtract( CP.IConst(i1, l1), CP.Var(CP.SpecVar(t2, id2, p2), l2), l3) ->
    let tmp = fresh_var_name (string_of_typ t2) l3.start_pos.Lexing.pos_lnum in
    let new_evar = CP.SpecVar(t2, tmp, Unprimed) in
    let additional_constr = CP.BForm((CP.Eq(CP.IConst(i1, l1), CP.Add(CP.Var(CP.SpecVar(t2, id2 , p2), l2), CP.Var(CP.SpecVar(t2, tmp, p2), l2), l3), l3), None), None) in
    (CP.Var(new_evar, l3), additional_constr, [new_evar])
  | CP.Add(CP.IConst(i1, _), CP.IConst(12, _) , l3) -> (CP.IConst(i1+12, l3), CP.BForm((CP.BConst (true, l3), None), None), [])
  | CP.Subtract( CP.IConst(i1, l1), CP.IConst(i2, l2), l3) ->
    let tmp = fresh_var_name "int" l3.start_pos.Lexing.pos_lnum in
    let new_evar = CP.SpecVar(Int, tmp, Unprimed) in
    let additional_constr = CP.BForm((CP.Eq(CP.IConst(i1, l1), CP.Add(CP.IConst(i2, l2), CP.Var(CP.SpecVar(Int, tmp, Unprimed), l3), l3), l3), None), None) in
    (CP.Var(new_evar, l3), additional_constr, [new_evar])
  | CP.Add (a1, a2, l1) -> 
    reconstr_2arg a1 a2 (fun e1 e2 l -> CP.Add(e1, e2, l)) l1
  | CP.Subtract(a1, a2, l1) -> 
    reconstr_2arg a1 a2 (fun e1 e2 l -> CP.Subtract(e1, e2, l)) l1
  | CP.Min (a1, a2, l1) ->  
    reconstr_2arg a1 a2 (fun e1 e2 l -> CP.Min(e1, e2, l)) l1
  | CP.Max (a1, a2, l1) ->  
    reconstr_2arg a1 a2 (fun e1 e2 l -> CP.Max(e1, e2, l)) l1
  | _ -> (e0,CP.BForm((CP.BConst (true, no_pos), None), None), [])


(* 
   Preprocessing boolean formulae 
*)
and preprocess_b_formula b : (CP.b_formula * CP.formula * CP.spec_var list) =
  let reconstr_2arg a1 a2 f l =
    let (e1, constr1, ev1) = preprocess_exp a1 in
    let (e2, constr2, ev2) = preprocess_exp a2 in
    ((f e1 e2 l), (CP.mkAnd constr1 constr2 l), ev1@ev2)
  in   
  let reconstr_3arg a1 a2 a3 f l =
    let (e1, constr1, ev1) = preprocess_exp a1 in
    let (e2, constr2, ev2) = preprocess_exp a2 in
    let (e3, constr3, ev3) = preprocess_exp a3 in
    ((f e1 e2 e3 l), (CP.mkAnd (CP.mkAnd constr1 constr2 l) constr3 l), ev1@ev2@ev3)
  in    
  let (pf,il) = b in
  let (npf, constr, ev)  = match pf with
    | CP.Lt (a1, a2, l1) -> 
      reconstr_2arg a1 a2 (fun e1 e2 l1 -> CP.Lt(e1, e2, l1)) l1
    | CP.Lte (a1, a2, l1) -> 
      reconstr_2arg a1 a2 (fun e1 e2 l1 -> CP.Lte(e1, e2, l1)) l1
    | CP.Gt (a1, a2, l1) -> 
      reconstr_2arg a1 a2 (fun e1 e2 l1 -> CP.Gt(e1, e2, l1)) l1
    | CP.Gte (a1, a2, l1) -> 
      reconstr_2arg a1 a2 (fun e1 e2 l1 -> CP.Gte(e1, e2, l1)) l1
    | CP.Eq(a1, a2, l1) -> 
      reconstr_2arg a1 a2 (fun e1 e2 l1 -> CP.Eq(e1, e2, l1)) l1
    | CP.Neq(a1, a2, l1) -> 
      reconstr_2arg a1 a2 (fun e1 e2 l1 -> CP.Neq(e1, e2, l1)) l1
    | CP.EqMin (a1, a2, a3, l1) -> 
      reconstr_3arg a1 a2 a3 (fun e1 e2 e3 l1 -> CP.EqMin(e1, e2, e3, l1)) l1
    | CP.EqMax (a1, a2, a3, l1) -> 
      reconstr_3arg a1 a2 a3 (fun e1 e2 e3 l1 -> CP.EqMax(e1, e2, e3, l1)) l1
    | _ -> (pf, CP.BForm((CP.BConst (true, no_pos), None), None), []) 
  in 
  ((npf,il), constr, ev)


(* 
   Preprocessing formulae 
*)
and preprocess_formula_x pr_w pr_s (f : CP.formula) : CP.formula =
  let rec helper f = 
    match f with
    | CP.Or (p1, p2,lbl, l1) -> (CP.mkOr (helper p1) (helper p2) lbl l1)
    | CP.And (p1, p2, l1) -> (CP.mkAnd (helper p1) (helper p2) l1)
    | CP.AndList b -> CP.AndList (Gen.map_l_snd helper b)
    | CP.Not (p1,lbl, l1) -> CP.Not((preprocess_formula pr_s pr_w p1),lbl, l1)
    | CP.Forall(sv1, p1,lbl, l1) -> CP.Forall(sv1, (helper p1),lbl, l1)
    | CP.Exists(sv1, p1,lbl, l1) -> CP.Exists(sv1, (helper p1),lbl, l1)
    | CP.BForm ((b,_) as bf,lbl) -> 		
      begin
        match (pr_w b) with
        | None -> 
          let (bf, constr, ev) = preprocess_b_formula bf in
          (mkEx ev (CP.mkAnd (CP.BForm(bf, lbl)) constr no_pos))
        | Some f -> helper f
      end
  in helper f

and preprocess_formula pr_w pr_s (f : CP.formula) : CP.formula =
  Debug.no_1 "preprocess_formula"
    Cprinter.string_of_pure_formula 
    Cprinter.string_of_pure_formula
    (fun f -> preprocess_formula_x pr_w pr_s f) f

(* 

   HASH TABLE CONSTRUCTION:
   This hash table maps each var to:
   0 - unknown (unconstrained)
   1 - first order
   2 - second order

*)

and find_order_x (f : CP.formula) vs = 
  let r = find_order_formula f vs in
  if r then (find_order_x f vs) 
(*keep finding until reach fixed point*)

and find_order (f : CP.formula) vs = 
  let lst = Hashtbl.fold (fun k v acc -> (k, v) :: acc) vs [] in
  let lst = List.sort (fun (k1,v1) (k2,v2) -> v2-v1 ) lst in
  let pr_out a = pr_list (fun (k,v) -> ((Cprinter.string_of_spec_var k)^" " ^(string_of_int v)) ) lst in
  Debug.no_eff_2 "find_order" [false;true]
    Cprinter.string_of_pure_formula string_of_hashtbl pr_out
    find_order_x f vs

and find_order_formula (f : CP.formula) vs : bool  = match f with
  | CP.And(f1, f2, _)
  | CP.Or(f1, f2, _,_) -> ((find_order_formula f1 vs) || (find_order_formula f2 vs))
  (* make sure everything is renamed *)
  | CP.Forall(_, f1, _,_)
  | CP.Exists(_, f1, _,_)
  | CP.Not(f1, _,_) -> (find_order_formula f1 vs)
  | CP.AndList b -> List.exists (fun (_,c)-> find_order_formula c vs) b
  | CP.BForm(bf,_) -> (find_order_b_formula bf vs)

and exp_order e vs =
  match e with
  | CP.Null _ -> 0 (* leave it unknown 0*)
  | CP.Var(sv, l) ->
    begin
      try
        Hashtbl.find vs sv
      with
      | Not_found ->  (Hashtbl.add vs sv 0;0) (* TO CHECK: 0 or 1*)
    end
  | CP.Add (e1, e2, l1) 
  | CP.Subtract (e1, e2, l1) ->
    let r1 = exp_order e1 vs in
    let r2 = exp_order e2 vs in
    if (r1 == 0) then r2
    else 
    if(r2 == 0) then r1
    else 
    if (r1 != r2) then Error.report_error { Error.error_loc = l1; Error.error_text = ("Mona translation failure \n")}
    else r1
  | CP.Mult _
  | CP.Max _
  | CP.Min _
  | CP.Div _ -> 1
  | CP.Bag _ 
  | CP.BagUnion _
  | CP.BagIntersect _
  | CP.BagDiff _ -> 2
  | _ -> 0

and find_order_b_formula_x (bf : CP.b_formula) vs : bool =
  let (pf,_) = bf in
  match pf with
  | CP.BagNotIn(sv1, e1, l1)
  | CP.BagIn(sv1, e1, l1) ->
    let rsv1 = 
      try
        let r = Hashtbl.find vs sv1 in
        if (r == 2) then 
          Error.report_error { Error.error_loc = l1; Error.error_text = ("Mona translation failure for variable " ^ (Cprinter.string_of_spec_var sv1) ^ "\n")}
        else 
          begin
            if (r == 0) then
              ((Hashtbl.replace vs sv1 1); true)
            else false
          end
      with
      | Not_found -> ((Hashtbl.add vs sv1 1); true)
      | _ -> false
    in
    rsv1 || (find_order_exp e1 2 vs)
  | CP.BagMax(sv1, sv2, l1) 
  | CP.BagMin(sv1, sv2, l1) ->
    let r1 = 
      try
        let r = Hashtbl.find vs sv1 in
        if (r == 2) then 
          Error.report_error { Error.error_loc = l1; Error.error_text = ("Mona translation failure for variable " ^ (Cprinter.string_of_spec_var sv1) ^ " in BagMin 1\n")}
        else 
        if (r == 0) then ((Hashtbl.replace vs sv1 1); true)
        else false
      with
      | Not_found -> ((Hashtbl.add vs sv1 1); true)
    in
    let r2 = 
      try
        let r = Hashtbl.find vs sv2 in
        if (r == 1) then 
          Error.report_error { Error.error_loc = l1; Error.error_text = ("Mona translation failure for variable " ^ (Cprinter.string_of_spec_var sv2) ^ "in BagMin 2\n")}
        else 
        if(r == 0) then ((Hashtbl.replace vs sv1 2); true)
        else
          false
      with
      | Not_found -> ((Hashtbl.add vs sv1 2); true)
    in
    (r1 || r2)
  | CP.BagSub(e1, e2, _) ->  ((find_order_exp e1 2 vs) || (find_order_exp e2 2 vs)) 
  | CP.ListIn(e1, e2, _)
  | CP.ListNotIn(e1, e2, _) 
  | CP.ListAllN(e1, e2, _)
  | CP.ListPerm(e1, e2, _)
  | CP.Lt(e1, e2, _)
  | CP.Lte(e1, e2, _) 
  | CP.SubAnn(e1, e2, _ )
  | CP.Gt(e1, e2, _)
  | CP.Gte(e1, e2, _) -> 
    (* let () = print_string("find_order_exp for e1=" ^ (Cprinter.string_of_formula_exp e1) ^ " and e2="  ^ (Cprinter.string_of_formula_exp e2) ^ "\n") in *)
    let r1 = exp_order e1 vs in 
    let r2 = exp_order e2 vs in
    if (r1 == 1 || r2 == 1) then
      ((find_order_exp e1 1 vs) || (find_order_exp e2 1 vs)) 
    else
      ((find_order_exp e1 0 vs) || (find_order_exp e2 0 vs)) 
  | CP.EqMax(e1, e2, e3, _)
  | CP.EqMin(e1, e2, e3, _) -> 
    let r1 = exp_order e1 vs in
    let r2 = exp_order e2 vs in
    let r3 = exp_order e3 vs in
    if (r1 == 1 || r2 == 1 || r3 == 1) then
      ((find_order_exp e1 1 vs) || (find_order_exp e2 1 vs) || (find_order_exp e3 1 vs)) 
    else
      ((find_order_exp e1 0 vs) || (find_order_exp e2 0 vs) || (find_order_exp e3 0 vs)) 
  | CP.BVar(sv1, l1) -> 
    begin
      try 
        let r = Hashtbl.find vs sv1 in
        if(r == 1) then
          Error.report_error { Error.error_loc = l1; Error.error_text = ("Mona translation failure for variable " ^ (Cprinter.string_of_spec_var sv1) ^ " in BVar \n")}
        else
        if(r == 0) then
          (Hashtbl.replace vs sv1 2; true)
        else false
      with
      | Not_found -> (Hashtbl.add vs sv1 2; true)
    end
  | CP.Eq(e1, e2, _)
  | CP.Neq(e1, e2, _) ->
    let r1 = exp_order e1 vs in
    let r2 = exp_order e2 vs in
    if (CP.is_bag e1) || (CP.is_bag e2) || (r1 == 2) || (r2 == 2) then
      ((find_order_exp e1 2 vs) || (find_order_exp e2 2 vs)) 
    else 
    if (r1 == 1 || r2 == 1) then
      ((find_order_exp e1 1 vs) || (find_order_exp e2 1 vs)) 
    else
      ((find_order_exp e1 0 vs) || (find_order_exp e2 0 vs)) 
  | CP.RelForm (_ , el, l) -> List.fold_left (fun a b -> a || (find_order_exp b 0 vs)) false el
  | _ -> false

and find_order_b_formula (bf : CP.b_formula) vs : bool =
  Debug.no_2 "find_order_b_formula" 
    Cprinter.string_of_b_formula string_of_hashtbl string_of_bool
    find_order_b_formula_x bf vs

(*
  order = 0 --> unknown (* TO CHECK: is it considered first or second order ??? *)
  = 1 --> inside bag
  = 2 --> bag
*)
and find_order_exp_x (e : CP.exp) order vs = match e with
  | CP.Var(sv1, l1) -> 
    begin
      try
        let r = Hashtbl.find vs sv1 in 
        if (r == 0 && order != 0) then
          ((Hashtbl.replace vs sv1 order); true) 
        else
        if ((r == 1 && order == 2) || (r == 2 && order == 1)) then
          Error.report_error { Error.error_loc = l1; Error.error_text = ("Mona translation failure for variable " ^ (Cprinter.string_of_spec_var sv1) ^ " in Var \n")}
        else false
      with
      | Not_found -> ((Hashtbl.add vs sv1 order); true)
    end
  | CP.Bag(el, l) -> List.fold_left (fun a b -> a || (find_order_exp b 1 vs)) false el
  | CP.BagIntersect(el, l) 
  | CP.BagUnion(el, l) -> List.fold_left (fun a b -> a || (find_order_exp b 2 vs)) false el
  | CP.BagDiff(e1, e2, l) -> ((find_order_exp e1 2 vs) || (find_order_exp e2 2 vs))    
  | CP.Add(e1, e2, l) ->
    (* let () = print_string ("e1 = " ^ (Cprinter.string_of_formula_exp e1) ^ " and e2 = " ^ (Cprinter.string_of_formula_exp e2) ^ "\n") in *)
    if (CP.exp_contains_spec_var e1) && (CP.exp_contains_spec_var e2) then (* non-monadic formula ==> need second order *)
      ((find_order_exp e1 2 vs) || (find_order_exp e2 2 vs))
    else
      ((find_order_exp e1 order vs) || (find_order_exp e2 order vs))
  | CP.Subtract(e1, e2, l)
  | CP.Mult(e1, e2, l)
  | CP.Div(e1, e2, l)
  | CP.Max(e1, e2, l)
  | CP.Min(e1, e2, l) 
  | CP.ListCons(e1, e2, l) -> ((find_order_exp e1 order vs) || (find_order_exp e2 order vs))
  | CP.List(el, l)
  | CP.ListAppend(el, l) -> List.fold_left (fun a b -> a || (find_order_exp b order vs)) false el
  | CP.ListHead(e, l)
  | CP.ListTail(e, l)
  | CP.ListLength(e, l)
  | CP.ListReverse(e, l) -> (find_order_exp e order vs)
  | CP.ArrayAt(sv, el, l) -> Error.report_error { Error.error_loc = l; Error.error_text = (" Mona does not handle arrays!\n")}
  | _ -> false

and find_order_exp (e : CP.exp) order vs =
  Debug.no_3 "find_order_exp"
    Cprinter.string_of_formula_exp string_of_int string_of_hashtbl string_of_bool
    find_order_exp_x e order vs

(*

   INTEROGATION

*)


and is_firstorder_mem_a e vs =
  match e with
  | CP.Var(sv1, l1) ->
    begin
      try 
        let r = Hashtbl.find vs sv1 in 
        if (r == 1) (* || (r == 0)*) then true (* andreeac *)
        else false
      with 
      | Not_found -> Error.report_error { Error.error_loc = l1; Error.error_text = (" Error during Mona translation for var " ^ (Cprinter.string_of_spec_var sv1) ^ "\n")}
    end
  | CP.IConst _ 
  | CP.Null _ -> true
  | _ -> false

and part_firstorder_mem e vs =
  match e with
  | CP.Var(sv1, l1) ->
    begin
      try 
        let r = Hashtbl.find vs sv1 in 
        if (r == 1) (*|| (r == 0)*) then true (* andreeac *)
        else false
      with 
      | Not_found -> false
    end
  | CP.IConst _
  | CP.Null _ -> true
  | _ -> false

(* and is_firstorder_mem e vs = (\* deprecated *\) *)
(*   Debug.no_1 "is_firstorder_mem" Cprinter.string_of_formula_exp string_of_bool (fun e -> is_firstorder_mem_a e vs) e  *)

and is_firstorder_mem_x e (var1,var2) =
  match e with
  | CP.Var(sv, _) -> List.exists (CP.eq_spec_var sv) var1
  | CP.IConst _ 
  | CP.Null _ -> true
  | _ -> false

and is_firstorder_mem e vs =
  Debug.no_1 "is_firstorder_mem" Cprinter.string_of_formula_exp string_of_bool (fun e -> is_firstorder_mem_x e vs) e

and is_firstorder_mem_sv sv (var1,var2) =
  List.exists (CP.eq_spec_var sv) var1

(*
  Pretty printing
*)

(* pretty printing for spec_vars*)
and mona_of_spec_var (sv : CP.spec_var) = match sv with
  | CP.SpecVar (_, v, p) -> 
    v ^ (if CP.is_primed sv then Oclexer.primed_str else "")

(* pretty printing for expressions *)
and mona_of_exp e0 f = 
  Debug.no_1 "mona_of_exp" Cprinter.string_of_formula_exp (fun x -> x)
    (fun e0 -> mona_of_exp_x e0 f) e0

(* pretty printing for expressions *)
and mona_of_exp_x e0 f = 
  let rec helper e0 =
    match e0 with
    | CP.Null _ -> " 0 "
    (* | CP.Null _ -> "pconst(0)" *)
    | CP.Var (sv, _) -> mona_of_spec_var sv
    | CP.IConst (i, _) -> " " ^ (string_of_int i) ^ " "
    (*  | CP.IConst (i, _) -> "pconst(" ^ (string_of_int i) ^ ")"*)
    | CP.Add(CP.IConst(i, _), a, _) -> "( " ^ (helper a) ^ " + " ^ (string_of_int i) ^ " )"
    | CP.Add (a1, a2, _) ->  " ( " ^ (helper a1) ^ " + " ^ (helper a2) ^ ")"
    | CP.Subtract(CP.IConst(i, _), a, _) -> "( " ^ (helper a) ^ " + " ^ (string_of_int i) ^ " )"
    | CP.Mult (a1, a2, p) -> "(" ^ (helper a1) ^ " * " ^ (helper a2) ^ ")"
    | CP.Div (a1, a2, p) -> failwith "[mona.ml]: divide is not supported."
    | CP.Max _
    | CP.Min _ -> failwith ("mona.mona_of_exp: min/max can never appear here")
    | CP.TypeCast _ -> failwith ("mona.mona_of_exp: TypeCast can never appear here")
    | CP.Bag (elist, _) -> "{"^ (mona_of_formula_exp_list elist f) ^ "}"
    | CP.BagUnion ([], _) -> ""
    | CP.BagUnion (e::[], _) -> (helper e)
    | CP.BagUnion (e::rest, l) -> " ( " ^ (helper e) ^ " union " ^ (helper (CP.BagUnion (rest, l))) ^ " ) "
    | CP.BagIntersect ([], _) -> ""
    | CP.BagIntersect (e::[], _) -> (helper e)
    | CP.BagIntersect (e::rest, l)-> " ( " ^ (helper e) ^ " inter " ^ (helper (CP.BagIntersect (rest, l))) ^ " ) "
    | CP.BagDiff (e1, e2, _)     -> " ( " ^ (helper e1) ^ "\\" ^ (helper e2) ^ " ) "
    | CP.List _
    | CP.ListCons _
    | CP.ListHead _
    | CP.ListTail _
    | CP.ListLength _
    | CP.ListAppend _
    | CP.ListReverse _ -> failwith ("Lists are not supported in Mona")
    | _ -> failwith ("mona.mona_of_exp: mona doesn't support..."^(Cprinter.string_of_formula_exp e0)) 
  in
  helper e0

and mona_of_exp_secondorder_x e0 f = 	match e0 with
  | CP.Null _ -> ([], "pconst(0)", "")
  | CP.Var (sv, _) -> ([], mona_of_spec_var sv, "")
  | CP.IConst (i, _) -> ([], ("pconst(" ^ (string_of_int i) ^ ")"), "")
  | CP.AConst (i, _) -> ([], ("pconst(" ^ (string_of_int (int_of_heap_ann i))
                              ^ ")"), "")
  | CP.Tsconst _ -> failwith ("mona.mona_of_exp_secondorder: mona doesn't support tree_shares"^(Cprinter.string_of_formula_exp e0))
  | CP.Add (a1, a2, pos) ->  
    let tmp = fresh_var_name "int" pos.start_pos.Lexing.pos_lnum in
    let (exs1, a1name, a1str) = mona_of_exp_secondorder a1 f in
    let (exs2, a2name, a2str) = mona_of_exp_secondorder a2 f in
    let add_string = " plus(" ^ a1name ^ ", " ^ a2name ^ ", " ^ tmp ^ ")" in
    let add_string2 = add_string ^ (if a1str <> "" then (" & " ^ a1str) else "") ^ (if a2str <> "" then (" & " ^ a2str) else "") in
    ((tmp :: (exs1 @ exs2)), tmp, add_string2)
  | CP.Max _
  | CP.Min _ -> failwith ("mona.mona_of_exp_secondorder: min/max can never appear here")
  | CP.Mult (a1, a2, p) ->
    (match a1 with
     | CP.IConst(i, _) -> 
       if (i > 10 || i < 1) then 
         failwith ("mona.mona_of_exp_secondorder: mona doesn't support multiplication and the constant is too big")
       else
         let rec mult i = if i==1 then a2 else CP.Add ((mult (i-1)), a2, p) in
         let sum = if (i>1) then (mult i) else CP.IConst (1, p) in
         mona_of_exp_secondorder sum f
     | _ -> failwith ("mona.mona_of_exp_secondorder: nonlinear arithmetic isn't supported."))
  | CP.Subtract (e1, e2, p) -> 	
    let () = print_string("Illegal subtraction: " ^ (Cprinter.string_of_pure_formula f) ) in
    failwith ("mona.mona_of_exp_secondorder: mona doesn't support subtraction ...")
  | CP.List _
  | CP.ListCons _
  | CP.ListHead _
  | CP.ListTail _
  | CP.ListLength _
  | CP.ListAppend _
  | CP.ListReverse _ -> failwith ("Lists are not supported in Mona")
  | CP.Bag (elist, _) -> ([],"{"^ (mona_of_formula_exp_list elist f) ^ "}", "")
  | CP.BagUnion (_, _) -> ([], mona_of_exp e0 f, "")
  | CP.BagIntersect ([], _) -> ([], mona_of_exp e0 f, "")
  | CP.BagIntersect (_, _) -> ([], mona_of_exp e0 f, "") (*TO CHECK: add non-empty case *)
  | CP.BagDiff (_,_,_) -> ([], mona_of_exp e0 f, "")
  | CP.Tup2 _ -> failwith ("mona.mona_of_exp_secondorder: mona doesn't support Tup2"^(Cprinter.string_of_formula_exp e0))
  | _ -> failwith ("mona.mona_of_exp_secondorder: mona doesn't support subtraction/mult/..."^(Cprinter.string_of_formula_exp e0))

and mona_of_exp_secondorder e0 f =
  Debug.no_1 "mona_of_exp_secondorder" Cprinter.string_of_formula_exp (fun (x_str_lst, y_str, z_str) -> y_str) 
    (fun e0 -> mona_of_exp_secondorder_x e0 f) e0

(* pretty printing for a list of expressions *)
and mona_of_formula_exp_list l f = match l with
  | []         -> ""
  | CP.IConst(i, _) :: [] -> string_of_int i
  | h::[]      -> mona_of_exp h f
  | CP.IConst(i, _) :: t -> string_of_int i ^ ", " ^ (mona_of_formula_exp_list t f)
  | h::t       -> (mona_of_exp h f) ^ ", " ^ (mona_of_formula_exp_list t f)

(* pretty printing for boolean vars *)
and mona_of_b_formula b f vs = 
  Debug.no_1 "mona_of_b_formula" Cprinter.string_of_b_formula (fun x -> x)
    (fun _ -> mona_of_b_formula_x b f vs) b

(* pretty printing for boolean vars *)
and mona_of_b_formula_x b f vs =
  let second_order_composite a1 a2 a3 f = 
    let (a1ex, a1name, a1str) = (mona_of_exp_secondorder a1 f) in
    let (a2ex, a2name, a2str) = (mona_of_exp_secondorder a2 f) in
    let (a3ex, a3name, a3str) = (mona_of_exp_secondorder a3 f) in
    let all_existentials = a1ex @ a2ex @ a3ex in
    let str = String.concat "" (List.map (fun name -> "ex2 " ^ name ^ " : (") all_existentials) in
    let end_str = String.concat "" (List.map (fun name -> ")") all_existentials) in
    let end_str = 
      (if a1str <> "" then " & " ^ a1str else "") ^ 
      (if a2str <> "" then " & " ^ a2str else "") ^ 
      (if a3str <> "" then " & " ^ a3str else "") ^ end_str in
    (a1name,a2name,a3name,str,end_str)  in
  let second_order_composite2 a1 a2 f = 
    let (a1ex, a1name, a1str) = (mona_of_exp_secondorder a1 f) in
    let (a2ex, a2name, a2str) = (mona_of_exp_secondorder a2 f) in
    let all_existentials = a1ex @ a2ex in
    let str = String.concat "" (List.map (fun name -> "ex2 " ^ name ^ " : (") all_existentials) in
    let end_str = String.concat "" (List.map (fun name -> ")") all_existentials) in
    let end_str = 
      (if a1str <> "" then " & " ^ a1str else "") ^ 
      (if a2str <> "" then " & " ^ a2str else "") ^ end_str in
    (a1name,a2name,str,end_str)  in

  let ret =
    let (pf, _) = b in
    match pf with
    | CP.Frm (bv, _) -> "greater(" ^ (mona_of_spec_var bv) ^ ", pconst(0))"
    | CP.XPure _ -> "(0=0)" (* WN : weakening *)
    | CP.BConst (c, _) -> if c then "(0 = 0)" else "(~ (0 <= 0))"
    | CP.BVar (bv, _) -> "greater(" ^ (mona_of_spec_var bv) ^ ", pconst(0))"
    (* CP.Lt *)   
    (*| CP.Lt((CP.Subtract(a3, a1, pos1)), a2, pos2) -> (mona_of_b_formula (CP.Lt(a3, CP.Add(a2, a1, pos1), pos2)) f vs)	 
      | CP.Lt(a2, (CP.Subtract(a3, a1, pos1)), pos2) -> (mona_of_b_formula (CP.Lt(CP.Add(a2, a1, pos1), a3, pos2)) f vs)	 *)
    | CP.Lt (a1, a2, _) -> (equation a1 a2 f "less" "<" vs)
    (* CP.Lte *)   
    (*| CP.Lte((CP.Subtract(a3, a1, pos1)), a2, pos2) -> (mona_of_b_formula (CP.Lte(a3, CP.Add(a2, a1, pos1), pos2)) f vs)	 
      | CP.Lte(a2, (CP.Subtract(a3, a1, pos1)), pos2) -> (mona_of_b_formula (CP.Lte(CP.Add(a2, a1, pos1), a3, pos2)) f vs)	 *)
    | CP.SubAnn (a1, a2, _) -> (equation a1 a2 f "lessEq" "<=" vs)
    | CP.Lte (a1, a2, _) -> (equation a1 a2 f "lessEq" "<=" vs)
    (* CP.Gt *)   
    (*| CP.Gt((CP.Subtract(a3, a1, pos1)), a2, pos2) -> (mona_of_b_formula (CP.Gt(a3, CP.Add(a2, a1, pos1), pos2)) f vs)	 
      | CP.Gt(a2, (CP.Subtract(a3, a1, pos1)), pos2) -> (mona_of_b_formula (CP.Gt(CP.Add(a2, a1, pos1), a3, pos2)) f vs)	 *)
    | CP.Gt (a1, a2, _) -> (equation a1 a2 f "greater" ">" vs)
    (* CP.Gte *)   
    (*| CP.Gte((CP.Subtract(a3, a1, pos1)), a2, pos2) -> (mona_of_b_formula (CP.Gte(a3, CP.Add(a2, a1, pos1), pos2)) f vs)	 
      | CP.Gte(a2, (CP.Subtract(a3, a1, pos1)), pos2) -> (mona_of_b_formula (CP.Gte(CP.Add(a2, a1, pos1), a3, pos2)) f vs)	 *)
    | CP.Gte (a1, a2, _) -> (equation a1 a2 f "greaterEq" ">=" vs)
    | CP.Neq((CP.Add(a1, a2, _)), a3, _)
    | CP.Neq(a3, (CP.Add(a1, a2, _)), _) ->
      if (is_firstorder_mem a1 vs) && (is_firstorder_mem a2 vs) && (is_firstorder_mem a3 vs) then
        let a1str = (mona_of_exp a1 f) in
        let a2str = (mona_of_exp a2 f) in
        let a3str = (mona_of_exp a3 f) in
        match a1 with
        | CP.IConst _ -> "(" ^ a3str ^ " ~= " ^ a2str ^ " + " ^ a1str ^ ") "
        | _ ->  
          "(" ^ a3str ^ " ~= " ^ a1str ^ " + " ^ a2str ^ ") "
      else
        let (a1name,a2name,a3name,str,end_str) = second_order_composite a1 a2 a3 f in
        str ^ " ~(plus(" ^ a1name ^ ", " ^ a2name ^ ", " ^ a3name ^ ")) "^ end_str
    | CP.Neq (CP.IConst(i, _), a1, _)
    | CP.Neq (a1, CP.IConst(i, _), _) ->
      if (is_firstorder_mem a1 vs) then
        "(" ^ (mona_of_exp a1 f) ^ " ~= " ^ (string_of_int i) ^ ")"
      else
        "(" ^ (mona_of_exp a1 f) ^ " ~= pconst(" ^ (string_of_int i) ^ "))"
    (* | CP.Neq (a, CP.Null _, _)  *)
    (* | CP.Neq (CP.Null _, a, _) -> *)
    (*       if (is_firstorder_mem a vs) then *)
    (*         "(" ^ (mona_of_exp a f) ^ " > 0)" *)
    (*       else *)
    (*         " greater(" ^ (mona_of_exp a f) ^ ", pconst(0))" *)
    | CP.Neq (a1, a2, _) ->
      if (is_firstorder_mem a1 vs)&& (is_firstorder_mem a2 vs) then
        "(" ^ (mona_of_exp a1 f) ^ " ~= " ^ (mona_of_exp a2 f) ^ ")"
      else
        let (a1name,a2name,str,end_str) = second_order_composite2 a1 a2 f in
        str ^ " nequal(" ^ a1name ^ ", " ^ a2name ^ ") "^ end_str
    | CP.Eq((CP.Add(a1, a2, _)), a3, _)
    | CP.Eq(a3, (CP.Add(a1, a2, _)), _) ->
      let () = Debug.ninfo_pprint "add and eq" no_pos in
      if (is_firstorder_mem a1 vs) && (is_firstorder_mem a2 vs) && (is_firstorder_mem a3 vs) then
        let a1str = (mona_of_exp a1 f) in
        let a2str = (mona_of_exp a2 f) in
        let a3str = (mona_of_exp a3 f) in
        match a1 with
        | CP.IConst _ -> "(" ^ a3str ^ " = " ^ a2str ^ " + " ^ a1str ^ ") "
        | _ ->  
          "(" ^ a3str ^ " = " ^ a1str ^ " + " ^ a2str ^ ") "
      else
        let (a1name,a2name,a3name,str,end_str) = second_order_composite a1 a2 a3 f in
        str ^ " plus(" ^ a1name ^ ", " ^ a2name ^ ", " ^ a3name ^ ") "^ end_str
    | CP.Eq (CP.IConst(i, _), a1, _)
    | CP.Eq (a1, CP.IConst(i, _), _) ->
      if (is_firstorder_mem a1 vs) then
        "(" ^ (mona_of_exp a1 f) ^ " = " ^ (string_of_int i) ^ ")"
      else
        "(" ^ (mona_of_exp a1 f) ^ " = pconst(" ^ (string_of_int i) ^ "))"
    (* | CP.Eq (a1, CP.Null _, _)  *)
    (* | CP.Eq (CP.Null _, a1, _) -> *)
    (*       if (is_firstorder_mem a1 vs) then *)
    (*             "(" ^ (mona_of_exp a1 f) ^ " = 0)" *)
    (*       else *)
    (*             "(" ^ (mona_of_exp a1 f) ^ " = pconst(0))" *)
    | CP.Eq (a1, a2, _) -> 
      if (is_firstorder_mem a1 vs)&& (is_firstorder_mem a2 vs) then
        "(" ^ (mona_of_exp a1 f) ^ " = " ^ (mona_of_exp a2 f) ^ ")"
      else	 
        let (a1name,a2name,str,end_str) = second_order_composite2 a1 a2 f in
        str ^ " " ^ a1name ^ " = " ^ a2name ^ " " ^ end_str
    | CP.EqMin (a1, a2, a3, _) ->
      if (is_firstorder_mem a1 vs) && (is_firstorder_mem a2 vs) && (is_firstorder_mem a3 vs) then
        let a1str = mona_of_exp a1 f in
        let a2str = mona_of_exp a2 f in
        let a3str = mona_of_exp a3 f in	  
        "((" ^ a3str ^ " <= " ^ a2str ^ " & " ^ a1str ^ " = " ^ a3str ^ ") | ("
        ^ a2str ^ " < " ^ a3str ^ " & " ^ a1str ^ " = " ^ a2str ^ "))" ^ Gen.new_line_str
      else
        let (a1name,a2name,a3name,str,end_str) = second_order_composite a1 a2 a3 f in
        (*str ^ " plus(" ^ a1name ^ ", " ^ a2name ^ ", " ^ a3name ^ ") "^ end_str*)
        str ^ "((lessEq(" ^ a3name ^ ", " ^ a2name ^ ") & " ^ a1name ^ " = " ^ a3name ^ ") | (less("
        ^ a2name ^ ", " ^ a3name ^ ") & " ^ a1name ^ " = " ^ a2name ^ "))"   ^end_str

    (*let a1str = mona_of_exp_secondorder a1 f in
      	    let a2str = mona_of_exp_secondorder a2 f in
      	    let a3str = mona_of_exp_secondorder a3 f in
      	    "((lessEq(" ^ a3str ^ ", " ^ a2str ^ ") & " ^ a1str ^ " = " ^ a3str ^ ") | (less("
      		^ a2str ^ ", " ^ a3str ^ ") & " ^ a1str ^ " = " ^ a2str ^ "))" ^ Gen.new_line_str*)
    | CP.EqMax (a1, a2, a3, _) ->	 
      if (is_firstorder_mem a1 vs) && (is_firstorder_mem a2 vs) && (is_firstorder_mem a3 vs) then
        let a1str = mona_of_exp a1 f in
        let a2str = mona_of_exp a2 f in
        let a3str = mona_of_exp a3 f in
        "((" ^ a3str ^ " <= " ^ a2str ^ " & " ^ a1str ^ " = " ^ a2str ^ ") | ("
        ^ a2str ^ " < " ^ a3str ^ " & " ^ a1str ^ " = " ^ a3str ^ "))" ^ Gen.new_line_str
      else
        let (a1name,a2name,a3name,str,end_str) = second_order_composite a1 a2 a3 f in
        (*str ^ " plus(" ^ a1name ^ ", " ^ a2name ^ ", " ^ a3name ^ ") "^ end_str*)
        str ^ "((lessEq(" ^ a3name ^ ", " ^ a2name ^ ") & " ^ a1name ^ " = " ^ a2name ^ ") | (less("
        ^ a2name ^ ", " ^ a3name ^ ") & " ^ a1name ^ " = " ^ a3name ^ "))"   ^end_str      

    (* let a1str = mona_of_exp_secondorder a1 f in
       	     let a2str = mona_of_exp_secondorder a2 f in
       	     let a3str = mona_of_exp_secondorder a3 f in
       	     "((lessEq(" ^ a3str ^ ", " ^ a2str ^ ") & " ^ a1str ^ " = " ^ a2str ^ ") | (less("
       		 ^ a2str ^ ", " ^ a3str ^ ") & " ^ a1str ^ " = " ^ a3str ^ "))\n"*)
    | CP.BagIn (v, e, l) -> (mona_of_spec_var v) ^ " in " ^ (mona_of_exp e f)
    | CP.BagNotIn (v, e, l) -> "~(" ^ (mona_of_spec_var v) ^ " in " ^ (mona_of_exp e f) ^")"
    | CP.BagSub (e1, e2, l) -> "(" ^ (mona_of_exp e1 f) ^ " sub " ^ (mona_of_exp e2 f) ^ ")"
    | CP.BagMin (v1, v2, l) -> (mona_of_spec_var v1) ^ " in " ^ (mona_of_spec_var v2) ^" & (all1 x0: x0 in " ^ (mona_of_spec_var v2) ^ " => " ^ (mona_of_spec_var v1) ^ " <= x0)"
    | CP.BagMax (v1, v2, l) -> (mona_of_spec_var v1) ^ " in " ^ (mona_of_spec_var v2) ^" & (all1 x0: x0 in " ^ (mona_of_spec_var v2) ^ " => x0 <= " ^ (mona_of_spec_var v1) ^ " )"
    | CP.ListIn _
    | CP.ListNotIn _
    | CP.ListAllN _
    | CP.ListPerm _ -> failwith ("Lists are not supported in Mona")
    | CP.LexVar _ -> failwith ("LexVar is not supported in Mona")
    (* | CP.VarPerm _ -> failwith ("VarPerm is not supported in Mona") *)
    | CP.ImmRel _ -> failwith ("Imm Relations are not supported in Mona")
    | CP.RelForm _ -> failwith ("Relations are not supported in Mona") (* An Hoa *) 
  in
  ret

and equation a1 a2 f sec_order_symbol first_order_symbol vs =
  Debug.no_2 "equation" Cprinter.string_of_formula_exp Cprinter.string_of_formula_exp (fun x -> x)
    (fun a1 a2 -> equation_a a1 a2 f sec_order_symbol first_order_symbol vs) a1 a2

and equation_a a1 a2 f sec_order_symbol first_order_symbol vs =
  if (is_firstorder_mem a1 vs && is_firstorder_mem a2 vs) then begin
    match a1 with
    | CP.IConst(i1, _) ->
      "(" ^ (string_of_int i1) ^ first_order_symbol ^ (mona_of_exp a2 f) ^ ")"
    | _ ->
      begin
        match a2 with
        | CP.IConst(i2, _) ->
          "(" ^ (mona_of_exp a1 f) ^ " " ^ first_order_symbol ^ " " ^ (string_of_int i2) ^ ")"
        | _ ->
          "(" ^ (mona_of_exp a1 f) ^ " " ^ first_order_symbol ^ " " ^ (mona_of_exp a2 f) ^ ")"
      end
  end else begin
    let (a1ex, a1name, a1str) = (mona_of_exp_secondorder a1 f) in
    let (a2ex, a2name, a2str) = (mona_of_exp_secondorder a2 f) in
    let all_existentials = a1ex @ a2ex in
    let str = String.concat "" (List.map (fun name -> "ex2 " ^ name ^ " : (") all_existentials) in
    let end_str = String.concat "" (List.map (fun name -> ")") all_existentials) in
    str ^ " " ^ sec_order_symbol ^ "(" ^ a1name ^ ", " ^ a2name ^ ")"
    ^ (if a1str <> "" then " & " ^ a1str else "") ^ (if a2str <> "" then " & " ^ a2str else "") ^ end_str
  end

and mona_of_formula f initial_f vs = 
  Debug.no_2 "mona_of_formula" Cprinter.string_of_pure_formula
    Cprinter.string_of_pure_formula 
    (fun x -> x) (fun f initial_f -> mona_of_formula_x f initial_f vs) 
    f initial_f 

(* pretty printing for formulas *)
and mona_of_formula_x f initial_f vs =
  let rec helper f =
    match f with
    | CP.BForm (b,_) -> "(" ^ (mona_of_b_formula b initial_f vs) ^ ")"
    | CP.And (p1, p2, _) -> "(" ^ (helper p1) ^ " & " ^ (helper p2) ^ ")"
    | CP.AndList _ -> Gen.report_error no_pos "mona.ml: encountered AndList, should have been already handled"
    | CP.Or (p1, p2, _,_) -> "(" ^ (helper p1) ^ " | " ^ (helper p2) ^ ")"
    | CP.Not (p, _,_) ->
      begin
        if !sat_optimize then
          match p with
          | CP.BForm ((CP.BVar (bv, _), _), _) -> (mona_of_spec_var bv) ^ " =pconst(0)" (*== pconst(1)*)
          (*              (equation (CP.Var (bv, no_pos)) (CP.IConst (1, no_pos)) f "less" "<" vs)*)
          | _ -> " (~" ^ (helper p) ^ ") "
        else " (~" ^ (helper p) ^ ") "
      end 
    (*| CP.Forall(CP.SpecVar (CP.Prim Bag, v, p), p1, _) ->
      	              "(all2 " ^ v ^ " : " ^ (helper p1) ^ ")"
      | CP.Forall (sv, p, _) ->
      	              "(all1 " ^ (mona_of_spec_var sv) ^ " : " ^ (helper p) ^ ")"
      | CP.Exists(CP.SpecVar (CP.Prim Bag, v, p), p1, _) ->
      	              "(ex2 " ^ v ^ " : " ^ (helper p1) ^ ")"
      | CP.Exists (sv, p, _) ->
      	              "(ex1 " ^ (mona_of_spec_var sv) ^ " : " ^ (helper p) ^ ")"*)
    | CP.Forall (sv, p, _,l) ->
      if (is_firstorder_mem (CP.Var(sv, l)) vs) then
        " (all1 " ^ (mona_of_spec_var sv) ^ ":" ^ (helper p) ^ ") "
      else
        " (all2 " ^ (mona_of_spec_var sv) ^ ":" ^ (helper p) ^ ") "
    | CP.Exists (sv, p, _,l) ->
      if (is_firstorder_mem (CP.Var(sv, l)) vs) then
        begin
          " (ex1 " ^ (mona_of_spec_var sv) ^ ":" ^ (helper p) ^ ") "
        end
      else
        begin
          " (ex2 " ^ (mona_of_spec_var sv) ^ ":" ^ (helper p) ^ ") "
        end
  in helper f 

(* pretty printing for boolean vars *)
and print_b_formula b f = match b with
  | CP.Frm (bv, _) -> "greater(" ^ (mona_of_spec_var bv) ^ ",pconst(0))" 
  | CP.BConst (c, _) -> if c then "(0 = 0)" else "(~ (0 <= 0))"
  | CP.BVar (bv, _) -> "greater(" ^ (mona_of_spec_var bv) ^ ",pconst(0))" 
  | CP.Lt (a1, a2, _) -> (mona_of_exp a1 f) ^ "<" ^ (mona_of_exp a2 f)
  | CP.Lte (a1, a2, _) -> (mona_of_exp a1 f) ^ "<=" ^ (mona_of_exp a2 f)
  | CP.SubAnn (a1, a2, _) -> (mona_of_exp a1 f) ^ "<=" ^ (mona_of_exp a2 f)
  | CP.Gt (a1, a2, _) -> (mona_of_exp a1 f) ^ ">" ^ (mona_of_exp a2 f)
  | CP.Gte (a1, a2, _) -> (mona_of_exp a1 f) ^ ">=" ^ (mona_of_exp a2 f)
  | CP.Neq(a1, a2, _) -> (mona_of_exp a1 f) ^ "~=" ^ (mona_of_exp a2 f)
  | CP.Eq(a1, a2, _) -> (mona_of_exp a1 f) ^ "=" ^ (mona_of_exp a2 f)
  | CP.EqMin (a1, a2, a3, _) -> (mona_of_exp a1 f) ^ "= min(" ^ (mona_of_exp a2 f) ^ "," ^ (mona_of_exp a3 f) ^ ")"
  | CP.EqMax (a1, a2, a3, _) -> (mona_of_exp a1 f) ^ "= max(" ^ (mona_of_exp a2 f) ^ "," ^ (mona_of_exp a3 f) ^ ")"
  | CP.BagIn (v, e, l) -> (mona_of_spec_var v) ^ " in " ^ (mona_of_exp e f)
  | CP.BagNotIn (v, e, l) -> "~(" ^ (mona_of_spec_var v) ^ " in " ^ (mona_of_exp e f) ^")"
  | CP.BagSub (e1, e2, l) -> "(" ^ (mona_of_exp e1 f) ^ " sub " ^ (mona_of_exp e2 f) ^ ")"
  | CP.BagMin (v1, v2, l) -> (mona_of_spec_var v1) ^ " in " ^ (mona_of_spec_var v2) ^" & (all1 x0: x0 in " ^ (mona_of_spec_var v2) ^ " => " ^ (mona_of_spec_var v1) ^ " <= x0)"
  | CP.BagMax (v1, v2, l) -> (mona_of_spec_var v1) ^ " in " ^ (mona_of_spec_var v2) ^" & (all1 x0: x0 in " ^ (mona_of_spec_var v2) ^ " => x0 <= " ^ (mona_of_spec_var v1) ^ " )"
  | CP.ListIn _
  | CP.ListNotIn _
  | CP.ListAllN _
  | CP.ListPerm _ -> failwith ("Lists are not supported in Mona")
  | CP.LexVar _ -> failwith ("LexVar is not supported in Mona")
  | CP.ImmRel _ -> failwith ("Imm Relations are not supported in Mona")
  (* | CP.VarPerm _ -> failwith ("VarPerm not suported in Mona") *)
  | CP.RelForm _ -> failwith ("Arrays are not supported in Mona") (* An Hoa *)
  | CP.XPure _ -> failwith ("XPure are not supported in Mona")

let rec get_answer acc chn : string =
  try
    let chr = input_char chn in
    match chr with
    |'\n' ->  acc (* "" *)
    | 'a'..'z' | 'A'..'Z' | ' ' -> (* (Char.escaped chr) ^ get_answer chn *) (*save only alpha characters*)
      get_answer (acc ^ (Char.escaped chr)) chn
    | _ -> (* "" ^ get_answer chn *) get_answer acc chn
  with _ -> acc

(* let get_answer acc chn = *)
(*   Debug.no_1 "get_answer" (fun _ -> "") (fun f -> f) *)
(*       (fun _ -> get_answer acc chn) acc *)

let send_cmd_with_answer str =
  if!log_all_flag==true then
    output_string log_all str;
  let fnc () = 
    if (String.length str < max_BUF_SIZE) then
      let () = (output_string !process.outchannel str;
                flush !process.outchannel) in
      let str = get_answer "" !process.inchannel in
      str 
    else
      "Formula is too large"
  in 
  let answ = Procutils.PrvComms.maybe_raise_timeout_num 1 fnc () !mona_timeout in
  answ

let wrap_collect_raw_result f x =
  try
    set_prover_type ();
    set_proof_string x;
    let out = f x in
    set_proof_result out;
    out
  with e ->
    set_proof_result ("Exception "^Printexc.to_string e);
    raise e

let send_cmd_with_answer str =
  let pr = fun f -> f in
  Debug.no_1 "[Mona.ml]send_cmd_with_answer" pr pr (wrap_collect_raw_result send_cmd_with_answer) str

let send_cmd_with_answer str =
  let pr = fun f -> f in
  Debug.no_1 "send_cmd_with_answer" pr pr send_cmd_with_answer str

(* modify mona for not sending answers *)
let send_cmd_no_answer str =
  (* let () = (print_string ("\nsned_cmd_no_asnwer " ^ str ^"- end string\n"); flush stdout) in *)
  let (todo_unk:string) = send_cmd_with_answer str in
  let () = x_tinfo_hp (add_str "no_answer" pr_id) todo_unk no_pos  in
  ()

let write_to_mona_predicates_file mona_filename =
  let filename = open_out mona_filename in
  output_string filename ("pred xor(var0 x,y) = x&~y | ~x&y;\n");
  output_string filename ("pred at_least_two(var0 x,y,z) = x&y | x&z | y&z;\n");
  output_string filename ("pred plus(var2 p,q,r) = ex2 c: 0 notin c & all1 t:(t+1 in c <=> at_least_two(t in p, t in q, t in c)) & (t in r <=> xor(xor(t in p, t in q), t in c));\n");
  output_string filename ("pred less(var2 p,q) = ex2 t: t ~= empty & plus(p,t,q);\n");
  output_string filename ("pred lessEq(var2 p, q) = less(p, q) | (p=q);\n");
  output_string filename ("pred greater(var2 p, q) = less(q, p);\n");
  output_string filename ("pred greaterEq(var2 p, q) = greater(p, q) | (p=q);\n");
  output_string filename ("pred nequal(var2 p,q) = p ~= q ;\n");
  flush filename;
  close_out filename

let get_mona_predicates_file () : string =
  if Sys.file_exists mona_pred_file then 
    mona_pred_file
  else
    begin
      (* let () = print_string ("\n WARNING: File " ^ mona_pred_file ^ " was not found in current directory. Searching in alternative path: " ^ mona_pred_file_alternative_path) in *)
      let alternative = mona_pred_file_alternative_path ^ mona_pred_file in
      if Sys.file_exists alternative then 
        alternative
      else
        let () = print_string ("\n WARNING: File " ^ alternative ^ " was not found. Aborting execution ...\n") in 
        (* Creating " ^ mona_pred_file ^ " file in current directory... " in" *)
        (* let () = write_to_mona_predicates_file mona_pred_file in *)
        (* let () = print_string (" done!\n") in *)
        (* mona_pred_file *)
        exit(0)
    end

let prelude () =
  let mona_pred_file_x = get_mona_predicates_file () in
  (* let () = print_endline  mona_pred_file_x in *)
  send_cmd_no_answer ("include \"" ^ mona_pred_file_x ^ "\";\n")

let set_process (proc: prover_process_t) = 
  process := proc

let rec check_prover_existence prover_cmd_str: bool =
  let exit_code = Sys.command ("which " ^ prover_cmd_str ^ " >/dev/null 2>&1") in
  if exit_code > 0 then
    let () = print_string_if (not !compete_mode)  ("WARNING: Command for starting mona interactively (" ^ prover_cmd_str ^ ") not found!\n") in
    false
  else true

let start () = 
  last_test_number := !test_number;
  (* let () = print_endline mona_prog in *)
  if(check_prover_existence mona_prog)then begin
    try
      print_endline_quiet  ("\nStarting MONA..."^mona_prog); flush stdout;
      let () = Procutils.PrvComms.start !log_all_flag log_all ("mona", mona_prog, [|mona_prog; "-v";|]) set_process prelude in
      (* let () = print_endline (mona_prog ^ "end") in *)
      is_mona_running := true
    with e ->
      begin
        print_endline "Unable to run the prover MONA!";
        print_endline "Please make sure its executable file (mona) is installed";
        raise e
      end
  end
  else 
    (print_endline  ("\nCannot find mona_inter code..."); flush stdout;)


let start () =
  let pr = (fun _ -> "") in
  Debug.no_1 "[mona.ml] start" pr pr start ()

let start () =
  (* Log.logtime_wrapper "start mona"  start ()  *)
  Gen.Profiling.do_1 "mona.start" start ()

let stop () = 
  let killing_signal = 
    match !is_mona_running with
    |true -> is_mona_running := false;  Sys.sigterm (* *)
    |false -> 9 in
  let num_tasks = !test_number - !last_test_number in
  let () = Procutils.PrvComms.stop !log_all_flag log_all !process num_tasks killing_signal (fun () -> ()) in
  is_mona_running := false

let stop () =
  (* Log.logtime_wrapper "stop mona"  stop ()  *)
  Gen.Profiling.do_1 "mona.stop" stop ()

let restart reason =
  if !is_mona_running then
    (* let () = print_string ("\n[mona.ml]: Mona is preparing to restart because of " ^ reason ^ "\nRestarting Mona ...\n"); flush stdout; in *)
    let () = print_endline_if (not !compete_mode && not !Globals.web_compile_flag) ("\nMona is restarting ... " ^ reason); flush stdout; in
    Procutils.PrvComms.restart !log_all_flag log_all reason "mona" start stop

let restart reason =
  (* Log.logtime_wrapper "restart mona" restart reason  *)
  if (not !compete_mode) then
    Gen.Profiling.do_1 "mona.restart" restart reason

let check_if_mona_is_alive () : bool = 
  try
    Unix.kill !process.pid 0;
    true
  with
  | e -> 
    ignore e;
    false

let create_failure_file (content: string) =
  let failure_filename = "mona.failure" in
  let fail_file = open_out failure_filename in 
  let () = output_string fail_file content in
  Log.last_proof_command # dump;
  flush fail_file;
  close_out fail_file

let check_answer_x (mona_file_content: string) (answ: string) (is_sat_b: bool)= 
  let imp_sat_str = match is_sat_b with
    | true -> "sat"
    | false -> "imply" in
  let answer =
    match answ with
    | "Formula is valid" ->
      if !log_all_flag==true then begin
        output_string log_all (" [mona.ml]: --> SUCCESS\n");
        output_string log_all ("[mona.ml]: " ^ imp_sat_str ^ " --> true\n");
      end;
      true;
    | "Formula is satisfiable or unknown" -> (*TO CHECK*)
      if !log_all_flag==true then begin
        output_string log_all (" [mona.ml]: --> Formula is satisfiable or unknown\n");
        output_string log_all ("[mona.ml]: " ^ imp_sat_str ^ " --> "  ^ (string_of_bool is_sat_b) ^ "\n");
      end;
      is_sat_b;
    | "Formula is unsatisfiable" -> 
      if !log_all_flag == true then
        output_string log_all ("[mona.ml]:" ^ imp_sat_str ^" --> false \n");
      false;
    | "Formula is too large" -> 
      begin
        if !log_all_flag == true then
          output_string log_all ("[mona.ml]: "^ imp_sat_str ^" --> " ^(string_of_bool is_sat_b) ^"(formula too large - not processed by mona)\n");
        print_endline_quiet ("[mona] Warning: "^ imp_sat_str ^" --> " ^(string_of_bool is_sat_b) ^"(formula too large  - not processed by mona)\n");
        is_sat_b;
      end
    | "" ->
      (* process might have died. maybe BDD was too large - restart mona*)
      (* print_string "MONA aborted execution! Restarting..."; *)
      let () = create_failure_file mona_file_content in
      restart "mona aborted execution";
      if !log_all_flag == true then
        output_string log_all ("[mona.ml]: "^ imp_sat_str ^" --> " ^(string_of_bool is_sat_b) ^"(from failure - formula too complex --> Mona aborted)\n");
      print_endline_if (not !compete_mode) ("[mona] Warning: "^ imp_sat_str ^" --> " ^(string_of_bool is_sat_b) ^"(from mona failure - formula too complex --> Mona aborted)\n");
      is_sat_b
    | s ->
      let () = create_failure_file mona_file_content in
      try
        let (todo_unk:int) = Str.search_forward (Str.regexp "Error in file") answ 0 in
        Error.report_error {
          Error.error_loc = no_pos;
          Error.error_text =("Mona translation failure: " ^ answ)
        }
      with
      | Not_found ->
        begin
          if !log_all_flag == true then
            output_string log_all ("[mona.ml]: "^ imp_sat_str ^" --> " ^(string_of_bool is_sat_b) ^"(from mona failure --> Mona aborted)\n");
          print_endline_quiet ("[mona] Warning: "^ imp_sat_str ^" --> " ^(string_of_bool is_sat_b) ^"(from mona failure --> Mona aborted)\n");
          is_sat_b;
        end
  in
  answer

let check_answer (mona_file_content: string) (answ: string) (is_sat_b: bool)= 
  Debug.no_3 "check_answer"
    (fun str -> str)
    (fun str -> str)
    string_of_bool
    string_of_bool
    check_answer_x mona_file_content answ is_sat_b

let maybe_restart_mona () : unit =
  if !is_mona_running then begin
    let num_tasks = !test_number - !last_test_number in
    if num_tasks >=(!mona_cycle) then restart "cycle limit reached"
  end

let prepare_formula_for_mona pr_w pr_s (f: CP.formula) (test_no: int): CP.spec_var list * CP.formula =
  let simp_f =  x_add CP.arith_simplify 8 f in
  let simp_f = (preprocess_formula pr_w pr_s simp_f) in
  let f_fv = CP.fv simp_f in
  let rename_spec_vars_fnct sv = 
    let new_name = ((CP.name_of_spec_var sv)^"_r"^(string_of_int test_no)) in
    CP.SpecVar (CP.type_of_spec_var sv, new_name, if CP.is_primed sv then Primed else Unprimed) in
  let renamed_f_fv = List.map rename_spec_vars_fnct f_fv in
  let renamed_f = CP.subst_avoid_capture f_fv renamed_f_fv simp_f in
  (renamed_f_fv, renamed_f)

let read_from_file chn: string = 
  let answ =  ref "" in
  try
    while true do
      let line = input_line chn in
      let rec search_str str_lst line =
        match str_lst with
        | [] -> ""
        | h::t -> 
          try 
            let (todo_unk:int) = Str.search_forward (Str.regexp h) line 0 in
            answ := h;
            raise End_of_file
          with
          | Not_found -> search_str t line;
      in
      answ := search_str ["Formula is valid"; "Formula is unsatisfiable";"Error in file"] line
    done;
    !answ
  with 
  | End_of_file ->  close_in chn; !answ


let create_file_for_mona_x (filename: string) (fv: CP.spec_var list) (f: CP.formula) (imp_no: string) vs =
  let mona_file = open_out filename in
  let mona_pred_file_x = get_mona_predicates_file () in
  output_string mona_file ("include \""^ mona_pred_file_x ^"\";\n");
  let f_str =
    try 
      begin
        let all_fv = CP.remove_dups_svl fv in
        (* let (part1, part2) = (List.partition (fun (sv) -> ((\*is_firstorder_mem*\)part_firstorder_mem *)
        (* (CP.Var(sv, no_pos)) vs)) all_fv) in  (\*deprecated*\) *)
        let (part1, part2) = (List.partition (fun sv -> is_firstorder_mem_sv sv vs) all_fv) in
        let first_order_var_decls =
          if Gen.is_empty part1 then ""
          else "var1 " ^ (String.concat ", " (List.map mona_of_spec_var part1)) ^ ";\n " in
        let second_order_var_decls =
          if Gen.is_empty part2 then ""
          else "var2 " ^ (String.concat ", " (List.map mona_of_spec_var part2)) ^ "; \n"in
        let var_decls = first_order_var_decls ^ second_order_var_decls in
        var_decls ^(mona_of_formula f f vs)
      end
    with exc -> print_endline_quiet ("\nEXC: " ^ Printexc.to_string exc); ""
  in
  if not (f_str == "") then  output_string mona_file (f_str ^ ";\n" );
  flush mona_file;
  close_out mona_file;
  f_str

let create_file_for_mona (filename: string) (fv: CP.spec_var list) (f: CP.formula) (imp_no: string) vs =
  Debug.no_1 "create_file_for_mona" Gen.pr_id Gen.pr_id (fun _ -> create_file_for_mona_x filename fv f imp_no vs ) filename

let write_to_file  (is_sat_b: bool) (fv: CP.spec_var list) (f: CP.formula) (imp_no: string) vs: bool =
  let mona_filename = "test" ^ imp_no ^ ".mona" in
  let file_content = ((create_file_for_mona mona_filename fv f imp_no vs) ^ ";\n") in
  (* let () = print_string("\nFile content of ["^mona_filename^"]:\n"^file_content^"[end of file]\n") in *)
  if !log_all_flag == true then
    begin
      output_string log_all (mona_filename ^ Gen.new_line_str);
      output_string log_all file_content;
      flush log_all;
    end;
  let () = Procutils.PrvComms.start !log_all_flag log_all ("mona", "mona", [|"mona"; "-q";  mona_filename|]) set_process (fun () -> ()) in
  let fnc () =
    let mona_answ = read_from_file !process.inchannel in
    let () = x_binfo_hp (add_str "mona_answ" pr_id) mona_answ no_pos  in
    let res = x_add check_answer file_content mona_answ is_sat_b in
    res
  in
  (* let res = Procutils.PrvComms.maybe_raise_timeout_num 2 fnc () !mona_timeout in  *)
  let t = (if is_sat_b then "SAT no :" else "IMPLY no :")^imp_no in
  (* let hproc exc = (print_endline ("Timeout for MONA "^t));true in *)
  let hproc () =   
    if not !Globals.web_compile_flag then print_string ("\n[MONA.ml]:Timeout exception "^t^"\n"); flush stdout;
    restart ("Timeout!");
    is_sat_b in
  let timeout  = if is_sat_b&& !user_sat_timeout then !sat_timeout_limit else !mona_timeout in
  let res = Procutils.PrvComms.maybe_raise_and_catch_timeout_bool fnc () timeout hproc in 
  Sys.remove mona_filename;
  stop();
  res

let write_to_file (is_sat_b: bool) (fv: CP.spec_var list) (f: CP.formula) (imp_no: string) vs: bool =
  Debug.no_2 "[mona.ml]: write_to_file" string_of_bool
    Cprinter.string_of_pure_formula
    string_of_bool
    (fun _ _ -> write_to_file is_sat_b fv f imp_no vs) is_sat_b f

let imply_sat_helper_x (is_sat_b: bool) (fv: CP.spec_var list) (f: CP.formula) (imp_no: string) vs : bool =
  let all_fv = CP.remove_dups_svl fv in
  (* let () = print_endline("[Mona] imply_sat_helper : vs = " ^ (string_of_hashtbl vs) ) in *)
  (* let (part1, part2) = (List.partition (fun (sv) -> ((\*is_firstorder_mem*\)part_firstorder_mem *)
  (*       (CP.Var(sv, no_pos)) vs)) all_fv) in  (\*deprecated*\) *)
  let (part1, part2) = (List.partition (fun (sv) -> (is_firstorder_mem_sv sv vs)) all_fv) in
  let first_order_var_decls =
    if Gen.is_empty part1 then ""
    else "var1 " ^ (String.concat ", " (List.map mona_of_spec_var part1)) ^ "; " in
  let second_order_var_decls =
    if Gen.is_empty part2 then ""
    else "var2 " ^ (String.concat ", " (List.map mona_of_spec_var part2)) ^ "; "in

  let cmd_to_send = ref "" in
  cmd_to_send := mona_of_formula f f vs;
  if not (Gen.is_empty part2) then
    cmd_to_send := second_order_var_decls ^ (!cmd_to_send) ;
  if not (Gen.is_empty part1) then
    cmd_to_send := first_order_var_decls  ^ (!cmd_to_send) ;
  cmd_to_send := !cmd_to_send ^ ";\n";
  let content = ("include \"" ^ get_mona_predicates_file () ^ "\";\n" ^ !cmd_to_send) in
  try
    begin
      let () = maybe_restart_mona () in
      (* let _  = print_endline "sending to mona prover.." in *)
      let answer = send_cmd_with_answer !cmd_to_send in
      let () = x_tinfo_hp (add_str "answer" pr_id) answer no_pos  in
      x_add check_answer content answer is_sat_b
    end
  with
  |Procutils.PrvComms.Timeout ->
    begin
      if not !Globals.web_compile_flag then print_string ("\n[mona.ml]:Timeout exception\n"); flush stdout;
      restart ("Timeout when checking #" ^ imp_no ^ "!");
      is_sat_b
    end
  | exc ->
    print_string ("\n[mona.ml]:Unexpected exception\n"); flush stdout;
    stop(); raise exc

let imply_sat_helper (is_sat_b: bool) (fv: CP.spec_var list) (f: CP.formula) (imp_no: string) sv : bool =
  let pr = Cprinter.string_of_spec_var_list in
  Debug.no_2 "imply_sat_helper"
    pr
    Cprinter.string_of_pure_formula
    string_of_bool
    (fun _ _  -> imply_sat_helper_x is_sat_b fv f imp_no sv) fv f

let imply_ops pr_w pr_s (ante : CP.formula) (conseq : CP.formula) (imp_no : string) : bool =
  (* let () = if not !is_mona_running then start () else () in *)
  let () = Gen.Profiling.inc_counter "stat_mona_count_imply" in
  if !log_all_flag == true then
    output_string log_all ("\n\n[mona.ml]: imply # " ^ imp_no ^ "\n");
  incr test_number;
  (* let ante = CP.drop_varperm_formula ante in     *)
  (* let conseq = CP.drop_varperm_formula conseq in *)
  let (ante,conseq) = Trans_arr.translate_array_imply ante conseq in
  let (ante_fv, ante) = prepare_formula_for_mona pr_w pr_s ante !test_number in
  let (conseq_fv, conseq) = prepare_formula_for_mona pr_s pr_w conseq !test_number in
  let tmp_form = CP.mkOr (CP.mkNot ante None no_pos) conseq None no_pos in
  (*let tmp_form = Trans_arr.translate_array_one_formula_for_validity tmp_form in*)
  let tmp_form = x_add_1 CP.subs_const_var_formula tmp_form in
  let tmp_form = if true (* !Globals.non_linear_flag *) then x_add_1 CP.drop_nonlinear_formula_rev tmp_form else tmp_form in
  (* let vs = Hashtbl.create 10 in *)
  (* let () = find_order tmp_form vs in    (\* deprecated *\) *)
  let (var1,var2,var0) = new_order_formula tmp_form in
  let () = set_prover_type () in (* change to MONA logging *)
    write_to_file false (ante_fv @ conseq_fv) tmp_form imp_no (var1,var2)
  (* if not !is_mona_running then
      write_to_file false (ante_fv @ conseq_fv) tmp_form imp_no (var1,var2)
    (* write_to_file false (ante_fv @ conseq_fv) tmp_form imp_no vs (\* deprecated *\) *)
  else
    imply_sat_helper false (ante_fv @ conseq_fv) tmp_form imp_no (var1,var2) *)
(* imply_sat_helper false (ante_fv @ conseq_fv) tmp_form imp_no vs (\* deprecated *\)  *)

let imply_ops pr_w pr_s (ante : CP.formula) (conseq : CP.formula) (imp_no : string) : bool =
  let pr = Cprinter.string_of_pure_formula in
  Debug.no_3 "mona.imply" pr pr (fun x -> x) string_of_bool 
    (fun _ _ _ -> imply_ops pr_w pr_s ante conseq imp_no) ante conseq imp_no

let imply_ops pr_w pr_s (ante : CP.formula) (conseq : CP.formula) (imp_no : string) : bool =
  Gen.Profiling.do_1 "mona.imply"
    (imply_ops pr_w pr_s ante conseq) imp_no

let is_sat_ops_x pr_w pr_s (f : CP.formula) (sat_no :  string) : bool =
  let f = Trans_arr.translate_array_one_formula f in
  (* let () = if not !is_mona_running then start () else () in *)
  let () = Gen.Profiling.inc_counter "stat_mona_count_sat" in
  if !log_all_flag == true then
    output_string log_all ("\n\n[mona.ml]: #is_sat " ^ sat_no ^ "\n");
  sat_optimize := true;
  incr test_number;
  (* let f = CP.drop_varperm_formula f in *)
  let f = if true (* !Globals.non_linear_flag *) then x_add_1 Cpure.drop_nonlinear_formula f else f in
  let (f_fv, f) = prepare_formula_for_mona pr_w pr_s f !test_number in
  (* let vs = Hashtbl.create 10 in *)
  (* let () = find_order f vs in (\* deprecated *\) *)
  let (var1, var2, _) = new_order_formula f in
  let () = set_prover_type () in (* change to MONA logging *)
  (* WN : what if var0 is non-empty? *)
  (* print_endline ("Mona.is_sat: " ^ (string_of_int !test_number) ^ " : " ^ (string_of_bool !is_mona_running)); *)
  let sat = 
    write_to_file true f_fv f sat_no (var1, var2) in
  (* if not !is_mona_running then
      begin
          let () = print_string ("mona not running?..\n") in
          write_to_file true f_fv f sat_no (var1, var2)
        (* write_to_file true f_fv f sat_no vs (\* deprecated *\) *)
      end
    else
      imply_sat_helper true f_fv f sat_no (var1, var2) in *)
  (* imply_sat_helper true f_fv f sat_no vs in (\* deprecated *\) *)
  sat_optimize := false;
  sat
;;

(*let imply = imply (-1.);;*)

let is_sat_ops pr_w pr_s (f : CP.formula) (sat_no :  string) : bool =
  let pr = Cprinter.string_of_pure_formula in
  Debug.no_2 "mona.is_sat_ops" pr (fun x -> x) string_of_bool 
    (fun _ _ -> is_sat_ops_x pr_w pr_s f sat_no) f sat_no

let is_sat_ops pr_w pr_s (f : CP.formula) (sat_no :  string) : bool =
  Gen.Profiling.do_1 "mona.is_sat_ops"
    (is_sat_ops pr_w pr_s f) sat_no

(* TODO: implement the following procedures; now they are only dummies *)
let hull (pe : CP.formula) : CP.formula = begin
  (*if !log_all_flag == true then
    	  output_string log_file "\n\n[mona.ml]: #hull\n";*)
  pe
end
let pairwisecheck (pe : CP.formula) : CP.formula = begin
  (*if !log_all_flag == true then
    	  output_string log_file "\n\n[mona.ml]: #pairwisecheck\n";*)
  pe
end
let simplify (pe : CP.formula) : CP.formula = begin
  (*if !log_all_flag == true then
    	  output_string log_file "\n\n[mona.ml]: #simplify\n";*)
  pe
end
(*| CP.EqMax (a1, a2, a3, _) ->
  	  let a1str = (mona_of_exp a1 f) in
  	  let a2str = (mona_of_exp a2 f) in
  	  let a3str = (mona_of_exp a3 f) in
  	  ("((" ^ a3str ^ " <= " ^ a2str ^ " & " ^ a1str ^ " = " ^ a2str ^ ") | ("
  		^ a2str ^ " < " ^ a3str ^ " & " ^ a1str ^ " = " ^ a3str ^ "))\n")*)
