#include "xdebug.cppo"
open VarGen
(*
  15-06-2006
*)

open Globals
module CP = Cpure

let is_mona_running = ref false
(* let channels = ref (stdin, stdout, stdin) *)
let last_test_number = ref 0
let test_number = ref 0
let mona_cycle = ref 90
let timeout = ref 11.0 (* default timeout is 10 seconds *)

let result_file_name = "res"
let log_all_flag = ref false
let log_all = open_log_out "allinput.mona"

let automaton_completed = ref false
let sat_optimize = ref false
let mona_pred_file = "mona_predicates.mona"
let mona_pred_file_alternative_path = "/usr/local/lib/"

let process = ref {name = "mona"; pid = 0;  inchannel = stdin; outchannel = stdout; errchannel = stdin}



(* pretty printing for primitive types *)
let rec mona_of_typ = function
  | Bool          -> "int"
  | Float         -> "float"	(* Can I really receive float? What do I do then? I don't have float in Mona. *)
  | Int           -> "int"
  | Void          -> "void" 	(* same as for float *)
  | BagT i		  -> "("^(mona_of_typ i)^") set"
  | TVar i        -> "TVar["^(string_of_int i)^"]"
  | UNK           -> 	
    Error.report_error {Error.error_loc = no_pos; 
                        Error.error_text = "unexpected UNKNOWN type"}
  | List t        -> "("^(mona_of_typ t)^") list"	(* lists are not supported *)
  | NUM | Named _ | Array _ ->
    Error.report_error {Error.error_loc = no_pos; 
                        Error.error_text = "array and named type not supported for mona"}

(*------------------------------------------*)
let rec mkEq l = match l with
  | e :: [] -> CP.BForm(e,None)
  | e :: rest -> CP.And(CP.BForm(e,None), (mkEq rest), no_pos)
  | _ -> assert false

let rec mkEx l f = match l with
  | [] -> f
  | sv :: rest -> mkEx rest (CP.Exists(sv, f, None, no_pos))

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
and preprocess_exp (e0 : CP.exp) : (CP.exp * CP.formula * CP.spec_var list) = 
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
and preprocess_formula (f : CP.formula) : CP.formula =
  match f with
  | CP.Or (p1, p2,lbl, l1) -> (CP.mkOr (preprocess_formula p1) (preprocess_formula p2) lbl l1)
  | CP.And (p1, p2, l1) -> (CP.mkAnd (preprocess_formula p1) (preprocess_formula p2) l1)
  | CP.Not (p1,lbl, l1) -> CP.Not((preprocess_formula p1),lbl, l1)
  | CP.Forall(sv1, p1,lbl, l1) -> CP.Forall(sv1, (preprocess_formula p1),lbl, l1)
  | CP.Exists(sv1, p1,lbl, l1) -> CP.Exists(sv1, (preprocess_formula p1),lbl, l1)

  | CP.BForm (b,lbl) -> 
    let (bf, constr, ev) = preprocess_b_formula b in
    (mkEx ev (CP.mkAnd (CP.BForm(bf, lbl)) constr no_pos))


(* 

   HASH TABLE CONSTRUCTION:
   This hash table maps each var to:
     0 - unknown (unconstrained)
     1 - first order
     2 - second order

*)

and find_order (f : CP.formula) vs = 
  let r = find_order_formula f vs in
  if r then (find_order f vs)

and find_order_formula (f : CP.formula) vs : bool  = match f with
  | CP.And(f1, f2, _)
  | CP.Or(f1, f2, _,_) -> ((find_order_formula f1 vs) || (find_order_formula f2 vs))
  (* make sure everything is renamed *)
  | CP.Forall(_, f1, _,_)
  | CP.Exists(_, f1, _,_)
  | CP.Not(f1, _,_) -> (find_order_formula f1 vs)
  | CP.BForm(bf,_) -> (find_order_b_formula bf vs)

and find_order_b_formula (bf : CP.b_formula) vs : bool =
  let rec exp_order e vs =
    match e with
    | CP.Var(sv, l) ->
      begin
        try
          Hashtbl.find vs sv
        with
        | Not_found -> 0
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

  in
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
          Error.report_error { Error.error_loc = l1; Error.error_text = ("Mona translation failure for variable " ^ (Cprinter.string_of_spec_var sv1) ^ "\n")}
        else 
        if (r == 0) then
          ((Hashtbl.replace vs sv1 1); true)
        else false
      with
      | Not_found -> ((Hashtbl.add vs sv1 1); true)
    in
    let r2 = 
      try
        let r = Hashtbl.find vs sv2 in
        if (r == 1) then 
          Error.report_error { Error.error_loc = l1; Error.error_text = ("Mona translation failure for variable " ^ (Cprinter.string_of_spec_var sv2) ^ "\n")}
        else 
        if(r == 0) then
          ((Hashtbl.replace vs sv1 2); true)
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
  | CP.Gt(e1, e2, _)
  | CP.Gte(e1, e2, _) -> 
    (* let () = print_string("find_order_exp for " ^ (Cprinter.string_of_formula_exp e1) ^ " and "  ^ (Cprinter.string_of_formula_exp e2) ^ "\n") in *)
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
          Error.report_error { Error.error_loc = l1; Error.error_text = ("Mona translation failure for variable " ^ (Cprinter.string_of_spec_var sv1) ^ "\n")}
        else
        if(r == 0) then
          (Hashtbl.replace vs sv1 2; true)
        else false
      with
      | Not_found -> (Hashtbl.replace vs sv1 2; true)
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


(*
  order = 0 --> unknown
        = 1 --> inside bag
        = 2 --> bag
*)
and find_order_exp (e : CP.exp) order vs = match e with
  | CP.Var(sv1, l1) -> 
    begin
      try
        let r = Hashtbl.find vs sv1 in 
        if (r == 0 && order != 0) then
          ((Hashtbl.replace vs sv1 order); true) 
        else
        if ((r == 1 && order == 2) || (r == 2 && order == 1)) then
          Error.report_error { Error.error_loc = l1; Error.error_text = ("Mona translation failure for variable " ^ (Cprinter.string_of_spec_var sv1) ^ "\n")}
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

(*

  HASH TABLE INTEROGATION

*)

and is_firstorder_mem e vs =
  Debug.no_1 "is_firstorder_mem" Cprinter.string_of_formula_exp string_of_bool (fun e -> is_firstorder_mem_a e vs) e

and is_firstorder_mem_a e vs =
  match e with
  | CP.Var(sv1, l1) ->
    begin
      try 
        let r = Hashtbl.find vs sv1 in 
        if (r == 1) then true
        else false
      with 
      | Not_found -> Error.report_error { Error.error_loc = l1; Error.error_text = (" Error during Mona translation for var " ^ (Cprinter.string_of_spec_var sv1) ^ "\n")}
    end
  | CP.IConst _ 
  | CP.Null _ -> true
  | _ -> false


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
    | CP.BagUnion (e::rest, l) -> (helper e) ^ " union " ^ (helper (CP.BagUnion (rest, l)))
    | CP.BagIntersect ([], _) -> ""
    | CP.BagIntersect (e::[], _) -> (helper e)
    | CP.BagIntersect (e::rest, l)->(helper e) ^ " inter " ^ (helper (CP.BagIntersect (rest, l)))
    | CP.BagDiff (e1, e2, _)     -> (helper e1) ^ "\\" ^ (helper e2)
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
  | CP.Add (a1, a2, pos) ->  
    let tmp = fresh_var_name "int" pos.start_pos.Lexing.pos_lnum in
    let (exs1, a1name, a1str) = mona_of_exp_secondorder a1 f in
    let (exs2, a2name, a2str) = mona_of_exp_secondorder a2 f in
    let add_string = " plus(" ^ a1name ^ ", " ^ a2name ^ ", " ^ tmp ^ ")" in
    let add_string2 = add_string ^ (if a1str <> "" then (" & " ^ a1str) else "") ^ (if a2str <> "" then (" & " ^ a2str) else "") in
    ((tmp :: (exs1 @ exs2)), tmp, add_string2)
  | CP.Max _
  | CP.Min _ -> failwith ("mona.mona_of_exp_secondorder: min/max can never appear here")
  | CP.TypeCast _ -> failwith ("mona.mona_of_exp_secondorder: TypeCast can never appear here")
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
    | CP.BConst (c, _) -> if c then "(0 = 0)" else "(~ (0 <= 0))"
    | CP.BVar (bv, _) -> "greater(" ^ (mona_of_spec_var bv) ^ ", pconst(0))"
    (* CP.Lt *)   
    (*| CP.Lt((CP.Subtract(a3, a1, pos1)), a2, pos2) -> (mona_of_b_formula (CP.Lt(a3, CP.Add(a2, a1, pos1), pos2)) f vs)	 
      | CP.Lt(a2, (CP.Subtract(a3, a1, pos1)), pos2) -> (mona_of_b_formula (CP.Lt(CP.Add(a2, a1, pos1), a3, pos2)) f vs)	 *)
    | CP.Lt (a1, a2, _) -> (equation a1 a2 f "less" "<" vs)
    (* CP.Lte *)   
    (*| CP.Lte((CP.Subtract(a3, a1, pos1)), a2, pos2) -> (mona_of_b_formula (CP.Lte(a3, CP.Add(a2, a1, pos1), pos2)) f vs)	 
      | CP.Lte(a2, (CP.Subtract(a3, a1, pos1)), pos2) -> (mona_of_b_formula (CP.Lte(CP.Add(a2, a1, pos1), a3, pos2)) f vs)	 *)
    | CP.Lte (a1, a2, _) -> (equation a1 a2 f "lessEq" "<=" vs)
    (* CP.Gt *)   
    (*| CP.Gt((CP.Subtract(a3, a1, pos1)), a2, pos2) -> (mona_of_b_formula (CP.Gt(a3, CP.Add(a2, a1, pos1), pos2)) f vs)	 
      | CP.Gt(a2, (CP.Subtract(a3, a1, pos1)), pos2) -> (mona_of_b_formula (CP.Gt(CP.Add(a2, a1, pos1), a3, pos2)) f vs)	 *)
    | CP.Gt (a1, a2, _) -> (equation a1 a2 f "greater" ">" vs)
    (* CP.Gte *)   
    (*| CP.Gte((CP.Subtract(a3, a1, pos1)), a2, pos2) -> (mona_of_b_formula (CP.Gte(a3, CP.Add(a2, a1, pos1), pos2)) f vs)	 
      | CP.Gte(a2, (CP.Subtract(a3, a1, pos1)), pos2) -> (mona_of_b_formula (CP.Gte(CP.Add(a2, a1, pos1), a3, pos2)) f vs)	 *)
    | CP.Gte (a1, a2, _) -> (equation a1 a2 f "greaterEq" ">=" vs)
    | CP.Neq (CP.IConst(i, _), a1, _)
    | CP.Neq (a1, CP.IConst(i, _), _) ->
      if (is_firstorder_mem a1 vs) then
        "(" ^ (mona_of_exp a1 f) ^ " ~= " ^ (string_of_int i) ^ ")"
      else
        "(" ^ (mona_of_exp a1 f) ^ " ~= pconst(" ^ (string_of_int i) ^ "))"
    | CP.Neq (a, CP.Null _, _) 
    | CP.Neq (CP.Null _, a, _) ->
      if (is_firstorder_mem a vs) then
        "(" ^ (mona_of_exp a f) ^ " > 0)"
      else
        " greater(" ^ (mona_of_exp a f) ^ ", pconst(0))"
    | CP.Neq (a1, a2, _) ->
      if (is_firstorder_mem a1 vs)&& (is_firstorder_mem a2 vs) then
        "(" ^ (mona_of_exp a1 f) ^ " ~= " ^ (mona_of_exp a2 f) ^ ")"
      else
        let (a1name,a2name,str,end_str) = second_order_composite2 a1 a2 f in
        str ^ " nequal(" ^ a1name ^ ", " ^ a2name ^ ") "^ end_str
    | CP.Eq((CP.Add(a1, a2, _)), a3, _)
    | CP.Eq(a3, (CP.Add(a1, a2, _)), _) ->
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
    | CP.Eq (a1, CP.Null _, _) 
    | CP.Eq (CP.Null _, a1, _) ->
      if (is_firstorder_mem a1 vs) then
        "(" ^ (mona_of_exp a1 f) ^ " = 0)"
      else
        "(" ^ (mona_of_exp a1 f) ^ " = pconst(0))"
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
  | CP.BConst (c, _) -> if c then "(0 = 0)" else "(~ (0 <= 0))"
  | CP.BVar (bv, _) -> "greater(" ^ (mona_of_spec_var bv) ^ ",pconst(0))" 
  | CP.Lt (a1, a2, _) -> (mona_of_exp a1 f) ^ "<" ^ (mona_of_exp a2 f)
  | CP.Lte (a1, a2, _) -> (mona_of_exp a1 f) ^ "<=" ^ (mona_of_exp a2 f)
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
  | CP.RelForm _ -> failwith ("Arrays are not supported in Mona") (* An Hoa *)

let rec get_answer chn : string =
  let chr = input_char chn in
  match chr with
  |'\n' ->  ""
  | 'a'..'z' | 'A'..'Z' | ' ' -> (Char.escaped chr) ^ get_answer chn (*save only alpha characters*)
  | _ -> "" ^ get_answer chn


let send_cmd_with_answer str =
  if!log_all_flag==true then
    output_string log_all str;
  let fnc () = 
    let () = (output_string !process.outchannel str;
              flush !process.outchannel) in
    let str = get_answer !process.inchannel in
    str 
  in 
  let answ = Procutils.PrvComms.maybe_raise_timeout_num 1 fnc () !timeout in
  answ

(* modify mona for not sending answers *)
let send_cmd_no_answer str =
  (* let () = (print_string ("\nsned_cmd_no_asnwer " ^ str ^"- end string\n"); flush stdout) in *)
  let (todo_unk:string) = send_cmd_with_answer str in
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
  send_cmd_no_answer ("include \"" ^ mona_pred_file_x ^ "\";\n")

let set_process (proc: Globals.prover_process_t) = 
  process := proc

let rec check_prover_existence prover_cmd_str: bool =
  let exit_code = Sys.command ("which "^prover_cmd_str^">/dev/null") in
  if exit_code > 0 then
    (* let () = print_string ("WARNING: Command for starting mona interactively (" ^ prover_cmd_str ^ ") not found!\n") in *)
    false
  else true

let start () = 
  last_test_number := !test_number;
  if(check_prover_existence "mona_inter")then begin
    let () = Procutils.PrvComms.start !log_all_flag log_all ("mona", "mona_inter", [|"mona_inter"; "-v";|]) set_process prelude in
    is_mona_running := true
  end

let stop () = 
  let killing_signal = 
    match !is_mona_running with
    |true -> is_mona_running := false;  2
    |false -> 9 in
  let num_tasks = !test_number - !last_test_number in
  let () = Procutils.PrvComms.stop !log_all_flag log_all !process num_tasks killing_signal (fun () -> ()) in
  is_mona_running := false

let restart reason =
  if !is_mona_running then 
    Procutils.PrvComms.restart !log_all_flag log_all reason "mona" start stop

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
  flush fail_file;
  close_out fail_file

let check_answer (mona_file_content: string) (answ: string) (is_sat_b: bool)= 
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
      true
    | "Formula is unsatisfiable" -> 
      if !log_all_flag == true then
        output_string log_all ("[mona.ml]:" ^ imp_sat_str ^" --> false \n");
      false;
    | "" ->
      (* process might have died. maybe BDD was too large - restart mona*)
      (* print_string "MONA aborted execution! Restarting..."; *)
      let () = create_failure_file mona_file_content in
      restart "mona aborted execution";
      if !log_all_flag == true then
        output_string log_all ("[mona.ml]: "^ imp_sat_str ^" --> " ^(string_of_bool is_sat_b) ^"(from mona failure)\n");
      is_sat_b
    | _ ->
      let () = create_failure_file mona_file_content in
      try
        let (todo_unk:int) = Str.search_forward (Str.regexp "Error in file") answ 0 in
        (print_string "MONA translation failure!";
         Error.report_error { Error.error_loc = no_pos; Error.error_text =("Mona translation failure!!\n"^answ)})
      with
      | Not_found ->
        begin
          if !log_all_flag == true then
            output_string log_all ("[mona.ml]: "^ imp_sat_str ^" --> " ^(string_of_bool is_sat_b) ^"(from mona failure)\n");
          is_sat_b;
        end
  in
  answer

let maybe_restart_mona () : unit =
  if !is_mona_running then begin
    let num_tasks = !test_number - !last_test_number in
    if num_tasks >=(!mona_cycle) then restart "upper limit reached"
  end

let prepare_formula_for_mona (f: CP.formula) (test_no: int): CP.spec_var list * CP.formula =
  let simp_f =  x_add CP.arith_simplify 8 f in
  let simp_f = (preprocess_formula simp_f) in
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


let create_file_for_mona (filename: string) (fv: CP.spec_var list) (f: CP.formula) (imp_no: string) vs =
  let mona_file = open_out filename in
  let mona_pred_file_x = get_mona_predicates_file () in
  output_string mona_file ("include \""^ mona_pred_file_x ^"\";\n");
  let f_str =
    try 
      begin
        let all_fv = CP.remove_dups_svl fv in
        (* let vs = Hashtbl.create 10 in *)
        (* let () = find_order f vs in *)
        let (part1, part2) = (List.partition (fun (sv) -> (is_firstorder_mem (CP.Var(sv, no_pos)) vs)) all_fv) in
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

let write_to_file  (is_sat_b: bool) (fv: CP.spec_var list) (f: CP.formula) (imp_no: string) vs : bool =
  let mona_filename = "test" ^ imp_no ^ ".mona" in
  let file_content = ((create_file_for_mona mona_filename fv f imp_no vs) ^ ";\n") in
  if !log_all_flag == true then
    begin
      output_string log_all (mona_filename ^ Gen.new_line_str);
      output_string log_all file_content;
      flush log_all;
    end;
  let () = Procutils.PrvComms.start !log_all_flag log_all ("mona", "mona", [|"mona"; "-q";  mona_filename|]) set_process (fun () -> ()) in
  let fnc () =
    let mona_answ = read_from_file !process.inchannel in
    let res = check_answer file_content mona_answ is_sat_b in
    res
  in
  (* let res = Procutils.PrvComms.maybe_raise_timeout_num 2 fnc () !timeout in  *)
  let t = (if is_sat_b then "SAT no :" else "IMPLY no :")^imp_no in
  (* let hproc exc = (print_endline ("Timeout for MONA "^t));true in *)
  let hproc () =   
    print_string ("\n[MONA.ml]:Timeout exception "^t^"\n"); flush stdout;
    restart ("Timeout!");
    is_sat_b in
  let res = Procutils.PrvComms.maybe_raise_and_catch_timeout_bool fnc () !timeout hproc in 
  Sys.remove mona_filename;
  stop();
  res

let imply_sat_helper (is_sat_b: bool) (fv: CP.spec_var list) (f: CP.formula) (imp_no: string) vs : bool =
  let all_fv = CP.remove_dups_svl fv in
  (* let () = print_string("f = " ^ (Cprinter.string_of_pure_formula f) ^ "\n") in *)
  (* let () = Hashtbl.iter (fun x y -> (print_string ("var " ^ (Cprinter.string_of_spec_var x) ^ " --> " ^ (string_of_int y) ^ "\n"))) vs in *)
  let (part1, part2) = (List.partition (fun (sv) -> (is_firstorder_mem (CP.Var(sv, no_pos)) vs)) all_fv) in
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
  let content = ("include mona_predicates.mona;\n" ^ !cmd_to_send) in
  try
    begin
      let () = maybe_restart_mona () in
      let answer = send_cmd_with_answer !cmd_to_send in
      check_answer content answer is_sat_b
    end
  with
  |Procutils.PrvComms.Timeout ->
    begin
      print_string ("\n[mona.ml]:Timeout exception\n"); flush stdout;
      restart ("Timeout when checking #" ^ imp_no ^ "!");
      is_sat_b
    end
  | exc ->
    print_string ("\n[mona.ml]:Unexpected exception\n"); flush stdout;
    stop(); raise exc

let imply (ante : CP.formula) (conseq : CP.formula) (imp_no : string) : bool =
  if !log_all_flag == true then
    output_string log_all ("\n\n[mona.ml]: imply # " ^ imp_no ^ "\n");
  incr test_number;
  let (ante_fv, ante) = prepare_formula_for_mona ante !test_number in
  let (conseq_fv, conseq) = prepare_formula_for_mona conseq !test_number in
  let tmp_form = CP.mkOr (CP.mkNot ante None no_pos) conseq None no_pos in
  let vs = Hashtbl.create 10 in
  let () = find_order tmp_form vs in
  if not !is_mona_running then
    write_to_file false (ante_fv @ conseq_fv) tmp_form imp_no vs
  else
    imply_sat_helper false (ante_fv @ conseq_fv) tmp_form imp_no vs

let imply (ante : CP.formula) (conseq : CP.formula) (imp_no : string) : bool =
  let pr = Cprinter.string_of_pure_formula in
  Debug.no_3 "mona.imply" pr pr (fun x -> x) string_of_bool 
    imply ante conseq imp_no

let is_sat (f : CP.formula) (sat_no :  string) : bool =
  if !log_all_flag == true then
    output_string log_all ("\n\n[mona.ml]: #is_sat " ^ sat_no ^ "\n");
  sat_optimize := true;
  incr test_number;
  let (f_fv, f) = prepare_formula_for_mona f !test_number in
  let vs = Hashtbl.create 10 in
  let () = find_order f vs in
  let sat = 
    if not !is_mona_running then
      write_to_file true f_fv f sat_no vs
    else
      imply_sat_helper true f_fv f sat_no vs in
  sat_optimize := false;
  sat
;;

(*let imply = imply (-1.);;*)

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
