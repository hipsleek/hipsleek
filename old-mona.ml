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
let first_order_vars = ref ([] : CP.spec_var list)
let second_order_vars = ref ([] : CP.spec_var list)
let additional_vars = ref ([] : CP.spec_var list)
let additional_vars_ = ref ([] : CP.spec_var list)
let substitution_list = ref ([] : CP.b_formula list)
let automaton_completed = ref false
let cycle = ref false
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
  | e :: [] -> CP.BForm(e,None,None)
  | e :: rest -> CP.And(CP.BForm(e,None,None), (mkEq rest), no_pos)
  | _ -> assert false

let rec mkEx l f = match l with
 | [] -> f
 | sv :: rest -> mkEx rest (CP.Exists(sv, f, None, no_pos))

(* in Mona, using the set representation for the integers, addition a1 = a2 + a3 is written plus(a2, a3, a1).
This is why I have a problem with formulas like a1 < a2 + a3. Therefore, I break all the presburger formulas,
meaning that whenever I find a a2 + a3, I replace it by the variable a2a3 and I add the relation a2a3 = a2 + a3 *)
(* w = weaken *)
let rec break_presburger (f : CP.formula) (w : bool) : CP.formula =
  begin
    additional_vars := [];
    additional_vars_ := [];
    (mona_of_formula_break f w);
  end

(* breaking expressions *)
and mona_of_exp_break e0 =
  match e0 with
  | CP.Add(CP.Var(CP.SpecVar(t1, id1, p1), _), CP.Var(CP.SpecVar(t2, id2, p2), _), l3) ->
      begin
        let tmp = fresh_var_name (string_of_typ t1) l3.start_pos.Lexing.pos_lnum in
		let new_tmp_var = CP.SpecVar(t1, tmp, Unprimed) in
		substitution_list := (CP.Eq(CP.Var(new_tmp_var, no_pos), CP.Add(CP.Var(CP.SpecVar(t1, id1, p1), no_pos), CP.Var(CP.SpecVar(t2, id2, p2), no_pos), no_pos), no_pos), None) :: !substitution_list;
        additional_vars := (new_tmp_var :: !additional_vars);
		additional_vars_ := (new_tmp_var :: !additional_vars_);
		CP.Var(new_tmp_var, l3);
      end
  | CP.Subtract(CP.Var(CP.SpecVar(t1, id1, p1), _), CP.Var(CP.SpecVar(t2, id2, p2), _), l3) ->
      begin
        let tmp = fresh_var_name (string_of_typ t1) l3.start_pos.Lexing.pos_lnum in
		let new_tmp_var = CP.SpecVar(t1, tmp, Unprimed) in
		substitution_list := (CP.Eq(CP.Var(new_tmp_var, no_pos), CP.Add(CP.Var(CP.SpecVar(t1, tmp, p1), no_pos), CP.Var(CP.SpecVar(t2, id2, p2), no_pos), no_pos), no_pos), None) :: !substitution_list;
        additional_vars := new_tmp_var :: !additional_vars;
        additional_vars_ := new_tmp_var :: !additional_vars_;
        CP.Var(new_tmp_var, l3);
      end
  | CP.Add(CP.IConst(i1, _), CP.Var(CP.SpecVar(t2, id2, p2), _) , l3)
  | CP.Add( CP.Var(CP.SpecVar(t2, id2, p2), _), CP.IConst(i1, _), l3) ->
      begin
        let tmp = fresh_var_name (string_of_typ t2) l3.start_pos.Lexing.pos_lnum in
		let new_tmp_var = CP.SpecVar(t2, tmp, Unprimed) in
		substitution_list := (CP.Eq(CP.Var(new_tmp_var, no_pos), CP.Add(CP.IConst(i1, no_pos), CP.Var(CP.SpecVar(t2, id2, p2), no_pos), no_pos), no_pos), None) :: !substitution_list;
		additional_vars := new_tmp_var :: !additional_vars;
        additional_vars_ := new_tmp_var :: !additional_vars_;
		CP.Var(new_tmp_var, l3);
      end
  | CP.Subtract( CP.Var(CP.SpecVar(t2, id2, p2), _), CP.IConst(i1, _), l3) ->
      begin
        let tmp = fresh_var_name (string_of_typ t2) l3.start_pos.Lexing.pos_lnum in
		let new_tmp_var = CP.SpecVar(t2, tmp, Unprimed) in
		substitution_list := (CP.Eq(CP.Var(new_tmp_var, no_pos), CP.Add(CP.IConst(i1, no_pos), CP.Var(CP.SpecVar(t2, tmp, p2), no_pos), no_pos), no_pos), None) :: !substitution_list;
        additional_vars := new_tmp_var :: !additional_vars;
        additional_vars_ := new_tmp_var :: !additional_vars_;
		CP.Var(new_tmp_var, l3);
      end
  | CP.Subtract( CP.IConst(i1, _), CP.Var(CP.SpecVar(t2, id2, p2), _), l3) ->
      begin
        let tmp = fresh_var_name (string_of_typ t2) l3.start_pos.Lexing.pos_lnum in
		let new_tmp_var = CP.SpecVar(t2, tmp, Unprimed) in
		substitution_list := (CP.Eq(CP.IConst(i1, no_pos), CP.Add(CP.Var(CP.SpecVar(t2, id2 , p2), no_pos), CP.Var(CP.SpecVar(t2, tmp, p2), no_pos), no_pos), no_pos), None) :: !substitution_list;
        additional_vars := new_tmp_var :: !additional_vars;
        additional_vars_ := new_tmp_var :: !additional_vars_;
		CP.Var(new_tmp_var, l3);
      end
  | CP.Add(CP.IConst(i1, _), CP.IConst(12, _) , l3) -> CP.IConst(i1+12, l3)
  | CP.Subtract( CP.IConst(i1, _), CP.IConst(i2, _), l3) ->
      begin
        let tmp = fresh_var_name "int" 0 in
		substitution_list := (CP.Eq(CP.IConst(i1, no_pos), CP.Add(CP.IConst(i2, no_pos), CP.Var(CP.SpecVar(Int, tmp, Globals.Unprimed), no_pos), no_pos), no_pos), None) :: !substitution_list;
		additional_vars := CP.SpecVar(Int, tmp, Globals.Unprimed) :: !additional_vars;
		additional_vars_ := CP.SpecVar(Int, tmp, Globals.Unprimed) :: !additional_vars_;
        CP.Var(CP.SpecVar(Int, tmp, Globals.Unprimed), l3);
      end
  | CP.Add (a1, a2, l1) -> CP.Add((mona_of_exp_break a1), (mona_of_exp_break a2), l1) (* Removed an outer recursive call to mona_of_exp_break *)
  | CP.Subtract(a1, a2, l1) -> CP.Subtract( (mona_of_exp_break a1), (mona_of_exp_break a2), l1) (* As above *)
  | CP.Min (a1, a2, l1) ->  CP.Min((mona_of_exp_break a1), (mona_of_exp_break a2), l1)
  | CP.Max (a1, a2, l1) ->  CP.Max((mona_of_exp_break a1), (mona_of_exp_break a2), l1)
  | _ -> e0

(* breaking boolean formulas *)
and mona_of_b_formula_break b w =
  let (pf,il) = b in
  let npf = match pf with
  | CP.Lt (a1, a2, l1) -> CP.Lt((mona_of_exp_break a1), (mona_of_exp_break a2), l1)
  | CP.Lte (a1, a2, l1) -> CP.Lte((mona_of_exp_break a1), (mona_of_exp_break a2), l1)
  | CP.Gt (a1, a2, l1) -> CP.Gt((mona_of_exp_break a1), (mona_of_exp_break a2), l1)
  | CP.Gte (a1, a2, l1) -> CP.Gte((mona_of_exp_break a1), (mona_of_exp_break a2), l1)
  (*-- try 02.04.09 *)
  (*| CP.Neq(CP.Add(CP.Mult _, _, _), _, _) 
  | CP.Neq(CP.Add(_, CP.Mult _, _), _, _) 
  | CP.Neq(CP.Add(_, _, _), CP.Mult _, _)
  | CP.Neq(CP.Add(CP.Add _, _, _), _, _) 
  | CP.Neq(CP.Add(_, CP.Add _, _), _, _) 
  | CP.Neq(_, CP.Add(_, CP.Add _ , _), _)
  | CP.Neq(_, CP.Add(CP.Add _ , _, _), _)*)
  (*commenting the weakening part*)
  (*| CP.Eq(CP.Add(CP.Mult _, _, _), _, _) 
  | CP.Eq(CP.Add(_, CP.Mult _, _), _, _) 
  | CP.Eq(CP.Add(_, _, _), CP.Mult _, _)
  | CP.Eq(CP.Add(CP.Add _, _, _), _, _) 
  | CP.Eq(CP.Add(_, CP.Add _, _), _, _) 
  | CP.Eq(_, CP.Add(_, CP.Add _ , _), _)
  | CP.Eq(_, CP.Add(CP.Add _ , _, _), _)  -> 
	if w then 
		(print_string("[mona.mona_of_b_formula_break]: weakening to true in test " ^ (string_of_int !mona_file_number) ^ "\n"); CP.BConst(true, no_pos))
	else	
	    mona_of_b_formula_break1 b
  *)		
  (*-- try 02.04.09 *)
  | CP.Eq(a1, a2, l1) -> CP.Eq((mona_of_exp_break a1), (mona_of_exp_break a2), l1)
  | CP.Neq(a1, a2, l1) -> CP.Neq((mona_of_exp_break a1), (mona_of_exp_break a2), l1)
  | CP.EqMin (a1, a2, a3, l1) -> CP.EqMin((mona_of_exp_break a1), (mona_of_exp_break a2), (mona_of_exp_break a3), l1)
  | CP.EqMax (a1, a2, a3, l1) -> CP.EqMax((mona_of_exp_break a1), (mona_of_exp_break a2), (mona_of_exp_break a3), l1)
  | _ -> pf
  in (npf,il)
  
and mona_of_b_formula_break1 b = match b with
  | CP.Eq(a1, a2, l1) -> CP.Eq((mona_of_exp_break a1), (mona_of_exp_break a2), l1)
  | _ -> b
  
(* breaking formulas *)
and mona_of_formula_break (f : CP.formula) (w : bool) : CP.formula =
  let res = match f with
  | CP.Or (p1, p2,lbl, l1) -> CP.Or((mona_of_formula_break p1 w), (mona_of_formula_break p2 w),lbl, l1)
  | CP.And (p1, p2, l1) -> CP.And((mona_of_formula_break p1 w), (mona_of_formula_break p2 w), l1)
  | CP.Not (p1,lbl, l1) -> CP.Not((mona_of_formula_break p1 w),lbl, l1)
  | CP.Forall(sv1, p1,lbl, l1) -> CP.Forall(sv1, (mona_of_formula_break p1 w),lbl, l1)
  | CP.Exists(sv1, p1,lbl, l1) -> CP.Exists(sv1, (mona_of_formula_break p1 w),lbl, l1)
  | CP.BForm (b,lbl,fo) -> CP.BForm((mona_of_b_formula_break b w),lbl,fo)
  in
      if (List.length !substitution_list) > 0 then
	   let eq = (mkEq !substitution_list) in
               begin
                 substitution_list := [];
		 let res1 = (mkEx !additional_vars (CP.And(eq, res, no_pos))) in
		   begin
     		additional_vars := [];
			res1;
		   end
               end
      else res

(*------------------------------------------*)

let hd list = match list with
 | [] -> failwith "[mona.ml] : Error when applying method head"
 | head :: tail -> head

let equal_types (t1: typ) (t2: typ) : bool =
      match t1 with
      | Named  _ ->
	  begin
	    match t2 with
	    | Named _ -> true
	    | _ -> false
	  end
      | _ -> (t1 = t2)

let equal_sv (CP.SpecVar(t1, i1, p1)) (CP.SpecVar(t2, i2, p2)) : bool =
  t1 = t2 && i1 = i2 && p1 = p2

let rec exists_sv (sv : CP.spec_var) (svlist : CP.spec_var list) : bool = match svlist with
 | [] -> false
 | sv1 :: rest ->
     if (sv1 = sv) (*sv1 = sv*) then true
     else (exists_sv sv rest)

let rec exists_sv_exp (sv : CP.spec_var) (elist : CP.exp list) : bool = match elist with
 | [] -> false
 | CP.Var(sv1, _) :: rest ->
     if sv1 = sv then true
     else (exists_sv_exp sv rest)
 | _ :: rest -> (exists_sv_exp sv rest)

let rec appears_in_formula v = function
  | CP.Not (f, _,_) -> appears_in_formula v f
  | CP.Forall (qv, f, _,_)
  | CP.Exists (qv, f, _,_) -> if qv = v then true else appears_in_formula v f
  | CP.And (f, g, _) -> (appears_in_formula v f) || (appears_in_formula v g)
  | CP.Or (f, g, _,_) -> (appears_in_formula v f) || (appears_in_formula v g)
  | CP.BForm ((pf,_),_,_) -> match pf with
      | CP.BVar (bv, _) -> v = bv
      | CP.Gt (l, r, _)
      | CP.Gte (l, r, _)
      | CP.Lte (l, r, _)
      | CP.Eq (l, r, _)
      | CP.Neq (l, r, _)
      | CP.BagSub (l, r, _)
      | CP.Lt (l, r, _) -> (appears_in_exp l (CP.Var (v,no_pos))) || (appears_in_exp r (CP.Var (v,no_pos)))
      | CP.EqMax (l, r, t, _)
      | CP.EqMin (l, r, t, _) -> (appears_in_exp l (CP.Var (v,no_pos))) || (appears_in_exp r (CP.Var (v,no_pos))) || (appears_in_exp t (CP.Var (v,no_pos)))
      | CP.BagNotIn (bv, r, _)
      | CP.BagIn (bv, r, _) -> v = bv || (appears_in_exp r (CP.Var (v,no_pos)))
      | CP.BagMin (l, r, _)
      | CP.BagMax (l, r, _) -> l = v || r = v
      | CP.BConst _ -> false
      | _ -> false

and is_first_order (f : CP.formula) (elem_list : CP.exp list) : bool =
  match (hd elem_list) with
    | CP.Var(sv1, _) ->
          if (exists_sv sv1 !additional_vars) then false else
            if (exists_sv sv1 !first_order_vars) then true else
	          if (exists_sv sv1 !second_order_vars) then false else
                if (is_inside_bag f (hd elem_list)) then
	              begin
	                first_order_vars := sv1 :: !first_order_vars;
	                true;
	              end
	            else
	              let res = (is_first_order_a f elem_list f) in
                  (*if (not (appears_in_formula sv1 f)) then false else*)
	              if res then
	                begin
                      (*first_order_vars := sv1 :: !first_order_vars;*)
                      let iter_fun v = match v with CP.Var(sv1, _) -> first_order_vars := sv1 :: !first_order_vars | _ -> assert false in
                      List.iter iter_fun elem_list;
		              true;
	                end
	              else
	                begin
		              if (!cycle = false) then
		                begin
                          (*second_order_vars := sv1 :: !second_order_vars;*)
                          let iter_fun v = match v with CP.Var(sv1, _) -> second_order_vars := sv1 :: !second_order_vars | _ -> assert false in
                          List.iter iter_fun elem_list;
		                end
		              else
		                begin
                          let iter_fun v = match v with CP.Var(sv1, _) -> second_order_vars := sv1 :: !second_order_vars | _ -> assert false in
                          List.iter iter_fun elem_list;
		                  cycle := false;
		                end;
		              false;
	                end
    | _ -> false

(* TODO : What is the role of initial_f? and the relation between
   f and initial_f *)
and is_first_order_a (f : CP.formula) (elem_list : CP.exp list) (initial_f : CP.formula) : bool =
  match f with
    | CP.And(f1, f2, _)
    | CP.Or(f1, f2,_, _) -> (is_first_order_a f1 elem_list initial_f) || (is_first_order_a f2 elem_list initial_f);
    | CP.Forall(_, f1, _,_)
    | CP.Exists(_, f1,_, _)
    | CP.Not(f1,_, _) -> (is_first_order_a f1 elem_list initial_f)
    | CP.BForm(bf,_,_) -> (is_first_order_b_formula bf elem_list initial_f);
          (*  | _ -> false;*)

and is_first_order_b_formula (bf : CP.b_formula) (elem_list : CP.exp list) (initial_f : CP.formula) : bool =
  let (pf,_) = bf in
  match pf with
  | CP.Lt(e1, e2, _)
  | CP.Lte(e1, e2, _)
  | CP.Gt(e1, e2, _)
  | CP.Gte(e1, e2, _)
  | CP.Eq(e1, e2, _)
  | CP.Neq(e1, e2, _) ->
        begin
	      if (appears_in_exp e1 (hd elem_list)) || (appears_in_exp e2 (hd elem_list)) then
	        begin
	          ((is_first_order_exp e1 elem_list initial_f) || (is_first_order_exp e2 elem_list initial_f));
	        end
          else false;
        end
  | CP.EqMax(e1, e2, e3, _)
  | CP.EqMin(e1, e2, e3, _) ->
      	if (appears_in_exp e1 (hd elem_list)) || (appears_in_exp e2 (hd elem_list)) || (appears_in_exp e3 (hd elem_list)) then
	      ((is_first_order_exp e1 elem_list initial_f) || (is_first_order_exp e2 elem_list initial_f) || (is_first_order_exp e3 elem_list initial_f))
	    else
	      false
  | _ ->
        begin
	      (*print_string ("I am here for " ^ (print_b_formula bf initial_f) ^ "\n");*)
	      false;
        end

and is_first_order_exp (e : CP.exp) (elem_list : CP.exp list) (initial_f : CP.formula) : bool = match e with
  | CP.Var(sv1, _) ->
   	    if (exists_sv_exp sv1 elem_list) then
	      begin
	        (* if I find a cycle when checking if a var is first order, I consider that one of the two interdependent vars is second order;
		       however, I make this assumption only when doing the checking for the other var. After finding whether the other var is first/second order,
		       I compute again the result for the var I first considered as second order *)
	        cycle := true;
	        false;
	      end
	    else (
            (*        print_char '<'; flush stdout;*)
            let ret = is_first_order initial_f (e::elem_list) in
            (*        print_char '>'; flush stdout;*)
            ret
        )
  | CP.Add(a1, a2, _)
  | CP.Subtract(a1, a2, _)
  | CP.Max(a1, a2, _)
  | CP.Min(a1, a2, _) ->
        begin
	      (*if !mona_file_number = 15 then print_string ("Min of " ^ (mona_of_exp a1 initial_f) ^ " and " ^ (mona_of_exp a2 initial_f) ^ "\n");*)
	      (is_first_order_exp a1 elem_list initial_f) || (is_first_order_exp a2 elem_list initial_f);
        end
  | CP.Mult(i1, a1, _) -> (is_first_order_exp a1 elem_list initial_f)
  | _ -> false

and appears_in_exp (e : CP.exp) (elem : CP.exp) : bool = match e with
  | CP.Var(sv1, _) ->
        begin
          match elem with
            | CP.Var(sv2, _) ->
	              if sv1 = sv2 then true
	              else false
            | _ -> false
        end
  | CP.Add(a1, a2, _)
  | CP.Subtract(a1, a2, _)
  | CP.Max(a1, a2, _)
  | CP.Min(a1, a2, _) ->
        (appears_in_exp a1 elem) || (appears_in_exp a2 elem)
  | CP.Mult(i1, a1, _) -> (appears_in_exp a1 elem)
  | _ -> false

and is_inside_bag (f : CP.formula) (elem : CP.exp) : bool = match f with
  | CP.And(f1, f2, _)
  | CP.Or(f1, f2, _,_) -> (is_inside_bag f1 elem) || (is_inside_bag f2 elem)
  | CP.Forall(_, f1, _,_)
  | CP.Exists(_, f1, _,_)
  | CP.Not(f1, _,_) -> (is_inside_bag f1 elem)
  | CP.BForm(bf,_,_) -> (is_inside_bag_b_formula bf elem)

and is_inside_bag_b_formula (bf : CP.b_formula) (elem : CP.exp) : bool =
  let (pf,_) = bf in
  match pf with
  | CP.BagNotIn(sv1, e1, _)
  | CP.BagIn(sv1, e1, _) ->
        begin
          match elem with
            | CP.Var(sv2, _) ->
	              if sv1=sv2 then true
	              else false
            | _ -> false
        end
  | CP.BagSub(e1, e2, _)
  | CP.Eq(e1, e2, _)
  | CP.Neq(e1, e2, _) ->
        ((CP.is_bag e1) && (is_inside_bag_exp e1 elem)) || ((CP.is_bag e2) && (is_inside_bag_exp e2 elem))
  | _ -> false

and is_inside_bag_exp (e : CP.exp) (elem : CP.exp) : bool = match e with
  | CP.Var(sv1, _) -> begin
      match elem with
        | CP.Var(sv2, _) ->
	          if sv1=sv2 then true
	          else false
        | _ -> false
    end
  | CP.Bag(e1 :: rest, p) -> (is_inside_bag_exp e1 elem) || (is_inside_bag_exp (CP.Bag(rest, p)) elem)
  | CP.BagIntersect(e1 :: rest, p) -> begin
      if CP.is_bag(e1) then (is_inside_bag_exp e1 elem) || (is_inside_bag_exp (CP.BagIntersect(rest, p)) elem)
      else  is_inside_bag_exp (CP.BagIntersect(rest, p)) elem
    end
  | CP.BagUnion(e1 :: rest, p) -> begin
      if CP.is_bag(e1) then (is_inside_bag_exp e1 elem) || (is_inside_bag_exp (CP.BagUnion(rest, p)) elem)
      else  is_inside_bag_exp (CP.BagUnion(rest, p)) elem
    end
  | CP.BagDiff(e1, e2, _) ->
        let res1 = is_inside_bag_exp e1 elem in
        let res2 = is_inside_bag_exp e2 elem in
        if CP.is_bag(e1) & CP.is_bag(e2) then res1 || res2
        else if CP.is_bag(e1) then res1
	    else if CP.is_bag(e2) then res2
	    else false
  | _ -> begin false; end

and is_firstorder_mem f e vs =
  Debug.no_1 "is_firstorder_mem" Cprinter.string_of_formula_exp string_of_bool (fun e -> is_firstorder_mem_a f e vs) e

and is_firstorder_mem_a f e vs =
  match e with
    | CP.Var(sv1, _) ->
          begin try Hashtbl.find vs sv1
          with Not_found ->
              let ret = is_first_order f [e] in
              Hashtbl.replace vs sv1 ret; ret
          end
    | CP.IConst _ | CP.Null _ -> true
    | _ -> false

(* pretty printing for spec_vars *)
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
		let _ = print_string("Illegal subtraction: " ^ (Cprinter.string_of_pure_formula f) ) in
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
            if (is_firstorder_mem f a1 vs) then
	          "(" ^ (mona_of_exp a1 f) ^ " ~= " ^ (string_of_int i) ^ ")"
            else
	          "(" ^ (mona_of_exp a1 f) ^ " ~= pconst(" ^ (string_of_int i) ^ "))"
      | CP.Neq (a, CP.Null _, _) 
      | CP.Neq (CP.Null _, a, _) ->
           if (is_firstorder_mem f a vs) then
              "(" ^ (mona_of_exp a f) ^ " > 0)"
           else
             " greater(" ^ (mona_of_exp a f) ^ ", pconst(0))"
      | CP.Neq (a1, a2, _) ->
	        if (is_firstorder_mem f a1 vs)&& (is_firstorder_mem f a2 vs) then
	                "(" ^ (mona_of_exp a1 f) ^ " ~= " ^ (mona_of_exp a2 f) ^ ")"
            else
              let (a1name,a2name,str,end_str) = second_order_composite2 a1 a2 f in
              str ^ " nequal(" ^ a1name ^ ", " ^ a2name ^ ") "^ end_str
      | CP.Eq((CP.Add(a1, a2, _)), a3, _)
      | CP.Eq(a3, (CP.Add(a1, a2, _)), _) ->
            if (is_firstorder_mem f a1 vs) && (is_firstorder_mem f a2 vs) && (is_firstorder_mem f a3 vs) then
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
          if (is_firstorder_mem f a1 vs) then
	        "(" ^ (mona_of_exp a1 f) ^ " = " ^ (string_of_int i) ^ ")"
          else
	        "(" ^ (mona_of_exp a1 f) ^ " = pconst(" ^ (string_of_int i) ^ "))"
      | CP.Eq (a1, CP.Null _, _) 
      | CP.Eq (CP.Null _, a1, _) ->
          if (is_firstorder_mem f a1 vs) then
	        "(" ^ (mona_of_exp a1 f) ^ " = 0)"
          else
	        "(" ^ (mona_of_exp a1 f) ^ " = pconst(0))"
      | CP.Eq (a1, a2, _) -> 
          if (is_firstorder_mem f a1 vs)&& (is_firstorder_mem f a2 vs) then
            "(" ^ (mona_of_exp a1 f) ^ " = " ^ (mona_of_exp a2 f) ^ ")"
          else	 
            let (a1name,a2name,str,end_str) = second_order_composite2 a1 a2 f in
            str ^ " " ^ a1name ^ " = " ^ a2name ^ " " ^ end_str
      | CP.EqMin (a1, a2, a3, _) ->
	        if (is_firstorder_mem f a1 vs) && (is_firstorder_mem f a2 vs) && (is_firstorder_mem f a3 vs) then
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
	        if (is_firstorder_mem f a1 vs) && (is_firstorder_mem f a2 vs) && (is_firstorder_mem f a3 vs) then
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
  if (is_firstorder_mem f a1 vs && is_firstorder_mem f a2 vs) then begin
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
      | CP.BForm (b,_,_) -> "(" ^ (mona_of_b_formula b initial_f vs) ^ ")"
      | CP.And (p1, p2, _) -> "(" ^ (helper p1) ^ " & " ^ (helper p2) ^ ")"
      | CP.Or (p1, p2, _,_) -> "(" ^ (helper p1) ^ " | " ^ (helper p2) ^ ")"
      | CP.Not (p, _,_) ->
            begin
              if !sat_optimize then
	            match p with
		          | CP.BForm ((CP.BVar (bv, _), _), _, _) -> (mona_of_spec_var bv) ^ " =pconst(0)" (*== pconst(1)*)
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
            if (is_firstorder_mem initial_f (CP.Var(sv, l)) vs) then
	          " (all1 " ^ (mona_of_spec_var sv) ^ ":" ^ (helper p) ^ ") "
            else
	          " (all2 " ^ (mona_of_spec_var sv) ^ ":" ^ (helper p) ^ ") "
      | CP.Exists (sv, p, _,l) ->
            if (is_firstorder_mem initial_f (CP.Var(sv, l)) vs) then
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
    let _ = (output_string !process.outchannel str;
             flush !process.outchannel) in
    let str = get_answer !process.inchannel in
    str 
  in 
  let answ = Procutils.PrvComms.maybe_raise_timeout_num 1 fnc () !timeout in
  answ

(* modify mona for not sending answers *)
let send_cmd_no_answer str =
  (* let _ = (print_string ("\nsned_cmd_no_asnwer " ^ str ^"- end string\n"); flush stdout) in *)
  let _ = send_cmd_with_answer str in
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
        (* let _ = print_string ("\n WARNING: File " ^ mona_pred_file ^ " was not found in current directory. Searching in alternative path: " ^ mona_pred_file_alternative_path) in *)
        let alternative = mona_pred_file_alternative_path ^ mona_pred_file in
        if Sys.file_exists alternative then 
          alternative
        else
          let _ = print_string ("\n WARNING: File " ^ alternative ^ " was not found. Aborting execution ...\n") in 
          (* Creating " ^ mona_pred_file ^ " file in current directory... " in" *)
          (* let _ = write_to_mona_predicates_file mona_pred_file in *)
          (* let _ = print_string (" done!\n") in *)
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
    (* let _ = print_string ("WARNING: Command for starting mona interactively (" ^ prover_cmd_str ^ ") not found!\n") in *)
    false
  else true

let start () = 
  last_test_number := !test_number;
  if(check_prover_existence "mona_inter")then begin
      let _ = Procutils.PrvComms.start !log_all_flag log_all ("mona", "mona_inter", [|"mona_inter"; "-v";|]) set_process prelude in
      is_mona_running := true
  end

let stop () = 
  let killing_signal = 
    match !is_mona_running with
      |true -> is_mona_running := false;  2
      |false -> 9 in
  let num_tasks = !test_number - !last_test_number in
  let _ = Procutils.PrvComms.stop !log_all_flag log_all !process num_tasks killing_signal (fun () -> ()) in
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
  let _ = output_string fail_file content in
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
            let _ = create_failure_file mona_file_content in
            restart "mona aborted execution";
            if !log_all_flag == true then
		      output_string log_all ("[mona.ml]: "^ imp_sat_str ^" --> " ^(string_of_bool is_sat_b) ^"(from mona failure)\n");
            is_sat_b
      | _ ->
            let _ = create_failure_file mona_file_content in
            try
              let _ = Str.search_forward (Str.regexp "Error in file") answ 0 in
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

let prepare_formula_for_mona (f: CP.formula) (break_presp: bool) (test_no: int): CP.spec_var list * CP.formula =
  let simp_f = CP.arith_simplify 8 f in
  let simp_f = (break_presburger simp_f break_presp) in
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
                  let _ = Str.search_forward (Str.regexp h) line 0 in
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


let create_file_for_mona (filename: string) (fv: CP.spec_var list) (f: CP.formula) (imp_no: string)  =
  let mona_file = open_out filename in
  let mona_pred_file_x = get_mona_predicates_file () in
  output_string mona_file ("include \""^ mona_pred_file_x ^"\";\n");
  let f_str =
    try 
      begin
        let all_fv = CP.remove_dups_svl fv in
        let vs = Hashtbl.create 10 in
        let (part1, part2) = (List.partition (fun (sv) -> (is_firstorder_mem f (CP.Var(sv, no_pos)) vs)) all_fv) in
        let first_order_var_decls =
          if Gen.is_empty part1 then ""
          else "var1 " ^ (String.concat ", " (List.map mona_of_spec_var part1)) ^ ";\n " in
        let second_order_var_decls =
          if Gen.is_empty part2 then ""
          else "var2 " ^ (String.concat ", " (List.map mona_of_spec_var part2)) ^ "; \n"in
        let var_decls = first_order_var_decls ^ second_order_var_decls in
        var_decls ^(mona_of_formula f f vs)
      end
    with exc -> print_endline ("\nEXC: " ^ Printexc.to_string exc); ""
  in
  if not (f_str == "") then  output_string mona_file (f_str ^ ";\n" );
  flush mona_file;
  close_out mona_file;
  f_str

let write_to_file  (is_sat_b: bool) (fv: CP.spec_var list) (f: CP.formula) (imp_no: string) : bool =
  let mona_filename = "test" ^ imp_no ^ ".mona" in
  let file_content = ((create_file_for_mona mona_filename fv f imp_no) ^ ";\n") in
  if !log_all_flag == true then
	begin
	  output_string log_all (mona_filename ^ Gen.new_line_str);
      output_string log_all file_content;
	  flush log_all;
	end;
  let _ = Procutils.PrvComms.start !log_all_flag log_all ("mona", "mona", [|"mona"; "-q";  mona_filename|]) set_process (fun () -> ()) in
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

let imply_sat_helper (is_sat_b: bool) (fv: CP.spec_var list) (f: CP.formula) (imp_no: string) : bool =
  let all_fv = CP.remove_dups_svl fv in
  let vs = Hashtbl.create 10 in
  let (part1, part2) = (List.partition (fun (sv) -> (is_firstorder_mem f (CP.Var(sv, no_pos)) vs)) all_fv) in
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
      let _ = maybe_restart_mona () in
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
  first_order_vars := [];
  second_order_vars := [];
  incr test_number;
  let (ante_fv, ante) = prepare_formula_for_mona ante true !test_number in
  let (conseq_fv, conseq) = prepare_formula_for_mona conseq false !test_number in
  let tmp_form = CP.mkOr (CP.mkNot ante None no_pos) conseq None no_pos in
  if not !is_mona_running then
    write_to_file false (ante_fv @ conseq_fv) tmp_form imp_no
  else
    imply_sat_helper false (ante_fv @ conseq_fv) tmp_form imp_no

let imply (ante : CP.formula) (conseq : CP.formula) (imp_no : string) : bool =
  let pr = Cprinter.string_of_pure_formula in
  Debug.no_3 "mona.imply" pr pr (fun x -> x) string_of_bool 
  imply ante conseq imp_no

let is_sat (f : CP.formula) (sat_no :  string) : bool =
  if !log_all_flag == true then
	output_string log_all ("\n\n[mona.ml]: #is_sat " ^ sat_no ^ "\n");
  sat_optimize := true;
  first_order_vars := [];
  second_order_vars := [];
  incr test_number;
  let (f_fv, f) = prepare_formula_for_mona f true !test_number in
  let sat = 
    if not !is_mona_running then
      write_to_file true f_fv f sat_no 
    else
      imply_sat_helper true f_fv f sat_no in
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
