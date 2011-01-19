(*
  Create the input file for Mona - 15-06-2006
*)

open Globals
module CP = Cpure

let mona_file_number = ref 0
let result_file_name = "res"
let first_order_vars = ref ([] : CP.spec_var list)
let second_order_vars = ref ([] : CP.spec_var list)
let additional_vars = ref ([] : CP.spec_var list)
let additional_vars_ = ref ([] : CP.spec_var list)
let substitution_list = ref ([] : CP.b_formula list)
let automaton_completed = ref false
let cycle = ref false
let sat_optimize = ref false;;

let log_all_flag = ref false
let log_all = ref (fun _ -> raise Not_found)
let log msg =
  if !log_all_flag then begin
    try !log_all msg
    with Not_found ->
      let out = open_out "allinput.mona" in
      log_all := (fun msg -> output_string out msg; flush out);
      !log_all msg
  end


(* pretty printing for primitive types *)
let mona_of_prim_type = function
  | Bool          -> "int"
  | Float         -> "float"	(* Can I really receive float? What do I do then? I don't have float in Mona. *)
  | Int           -> "int"
  | Void          -> "void" 	(* same as for float *)
  | Bag		  -> "int set"
  | List          -> "list"	(* lists are not supported *)


(*------------------------------------------*)
let rec mkEq l = match l with
  | e :: [] -> CP.BForm(e,None)
  | e :: rest -> CP.And(CP.BForm(e,None), (mkEq rest), no_pos)
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
        let tmp = fresh_var_name (Cprinter.string_of_typ t1) l3.start_pos.Lexing.pos_lnum in
		let new_tmp_var = CP.SpecVar(t1, tmp, Unprimed) in
		substitution_list := CP.Eq(CP.Var(new_tmp_var, no_pos), CP.Add(CP.Var(CP.SpecVar(t1, id1, p1), no_pos), CP.Var(CP.SpecVar(t2, id2, p2), no_pos), no_pos), no_pos) :: !substitution_list;
        additional_vars := (new_tmp_var :: !additional_vars);
		additional_vars_ := (new_tmp_var :: !additional_vars_);
		CP.Var(new_tmp_var, l3);
      end
  | CP.Subtract(CP.Var(CP.SpecVar(t1, id1, p1), _), CP.Var(CP.SpecVar(t2, id2, p2), _), l3) ->
      begin
        let tmp = fresh_var_name (Cprinter.string_of_typ t1) l3.start_pos.Lexing.pos_lnum in
		let new_tmp_var = CP.SpecVar(t1, tmp, Unprimed) in
		substitution_list := CP.Eq(CP.Var(new_tmp_var, no_pos), CP.Add(CP.Var(CP.SpecVar(t1, tmp, p1), no_pos), CP.Var(CP.SpecVar(t2, id2, p2), no_pos), no_pos), no_pos) :: !substitution_list;
        additional_vars := new_tmp_var :: !additional_vars;
        additional_vars_ := new_tmp_var :: !additional_vars_;
        CP.Var(new_tmp_var, l3);
      end
  | CP.Add(CP.IConst(i1, _), CP.Var(CP.SpecVar(t2, id2, p2), _) , l3)
  | CP.Add( CP.Var(CP.SpecVar(t2, id2, p2), _), CP.IConst(i1, _), l3) ->
      begin
        let tmp = fresh_var_name (Cprinter.string_of_typ t2) l3.start_pos.Lexing.pos_lnum in
		let new_tmp_var = CP.SpecVar(t2, tmp, Unprimed) in
		substitution_list := CP.Eq(CP.Var(new_tmp_var, no_pos), CP.Add(CP.IConst(i1, no_pos), CP.Var(CP.SpecVar(t2, id2, p2), no_pos), no_pos), no_pos) :: !substitution_list;
		additional_vars := new_tmp_var :: !additional_vars;
        additional_vars_ := new_tmp_var :: !additional_vars_;
		CP.Var(new_tmp_var, l3);
      end
  | CP.Subtract( CP.Var(CP.SpecVar(t2, id2, p2), _), CP.IConst(i1, _), l3) ->
      begin
        let tmp = fresh_var_name (Cprinter.string_of_typ t2) l3.start_pos.Lexing.pos_lnum in
		let new_tmp_var = CP.SpecVar(t2, tmp, Unprimed) in
		substitution_list := CP.Eq(CP.Var(new_tmp_var, no_pos), CP.Add(CP.IConst(i1, no_pos), CP.Var(CP.SpecVar(t2, tmp, p2), no_pos), no_pos), no_pos) :: !substitution_list;
        additional_vars := new_tmp_var :: !additional_vars;
        additional_vars_ := new_tmp_var :: !additional_vars_;
		CP.Var(new_tmp_var, l3);
      end
  | CP.Subtract( CP.IConst(i1, _), CP.Var(CP.SpecVar(t2, id2, p2), _), l3) ->
      begin
        let tmp = fresh_var_name (Cprinter.string_of_typ t2) l3.start_pos.Lexing.pos_lnum in
		let new_tmp_var = CP.SpecVar(t2, tmp, Unprimed) in
		substitution_list := CP.Eq(CP.IConst(i1, no_pos), CP.Add(CP.Var(CP.SpecVar(t2, id2 , p2), no_pos), CP.Var(CP.SpecVar(t2, tmp, p2), no_pos), no_pos), no_pos) :: !substitution_list;
        additional_vars := new_tmp_var :: !additional_vars;
        additional_vars_ := new_tmp_var :: !additional_vars_;
		CP.Var(new_tmp_var, l3);
      end
  | CP.Add(CP.IConst(i1, _), CP.IConst(12, _) , l3) -> CP.IConst(i1+12, l3)
  | CP.Subtract( CP.IConst(i1, _), CP.IConst(i2, _), l3) ->
      begin
        let tmp = fresh_var_name "int" 0 in
		substitution_list := CP.Eq(CP.IConst(i1, no_pos), CP.Add(CP.IConst(i2, no_pos), CP.Var(CP.SpecVar(CP.Prim Int, tmp, Globals.Unprimed), no_pos), no_pos), no_pos) :: !substitution_list;
		additional_vars := CP.SpecVar(CP.Prim Int, tmp, Globals.Unprimed) :: !additional_vars;
		additional_vars_ := CP.SpecVar(CP.Prim Int, tmp, Globals.Unprimed) :: !additional_vars_;
        CP.Var(CP.SpecVar(CP.Prim Int, tmp, Globals.Unprimed), l3);
      end
  | CP.Add (a1, a2, l1) -> CP.Add((mona_of_exp_break a1), (mona_of_exp_break a2), l1) (* Removed an outer recursive call to mona_of_exp_break *)
  | CP.Subtract(a1, a2, l1) -> CP.Subtract( (mona_of_exp_break a1), (mona_of_exp_break a2), l1) (* As above *)
  | CP.Min (a1, a2, l1) ->  CP.Min((mona_of_exp_break a1), (mona_of_exp_break a2), l1)
  | CP.Max (a1, a2, l1) ->  CP.Max((mona_of_exp_break a1), (mona_of_exp_break a2), l1)
  | _ -> e0

(* breaking boolean formulas *)
and mona_of_b_formula_break b w = match b with
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
  | _ -> b
  
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
  | CP.BForm (b,lbl) -> CP.BForm((mona_of_b_formula_break b w),lbl)
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

let string_of_type (t) =
  match t with
  | CP.Prim Int -> "int"
  | CP.Prim Bool -> "bool"
  | CP.Prim Void -> "void"
  | CP.OType c -> "otype " ^ c
  | _ -> "smth else"


let equal_types (t1:CP.typ) (t2:CP.typ) : bool =
      match t1 with
      | CP.OType _ ->
	  begin
	    match t2 with
	    | CP.OType _ -> true
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
  | CP.BForm (bf,_) -> match bf with
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

and is_first_order_a (f : CP.formula) (elem_list : CP.exp list) (initial_f : CP.formula) : bool =
  match f with
  | CP.And(f1, f2, _)
  | CP.Or(f1, f2,_, _) -> (is_first_order_a f1 elem_list initial_f) || (is_first_order_a f2 elem_list initial_f);
  | CP.Forall(_, f1, _,_)
  | CP.Exists(_, f1,_, _)
  | CP.Not(f1,_, _) -> (is_first_order_a f1 elem_list initial_f)
  | CP.BForm(bf,_) -> (is_first_order_b_formula bf elem_list initial_f);
(*  | _ -> false;*)

and is_first_order_b_formula (bf : CP.b_formula) (elem_list : CP.exp list) (initial_f : CP.formula) : bool = match bf with
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
  | CP.BForm(bf,_) -> (is_inside_bag_b_formula bf elem)

and is_inside_bag_b_formula (bf : CP.b_formula) (elem : CP.exp) : bool = match bf with
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
  match e with
  | CP.Var(sv1, _) ->
      begin try Hashtbl.find vs sv1
      with Not_found ->
        let ret = is_first_order f [e] in
        Hashtbl.replace vs sv1 ret; ret
      end
  | CP.IConst _ -> true
  | _ -> false

(* pretty printing for spec_vars *)
and mona_of_spec_var (sv : CP.spec_var) = match sv with
  | CP.SpecVar (_, v, p) -> 
	(*let _ = print_string("var " ^ (Cprinter.string_of_spec_var sv) ^ "\n") in*)
		v ^ (if CP.is_primed sv then Oclexer.primed_str else "")

(* pretty printing for expressions *)
and mona_of_exp e0 f = match e0 with
  (*| CP.Null _ -> " 0 "*)
  | CP.Null _ -> "pconst(0)"
  | CP.Var (sv, _) -> mona_of_spec_var sv
  | CP.IConst (i, _) -> " " ^ (string_of_int i) ^ " "
(*  | CP.IConst (i, _) -> "pconst(" ^ (string_of_int i) ^ ")"*)
  | CP.Add(CP.IConst(i, _), a, _) -> "( " ^ (mona_of_exp a f) ^ " + " ^ (string_of_int i) ^ " )"
  | CP.Add (a1, a2, _) ->  " ( " ^ (mona_of_exp a1 f) ^ " + " ^ (mona_of_exp a2 f) ^ ")"
  | CP.Subtract(CP.IConst(i, _), a, _) -> "( " ^ (mona_of_exp a f) ^ " + " ^ (string_of_int i) ^ " )"
  | CP.Mult (a1, a2, p) -> "(" ^ (mona_of_exp a1 f) ^ " * " ^ (mona_of_exp a2 f) ^ ")"
  | CP.Div (a1, a2, p) -> failwith "[mona.ml]: divide is not supported."
  | CP.Max _
  | CP.Min _ -> failwith ("mona.mona_of_exp: min/max can never appear here")
  | CP.Bag (elist, _) -> "{"^ (mona_of_formula_exp_list elist f) ^ "}"
  | CP.BagUnion ([], _) -> ""
  | CP.BagUnion (e::[], _) -> (mona_of_exp e f)
  | CP.BagUnion (e::rest, l) -> (mona_of_exp e f) ^ " union " ^ (mona_of_exp (CP.BagUnion (rest, l)) f)
  | CP.BagIntersect ([], _) -> ""
  | CP.BagIntersect (e::[], _) -> (mona_of_exp e f)
  | CP.BagIntersect (e::rest, l)->(mona_of_exp e f) ^ " inter " ^ (mona_of_exp (CP.BagIntersect (rest, l)) f)
  | CP.BagDiff (e1, e2, _)     -> (mona_of_exp e1 f) ^ "\\" ^ (mona_of_exp e2 f)
  | CP.List _
  | CP.ListCons _
  | CP.ListHead _
  | CP.ListTail _
  | CP.ListLength _
  | CP.ListAppend _
  | CP.ListReverse _ -> failwith ("Lists are not supported in Mona")
  | _ -> failwith ("mona.mona_of_exp: mona doesn't support subtraction/...")

and mona_of_exp_secondorder e0 f = 	match e0 with
  | CP.Null _ -> ([], "pconst(0)", "")
  | CP.Var (sv, _) -> ([], mona_of_spec_var sv, "")
  | CP.IConst (i, _) -> ([], ("pconst(" ^ (string_of_int i) ^ ")"), "")
  | CP.Add (a1, a2, pos) ->  
      let tmp = fresh_var_name "int" pos.start_pos.Lexing.pos_lnum in
(*      print_endline ("\nCCC: " ^ tmp); *)
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
		let _ = print_string("Illegal subtraction: " ^ (Cprinter.string_of_pure_formula f) ^ "\n") in
		failwith ("mona.mona_of_exp_secondorder: mona doesn't support subtraction ...")
  | CP.List _
  | CP.ListCons _
  | CP.ListHead _
  | CP.ListTail _
  | CP.ListLength _
  | CP.ListAppend _
  | CP.ListReverse _ -> failwith ("Lists are not supported in Mona")
	| _ -> failwith ("mona.mona_of_exp_secondorder: mona doesn't support subtraction/mult/...")


(* pretty printing for a list of expressions *)
and mona_of_formula_exp_list l f = match l with
  | []         -> ""
  | CP.IConst(i, _) :: [] -> string_of_int i
  | h::[]      -> mona_of_exp h f
  | CP.IConst(i, _) :: t -> string_of_int i ^ ", " ^ (mona_of_formula_exp_list t f)
  | h::t       -> (mona_of_exp h f) ^ ", " ^ (mona_of_formula_exp_list t f)

(* pretty printing for boolean vars *)
and mona_of_b_formula b f vs =
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
          (if a3str <> "" then " & " ^ a3str else "") ^ end_str^"\n" in
        (a1name,a2name,a3name,str,end_str)  in

  let ret =
  match b with
  | CP.BConst (c, _) -> if c then "(0 = 0)" else "(~ (0 <= 0))"
  | CP.BVar (bv, _) -> "(" ^ (mona_of_spec_var bv) ^ " = pconst(0))"
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
  (* CP.Neq *)   
  | CP.Neq((CP.Add(a1, a2, l1)), a3, l2)
  | CP.Neq(a3, (CP.Add(a1, a2, l1)), l2)
  (*| CP.Neq((CP.Subtract(a3, a1, l1)), a2, l2)
  | CP.Neq(a2, (CP.Subtract(a3, a1, l1)), l2)*)
    -> "(~" ^ (mona_of_b_formula (CP.Eq((CP.Subtract(a3, a1, l1)), a2, l2)) f vs) ^ ")"
  | CP.Neq (CP.IConst(i, _), a1, _)
  | CP.Neq (a1, CP.IConst(i, _), _) ->
      if (is_firstorder_mem f a1 vs) then
	"(" ^ (mona_of_exp a1 f) ^ " ~= " ^ (string_of_int i) ^ ")"
      else
	"(" ^ (mona_of_exp a1 f) ^ " ~= pconst(" ^ (string_of_int i) ^ "))"
  | CP.Neq (a1, a2, _) ->
	if (is_firstorder_mem f a1 vs) then
	  begin
	  if CP.is_null a2 then
	  "(" ^ (mona_of_exp a1 f) ^ " > 0)"
	  else
	    if CP.is_null a1 then
	      "(" ^ (mona_of_exp a2 f) ^ " > 0)"
	    else
	      "(" ^ (mona_of_exp a1 f) ^ " ~= " ^ (mona_of_exp a2 f) ^ ")"
	  end
        else
	  begin
	  if CP.is_null a2 then
	    " greater(" ^ (mona_of_exp a1 f) ^ ", pconst(0))"
	  else
	    if CP.is_null a1 then
	      " greater(" ^ (mona_of_exp a2 f) ^ ",  pconst(0))"
	    else
	      "(" ^ (mona_of_exp a1 f) ^ " ~= " ^ (mona_of_exp a2 f) ^ ")"
	  end
  (* CP.Eq *)
  (*| CP.Eq((CP.Subtract(a1, a2, pos1)), (CP.Subtract(a3, a4, pos2)), pos3) -> (mona_of_b_formula (CP.Eq(CP.Add(a1, a4, pos1), CP.Add(a2, a3, pos2), pos3)) f vs)	 
  | CP.Eq(a1,CP.Add(CP.Subtract(a2, a3, pos1), a4, pos2), pos3)  
  | CP.Eq(CP.Add(CP.Subtract(a2, a3, pos1), a4, pos2), a1, pos3) -> (mona_of_b_formula (CP.Eq(CP.Add(a1, a3, pos1), CP.Add(a2, a4, pos2), pos3)) f vs)
  | CP.Eq((CP.Subtract(a3, a1, pos1)), a2, pos2)
  | CP.Eq(a2, (CP.Subtract(a3, a1, pos1)), pos2) -> (mona_of_b_formula (CP.Eq(CP.Add(a2, a1, pos1), a3, pos2)) f vs)	 
  *)
  (* try: todo: I think it's not the best place cause the existentials are already introduced *)
  (*| CP.Eq(CP.Add(CP.Mult _, _, _), _, _) 
  | CP.Eq(CP.Add(_, CP.Mult _, _), _, _) 
  | CP.Eq(CP.Add(_, _, _), CP.Mult _, _)
  | CP.Eq(CP.Add(CP.Add _, _, _), _, _) 
  | CP.Eq(CP.Add(_, CP.Add _, _), _, _) 
  | CP.Eq(_, CP.Add(_, CP.Add _ , _), _)
  | CP.Eq(_, CP.Add(CP.Add _ , _, _), _)  -> ((*print_string("[mona]: weakening to true\n");*) "true")*)
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
  (***********************)
  | CP.Eq (a1, CP.Null _, _) ->
      if (is_firstorder_mem f a1 vs) then
	"(" ^ (mona_of_exp a1 f) ^ " = 0)"
      else
	"(" ^ (mona_of_exp a1 f) ^ " = pconst(0))"
  (**********************)	
  | CP.Eq (a1, a2, _) -> "(" ^ (mona_of_exp a1 f) ^ " = " ^ (mona_of_exp a2 f) ^ ")"	 
  | CP.EqMin (a1, a2, a3, _) ->
	  if (is_firstorder_mem f a1 vs) && (is_firstorder_mem f a2 vs) && (is_firstorder_mem f a3 vs) then
      let a1str = mona_of_exp a1 f in
      let a2str = mona_of_exp a2 f in
      let a3str = mona_of_exp a3 f in	  
      "((" ^ a3str ^ " <= " ^ a2str ^ " & " ^ a1str ^ " = " ^ a3str ^ ") | ("
      ^ a2str ^ " < " ^ a3str ^ " & " ^ a1str ^ " = " ^ a2str ^ "))" ^ Util.new_line_str
    else
      let (a1name,a2name,a3name,str,end_str) = second_order_composite a1 a2 a3 f in
      (*str ^ " plus(" ^ a1name ^ ", " ^ a2name ^ ", " ^ a3name ^ ") "^ end_str*)
      str ^ "((lessEq(" ^ a3name ^ ", " ^ a2name ^ ") & " ^ a1name ^ " = " ^ a3name ^ ") | (less("
		^ a2name ^ ", " ^ a3name ^ ") & " ^ a1name ^ " = " ^ a2name ^ "))"   ^end_str
          
    (*let a1str = mona_of_exp_secondorder a1 f in
	  let a2str = mona_of_exp_secondorder a2 f in
	  let a3str = mona_of_exp_secondorder a3 f in
	  "((lessEq(" ^ a3str ^ ", " ^ a2str ^ ") & " ^ a1str ^ " = " ^ a3str ^ ") | (less("
		^ a2str ^ ", " ^ a3str ^ ") & " ^ a1str ^ " = " ^ a2str ^ "))" ^ Util.new_line_str*)
  | CP.EqMax (a1, a2, a3, _) ->	 
	  if (is_firstorder_mem f a1 vs) && (is_firstorder_mem f a2 vs) && (is_firstorder_mem f a3 vs) then
       let a1str = mona_of_exp a1 f in
       let a2str = mona_of_exp a2 f in
       let a3str = mona_of_exp a3 f in
      "((" ^ a3str ^ " <= " ^ a2str ^ " & " ^ a1str ^ " = " ^ a2str ^ ") | ("
        ^ a2str ^ " < " ^ a3str ^ " & " ^ a1str ^ " = " ^ a3str ^ "))" ^ Util.new_line_str
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
  in
  ret

and equation a1 a2 f sec_order_symbol first_order_symbol vs =
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


(* pretty printing for formulas *)
and mona_of_formula f initial_f vs =
  let ret = begin
  match f with
  | CP.BForm (b,_) -> "(" ^ (mona_of_b_formula b initial_f vs) ^ ")"
  | CP.And (p1, p2, _) -> "(" ^ (mona_of_formula p1 initial_f vs) ^ " & " ^ (mona_of_formula p2 initial_f vs) ^ ")"
  | CP.Or (p1, p2, _,_) -> "(" ^ (mona_of_formula p1 initial_f vs) ^ " | " ^ (mona_of_formula p2 initial_f vs) ^ ")"
  | CP.Not (p, _,_) ->
      begin
        if !sat_optimize then
	      match p with
		  | CP.BForm (CP.BVar (bv, _),_) -> (mona_of_spec_var bv) ^ " = pconst(1)"
(*              (equation (CP.Var (bv, no_pos)) (CP.IConst (1, no_pos)) f "less" "<" vs)*)
		  | _ -> " (~" ^ (mona_of_formula p initial_f vs) ^ ") "
        else " (~" ^ (mona_of_formula p initial_f vs) ^ ") "
      end 
  (*| CP.Forall(CP.SpecVar (CP.Prim Bag, v, p), p1, _) ->
	"(all2 " ^ v ^ " : " ^ (mona_of_formula p1 initial_f) ^ ")"
  | CP.Forall (sv, p, _) ->
  	"(all1 " ^ (mona_of_spec_var sv) ^ " : " ^ (mona_of_formula p initial_f) ^ ")"
  | CP.Exists(CP.SpecVar (CP.Prim Bag, v, p), p1, _) ->
	"(ex2 " ^ v ^ " : " ^ (mona_of_formula p1 initial_f) ^ ")"
  | CP.Exists (sv, p, _) ->
  	"(ex1 " ^ (mona_of_spec_var sv) ^ " : " ^ (mona_of_formula p initial_f) ^ ")"*)
  | CP.Forall (sv, p, _,l) ->
      if (is_firstorder_mem initial_f (CP.Var(sv, l)) vs) then
	" (all1 " ^ (mona_of_spec_var sv) ^ ":" ^ (mona_of_formula p initial_f vs) ^ ") "
     else
	" (all2 " ^ (mona_of_spec_var sv) ^ ":" ^ (mona_of_formula p initial_f vs) ^ ") "
  | CP.Exists (sv, p, _,l) ->
      if (is_firstorder_mem initial_f (CP.Var(sv, l)) vs) then
	begin
	  " (ex1 " ^ (mona_of_spec_var sv) ^ ":" ^ (mona_of_formula p initial_f vs) ^ ") "
	end
      else
	begin
	  " (ex2 " ^ (mona_of_spec_var sv) ^ ":" ^ (mona_of_formula p initial_f vs) ^ ") "
	end
   end in
  ret

(* pretty printing for boolean vars *)
and print_b_formula b f = match b with
  | CP.BConst (c, _) -> if c then "(0 = 0)" else "(~ (0 <= 0))"
  | CP.BVar (bv, _) -> "(" ^ (mona_of_spec_var bv) ^ (*" = 1")*)" = pconst(1))"
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



(*let set_timer tsecs =
  ignore (Unix.setitimer Unix.ITIMER_REAL
            { Unix.it_interval = 0.0; Unix.it_value = tsecs })

let continue f arg tsecs =
  let oldsig = Sys.signal Sys.sigalrm (Sys.Signal_handle (fun _ -> raise Exit)) in
  try
    set_timer tsecs;
    let res = f arg in
    set_timer 0.0;
    Sys.set_signal Sys.sigalrm oldsig;
    Some res
  with Exit ->
    Sys.set_signal Sys.sigalrm oldsig; None
*)

(* checking the result given by Mona *)
let rec check fd timeout pid : bool =
  try begin
    if (Unix.select [Unix.descr_of_in_channel fd] [] [] timeout) = ([],[],[]) then begin
        print_endline "\nMOna timeout reached."; flush stdout; false
    end else 
    let r = input_line fd in
    let err= "Error in file " in 
    match r with
    | "Formula is valid" ->
        log (" [mona.ml]: --> SUCCESS\n");
        true
    | _ -> 
      let l = String.length err in
      if ((String.length r) >=l) && String.compare err (String.sub r 0 l)=0 then
        (print_string "MONA translation failure!";
        Error.report_error { Error.error_loc = no_pos; Error.error_text =("Mona translation failure!!\n"^r)})
      else
        false
    end
  with
	End_of_file -> false


(* writing the Mona file *)
let write (var_decls:string) (pe : CP.formula) vs timeout : bool =
  let mona_file_name = "test" ^ (string_of_int !mona_file_number) ^ ".mona" in
  let mona_file = open_out mona_file_name in
  output_string mona_file ("# auxiliary predicates\n");
  output_string mona_file ("pred xor(var0 x,y) = x&~y | ~x&y;\n");
  output_string mona_file ("pred at_least_two(var0 x,y,z) = x&y | x&z | y&z;\n\n");
  output_string mona_file ("# addition relation (P + q = r)\n");
  output_string mona_file ("pred plus(var2 p,q,r) =\n");
  output_string mona_file ("ex2 c: \n");
  output_string mona_file ("\t0 notin c\n");
  output_string mona_file ("& all1 t:\n");
  output_string mona_file ("\t(t+1 in c <=> at_least_two(t in p, t in q, t in c))\n");
  output_string mona_file ("\t& (t in r <=> xor(xor(t in p, t in q), t in c));\n\n");
  output_string mona_file ("# less-than relation (p<q)\n");
  output_string mona_file ("pred less(var2 p,q) = \n");
  output_string mona_file ("ex2 t: t ~= empty & plus(p,t,q);\n\n");
  output_string mona_file ("# less-or-equal than relation (p<=q)\n");
  output_string mona_file ("pred lessEq(var2 p, q) = \n");
  output_string mona_file ("less(p, q) | (p=q);\n\n");
  output_string mona_file ("# greater-than relation (p>q)\n");
  output_string mona_file ("pred greater(var2 p, q) = \n");
  output_string mona_file ("less(q, p);\n\n");
  output_string mona_file ("# greater-or-equal than relation (p>=q)\n");
  output_string mona_file ("pred greaterEq(var2 p, q) = \n");
  output_string mona_file ("greater(p, q) | (p=q);\n\n");
  let fstr = 
    try (var_decls ^ (mona_of_formula pe pe vs))
    with exc -> print_endline ("\nEXC: " ^ Printexc.to_string exc); "" 
  in
  output_string mona_file (fstr ^ ";\n" );
  flush mona_file;
  close_out mona_file;
  
(*  print_endline ("Mona will be started."); flush stdout;*)
  let (inc, outc, errc, pid) = Unix_add.open_process_full "/usr/bin/mona" [|"/usr/bin/mona"; "-q"; "test" ^ (string_of_int !mona_file_number) ^ ".mona"|] in
(*  print_endline ("Mona started: " ^ (string_of_int pid)); flush stdout;*)
  (* if log_all_flag is on -> writing the formula in the mona log file  *)
  log ("test" ^ string_of_int !mona_file_number ^ Util.new_line_str);
  log (fstr ^ ";\n");
  let res = 
    try
      check inc timeout pid 
    with
    | e-> 
      (print_string ("MONA failed : "^(Printexc.to_string e)^(Cprinter.string_of_pure_formula pe)^"\n");
      raise e) in
  Unix.kill pid 9;
  (try (Unix.close (Unix.descr_of_in_channel inc)) with _ -> ());
  (try (Unix.close (Unix.descr_of_out_channel outc)) with _ -> ());
  (try (Unix.close (Unix.descr_of_in_channel errc)) with _ -> ());
  (*(try ignore (Unix.close_process_full (inc, outc, errc)) with _ -> ());*)
  begin match Unix.waitpid [] pid with
  | dpid, Unix.WSIGNALED signo -> () (*print_endline ("Signal: " ^ (string_of_int signo) ^ " dpid " ^ (string_of_int dpid) ^ " pid " ^ (string_of_int pid))*)
  | _ -> ()
  end;
(*  print_endline "Mona died."; flush stdout;*)
  Sys.remove ("test" ^ (string_of_int !mona_file_number) ^ ".mona");
  let msg =
    if res then
      "[mona.ml]: imply --> true\n"
    else
      "[mona.ml]: imply --> false\n"
  in
  log msg;
  res

let imply timeout (ante : CP.formula) (conseq : CP.formula) (imp_no : string) : bool = begin
  mona_file_number.contents <- !mona_file_number + 1;
  first_order_vars := [];
  second_order_vars := [];
  log ("\n\n[mona.ml]: imply # " ^ imp_no ^ "\n");
  (*	
  let ante_fv = CP.fv ante in
  let conseq_fv = CP.fv conseq in
  let all_fv = CP.remove_dups (ante_fv @ conseq_fv) in
  let tmp_form = CP.mkOr (CP.mkNot ante no_pos) conseq no_pos in
  let vs = Hashtbl.create 10 in
  let (part1, part2) = (List.partition (fun (sv) -> (is_firstorder_mem tmp_form (CP.Var(sv, no_pos)) vs)) all_fv) in
  let first_order_var_decls =
    if Util.empty (*!first_order_vars*) part1 then ""
    else "var1 " ^ (String.concat ", " (List.map mona_of_spec_var (*(!first_order_vars)*)part1)) ^ ";\n" in
  let second_order_var_decls =
    if Util.empty (*!second_order_vars*) part2 then ""
    else "var2 " ^ (String.concat ", " (List.map mona_of_spec_var (*!second_order_vars*) part2)) ^ ";\n" in
  let var_decls = first_order_var_decls ^ second_order_var_decls in
  (*let tmp_form = CP.mkOr (CP.mkNot ante no_pos) conseq no_pos in*)
  let simp_form = break_presburger tmp_form in
  (write var_decls simp_form vs timeout)
  *)
  (* try 02.04.09 *)
  (* ante *)
  
  let ante = CP.arith_simplify ante in
  let conseq = CP.arith_simplify conseq in
  let simp_ante = (break_presburger ante true) in
  let simp_conseq = (break_presburger conseq false) in
  let ante_fv = CP.fv simp_ante in
  let conseq_fv = CP.fv simp_conseq in
  let tmp_form = CP.mkOr (CP.mkNot simp_ante None no_pos) simp_conseq None no_pos in
  let all_fv = Util.remove_dups (ante_fv @ conseq_fv) in
  let vs = Hashtbl.create 10 in
  let (part1, part2) = (List.partition (fun (sv) -> (is_firstorder_mem tmp_form (CP.Var(sv, no_pos)) vs)) all_fv) in
  let first_order_var_decls =
    if Util.empty (*!first_order_vars*) part1 then ""
    else "var1 " ^ (String.concat ", " (List.map mona_of_spec_var (*(!first_order_vars)*)part1)) ^ ";\n" in
  let second_order_var_decls =
    if Util.empty (*!second_order_vars*) part2 then ""
    else "var2 " ^ (String.concat ", " (List.map mona_of_spec_var (*!second_order_vars*) part2)) ^ ";\n" in
  let var_decls = first_order_var_decls ^ second_order_var_decls in
  if (timeout = 0.) then (write var_decls tmp_form vs (-1.))
  else (write var_decls tmp_form vs timeout)
 end

let is_sat (f : CP.formula) (sat_no :  string) : bool =
  log ("\n\n[mona.ml]: #is_sat " ^ sat_no ^ "\n");
  sat_optimize := true;
  let tmp_form = (imply !Globals.sat_timeout f (CP.BForm(CP.BConst(false, no_pos),None)) ("from sat#" ^ sat_no)) in
  sat_optimize := false;
  let msg =
    if tmp_form then
      "[mona.ml]: is_sat --> false\n"
    else
      "[mona.ml]: is_sat --> true\n"
  in
  log msg;
  not tmp_form

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

