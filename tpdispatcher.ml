(*
  Choose with theorem prover to prove formula
*)

open Globals
module CP = Cpure

type tp_type =
  | OmegaCalc
  | CvcLite
  | CO (* CVC Lite then Omega combination *)
  | Isabelle
  | Mona
  | OM
  | OI
  | SetMONA
  | CM (* CVC Lite then MONA *)
  | Coq

let tp = ref OmegaCalc

let prover_arg = ref "omega"
type prove_type = Sat of CP.formula | Simplify of CP.formula | Imply of CP.formula * CP.formula
let external_prover = ref false

module Netprover = struct
	let use_pipe = ref false
	let in_ch = ref stdin
	let out_ch = ref stdout
  
  let start_prover_process () = 
    let is_running cmd =  
      let ch = Unix.open_process_in ("ps -u$USER -f |grep '"^cmd^"'") in
      let count = ref 0 in
      (try
	      while !count < 2 do 
	          let _ = input_line ch in
	         incr count
	      done;
      with End_of_file -> ());
      !count >= 2
    in 
(*    let cmd = "prover --dpipe 1>prove.log 2>prove.log" in*)
    let cmd = "prover --dpipe" in
    if is_running cmd = false then
      ignore(Unix.open_process_in cmd)
    
	let set_use_pipe pipe_name =
    if pipe_name = "" then start_prover_process ();
		external_prover := true;
		use_pipe := true;
		let i, o = Net.Pipe.init_client pipe_name in
		in_ch := i; out_ch := o
	
	let set_use_socket host_port =
		external_prover := true ;
		use_pipe := false;
		let i, o = Net.Socket.init_client host_port in
		in_ch := i; out_ch := o
	
	let call_prover (data : prove_type) =
		let _ = Net.IO.write_job !out_ch 0 !prover_arg data in
		let seq, result_str = Net.IO.read_result !in_ch in
				 Net.IO.from_string result_str
end 

let set_tp tp_str =
  prover_arg := tp_str;  
  if tp_str = "omega" then
	tp := OmegaCalc
  else if tp_str = "cvcl" then 
	tp := CvcLite
  else if tp_str = "co" then
	tp := CO
  else if tp_str = "isabelle" then
	tp := Isabelle
  else if tp_str = "mona" then
	tp := Mona
  else if tp_str = "om" then
	tp := OM
  else if tp_str = "oi" then
	tp := OI
  else if tp_str = "set" then
	tp := SetMONA
  else if tp_str = "cm" then
	tp := CM
  else if tp_str = "coq" then
	tp := Coq
  else
	()

let omega_count = ref 0

(* Method checking whether a formula contains bag constraints *)
let rec is_bag_constraint(f : CP.formula) : bool = match f with
  | CP.BForm(bf) -> (is_bag_constraint_b_formula bf)
  | CP.And(f1, f2, _) -> (is_bag_constraint f1) || (is_bag_constraint f2)
  | CP.Or(f1, f2, _) -> (is_bag_constraint f1) || (is_bag_constraint f2)
  | CP.Not(f1, _) -> (is_bag_constraint f1)
  | CP.Forall(_, f1, _) -> (is_bag_constraint f1)
  | CP.Exists(_, f1, _) -> (is_bag_constraint f1)

and is_bag_constraint_b_formula (bf : CP.b_formula) : bool =  match bf with
  | CP.BConst _
  | CP.BVar _
	  -> false
  | CP.Lt (e1, e2, _)
  | CP.Lte (e1, e2, _)
  | CP.Gt (e1, e2, _)
  | CP.Gte (e1, e2, _)
  | CP.EqMax (e1, e2, _, _) (* first is max of second and third *)
  | CP.EqMin (e1, e2, _, _) (* first is min of second and third *)
	  -> false
  | CP.Eq (e1, e2, _) (* these two could be arithmetic or pointer *)
  | CP.Neq (e1, e2, _)
	-> (is_bag_constraint_exp e1) || (is_bag_constraint_exp e2)
	  (* bag formulas *)
  | CP.BagIn _
  | CP.BagNotIn _
  | CP.BagSub _
  | CP.BagMin _
  | CP.BagMax _ -> true

and is_bag_constraint_exp (e :CP.exp) : bool = match e with
  | CP.Null _
  | CP.Var _
  | CP.IConst _ -> false
  | CP.Add (e1, e2, _)
  | CP.Subtract (e1, e2, _) (* ->  (is_bag_constraint_exp e1) || (is_bag_constraint_exp e2) *)
	  -> false
  | CP.Mult _
  | CP.Max _
  | CP.Min _ -> false
	  (* bag expressions *)
  | CP.Bag _
  | CP.BagUnion _
  | CP.BagIntersect _
  | CP.BagDiff _ -> true

(*
let rec is_bag_constraint(f : CP.formula) : bool =
  match f with
  | CP.BForm(bf) -> (is_bag_constraint_b_formula bf)
  | CP.And(f1, f2, _) -> (is_bag_constraint f1) || (is_bag_constraint f2)
  | CP.Or(f1, f2, _) -> (is_bag_constraint f1) || (is_bag_constraint f2)
  | CP.Not(f1, _) -> (is_bag_constraint f1)
  | CP.Forall(_, f1, _) -> (is_bag_constraint f1)
  | CP.Exists(_, f1, _) -> (is_bag_constraint f1)

and is_bag_constraint_b_formula (bf : CP.b_formula) : bool =
  match bf with
  | CP.BConst _ -> false
  | CP.BVar _ -> false
  | CP.Lt (e1, e2, _)
  | CP.Lte (e1, e2, _)
  | CP.Gt (e1, e2, _)
  | CP.Gte (e1, e2, _)
  | CP.Eq (e1, e2, _) (* these two could be arithmetic or pointer *)
  | CP.Neq (e1, e2, _)  -> (is_bag_constraint_exp e1) || (is_bag_constraint_exp e2)
  | CP.EqMax (e1, e2, e3, _) (* first is max of second and third *)
  | CP.EqMin (e1, e2, e3, _) (* first is min of second and third *)
       -> (is_bag_constraint_exp e1) || (is_bag_constraint_exp e2) || (is_bag_constraint_exp e3)
  (* bag formulas *)
  | CP.BagIn _
  | CP.BagNotIn _
  | CP.BagSub _
  | CP.BagMin _
  | CP.BagMax _ -> true

and is_bag_constraint_exp (e :CP.exp) : bool =
  match e with
  | CP.Null _
  | CP.Var _
  | CP.IConst _ -> false
  | CP.Add (e1, e2, _)
  | CP.Subtract (e1, e2, _) ->  (is_bag_constraint_exp e1) || (is_bag_constraint_exp e2)
  | CP.Mult _
  | CP.Max _
  | CP.Min _ -> false
  (* bag expressions *)
  | CP.Bag _
  | CP.BagUnion _
  | CP.BagIntersect _
  | CP.BagDiff _ -> true
*)

(*
let start () = match !tp with
  | OmegaCalc -> ()
  | CvcLite -> Cvclite.start ()
  | Isabelle -> Isabelle.start ()

let stop () = match !tp with
  | OmegaCalc -> ()
  | CvcLite -> let _ = Cvclite.stop () in ()
*)

let elim_exists_flag = ref true
let filtering_flag = ref true

let elim_exists (f : CP.formula) : CP.formula =
  if !elim_exists_flag then CP.elim_exists f
  else f

let filter (ante : CP.formula) (conseq : CP.formula) : (CP.formula * CP.formula) =
  if !filtering_flag then
	let fvar = CP.fv conseq in
	let new_ante = CP.filter_var ante fvar in
	  (new_ante, conseq)
  else
	(ante, conseq)

let tp_is_sat (f : CP.formula) =
	match !tp with
	  | OmegaCalc ->
(*
		  if (is_bag_constraint f) then
			begin
	          failwith ("[Tpdispatcher.ml]: The specification contains bag constraints which cannot be handled by Omega\n");
			end
		  else
*)
			begin
			  (Omega.is_sat f);
			end
	  | CvcLite -> Cvclite.is_sat f
	  | Isabelle -> Isabelle.is_sat f
	  | Coq -> Coq.is_sat f
	  | Mona -> Mona.is_sat f
	  | CO -> begin
		  let result1 = Cvclite.is_sat_raw f in
			match result1 with
			  | Some f -> f
			  | None ->
				  omega_count := !omega_count + 1;
				  Omega.is_sat f
		end
	  | CM -> begin
		  if (is_bag_constraint f) then
			Mona.is_sat f
		  else
			let result1 = Cvclite.is_sat_raw f in
			  match result1 with
				| Some f -> f
				| None ->
					omega_count := !omega_count + 1;
					Omega.is_sat f
		end
	  | OM ->
          if (is_bag_constraint f) then
			begin
			  (Mona.is_sat f);
			end
		  else
			begin
			  (Omega.is_sat f);
			end
	  | OI ->
          if (is_bag_constraint f) then
			begin
			  (Isabelle.is_sat f);
			end
		  else
			begin
			  (Omega.is_sat f);
			end
	  | SetMONA -> Setmona.is_sat f

let simplify (f : CP.formula) : CP.formula =
	if !external_prover then 
		Netprover.call_prover (Simplify f)
	else	 
	match !tp with
  | Isabelle -> Isabelle.simplify f
  | Coq -> Coq.simplify f
  | Mona -> Mona.simplify f
  | OM ->
	  if (is_bag_constraint f) then
		(Mona.simplify f)
	  else (Omega.simplify f)
  | OI ->
	  if (is_bag_constraint f) then
		(Isabelle.simplify f)
	  else (Omega.simplify f)
  | SetMONA -> Mona.simplify f
  | CM ->
	  if is_bag_constraint f then Mona.simplify f
	  else Omega.simplify f
  | _ ->
(*
	  if (is_bag_constraint f) then
		failwith ("[Tpdispatcher.ml]: The specification contains bag constraints which cannot be handled by Omega\n")
	  else
*)
	  (Omega.simplify f)

let hull (f : CP.formula) : CP.formula = match !tp with
  | Isabelle -> Isabelle.hull f
  | Coq -> Coq.hull f
  | Mona -> Mona.hull f
  | OM ->
	  if (is_bag_constraint f) then
		(Mona.hull f)
	  else (Omega.hull f)
  | OI ->
	  if (is_bag_constraint f) then
		(Isabelle.hull f)
	  else (Omega.hull f)
  | SetMONA -> Mona.hull f
  | CM ->
	  if is_bag_constraint f then Mona.hull f
	  else Omega.hull f
  | _ ->
	  (*
		if (is_bag_constraint f) then
		failwith ("[Tpdispatcher.ml]: The specification contains bag constraints which cannot be handled by Omega\n")
	  else
	  *)
	  (Omega.hull f)


let pairwisecheck (f : CP.formula) : CP.formula = match !tp with
  | Isabelle -> Isabelle.pairwisecheck f
  | Coq -> Coq.pairwisecheck f
  | Mona -> Mona.pairwisecheck f
  | OM ->
	  if (is_bag_constraint f) then
		(Mona.pairwisecheck f)
	  else (Omega.pairwisecheck f)
  | OI ->
	  if (is_bag_constraint f) then
		(Isabelle.pairwisecheck f)
	  else (Omega.pairwisecheck f)
  | SetMONA -> Mona.pairwisecheck f
  | CM ->
	  if is_bag_constraint f then Mona.pairwisecheck f
	  else Omega.pairwisecheck f
  | _ ->
	  (*
	  if (is_bag_constraint f) then
		failwith ("[Tpdispatcher.ml]: The specification contains bag constraints which cannot be handled by Omega\n")
	  else
	  *)
	  (Omega.pairwisecheck f)

(*
let rec imply (ante : CP.formula) (conseq : CP.formula) : bool =
  let tmp1 = CP.break_implication ante conseq in
	if (List.length tmp1) <= 1 then
	  imply1 ante conseq
	else
	  let _ = print_string ("splitting...") in
	  let res = List.for_all (fun (a, c) -> imply1 a c) tmp1 in
		res
*)

let rec split_conjunctions = function
  | CP.And (x, y, _) -> (split_conjunctions x) @ (split_conjunctions y)
  | z -> [z]
;;

let tp_imply ante conseq =
  match !tp with
  | OmegaCalc -> (Omega.imply ante conseq)
  | CvcLite -> Cvclite.imply ante conseq
  | Isabelle -> Isabelle.imply ante conseq
  | Coq -> Coq.imply ante conseq
  | Mona -> Mona.imply ante conseq
  | CO -> begin
	  let result1 = Cvclite.imply_raw ante conseq in
	  match result1 with
	  | Some f -> f
	  | None -> (* CVC Lite is not sure is this case, try Omega *)
		  omega_count := !omega_count + 1;
		  Omega.imply ante conseq
  end
  | CM -> begin
	  if (is_bag_constraint ante) || (is_bag_constraint conseq) then
		Mona.imply ante conseq
	  else
		let result1 = Cvclite.imply_raw ante conseq in
		match result1 with
		| Some f -> f
		| None -> (* CVC Lite is not sure is this case, try Omega *)
			omega_count := !omega_count + 1;
			Omega.imply ante conseq
  end
  | OM ->
	  if (is_bag_constraint ante) || (is_bag_constraint conseq) then
		(Mona.imply ante conseq)
	  else
		(Omega.imply ante conseq)
  | OI ->
	  if (is_bag_constraint ante) || (is_bag_constraint conseq) then
		(Isabelle.imply ante conseq)
	  else
		(Omega.imply ante conseq)
  | SetMONA ->
	  Setmona.imply ante conseq
;;

(* renames all quantified variables *)
let rec requant = function
  | CP.And (f, g, l) -> CP.And (requant f, requant g, l)
  | CP.Or (f, g, l) -> CP.Or (requant f, requant g, l)
  | CP.Not (f, l) -> CP.Not (requant f, l)
  | CP.Forall (v, f, l) ->
      let nv = CP.fresh_spec_var v in
      CP.Forall (nv, (CP.subst [v, nv] (requant f)), l)
  | CP.Exists (v, f, l) ->
      let nv = CP.fresh_spec_var v in
      CP.Exists (nv, (CP.subst [v, nv] (requant f)), l)
  | x -> x
;;

let rewrite_in_list list formula =
  match formula with
  | CP.BForm (CP.Eq (CP.Var (v1, _), CP.Var(v2, _), _)) ->
      List.map (fun x -> if x <> formula then CP.subst [v1, v2] x else x) list
  | CP.BForm (CP.Eq (CP.Var (v1, _), (CP.IConst(i, _) as term), _)) ->
      List.map (fun x -> if x <> formula then CP.subst_term [v1, term] x else x) list
  | x -> list
;;

let rec rewrite_in_and_tree rid formula rform =
  match formula with
  | CP.And (x, y, l) ->
      let (x, fx) = rewrite_in_and_tree rid x rform in
      let (y, fy) = rewrite_in_and_tree rid y rform in
      (CP.And (x, y, l), (fun e -> fx (fy e)))
  | x ->
      let subst_fun =
        match rform with
        | CP.BForm (CP.Eq (CP.Var (v1, _), CP.Var(v2, _), _)) -> CP.subst [v1, v2]
        | CP.BForm (CP.Eq (CP.Var (v1, _), (CP.IConst(i, _) as term), _)) -> CP.subst_term [v1, term]
        | CP.BForm (CP.Eq ((CP.IConst(i, _) as term), CP.Var (v1, _), _)) -> CP.subst_term [v1, term]
        | _ -> fun x -> x
      in
      if ((not rid) && x = rform) then (x, subst_fun) else (subst_fun x, subst_fun)
;;

let is_irrelevant = function
  | CP.BForm (CP.Eq (CP.Var (v1, _), CP.Var(v2, _), _)) -> v1 = v2
  | CP.BForm (CP.Eq (CP.IConst(i1, _), CP.IConst(i2, _), _)) -> i1 = i2
  | _ -> false
;;

let rec get_rid_of_eq = function
  | CP.And (x, y, l) -> 
      if is_irrelevant x then (get_rid_of_eq y) else
      if is_irrelevant y then (get_rid_of_eq x) else
      CP.And (get_rid_of_eq x, get_rid_of_eq y, l)
  | z -> z
;;

let rec fold_with_subst fold_fun current = function
  | [] -> current
  | h :: t ->
      let current, subst_fun = fold_fun current h in
      fold_with_subst fold_fun current (List.map subst_fun t)
;;

(* TODO goes in just once *)
let rec simpl_in_quant formula negated rid =
  match negated with
  | true ->
      begin match formula with
      | CP.Not (f, l) -> CP.Not (simpl_in_quant f false rid, l)
      | CP.Forall (v, f, l) -> CP.Forall (v, simpl_in_quant f true rid, l)
      | CP.Exists (v, f, l) -> CP.Exists (v, simpl_in_quant f true rid, l)
      | CP.Or (f, g, l) -> CP.Or (simpl_in_quant f false false, simpl_in_quant g false false, l)
      | CP.And (_, _, _) ->
          let subfs = split_conjunctions formula in
          let nformula = fold_with_subst (rewrite_in_and_tree rid) formula subfs in
          let nformula = get_rid_of_eq nformula in
          nformula
      | x -> x
      end
  | false ->
      begin match formula with
      | CP.Not (f, l) -> CP.Not (simpl_in_quant f true true, l)
      | CP.Forall (v, f, l) -> CP.Forall (v, simpl_in_quant f false rid, l)
      | CP.Exists (v, f, l) -> CP.Exists (v, simpl_in_quant f false rid, l)
      | CP.And (f, g, l) -> CP.And (simpl_in_quant f true false, simpl_in_quant g true false, l)
      | x -> x
      end
;;

let simpl_pair rid (ante, conseq) =
  let antes = split_conjunctions ante in
  let fold_fun (ante, conseq) = function
    | CP.BForm (CP.Eq (CP.Var (v1, _), CP.Var(v2, _), _)) ->
        ((CP.subst [v1, v2] ante, CP.subst [v1, v2] conseq), (CP.subst [v1, v2]))
    | CP.BForm (CP.Eq (CP.Var (v1, _), (CP.IConst(i, _) as term), _)) ->
        ((CP.subst_term [v1, term] ante, CP.subst_term [v1, term] conseq), (CP.subst_term [v1, term]))
    | CP.BForm (CP.Eq ((CP.IConst(i, _) as term), CP.Var (v1, _), _)) ->
        ((CP.subst_term [v1, term] ante, CP.subst_term [v1, term] conseq), (CP.subst_term [v1, term]))
    | _ -> ((ante, conseq), fun x -> x)
  in
  let (ante1, conseq) = fold_with_subst fold_fun (ante, conseq) antes in
  let ante1 = get_rid_of_eq ante1 in
  let ante2 = simpl_in_quant ante1 true rid in
  let ante3 = simpl_in_quant ante2 true rid in
  (ante3, conseq)
;;

let is_sat (f : CP.formula) : bool =
	if !external_prover then 
	    Netprover.call_prover (Simplify f)
	else     
  let f = elim_exists f in
  let (f, _) = simpl_pair true (f, CP.mkFalse no_pos) in
  tp_is_sat f
;;

let imply (ante0 : CP.formula) (conseq0 : CP.formula) : bool =
  if !external_prover then 
    Netprover.call_prover (Imply (ante0,conseq0))
  else begin 
	let conseq =
	if CP.should_simplify conseq0 then simplify conseq0
	else conseq0
  in
	(*	print_string ("conseq0: " ^ (Cprinter.string_of_pure_formula conseq0) ^ "\n");
		print_string ("conseq: " ^ (Cprinter.string_of_pure_formula conseq) ^ "\n"); *)
	if CP.isConstTrue conseq0 then
	  true
	else
	  let ante =
		if CP.should_simplify ante0 then simplify ante0
		else ante0
	  in
	  if CP.isConstFalse ante0 || CP.isConstFalse ante then true
	  else
		let ante = elim_exists ante in
		let conseq = elim_exists conseq in
        let split_conseq = split_conjunctions conseq in
        let pairs = List.map (fun cons -> let (ante,cons) = simpl_pair false (requant ante, requant cons) in filter ante cons) split_conseq in
        (*let pairs = [filter ante conseq] in*)
        (*print_endline ("EEE: " ^ (string_of_int (List.length pairs)));*)
        let fold_fun res (ante, conseq) =
          if res then tp_imply ante conseq else false
        in
        List.fold_left fold_fun true pairs
  end
;;

let sat_timer = ref 0.;;
let imply_timer = ref 0.;;

let imply ante0 conseq0 =
  let timer = Unix.gettimeofday () in
  let res = imply ante0 conseq0 in
  imply_timer := !imply_timer +. (Unix.gettimeofday ()) -. timer;
  res
;;

let is_sat f =
  if !external_prover then 
    Netprover.call_prover (Sat f)
  else     
	
  let timer = Unix.gettimeofday () in
  let res = is_sat f in
  sat_timer := !sat_timer +. (Unix.gettimeofday ()) -. timer;
  res
;;

let print_stats () =
  print_string ("\nTP statistics:\n");
  print_string ("omega_count = " ^ (string_of_int !omega_count) ^ "\n")
