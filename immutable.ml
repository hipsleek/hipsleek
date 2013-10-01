(*
2011: Immutability module:
  - utils for immutability
*)

open Globals
open Cast
open Prooftracer
open Gen.Basic
open Cformula

module CP = Cpure
module PR = Cprinter
module MCP = Mcpure
module Err = Error
module TP = Tpdispatcher
module IF = Iformula
module IP = Iprinter
module C  = Cast


(* let rec split_phase_debug_lhs h = Debug.no_1 "split_phase(lhs)" *)
(*   Cprinter.string_of_h_formula  *)
(*   (fun (a,b,c) -> "RD = " ^ (Cprinter.string_of_h_formula a) ^ "; WR = " ^ (Cprinter.string_of_h_formula b) ^ "; NEXT = " ^ (Cprinter.string_of_h_formula c) ^ "\n")  *)
(*   split_phase h *)

(* and split_phase_debug_rhs h = Debug.no_1 "split_phase(rhs)" *)
(*   Cprinter.string_of_h_formula  *)
(*   (fun (a,b,c) -> "RD = " ^ (Cprinter.string_of_h_formula a) ^ "; WR = " ^ (Cprinter.string_of_h_formula b) ^ "; NEXT = " ^ (Cprinter.string_of_h_formula c) ^ "\n")  *)
(*   split_phase 0 h *)

let rec remove_true_rd_phase (h : CF.h_formula) : CF.h_formula = 
  match h with
    | CF.Phase ({CF.h_formula_phase_rd = h1;
	  CF.h_formula_phase_rw = h2;
	  CF.h_formula_phase_pos = pos
	 }) -> 
      if (h1 == CF.HEmp) then h2
      else if (h2 == CF.HEmp) then h1
      else h
    | CF.Star ({CF.h_formula_star_h1 = h1;
	  CF.h_formula_star_h2 = h2;
	  CF.h_formula_star_pos = pos
	 }) -> 
      let h1r = remove_true_rd_phase h1 in
      let h2r = remove_true_rd_phase h2 in
      CF.mkStarH h1r h2r pos
    | _ -> h


let rec split_wr_phase (h : h_formula) : (h_formula * h_formula) = 
  match h with 
    | Star ({h_formula_star_h1 = h1;
	  h_formula_star_h2 = h2;
	  h_formula_star_pos = pos}) -> 
      (* let _ = print_string("[cris]: split star " ^ (Cprinter.string_of_h_formula h) ^ "\n") in *)
	      (match h2 with
	        | Phase _ -> (h1, h2)
	        | Star ({h_formula_star_h1 = sh1;
		      h_formula_star_h2 = sh2;
		      h_formula_star_pos = spos}) ->
		          split_wr_phase (CF.mkStarH (CF.mkStarH h1 sh1 pos ) sh2 pos )
	        | _ -> 
		  (* if ((is_lend_h_formula h1) && is_lend_h_formula h2) then *)
		  (*   (, h2) *)
		  (* else  *)
		    (h, HEmp)
	      )
    | Conj _ 
    | ConjStar _ 	      
    | ConjConj _ -> report_error no_pos ("[solver.ml] : Conjunction should not appear at this level \n")
    | Phase({h_formula_phase_rd = h1;
	  h_formula_phase_rw = h2;
	  h_formula_phase_pos = pos}) ->
	      (HEmp, h)
    | _ -> (h, HEmp)

            
let rec consume_heap_h_formula (f : h_formula) : bool =  match f with
  | DataNode (h1) -> ((CP.isMutable h1.h_formula_data_imm) || (CP.isImm h1.h_formula_data_imm))
  | ViewNode (h1) -> ((CP.isMutable h1.h_formula_view_imm) || (CP.isImm h1.h_formula_view_imm))
  | Conj({h_formula_conj_h1 = h1;
	h_formula_conj_h2 = h2;
	h_formula_conj_pos = pos})
  | ConjStar({h_formula_conjstar_h1 = h1;
	h_formula_conjstar_h2 = h2;
	h_formula_conjstar_pos = pos})
  | ConjConj({h_formula_conjconj_h1 = h1;
	h_formula_conjconj_h2 = h2;
	h_formula_conjconj_pos = pos})		
  | Phase({h_formula_phase_rd = h1;
	h_formula_phase_rw = h2;
	h_formula_phase_pos = pos})
  | Star({h_formula_star_h1 = h1;
	h_formula_star_h2 = h2;
	h_formula_star_pos = pos}) -> (consume_heap_h_formula h1) or (consume_heap_h_formula h2)
  | _ -> false


let rec consume_heap (f : formula) : bool =  match f with
  | Base(bf) -> consume_heap_h_formula bf.formula_base_heap
  | Exists(ef) -> consume_heap_h_formula ef.formula_exists_heap
  | Or({formula_or_f1 = f1;
    formula_or_f2 = f2;
    formula_or_pos = pos}) ->
        (consume_heap f1) or (consume_heap f2)

let rec split_phase_x (h : h_formula) : (h_formula * h_formula * h_formula ) = 
  let h = remove_true_rd_phase h in
  match h with
    | Phase ({h_formula_phase_rd = h1;
	  h_formula_phase_rw = h2;
	  h_formula_phase_pos = pos}) -> 
	      let h3, h4 = split_wr_phase h2 in
	      (h1, h3, h4)
    | Star _ ->
	      let h3, h4 = split_wr_phase h in
	      (HEmp, h3, h4)
    | _ ->
	      if (consume_heap_h_formula h) then
	        (HEmp, h, HEmp)
	      else
	        (h, HEmp, HEmp)

let split_phase i (h : h_formula) : (h_formula * h_formula * h_formula )= 
  let pr = Cprinter.string_of_h_formula in
  let pr2 = pr_triple pr pr pr in
  Debug.no_1_num i "split_phase" pr pr2 split_phase_x h

let isAccs = CP.isAccs 
let isLend = CP.isLend 
let isImm = CP.isImm 
let isMutable = CP.isMutable

let isAccsList (al : CP.ann list) : bool = List.for_all isAccs al

let isExistsLendList (al : CP.ann list) : bool = List.exists isLend al

(* should be the opposite of consumes produces_hole x = not(consumes x); 
   depending on the LHS CP.ann, PolyCP.Ann might consume after a match, but it is considered to
   initialy create a hole. *)
let produces_hole (a: CP.ann): bool = 
  if isLend a || isAccs  a (* || isPoly a *) then true
  else false

let maybe_replace_w_empty h = 
  match h with
    | CF.DataNode dn -> 
          let node_imm = dn.CF.h_formula_data_imm in
          let param_imm = dn.CF.h_formula_data_param_imm in
          let new_h = 
            match !Globals.allow_field_ann, !Globals.allow_imm with
              | true, _     -> if (isAccsList param_imm) then HEmp else h
              | false, true -> if (isAccs node_imm) then HEmp else h
              | _,_         -> HEmp
          in new_h
    | _ -> h

let ann_opt_to_ann (ann_opt: IF.ann option) (default_ann: IF.ann): IF.ann = 
  match ann_opt with
    | Some ann0 -> ann0
    | None      -> default_ann

let rec ann_opt_to_ann_lst (ann_opt_lst: IF.ann option list) (default_ann: IF.ann): IF.ann list = 
  match ann_opt_lst with
    | [] -> []
    | ann0 :: t -> (ann_opt_to_ann ann0 default_ann) :: (ann_opt_to_ann_lst t default_ann)

let iformula_ann_to_cformula_ann (iann : IF.ann) : CP.ann = 
  match iann with
    | IF.ConstAnn(x) -> CP.ConstAnn(x)
    | IF.PolyAnn((id,p), l) -> 
          CP.PolyAnn(CP.SpecVar (AnnT, id, p))

let iformula_ann_to_cformula_ann_lst (iann_lst : IF.ann list) : CP.ann list = 
  List.map iformula_ann_to_cformula_ann iann_lst

let iformula_ann_opt_to_cformula_ann_lst (iann_lst : IF.ann option list) : CP.ann list = 
  List.map iformula_ann_to_cformula_ann (ann_opt_to_ann_lst iann_lst  (IF.ConstAnn(Mutable)))


let rec is_lend_h_formula (f : h_formula) : bool =  match f with
  | DataNode (h1) -> 
        if (isLend h1.h_formula_data_imm) then
          (* let _ = print_string("true for h = " ^ (!print_h_formula f) ^ "\n\n")  in *) true
        else
          false
  | ViewNode (h1) ->
        if (isLend h1.h_formula_view_imm) then
          (* let _ = print_string("true for h = " ^ (!print_h_formula f) ^ "\n\n") in *) true
        else
          false

  | Conj({h_formula_conj_h1 = h1;
	h_formula_conj_h2 = h2;
	h_formula_conj_pos = pos})
  | ConjStar({h_formula_conjstar_h1 = h1;
	h_formula_conjstar_h2 = h2;
	h_formula_conjstar_pos = pos})
  | ConjConj({h_formula_conjconj_h1 = h1;
	h_formula_conjconj_h2 = h2;
	h_formula_conjconj_pos = pos})		
  | Phase({h_formula_phase_rd = h1;
	h_formula_phase_rw = h2;
	h_formula_phase_pos = pos}) -> true
  | Star({h_formula_star_h1 = h1;
	h_formula_star_h2 = h2;
	h_formula_star_pos = pos}) -> (is_lend_h_formula h1) or (is_lend_h_formula h2)
  | Hole _ -> false
  | _ -> false

let is_lend_h_formula_debug f = 
  Debug.no_1 "is_lend_h_formula"
      (!print_h_formula)
      (string_of_bool)
      is_lend_h_formula f

let rec is_lend (f : formula) : bool =  match f with
  | Base(bf) -> is_lend_h_formula bf.formula_base_heap
  | Exists(ef) -> is_lend_h_formula ef.formula_exists_heap
  | Or({formula_or_f1 = f1;
    formula_or_f2 = f2;
    formula_or_pos = pos}) ->
        (is_lend f1) or (is_lend f2)

let is_lend_debug f = 
  Debug.no_1 "is_lend"
      (!print_formula)
      (string_of_bool)
      is_lend f

let decide_where_to_add_constr constr1 constr2  impl_vars expl_vars evars sv fsv =
  if CP.mem sv impl_vars then (constr1::[constr2], [], [], [])
  else if CP.mem sv expl_vars then
    ([constr2], [constr1], (* [r_constr] *)[], [])
  else if CP.mem sv evars then
    ([constr2], [(* constr1 *)], [(* constr1 *)], [(sv,fsv)])
  else (constr1::[constr2], [], [], [])

let mkTempRes_x ann_l ann_r  impl_vars expl_vars evars =
  match ann_r with
    | CP.PolyAnn sv ->
          let fresh_v = "ann_" ^ (fresh_name ()) in
          let fresh_sv = (CP.SpecVar(AnnT, fresh_v, Unprimed)) in
          let fresh_var = CP.Var(fresh_sv, no_pos) in
          let poly_ann = CP.mkPolyAnn fresh_sv in
          let constr1 = CP.BForm ((CP.Eq(fresh_var,(CP.mkExpAnnSymb ann_r no_pos),no_pos),None), None) in
          let constr2 = CP.BForm ((CP.SubAnn((CP.mkExpAnnSymb ann_l no_pos),fresh_var,no_pos),None), None) in
          let to_lhs, to_rhs, to_rhs_ex, subst = decide_where_to_add_constr constr1 constr2  impl_vars expl_vars evars sv fresh_sv in
          ((CP.TempRes(ann_l,poly_ann),poly_ann), [fresh_sv], ((to_lhs, to_rhs, to_rhs_ex),subst))
    | _ -> ((CP.TempRes(ann_l, ann_r), ann_r), [], (([], [], []),[]))       (* should not reach this branch *)

let mkTempRes ann_l ann_r  impl_vars expl_vars evars =
  let pr = Cprinter.string_of_imm in
  let pr1 = pr_pair pr pr in
  let pr3a = pr_list !CP.print_formula in
  let pr3 = pr_pair (pr_triple pr3a pr3a pr3a) (add_str "\n\t subst" (pr_list (pr_pair Cprinter.string_of_spec_var Cprinter.string_of_spec_var) )) in 
  let pr_out = pr_triple (add_str "(residue,cosumed) = " pr1) 
    (add_str "\n\tnew var:" (pr_list Cprinter.string_of_spec_var))
    (add_str "\n\tconstraints: " pr3) in 
  Debug.no_2 "mkTempRes"  pr pr pr_out (fun _ _ -> mkTempRes_x ann_l ann_r  impl_vars expl_vars evars ) ann_l ann_r

let apply_f_to_annot_arg f_imm (args: CP.annot_arg list) : CP.annot_arg list=
  let args = CP.annot_arg_to_imm_ann_list args in
  let args =  f_imm args in
  let args = CP.imm_ann_to_annot_arg_list args in
  args

let build_eset_of_conj_formula f =
  let lst = CP.split_conjunctions f in
  let emap = List.fold_left (fun acc f -> match f with
    | CP.BForm (bf,_) ->
          (match bf with
            | (CP.Eq (CP.Var (v1,_), CP.Var (v2,_), _),_) -> 
                  if (CP.is_bag_typ v1) then acc
                  else CP.EMapSV.add_equiv acc v1 v2
            | (CP.Eq (ex, CP.Var (v1,_), _),_) 
            | (CP.Eq (CP.Var (v1,_), ex, _),_) -> 
                  (match CP.conv_ann_exp_to_var ex with
                    | Some (v2,_) -> CP.EMapSV.add_equiv acc v1 v2
                    | None -> acc)
            | (CP.SubAnn (CP.Var (v1,_), (CP.AConst(Mutable,_) as exp), _),_) -> (* bot *)
                  let v2 = CP.mk_sv_aconst Mutable in CP.EMapSV.add_equiv acc v1 v2
            | (CP.SubAnn(CP.AConst(Accs,_) as exp, CP.Var (v1,_), _),_) -> (* top *)
                  let v2 = CP.mk_sv_aconst Accs in CP.EMapSV.add_equiv acc v1 v2
            | _ -> acc)
    | _ -> acc
  ) CP.EMapSV.mkEmpty lst in emap

(* and contains_phase_debug (f : h_formula) : bool =   *)
(*   Debug.no_1 "contains_phase" *)
(*       (!print_h_formula)  *)
(*       (string_of_bool) *)
(*       (contains_phase) *)
(*       f *)
(* normalization for iformula *)
(* normalization of the heap formula *)
(* emp & emp * K == K *)
(* KR: check there is only @L *)
(* KR & KR ==> KR ; (KR ; true) *)

let rec normalize_h_formula (h : IF.h_formula) (wr_phase : bool) : IF.h_formula =
  Debug.no_1 "normalize_h_formula"
      (IP.string_of_h_formula)
      (IP.string_of_h_formula)
      (fun _ -> normalize_h_formula_x h wr_phase) h

and normalize_h_formula_x (h : IF.h_formula) (wr_phase : bool) : IF.h_formula =
  let h = normalize_h_formula_phase h wr_phase in
  (* let h = normalize_field_ann_heap_node h in *)
  h

and normalize_h_formula_phase (h : IF.h_formula) (wr_phase : bool) : IF.h_formula =
  let get_imm (h : IF.h_formula) : CP.ann = 
    let iann =
      match h with
        | IF.HeapNode2 hf -> hf.IF.h_formula_heap2_imm
        | IF.HeapNode hf -> hf.IF.h_formula_heap_imm
        | _ -> failwith ("Error in  normalize_h_formula\n")
    in
    (iformula_ann_to_cformula_ann iann)
  in
  let rec extract_inner_phase f = match f with
    | IF.Phase _ -> (IF.HEmp, f)
    | IF.Star ({IF.h_formula_star_h1 = h1;
      IF.h_formula_star_h2 = h2;
      IF.h_formula_star_pos = pos
      }) ->
          let r11, r12 = extract_inner_phase h1 in
          let r21, r22 = extract_inner_phase h2 in
          (IF.mkStar r11 r21 pos, IF.mkStar r12 r22 pos)
    | _ -> (f,IF.HEmp)
  in
  let rec aux h wr_phase = 
  match h with
    | IF.Phase({IF.h_formula_phase_rd = h1;
      IF.h_formula_phase_rw = h2;
      IF.h_formula_phase_pos = pos
      }) ->
            let rd_phase = normalize_h_formula_rd_phase h1 in
            let wr_phase = aux h2 true in 
            let res = insert_wr_phase rd_phase wr_phase in
            res
    | IF.Star({IF.h_formula_star_h1 = h1;
      IF.h_formula_star_h2 = h2;
      IF.h_formula_star_pos = pos
      }) ->
          let r1, r2 = extract_inner_phase h2 in
          if (r1 == IF.HEmp) || (r2 == IF.HEmp) then 
            IF.Star({IF.h_formula_star_h1 = h1;
            IF.h_formula_star_h2 = aux h2 false;
            IF.h_formula_star_pos = pos
            }) 
          else
            (* isolate the inner phase *)
            IF.Star({IF.h_formula_star_h1 = IF.mkStar h1 r1 pos;
            IF.h_formula_star_h2 = aux r2 false;
            IF.h_formula_star_pos = pos
            }) 
    | IF.Conj({IF.h_formula_conj_h1 = h1;
      IF.h_formula_conj_h2 = h2;
      IF.h_formula_conj_pos = pos
      }) 
    | IF.ConjStar({IF.h_formula_conjstar_h1 = h1;
      IF.h_formula_conjstar_h2 = h2;
      IF.h_formula_conjstar_pos = pos
      }) 
    | IF.ConjConj({IF.h_formula_conjconj_h1 = h1;
      IF.h_formula_conjconj_h2 = h2;
      IF.h_formula_conjconj_pos = pos
      })               ->
          if (wr_phase) && (!Globals.allow_mem) then h else
            normalize_h_formula_rd_phase h
    | IF.HeapNode2 hf -> 
          (let annv = get_imm h in
          match annv with
            | CP.ConstAnn(Lend)  | CP.ConstAnn(Imm)  | CP.ConstAnn(Accs) -> h
            | _ ->
                  begin
                    (* write phase *)
                    if (wr_phase) then h
                    else
                      IF.Phase({IF.h_formula_phase_rd = IF.HEmp;
                      IF.h_formula_phase_rw = h;
                      IF.h_formula_phase_pos = no_pos;
                      })
                  end)
    | IF.HeapNode hf ->
          (let annv = get_imm h in
          match annv with
            | CP.ConstAnn(Lend) | CP.ConstAnn(Imm)  | CP.ConstAnn(Accs) -> h
            | _ ->
                  begin
                    (* write phase *)
                    if (wr_phase) then h
                    else
                      IF.Phase({IF.h_formula_phase_rd = IF.HEmp;
                      IF.h_formula_phase_rw = h;
                      IF.h_formula_phase_pos = no_pos;
                      })
                  end)
    | _ ->  IF.Phase { IF.h_formula_phase_rd = IF.HEmp;
      IF.h_formula_phase_rw = h;
      IF.h_formula_phase_pos = no_pos }
  in aux h wr_phase

and contains_phase (h : IF.h_formula) : bool = match h with
  | IF.Phase _ -> true
  | IF.Conj ({IF.h_formula_conj_h1 = h1;
    IF.h_formula_conj_h2 = h2;
    IF.h_formula_conj_pos = pos;
    }) 
  | IF.ConjStar ({IF.h_formula_conjstar_h1 = h1;
    IF.h_formula_conjstar_h2 = h2;
    IF.h_formula_conjstar_pos = pos;
    })
  | IF.ConjConj ({IF.h_formula_conjconj_h1 = h1;
    IF.h_formula_conjconj_h2 = h2;
    IF.h_formula_conjconj_pos = pos;
    })        
  | IF.Star ({IF.h_formula_star_h1 = h1;
    IF.h_formula_star_h2 = h2;
    IF.h_formula_star_pos = pos}) ->
        (contains_phase h1) or (contains_phase h2)
  | _ -> false

(* conj in read phase -> split into two separate read phases *)
and normalize_h_formula_rd_phase (h : IF.h_formula) : IF.h_formula = match h with
  | IF.Conj({IF.h_formula_conj_h1 = h1;
    IF.h_formula_conj_h2 = h2;
    IF.h_formula_conj_pos = pos})
  | IF.ConjStar({IF.h_formula_conjstar_h1 = h1;
    IF.h_formula_conjstar_h2 = h2;
    IF.h_formula_conjstar_pos = pos})
  | IF.ConjConj({IF.h_formula_conjconj_h1 = h1;
    IF.h_formula_conjconj_h2 = h2;
    IF.h_formula_conjconj_pos = pos})	 	 
      ->
        (* conj in read phase -> split into two separate read phases *)
        let conj1 = normalize_h_formula_rd_phase h1 in
	insert_rd_phase conj1 h2 
  | IF.Phase _ -> failwith "Shouldn't have phases inside the reading phase\n"
  | _ -> IF.Phase({IF.h_formula_phase_rd = h;
    IF.h_formula_phase_rw = IF.HEmp;
    IF.h_formula_phase_pos = no_pos;
    })

(* the read phase contains only pred with the annotation @L *)
and validate_rd_phase (h : IF.h_formula) : bool = match h with
  | IF.Star({IF.h_formula_star_h1 = h1;
    IF.h_formula_star_h2 = h2;
    IF.h_formula_star_pos = pos}) 
  | IF.Conj({IF.h_formula_conj_h1 = h1;
    IF.h_formula_conj_h2 = h2;
    IF.h_formula_conj_pos = pos}) 
  | IF.ConjStar({IF.h_formula_conjstar_h1 = h1;
    IF.h_formula_conjstar_h2 = h2;
    IF.h_formula_conjstar_pos = pos})
  | IF.ConjConj({IF.h_formula_conjconj_h1 = h1;
    IF.h_formula_conjconj_h2 = h2;
    IF.h_formula_conjconj_pos = pos})	 	 
      -> (validate_rd_phase h1) && (validate_rd_phase h2)
  | IF.Phase _ -> false (* Shouldn't have phases inside the reading phase *)
  | IF.HeapNode2 hf -> (IF.isLend hf.IF.h_formula_heap2_imm) 
  | IF.HeapNode hf -> (IF.isLend hf.IF.h_formula_heap_imm)
  | _ -> true

and insert_wr_phase_x (f : IF.h_formula) (wr_phase : IF.h_formula) : IF.h_formula = 
  match f with
    | IF.Phase ({IF.h_formula_phase_rd = h1;
      IF.h_formula_phase_rw = h2;
      IF.h_formula_phase_pos = pos}) ->
	  let new_h2 = 
	    match h2 with
	      | IF.HEmp -> wr_phase (* insert the new phase *)
	      | IF.Star({IF.h_formula_star_h1 = h1_star;
		IF.h_formula_star_h2 = h2_star;
		IF.h_formula_star_pos = pos_star
		}) ->
		    (* when insert_wr_phase is called, f represents a reading phase ->
		       all the writing phases whould be emp *)
		    if (contains_phase h2_star) then
		      (* insert in the nested phase *)
		      IF.Star({
			  IF.h_formula_star_h1 = h1_star;
			  IF.h_formula_star_h2 = insert_wr_phase h2_star wr_phase;
			  IF.h_formula_star_pos = pos_star
		      })
		    else failwith ("[iformula.ml] : should contain phase\n")
		      
	      | _ -> IF.Star({
		    IF.h_formula_star_h1 = h2;
		    IF.h_formula_star_h2 = wr_phase;
		    IF.h_formula_star_pos = pos
		})
	  in
	  (* reconstruct the phase *)
	  IF.Phase({IF.h_formula_phase_rd = h1;
	  IF.h_formula_phase_rw = new_h2;
	  IF.h_formula_phase_pos = pos})
    | _ -> failwith ("[iformula.ml] : There should be a phase at this point\n")

and insert_wr_phase (f : IF.h_formula) (wr_phase : IF.h_formula) : IF.h_formula =
  let pr_h = Iprinter.string_of_h_formula in
  Debug.no_2 "Immutable.insert_wr_phase" pr_h pr_h pr_h insert_wr_phase_x f wr_phase

and insert_rd_phase_x (f : IF.h_formula) (rd_phase : IF.h_formula) : IF.h_formula = 
  match f with
    | IF.Phase ({IF.h_formula_phase_rd = h1;
      IF.h_formula_phase_rw = h2;
      IF.h_formula_phase_pos = pos}) ->
	  let new_h2 = 
	    (match h2 with
	      | IF.HEmp -> 
	            (* construct the new phase *)
		    let new_phase = IF.Phase({IF.h_formula_phase_rd = rd_phase; 
		    IF.h_formula_phase_rw = IF.HEmp;
		    IF.h_formula_phase_pos = pos})
		    in
		    (* input the new phase *)
		    IF.Star({IF.h_formula_star_h1 = IF.HEmp;
		    IF.h_formula_star_h2 = new_phase;
		    IF.h_formula_star_pos = pos})
		        
	      | IF.Conj _ 
	      | IF.ConjStar _ 
	      | IF.ConjConj _ -> failwith ("[cformula.ml] : Should not have conj at this point\n") (* the write phase does not contain conj *)	     
	      | IF.Star ({IF.h_formula_star_h1 = h1_star;
		IF.h_formula_star_h2 = h2_star;
		IF.h_formula_star_pos = pos_star
		}) ->
	            let new_phase = insert_rd_phase h2_star rd_phase in
	            IF.Star({IF.h_formula_star_h1 = h1_star;
		    IF.h_formula_star_h2 = new_phase;
		    IF.h_formula_star_pos = pos_star})
	      | _ ->
		    let new_phase = IF.Phase({IF.h_formula_phase_rd = rd_phase; 
		    IF.h_formula_phase_rw = IF.HEmp;
		    IF.h_formula_phase_pos = pos})
		    in
		    IF.Star({IF.h_formula_star_h1 = h2;
		    IF.h_formula_star_h2 = new_phase;
		    IF.h_formula_star_pos = pos})
	    )
	  in
	  IF.Phase({
	      IF.h_formula_phase_rd = h1;
	      IF.h_formula_phase_rw = new_h2;
	      IF.h_formula_phase_pos = pos;
	  })
    | IF.Conj _
    | IF.ConjStar _
    | IF.ConjConj _ -> failwith ("[cformula.ml] : Should not have conj at this point\n")	     
    | _ -> 
	  let new_phase = IF.Phase({IF.h_formula_phase_rd = rd_phase; 
	  IF.h_formula_phase_rw = IF.HEmp;
	  IF.h_formula_phase_pos = no_pos})
	  in
	  let new_star = IF.Star({IF.h_formula_star_h1 = IF.HEmp;
	  IF.h_formula_star_h2 = new_phase;
	  IF.h_formula_star_pos = no_pos})
	  in 
	  IF.Phase({
	      IF.h_formula_phase_rd = f;
	      IF.h_formula_phase_rw = new_star;
	      IF.h_formula_phase_pos = no_pos;
	  })
and insert_rd_phase (f : IF.h_formula) (wr_phase : IF.h_formula) : IF.h_formula =
  let pr_h = Iprinter.string_of_h_formula in
  Debug.no_2 "Immutable.insert_rd_phase" pr_h pr_h pr_h insert_rd_phase_x f wr_phase

(* and propagate_imm_struc_formula e (imm : CP.ann)  (imm_p: (CP.annot_arg * CP.annot_arg) list) emap = *)
(*   (\* andreeac: to check why do we have all these constructs? *\) *)
(*   let f_e_f e = None  in *)
(*   let f_f e = None in *)
(*   let f_h_f  f = Some (propagate_imm_h_formula f imm imm_p emap) in *)
(*   let f_p_t1 e = Some e in *)
(*   let f_p_t2 e = Some e in *)
(*   let f_p_t3 e = Some e in *)
(*   let f_p_t4 e = Some e in *)
(*   let f_p_t5 e = Some e in *)
(*   let f=(f_e_f,f_f,f_h_f,(f_p_t1,f_p_t2,f_p_t3,f_p_t4,f_p_t5)) in *)
(*   transform_struc_formula f e *)

and propagate_imm_struc_formula sf (imm : CP.ann)  (imm_p: (CP.annot_arg * CP.annot_arg) list) =
  match sf with
    | EBase f   -> EBase {f with 
          formula_struc_base = propagate_imm_formula f.formula_struc_base imm imm_p }
    | EList l   -> EList  (map_l_snd (fun c->  propagate_imm_struc_formula c imm imm_p) l)
    | ECase f   -> ECase {f with formula_case_branches = map_l_snd (fun c->  propagate_imm_struc_formula c imm imm_p) f.formula_case_branches;}
    | EAssume f -> EAssume {f with
	  formula_assume_simpl = propagate_imm_formula f.formula_assume_simpl imm imm_p;
	  formula_assume_struc = propagate_imm_struc_formula  f.formula_assume_struc imm imm_p;}
    | EInfer f  -> EInfer {f with formula_inf_continuation = propagate_imm_struc_formula f.formula_inf_continuation imm imm_p} 

and propagate_imm_formula (f : formula) (imm : CP.ann) (imm_p: (CP.annot_arg * CP.annot_arg) list): formula = match f with
  | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) ->
	let rf1 = propagate_imm_formula f1 imm imm_p in
	let rf2 = propagate_imm_formula f2 imm imm_p in
	let resform = mkOr rf1 rf2 pos in
	resform
  | Base f1 ->
        let emap = build_eset_of_conj_formula (MCP.pure_of_mix  f1.CF.formula_base_pure) in
        let f1_heap = propagate_imm_h_formula f1.formula_base_heap imm imm_p emap in
        Base({f1 with formula_base_heap = f1_heap})
  | Exists f1 ->
        let emap = build_eset_of_conj_formula (MCP.pure_of_mix  f1.CF.formula_exists_pure) in
        let f1_heap = propagate_imm_h_formula f1.formula_exists_heap imm imm_p emap in
        Exists({f1 with formula_exists_heap = f1_heap})

(* andreeac TODOIMM: to replace below so that it uses emap *)
and replace_imm imm map emap=
  match imm with
    | CP.ConstAnn _ -> imm
    | CP.PolyAnn sv -> 
          begin
            let new_imm = List.fold_left (fun acc (fr,t) ->
                if ( Gen.BList.mem_eq CP.eq_ann imm (CP.annot_arg_to_imm_ann fr)) then (CP.annot_arg_to_imm_ann t) else acc) [] map in
            match new_imm with
              | []   -> imm
              | h::_ -> h
          end
    | _ -> imm                          (* replace temp as well *)


and propagate_imm_h_formula_x (f : h_formula) (imm : CP.ann)  (imm_p: (CP.annot_arg * CP.annot_arg) list) emap : h_formula = 
  match f with
    | ViewNode f1 -> 
          let new_node_imm = imm in
          let new_args_imm = List.fold_left (fun acc (fr,t) -> 
              if (Gen.BList.mem_eq CP.eq_annot_arg fr (f1.CF.h_formula_view_annot_arg)) then acc@[t] else acc) []  imm_p in
          (* andreeac: why was below needed? *)
          (* match f1.Cformula.h_formula_view_imm with *)
	  (*   | CP.ConstAnn _ -> imm *)
	  (*   | _ ->  *)
	  (*         begin *)
	  (*           match imm with  *)
	  (*             | CP.ConstAnn _ -> imm *)
	  (*             | _ -> f1.Cformula.h_formula_view_imm  *)
	  (*         end *)
          ViewNode({f1 with h_formula_view_imm = new_node_imm;
              h_formula_view_annot_arg = new_args_imm;
          })
    | DataNode f1 -> 
          let new_param_imm = List.map (fun a -> replace_imm a imm_p emap) f1.CF.h_formula_data_param_imm in
          DataNode({f1 with h_formula_data_imm = imm;
              h_formula_data_param_imm = new_param_imm;})

          (* andreeac: why was below needed? *)
          (* DataNode({f1 with h_formula_data_imm = *)
	      (* (match f1.Cformula.h_formula_data_imm with *)
	      (*   | CP.ConstAnn _ -> imm *)
	      (*   | _ -> begin *)
	      (*       match imm with  *)
	      (*         | CP.ConstAnn _ -> imm *)
	      (* (\*         | _ -> f1.Cformula.h_formula_data_imm  *\) *)
	      (* (\*     end); *\) *)
	      (*     h_formula_data_param_imm =  *)
	      (*     List.map (fun c -> if (subtype_ann 1 imm c) then c else imm) f1.Cformula.h_formula_data_param_imm}) *)
    | Star f1 ->
	  let h1 = propagate_imm_h_formula f1.h_formula_star_h1 imm imm_p emap in
	  let h2 = propagate_imm_h_formula f1.h_formula_star_h2 imm imm_p emap in
	  mkStarH h1 h2 f1.h_formula_star_pos 
    | Conj f1 ->
	  let h1 = propagate_imm_h_formula f1.h_formula_conj_h1 imm imm_p emap in
	  let h2 = propagate_imm_h_formula f1.h_formula_conj_h2 imm imm_p emap in
	  mkConjH h1 h2 f1.h_formula_conj_pos
    | ConjStar f1 ->
	  let h1 = propagate_imm_h_formula f1.h_formula_conjstar_h1 imm imm_p emap in
	  let h2 = propagate_imm_h_formula f1.h_formula_conjstar_h2 imm imm_p emap in
	  mkConjStarH h1 h2 f1.h_formula_conjstar_pos
    | ConjConj f1 ->
	  let h1 = propagate_imm_h_formula f1.h_formula_conjconj_h1 imm imm_p emap in
	  let h2 = propagate_imm_h_formula f1.h_formula_conjconj_h2 imm imm_p emap in
	  mkConjConjH h1 h2 f1.h_formula_conjconj_pos	      	      
    | Phase f1 ->
	  let h1 = propagate_imm_h_formula f1.h_formula_phase_rd imm imm_p emap in
	  let h2 = propagate_imm_h_formula f1.h_formula_phase_rw imm imm_p emap in
	  mkPhaseH h1 h2 f1.h_formula_phase_pos
    | _ -> f

and propagate_imm_h_formula (f : h_formula) (imm : CP.ann)  (map: (CP.annot_arg * CP.annot_arg) list) emap: h_formula = 
  Debug.no_3 "propagate_imm_h_formula" 
      (Cprinter.string_of_h_formula) 
      (Cprinter.string_of_imm) 
      (pr_list (pr_pair Cprinter.string_of_annot_arg Cprinter.string_of_annot_arg )) 
      (Cprinter.string_of_h_formula) 
      (fun _ _ _ -> propagate_imm_h_formula_x f imm map emap) f imm map

(* return true if imm1 <: imm2 *)	
(* M <: I <: L <: A*)
and subtype_ann caller (imm1 : CP.ann) (imm2 : CP.ann) : bool = 
  let pr_imm = Cprinter.string_of_imm in
  let pr1 (imm1,imm2) =  (pr_imm imm1) ^ " <: " ^ (pr_imm imm2) ^ "?" in
  Debug.no_1_num caller "subtype_ann"  pr1 string_of_bool (fun _ -> subtype_ann_x imm1 imm2) (imm1,imm2)

(* bool denotes possible subyping *)
(* return true if imm1 <: imm2 *)	
(* M <: I <: L <: A*)
and subtype_ann_x (imm1 : CP.ann) (imm2 : CP.ann) : bool =
  let (r,op) = subtype_ann_pair imm1 imm2 in r
               
(* result: res:bool * (ann constraint = relation between lhs_ann and rhs_ann) *)
and subtype_ann_pair_x (imm1 : CP.ann) (imm2 : CP.ann) : bool * ((CP.exp * CP.exp) option) =
  match imm1 with
    | CP.PolyAnn v1 ->
          (match imm2 with
            | CP.PolyAnn v2 -> (true, Some (CP.Var(v1, no_pos), CP.Var(v2, no_pos)))
            | CP.ConstAnn k2 -> 
                  (true, Some (CP.Var(v1,no_pos), CP.AConst(k2,no_pos)))
	    | CP.TempAnn t2 -> (subtype_ann_pair_x imm1 (CP.ConstAnn(Accs)))
            | CP.TempRes (al,ar) -> (subtype_ann_pair_x imm1 ar)  (* andreeac should it be Accs? *)
          )
    | CP.ConstAnn k1 ->
          (match imm2 with
            | CP.PolyAnn v2 -> (true, Some (CP.AConst(k1,no_pos), CP.Var(v2,no_pos)))
            | CP.ConstAnn k2 -> ((int_of_heap_ann k1)<=(int_of_heap_ann k2),None) 
	    | CP.TempAnn t2 -> (subtype_ann_pair_x imm1 (CP.ConstAnn(Accs)))
            | CP.TempRes (al,ar) -> (subtype_ann_pair_x imm1 ar)  (* andreeac should it be Accs? *)
          ) 
    | CP.TempAnn t1 -> (subtype_ann_pair_x (CP.ConstAnn(Accs)) imm2) 
    | CP.TempRes (l,ar) -> (subtype_ann_pair_x (CP.ConstAnn(Accs)) imm2)  (* andreeac should it be ar-al? or Accs? *)
          
and subtype_ann_pair (imm1 : CP.ann) (imm2 : CP.ann) : bool * ((CP.exp * CP.exp) option) =
  let pr_imm = Cprinter.string_of_imm in
  let pr1 (imm1,imm2) =  (pr_imm imm1) ^ " <: " ^ (pr_imm imm2) ^ "?" in
  let pr_exp = CP.ArithNormalizer.string_of_exp in
  let pr_out = pr_pair string_of_bool (pr_option (pr_pair (add_str "l" pr_exp) (add_str "r" pr_exp)) ) in
  Debug.no_1 "subtype_ann_pair" pr1 pr_out (fun _ -> subtype_ann_pair_x imm1 imm2) (imm1,imm2)

and subtype_ann_gen_x impl_vars evars (imm1 : CP.ann) (imm2 : CP.ann) : bool * (CP.formula list) * (CP.formula list) * (CP.formula list) =
  let (f,op) = subtype_ann_pair imm1 imm2 in
  match op with
    | None -> (f,[],[],[])
    | Some (l,r) -> 
          let to_rhs = CP.BForm ((CP.SubAnn(l,r,no_pos),None), None) in
          (* implicit instantiation of @v made stronger into an equality *)
          (* two examples in ann1.slk fail otherwise; unsound when we have *)
          (* multiple implicit being instantiated ; use explicit if needed *)
          let to_lhs = CP.BForm ((CP.Eq(l,r,no_pos),None), None) in
          (* let to_lhs = CP.BForm ((CP.SubAnn(l,r,no_pos),None), None) in *)
          (* let lhs = c in *)
          begin
            match r with
              | CP.Var(v,_) -> 
                    (* implicit var annotation on rhs *)
                    if CP.mem v impl_vars then (f,[to_lhs],[],[])
                    else if CP.mem v evars then
                            (f,[], [to_rhs], [to_rhs])
                    else (f,[],[to_rhs], [])
              | _ -> (f,[],[to_rhs], [])
          end

and subtype_ann_gen impl_vars evars (imm1 : CP.ann) (imm2 : CP.ann) : bool * (CP.formula list) * (CP.formula list) * (CP.formula list) =
  let pr1 = !CP.print_svl in
  let pr2 = (Cprinter.string_of_imm)  in
  let pr2a = pr_list !CP.print_formula in
  let prlst =  (pr_pair (pr_list Cprinter.string_of_spec_var) (pr_list Cprinter.string_of_spec_var)) in
  let pr3 = pr_quad string_of_bool pr2a pr2a pr2a  in
  Debug.no_4 "subtype_ann_gen" pr1 pr1 pr2 pr2 pr3 subtype_ann_gen_x impl_vars evars (imm1 : CP.ann) (imm2 : CP.ann) 

and mkAndOpt (old_f: CP.formula option) (to_add: CP.formula option): CP.formula option =
  match (old_f, to_add) with
    | (None, None)       -> None
    | (Some f, None)
    | (None, Some f)     -> Some f 
    | (Some f1, Some f2) -> Some (CP.mkAnd f1 f2 no_pos)

(* and mkAnd (old_f: CP.formula list) (to_add: CP.formula list): CP.formula option = *)
(*   match (old_f, to_add) with *)
(*     | ([], [])       -> None *)
(*     | (f::[], []) *)
(*     | ([], f::[])     -> Some f  *)
(*     | (f1::[], f2::[]) -> Some (CP.mkAnd f1 f2 no_pos) *)

and subtype_ann_list impl_vars evars (ann1 : CP.ann list) (ann2 : CP.ann list) : bool * (CP.formula  list) * (CP.formula  list) * (CP.formula  list) =
  match (ann1, ann2) with
    | ([], [])         -> (true, [], [], [])
    | (a1::[], a2::[]) -> 
          let (r, f1, f2, f3) = subtype_ann_gen impl_vars evars a1 a2 in
          (r, f1, f2, f3)
    | (a1::t1, a2::t2) -> 
          let (r, ann_lhs_new, ann_rhs_new, ann_rhs_new_ex) = subtype_ann_gen impl_vars evars a1 a2 in
          let (res, ann_lhs, ann_rhs,  ann_rhs_ex) = subtype_ann_list impl_vars evars t1 t2 in
          (r&&res, ann_lhs_new@ann_lhs, ann_rhs_new@ann_rhs, ann_rhs_new_ex@ann_rhs_ex)
              (* (r&&res, mkAndOpt ann_lhs ann_lhs_new, mkAndOpt ann_rhs ann_rhs_new) *)
    | _ ->      (false, [], [], [])                        (* different lengths *)

and param_ann_equals_node_ann (ann_lst : CP.ann list) (node_ann: CP.ann): bool =
  List.fold_left (fun res x -> res && (CP.eq_ann x node_ann)) true ann_lst

(* and remaining_ann_x (ann_l: ann) (ann_r: ann) impl_vars evars(\* : ann *\) = *)
(*   match ann_r with *)
(*     | CP.ConstAnn(Mutable) *)
(*     | CP.ConstAnn(Imm)     -> ((CP.ConstAnn(Accs)), [],([],[],[])) *)
(*     | CP.ConstAnn(Lend)    -> (CP.TempAnn(ann_l), [],([],[],[])) *)
(*     | CP.TempAnn _ *)
(*     | CP.TempRes _   *)
(*     | CP.ConstAnn(Accs)    -> (ann_l, [],([],[],[])) *)
(*     | CP.PolyAnn(_)        -> *)
(*           (\* must check ann_l (probl cases: @M,@I,@v), decide between retruning a Accs or CP.TempRes*\) *)
(*           match ann_l with *)
(*               (\*must check ann_l (probl cases: @M,@I,@v), decide between returning Accs or TempCons*\) *)
(*             | CP.ConstAnn(Mutable) *)
(*             | CP.ConstAnn(Imm) *)
(*             | CP.PolyAnn(_) ->  *)
(*                   let (new_ann,_), fv, (to_lhs, to_rhs, to_rhs_ex) = mkCP.TempRes ann_l ann_r impl_vars evars in *)
(*                   (new_ann,fv, (to_lhs, to_rhs, to_rhs_ex)) *)
(*                   (\* CP.TempRes(ann_l, ann_r) *\) *)
(*             | _          -> (ann_l, [],([],[],[])) *)

(* and remaining_ann (ann_l: ann) (ann_r: ann) impl_vars evars(\* : ann  *\)= *)
(*   let pr = Cprinter.string_of_imm in *)
(*   let pr_out  = pr_triple  pr pr_none pr_none in *)
(*   Debug.no_2 "remaining_ann" pr pr pr_out (fun _ _-> remaining_ann_x ann_l ann_r impl_vars evars) ann_l ann_r *)

and remaining_ann_x (ann_l: CP.ann) (ann_r: CP.ann) impl_vars evars(* : ann *) =
  match ann_l with
    | CP.TempAnn ann -> ann
    | _ -> ann_l

and remaining_ann (ann_l: CP.ann) (ann_r: CP.ann) impl_vars evars(* : ann  *)=
  let pr = Cprinter.string_of_imm in
  let pr_out  = pr_triple  pr pr_none pr_none in
  Debug.no_2 "remaining_ann" pr pr pr (fun _ _-> remaining_ann_x ann_l ann_r impl_vars evars) ann_l ann_r

(* residue * consumed *)
and subtract_ann (ann_l: CP.ann) (ann_r: CP.ann)  impl_vars expl_vars evars norm (* : ann *) =
  match ann_r with
    | CP.ConstAnn(Mutable)
    | CP.ConstAnn(Imm)     -> ((CP.ConstAnn(Accs), ann_r), [],(([],[],[]),[]))
    | CP.ConstAnn(Lend)    -> ((CP.TempAnn(ann_l), CP.ConstAnn(Accs)), [],(([],[],[]),[]))
    | CP.TempAnn _
    | CP.TempRes _  
    | CP.ConstAnn(Accs)    -> ((ann_l, CP.ConstAnn(Accs)), [],(([],[],[]),[]))
    | CP.PolyAnn(_)        ->
          match ann_l with
            | CP.ConstAnn(Mutable)
            | CP.ConstAnn(Imm)
            | CP.PolyAnn(_) -> 
                  if norm then 
                    let (res_ann,cons_ann), fv, ((to_lhs, to_rhs, to_rhs_ex),subst) = mkTempRes ann_l ann_r  impl_vars expl_vars evars in
                    ((res_ann, cons_ann),fv, ((to_lhs, to_rhs, to_rhs_ex),subst))
                  else  ((CP.TempRes(ann_l, ann_r), ann_r), [], (([],[],[]),[]))
                  (* TempRes(ann_l, ann_r) *)
            | _          -> ((ann_l, CP.ConstAnn(Accs)), [],(([],[],[]),[]))


(* during matching - for residue*)
and replace_list_ann_x (ann_lst_l: CP.ann list) (ann_lst_r: CP.ann list) es =
  let impl_vars = es.es_gen_impl_vars in
  let expl_vars = es.es_gen_expl_vars in
  let evars     = es.es_evars in
  let n_ann_lst, niv, constr = List.fold_left (fun ((res_ann_acc,cons_ann_acc), n_iv, ((to_lhsl, to_rhsl, to_rhs_exl),substl)) (ann_l,ann_r) -> 
      let (resid_ann, cons_ann), niv, ((to_lhs, to_rhs, to_rhs_ex),subst) = subtract_ann ann_l ann_r impl_vars expl_vars evars true in 
      ((res_ann_acc@[resid_ann], cons_ann_acc@[cons_ann]), niv@n_iv, ((to_lhs@to_lhsl, to_rhs@to_rhsl, to_rhs_ex@to_rhs_exl),subst@substl))
  ) (([],[]), [], (([],[],[]),[])) (List.combine ann_lst_l ann_lst_r ) in
  n_ann_lst, niv, constr 

and replace_list_ann (ann_lst_l: CP.ann list) (ann_lst_r: CP.ann list) es =
  let pr lst = "[" ^ (List.fold_left (fun y x-> (Cprinter.string_of_imm x) ^ ", " ^ y) "" lst) ^ "]; " in
  let pr_p =  pr_pair pr pr in 
  let pr_out = pr_triple pr_p pr_none pr_none in
  Debug.no_2 "replace_list_ann" pr pr pr_out (fun _ _-> replace_list_ann_x ann_lst_l ann_lst_r es) ann_lst_l ann_lst_r

and replace_list_ann_mem (ann_lst_l: CP.ann list) (ann_lst_r: CP.ann list) impl_vars expl_vars evars =
  let n_ann_lst, niv, constr = List.fold_left (fun ((res_ann_acc,cons_ann_acc), n_iv, (to_lhsl, to_rhsl, to_rhs_exl)) (ann_l,ann_r) -> 
      let (resid_ann, cons_ann), niv, ((to_lhs, to_rhs, to_rhs_ex),_) = subtract_ann ann_l ann_r impl_vars expl_vars evars true in 
      ((res_ann_acc@[resid_ann], cons_ann_acc@[cons_ann]), niv@n_iv, (to_lhs@to_lhsl, to_rhs@to_rhsl, to_rhs_ex@to_rhs_exl))
  ) (([],[]), [], ([],[],[])) (List.combine ann_lst_l ann_lst_r ) in
  n_ann_lst, niv, constr 

and consumed_ann (ann_l: CP.ann) (ann_r: CP.ann): CP.ann = 
  match ann_r with
    | CP.ConstAnn(Accs)    
    | CP.TempAnn _
    | CP.TempRes _
    | CP.ConstAnn(Lend)    -> (CP.ConstAnn(Accs)) 
    | CP.PolyAnn(_)        (* -> *)
            (* match ann_l with *)
            (*     (\*must check ann_l (probl cases: @M,@I,@v), decide between returning Accs or TempCons*\) *)
            (*   | CP.ConstAnn(Mutable) *)
            (*   | CP.ConstAnn(Imm) *)
            (*   | CP.PolyAnn() -> TempCons(ann_l) *)
            (*   | _         -> CP.ConstAnn(Accs) *)
    | CP.ConstAnn(Mutable) 
    | CP.ConstAnn(Imm)     -> ann_r


(* during matching *)
and consumed_list_ann_x (ann_lst_l: CP.ann list) (ann_lst_r: CP.ann list): CP.ann list =
  match (ann_lst_l, ann_lst_r) with
    | ([], []) -> []
    | (ann_l :: tl, ann_r :: tr ) -> (consumed_ann ann_l ann_r):: (consumed_list_ann_x tl tr)
    | (_, _) -> ann_lst_l (* report_error no_pos ("[immutable.ml] : nodes should have same no. of fields \n") *)

and consumed_list_ann (ann_lst_l: CP.ann list) (ann_lst_r: CP.ann list): CP.ann list =
  let pr lst = "[" ^ (List.fold_left (fun y x-> (Cprinter.string_of_imm x) ^ ", " ^ y) "" lst) ^ "]; " in
  Debug.no_2 "consumed_list_ann" pr pr pr (fun _ _-> consumed_list_ann_x ann_lst_l ann_lst_r) ann_lst_l ann_lst_r


and merge_ann_formula_list_x(conjs: CP.formula list): heap_ann option = 
  (* form a list with the constants on the lhs of "var=AConst.." formulae *)
  let rec helper conjs =
    match conjs with
      | []    -> []
      | x::xs -> 
            let acst = CP.get_aconst x in
            match acst with
              | Some ann -> ann::(helper xs)
              | None     -> helper xs
  in
  let anns = helper conjs in
  let ann = 
    (* merge the set of annotations anns as follows: 
       if all the annotations in the set are the same, eg. equal to ann0, 
       return Some ann0, otherwise return None *)
    match anns with
      | []     -> None
      | x::xs  -> List.fold_left (fun a1_opt a2 -> 
            match a1_opt with
              | Some a1 -> if not(CP.is_diff (CP.AConst(a1,no_pos)) (CP.AConst(a2,no_pos))) then Some a1 else None
              | None    -> None ) (Some x) xs
  in
  ann

and merge_ann_formula_list(conjs: CP.formula list): heap_ann option = 
  let pr1 = pr_list Cprinter.string_of_pure_formula in
  let pr_out = pr_opt string_of_heap_ann in
  Debug.no_1 "merge_ann_formula_list" pr1 pr_out merge_ann_formula_list_x conjs

and collect_ann_info_from_formula_x (a: CP.ann) (conjs: CP.formula list) (pure: CP.formula): heap_ann option =
  let lst = 
    match a with
      | CP.PolyAnn sv -> CP.find_closure_pure_formula sv pure 
      | _ -> []
  in
  Debug.tinfo_hprint (add_str "conjs bef:" (pr_list Cprinter.string_of_pure_formula)) conjs no_pos;
  (* keep only Eq formulae of form var = AConst, where var is in lst *)
  let conjs = List.filter (fun f -> 
      (CP.is_eq_with_aconst f) && not(CP.disjoint (CP.fv f) lst )) conjs in
 Debug.tinfo_hprint (add_str "conjs:" (pr_list Cprinter.string_of_pure_formula)) conjs no_pos;
  let ann = merge_ann_formula_list conjs in
  ann

and collect_ann_info_from_formula (a: CP.ann) (conjs: CP.formula list) (pure: CP.formula): heap_ann option =
  
  Debug.no_3 "collect_ann_info_from_formula" 
      Cprinter.string_of_imm 
      (pr_list Cprinter.string_of_pure_formula)
      Cprinter.string_of_pure_formula
      (pr_opt string_of_heap_ann)
      collect_ann_info_from_formula_x a conjs pure 

(* restore ann for residue * consumed *)
and restore_tmp_res_ann_x (annl: CP.ann) (annr: CP.ann) (pure0: MCP.mix_formula) impl_vars evars: CP.ann =
    let pure = MCP.pure_of_mix pure0 in
    (* let pairs = CP.pure_ptr_equations pure in *)
    Debug.tinfo_hprint (add_str "pure:" (Cprinter.string_of_pure_formula)) pure no_pos;
    (* Debug.tinfo_hprint (add_str "pairs:" (pr_list (pr_pair Cprinter.string_of_spec_var Cprinter.string_of_spec_var))) pairs no_pos; *)
    let conjs = CP.split_conjunctions pure in
    Debug.tinfo_hprint (add_str "conjs:" (pr_list Cprinter.string_of_pure_formula)) conjs no_pos;
    let ann_r0 = collect_ann_info_from_formula annr conjs pure in
    let ann_l0 = collect_ann_info_from_formula annl conjs pure in
    Debug.tinfo_hprint (add_str "annr:" (pr_opt string_of_heap_ann)) ann_r0 no_pos;
    Debug.tinfo_hprint (add_str "annl:" (pr_opt string_of_heap_ann)) ann_l0 no_pos;
    let ann_subst ann def_ann = match ann with
      | Some a -> CP.ConstAnn(a)
      | None   -> def_ann in
    let annl = ann_subst ann_l0 annl in
    let annr = ann_subst ann_r0 annr in
    let res = remaining_ann annl annr impl_vars evars in
    res

and restore_tmp_res_ann (annl: CP.ann) (annr: CP.ann) (pure0: MCP.mix_formula) impl_vars evars: CP.ann =
  let pr = Cprinter.string_of_imm in
  Debug.no_3 "restore_tmp_res_ann" pr pr Cprinter.string_of_mix_formula pr (fun _ _ _ -> restore_tmp_res_ann_x annl annr pure0 impl_vars evars) annl annr pure0 

and remaining_ann_new_x (annl: CP.ann) emap: CP.ann=
  let elem_const = (CP.mk_sv_aconst Mutable)::(CP.mk_sv_aconst Imm)::(CP.mk_sv_aconst Lend)::[(CP.mk_sv_aconst Accs)] in
  let anns =  (CP.ConstAnn(Mutable))::(CP.ConstAnn(Imm))::(CP.ConstAnn(Lend))::[(CP.ConstAnn(Accs))] in
  let anns = List.combine elem_const anns in
  let getAnn aconst = snd (List.find (fun (a,_) -> CP.eq_spec_var a aconst)  anns) in    
  let normalize_imm ann = 
    match (CP.imm_to_sv ann) with
      | Some v -> 
            begin
              let elst  =  CP.EMapSV.find_equiv_all v emap in
              let const =  Gen.BList.intersect_eq CP.eq_spec_var elst elem_const in
              match const with
                | []    -> ann
                | h::[] -> getAnn h 
                | _     -> failwith "an imm ann cannot be assigned to 2 different values (imm)"
            end
      | _ -> ann                        (* should never reach this branch *)
  in
  let res = match annl with
    | CP.TempAnn ann -> normalize_imm ann
    | CP.TempRes (ann_l,ann_r) -> (* ann_l *)
          let ann_l = normalize_imm ann_l in
          let ann_r = normalize_imm ann_r in
          let (res,_),_,_ = subtract_ann ann_l ann_r [] [] [] false in
          res
    | CP.PolyAnn ann -> normalize_imm annl 
    | _ -> annl in
  res

and remaining_ann_new (ann_l: CP.ann) emap(* : ann  *)=
  let pr = Cprinter.string_of_imm in
  let pr_out  = pr_triple  pr pr_none pr_none in
  Debug.no_1 "remaining_ann" pr pr (fun _-> remaining_ann_new_x ann_l emap) ann_l

(* restore ann for residue * consumed *)
and restore_tmp_res_ann_new_x (annl: CP.ann) (pure0: MCP.mix_formula): CP.ann =
  let pure = MCP.pure_of_mix pure0 in
  let emap = build_eset_of_conj_formula pure in 
  let res = remaining_ann_new annl emap  in
  res 


and restore_tmp_res_ann_new (annl: CP.ann)(pure0: MCP.mix_formula): CP.ann =
  let pr = Cprinter.string_of_imm in
  Debug.no_2 "restore_tmp_res_ann" pr  Cprinter.string_of_mix_formula pr (fun _ _ -> restore_tmp_res_ann_new_x annl pure0 ) annl  pure0 

and restore_tmp_ann_x (ann_lst: CP.ann list) (pure0: MCP.mix_formula): CP.ann list =
  match ann_lst with
    | [] -> []
    | ann_l::tl ->
          let ann_l = restore_tmp_res_ann_new ann_l pure0 in
          ann_l :: (restore_tmp_ann_x tl pure0)

and restore_tmp_ann (ann_lst: CP.ann list) (pure0: MCP.mix_formula): CP.ann list =
  let pr = pr_list Cprinter.string_of_imm in 
  Debug.no_2 "restore_tmp_ann" pr  (Cprinter.string_of_mix_formula) pr restore_tmp_ann_x ann_lst pure0

and restore_tmp_ann_x_old (ann_lst: CP.ann list) (pure0: MCP.mix_formula): CP.ann list =
  match ann_lst with
    | [] -> []
    | ann_l::tl ->
          begin
	    match ann_l with 
	      | CP.TempAnn(t)     -> 
                    let ann_l = restore_tmp_res_ann t (CP.ConstAnn(Accs))(* t *) pure0 [] [] in
                    ann_l :: (restore_tmp_ann_x tl pure0)
              | CP.TempRes(al,ar) ->  
                    (* Debug.tinfo_hprint (add_str "CP.TempRes:" (Cprinter.string_of_imm)) ann_l no_pos; *)
                    (* Debug.tinfo_hprint (add_str "pure0:" (Cprinter.string_of_mix_formula)) pure0 no_pos; *)
                    (* let ann_l = restore_tmp_res_ann al ar pure0 [] [] in *)
                    ann_l :: (restore_tmp_ann_x tl pure0)
	      | _        -> ann_l :: (restore_tmp_ann_x tl pure0)
          end

and restore_tmp_ann_old (ann_lst: CP.ann list) (pure0: MCP.mix_formula): CP.ann list =
  let pr = pr_list Cprinter.string_of_imm in 
  Debug.no_2 "restore_tmp_ann" pr  (Cprinter.string_of_mix_formula) pr restore_tmp_ann_x ann_lst pure0

(* and update_field_ann (f : h_formula) (pimm1 : ann list) (pimm : ann list)  impl_vars evars: h_formula =  *)
(*   let pr lst = "[" ^ (List.fold_left (fun y x-> (Cprinter.string_of_imm x) ^ ", " ^ y) "" lst) ^ "]; " in *)
(*   Debug.no_3 "update_field_ann" (Cprinter.string_of_h_formula) pr pr  (Cprinter.string_of_h_formula) (fun _ _ _-> update_field_ann_x f pimm1 pimm impl_vars evars) f pimm1 pimm *)

(* and update_field_ann_x (f : h_formula) (pimm1 : ann list) (pimm : ann list) impl_vars evars: h_formula =  *)
(*   let new_field_ann_lnode = replace_list_ann pimm1 pimm impl_vars evars in *)
(*   (\* asankhs: If node has all field annotations as @A make it HEmp *\) *)
(*   if (isAccsList new_field_ann_lnode) then HEmp else (\*andreea temporarily allow nodes only with @A fields*\) *)
(*   let updated_f = match f with  *)
(*     | DataNode d -> DataNode ( {d with h_formula_data_param_imm = new_field_ann_lnode} ) *)
(*     | _          -> report_error no_pos ("[context.ml] : only data node should allow field annotations \n") *)
(*   in *)
(*   updated_f *)

(* and update_ann (f : h_formula) (ann_l: ann) (ann_r: ann) impl_vars evars: h_formula =  *)
(*   let pr = Cprinter.string_of_imm in *)
(*   Debug.no_3 "update_ann" (Cprinter.string_of_h_formula) pr pr  (Cprinter.string_of_h_formula) (fun _ _ _-> update_ann_x f ann_l ann_r impl_vars evars) f ann_l ann_r *)

(* and update_ann_x (f : h_formula) (ann_l: ann) (ann_r: ann) impl_vars evars : h_formula =  *)
(*   let new_ann_lnode = remaining_ann ann_l ann_r impl_vars evars in *)
(*   (\* asankhs: If node has all field annotations as @A make it HEmp *\) *)
(*   if (isAccs new_ann_lnode) then HEmp else  *)
(*   let updated_f = match f with  *)
(*     | DataNode d -> DataNode ( {d with h_formula_data_imm = new_ann_lnode} ) *)
(*     | ViewNode v -> ViewNode ( {v with h_formula_view_imm = new_ann_lnode} ) *)
(*     | _          -> report_error no_pos ("[context.ml] : only data node or view node should allow annotations \n") *)
(*   in *)
(*   updated_f *)

(* utilities for handling lhs heap state continuation *)
and push_cont_ctx (cont : h_formula) (ctx : Cformula.context) : Cformula.context =
  match ctx with
    | Ctx(es) -> Ctx(push_cont_es cont es)
    | OCtx(c1, c2) ->
	  OCtx(push_cont_ctx cont c1, push_cont_ctx cont c2)

and push_cont_es (cont : h_formula) (es : entail_state) : entail_state =  
  {  es with
      es_cont = cont::es.es_cont;
  }

and pop_cont_es (es : entail_state) : (h_formula * entail_state) =  
  let cont = es.es_cont in
  let crt_cont, cont =
    match cont with
      | h::r -> (h, r)
      | [] -> (HEmp, [])
  in
  (crt_cont, 
  {  es with
      es_cont = cont;
  })

(* utilities for handling lhs holes *)
(* push *)
and push_crt_holes_list_ctx (ctx : list_context) (holes : (h_formula * int) list) : list_context = 
  let pr1 = Cprinter.string_of_list_context in
  let pr2 = pr_no (* pr_list (pr_pair string_of_h_formula string_of_int ) *) in
  Debug.no_2 "push_crt_holes_list_ctx" pr1 pr2 pr1 (fun _ _-> push_crt_holes_list_ctx_x ctx holes) ctx holes
      
and push_crt_holes_list_ctx_x (ctx : list_context) (holes : (h_formula * int) list) : list_context = 
  match ctx with
    | FailCtx _ -> ctx
    | SuccCtx(cl) ->
	  SuccCtx(List.map (fun x -> push_crt_holes_ctx x holes) cl)

and push_crt_holes_ctx (ctx : context) (holes : (h_formula * int) list) : context = 
  match ctx with
    | Ctx(es) -> Ctx(push_crt_holes_es es holes)
    | OCtx(c1, c2) ->
	  let nc1 = push_crt_holes_ctx c1 holes in
	  let nc2 = push_crt_holes_ctx c2 holes in
	  OCtx(nc1, nc2)

and push_crt_holes_es (es : Cformula.entail_state) (holes : (h_formula * int) list) : Cformula.entail_state =
  {
      es with
          es_crt_holes = holes @ es.es_crt_holes; 
  }
      
and push_holes (es : Cformula.entail_state) : Cformula.entail_state = 
  {  es with
      es_hole_stk   = es.es_crt_holes::es.es_hole_stk;
      es_crt_holes = [];
  }

(* pop *)

and pop_holes_es (es : Cformula.entail_state) : Cformula.entail_state = 
  match es.es_hole_stk with
    | [] -> es
    | c2::stk -> {  es with
	  es_hole_stk = stk;
	  es_crt_holes = es.es_crt_holes @ c2;
      }

(* restore temporarily removed annotations *)
and restore_tmp_ann_list_ctx (ctx : list_context) : list_context = 
  match ctx with
    | FailCtx _ -> ctx
    | SuccCtx(cl) ->
	  SuccCtx(List.map restore_tmp_ann_ctx cl)

and restore_tmp_ann_ctx (ctx : context) : context = 
  if (!Globals.allow_imm) || (!Globals.allow_field_ann) then
    let rec helper ctx = 
      match ctx with
        | Ctx(es) -> Ctx(restore_tmp_ann_es es)
        | OCtx(c1, c2) ->
	      let nc1 = helper c1 in
	      let nc2 = helper c2 in
	      OCtx(nc1, nc2)
    in helper ctx
  else ctx

and restore_tmp_ann_h_formula (f: h_formula) pure0: h_formula =
  match f with
    | CF.Star h  -> CF.Star {h with h_formula_star_h1 = restore_tmp_ann_h_formula h.CF.h_formula_star_h1 pure0; 
	  h_formula_star_h2 = restore_tmp_ann_h_formula h.CF.h_formula_star_h2 pure0;}
    | CF.Conj h  -> CF.Conj {h with h_formula_conj_h1 = restore_tmp_ann_h_formula h.CF.h_formula_conj_h1 pure0; 
	  h_formula_conj_h2 = restore_tmp_ann_h_formula h.CF.h_formula_conj_h2 pure0;}
    | CF.ConjStar h  -> CF.ConjStar {h with h_formula_conjstar_h1 = restore_tmp_ann_h_formula h.CF.h_formula_conjstar_h1 pure0; 
	  h_formula_conjstar_h2 = restore_tmp_ann_h_formula h.CF.h_formula_conjstar_h2 pure0;}
    | CF.ConjConj h  -> CF.ConjConj {h with h_formula_conjconj_h1 = restore_tmp_ann_h_formula h.CF.h_formula_conjconj_h1 pure0; 
	  h_formula_conjconj_h2 = restore_tmp_ann_h_formula h.CF.h_formula_conjconj_h2 pure0; }
    | CF.Phase h -> CF.Phase  {h with h_formula_phase_rd = restore_tmp_ann_h_formula h.CF.h_formula_phase_rd pure0; 
	  h_formula_phase_rw = restore_tmp_ann_h_formula h.CF.h_formula_phase_rw pure0;}
    | CF.DataNode h -> 
          let new_f = 
            CF.DataNode {h with h_formula_data_param_imm = restore_tmp_ann h.CF.h_formula_data_param_imm pure0;
                h_formula_data_imm = List.hd (restore_tmp_ann [h.CF.h_formula_data_imm] pure0);
            } in
          let new_f = maybe_replace_w_empty new_f in
          new_f
    | CF.ViewNode h -> 
          let f args = restore_tmp_ann args pure0 in
          let new_pimm = apply_f_to_annot_arg f h.CF.h_formula_view_annot_arg in 
          CF.ViewNode {h with h_formula_view_imm = List.hd (restore_tmp_ann [h.CF.h_formula_view_imm] pure0);
              h_formula_view_annot_arg = new_pimm }
    | _          -> f

and restore_tmp_ann_formula (f: formula): formula =
  match f with
    | Base(bf) -> Base{bf with formula_base_heap = restore_tmp_ann_h_formula bf.formula_base_heap  bf.formula_base_pure;}
    | Exists(ef) -> Exists{ef with formula_exists_heap = restore_tmp_ann_h_formula ef.formula_exists_heap  ef.formula_exists_pure;}
    | Or(orf) -> Or {orf with formula_or_f1 = restore_tmp_ann_formula orf.formula_or_f1; 
          formula_or_f2 = restore_tmp_ann_formula orf.formula_or_f2;}

and restore_tmp_ann_es (es : Cformula.entail_state) : Cformula.entail_state = 
  (* subs away current hole list *)
  {  es with
      es_formula = restore_tmp_ann_formula es.es_formula;
  }

(* substitute *)
and subs_crt_holes_list_ctx (ctx : list_context) : list_context = 
  match ctx with
    | FailCtx _ -> ctx
    | SuccCtx(cl) ->
	  SuccCtx(List.map subs_crt_holes_ctx cl)

and subs_crt_holes_ctx (ctx : context) : context = 
  match ctx with
    | Ctx(es) -> Ctx(subs_holes_es es)
    | OCtx(c1, c2) ->
	  let nc1 = subs_crt_holes_ctx c1 in
	  let nc2 = subs_crt_holes_ctx c2 in
	  OCtx(nc1, nc2)

and subs_holes_es (es : Cformula.entail_state) : Cformula.entail_state = 
  (* subs away current hole list *)
  {  es with
      es_crt_holes   = [];
      es_formula = apply_subs es.es_crt_holes es.es_formula;
  }

and apply_subs (crt_holes : (h_formula * int) list) (f : formula) : formula =
  match f with
    | Base(bf) ->
	  Base{bf with formula_base_heap = apply_subs_h_formula crt_holes bf.formula_base_heap;}
    | Exists(ef) ->
	  Exists{ef with formula_exists_heap = apply_subs_h_formula crt_holes ef.formula_exists_heap;}
    | Or({formula_or_f1 = f1;
      formula_or_f2 = f2;
      formula_or_pos = pos}) ->
	  let sf1 = apply_subs crt_holes f1 in
	  let sf2 = apply_subs crt_holes f2 in
	  mkOr sf1  sf2 pos

and apply_subs_h_formula crt_holes (h : h_formula) : h_formula = 
  let rec helper (i : int) crt_holes : h_formula = 
    (match crt_holes with
      | (h1, i1) :: rest -> 
	    if i==i1 then h1
	    else helper i rest
      | [] -> Hole(i))
  in
  match h with
    | Hole(i) -> helper i crt_holes
    | Star({h_formula_star_h1 = h1;
      h_formula_star_h2 = h2;
      h_formula_star_pos = pos}) ->
	  let nh1 = apply_subs_h_formula crt_holes h1 in
	  let nh2 = apply_subs_h_formula crt_holes h2 in
	  Star({h_formula_star_h1 = nh1;
	  h_formula_star_h2 = nh2;
	  h_formula_star_pos = pos})
    | Conj({h_formula_conj_h1 = h1;
      h_formula_conj_h2 = h2;
      h_formula_conj_pos = pos}) ->
	  let nh1 = apply_subs_h_formula crt_holes h1 in
	  let nh2 = apply_subs_h_formula crt_holes h2 in
	  Conj({h_formula_conj_h1 = nh1;
	  h_formula_conj_h2 = nh2;
	  h_formula_conj_pos = pos})
    | ConjStar({h_formula_conjstar_h1 = h1;
      h_formula_conjstar_h2 = h2;
      h_formula_conjstar_pos = pos}) ->
	  let nh1 = apply_subs_h_formula crt_holes h1 in
	  let nh2 = apply_subs_h_formula crt_holes h2 in
	  ConjStar({h_formula_conjstar_h1 = nh1;
	  h_formula_conjstar_h2 = nh2;
	  h_formula_conjstar_pos = pos})
    | ConjConj({h_formula_conjconj_h1 = h1;
      h_formula_conjconj_h2 = h2;
      h_formula_conjconj_pos = pos}) ->
	  let nh1 = apply_subs_h_formula crt_holes h1 in
	  let nh2 = apply_subs_h_formula crt_holes h2 in
	  ConjConj({h_formula_conjconj_h1 = nh1;
	  h_formula_conjconj_h2 = nh2;
	  h_formula_conjconj_pos = pos})	      	      
    | Phase({h_formula_phase_rd = h1;
      h_formula_phase_rw = h2;
      h_formula_phase_pos = pos}) ->
	  let nh1 = apply_subs_h_formula crt_holes h1 in
	  let nh2 = apply_subs_h_formula crt_holes h2 in
	  Phase({h_formula_phase_rd = nh1;
	  h_formula_phase_rw = nh2;
	  h_formula_phase_pos = pos})
    | _ -> h



and get_imm (f : h_formula) : CP.ann =  match f with
  | DataNode (h1) -> h1.h_formula_data_imm
  | ViewNode (h1) -> h1.h_formula_view_imm
  | _ -> CP.ConstAnn(Mutable) (* we shouldn't get here *)


(* muatble or immutable annotations on the RHS consume the match on the LHS  *)
and consumes (a: CP.ann): bool = 
  if isMutable a || isImm a then true
  else false



and compute_ann_list all_fields (diff_fields : ident list) (default_ann : CP.ann) : CP.ann list =
  let pr1 ls =
    let helper i = match i with
    | ((_,h), _, _, _) -> h
    in
    List.fold_left (fun res id -> res ^ ", " ^ (helper id)) "" ls in
  let pr2 ls = List.fold_left (fun res id -> res ^ ", " ^ id ) "" ls in
  let pr_out ls = List.fold_left (fun res id ->  res ^ ", " ^ (Cprinter.string_of_imm id) ) "" ls in
  Debug.no_3 "compute_ann_list" pr1 pr2 (Cprinter.string_of_imm) pr_out
  (fun _ _ _ -> compute_ann_list_x all_fields diff_fields default_ann ) all_fields diff_fields default_ann

and compute_ann_list_x all_fields (diff_fields : ident list) (default_ann : CP.ann) : CP.ann list =
  match all_fields with
    | ((_,h),_,_,_) :: r ->
      if (List.mem h diff_fields) then default_ann :: (compute_ann_list_x r diff_fields default_ann)
      else let ann = if(!Globals.allow_field_ann) then (CP.ConstAnn(Accs)) else default_ann in ann:: (compute_ann_list_x r diff_fields default_ann)
    | [] -> []
;; 

let rec normalize_h_formula_dn auxf (h : CF.h_formula) : CF.h_formula * (CP.formula list) * ((Globals.ident * Globals.primed) list) = 
  match h with
    | CF.Star({CF.h_formula_star_h1 = h1;
      CF.h_formula_star_h2 = h2;
      CF.h_formula_star_pos = pos}) ->
	  let nh1, lc1, nv1 = normalize_h_formula_dn auxf h1 in
	  let nh2, lc2, nv2 = normalize_h_formula_dn auxf h2 in
	  let h = CF.Star({CF.h_formula_star_h1 = nh1;
	  CF.h_formula_star_h2 = nh2;
	  CF.h_formula_star_pos = pos}) in
          (h, lc1@lc2, nv1@nv2)
    | CF.Conj({CF.h_formula_conj_h1 = h1;
      CF.h_formula_conj_h2 = h2;
      CF.h_formula_conj_pos = pos}) ->
	  let nh1, lc1, nv1 = normalize_h_formula_dn auxf h1 in
	  let nh2, lc2, nv2 = normalize_h_formula_dn auxf h2 in
	  let h = CF.Conj({CF.h_formula_conj_h1 = nh1;
	  CF.h_formula_conj_h2 = nh2;
	  CF.h_formula_conj_pos = pos}) in
          (h, lc1@lc2, nv1@nv2)
    | CF.ConjStar({CF.h_formula_conjstar_h1 = h1;
      CF.h_formula_conjstar_h2 = h2;
      CF.h_formula_conjstar_pos = pos}) ->
	  let nh1, lc1, nv1 = normalize_h_formula_dn auxf h1 in
	  let nh2, lc2, nv2 = normalize_h_formula_dn auxf h2 in
	  let h = CF.ConjStar({CF.h_formula_conjstar_h1 = nh1;
	  CF.h_formula_conjstar_h2 = nh2;
	  CF.h_formula_conjstar_pos = pos}) in
          (h, lc1@lc2, nv1@nv2)
    | CF.ConjConj({CF.h_formula_conjconj_h1 = h1;
      CF.h_formula_conjconj_h2 = h2;
      CF.h_formula_conjconj_pos = pos}) ->
	  let nh1, lc1, nv1 = normalize_h_formula_dn auxf h1 in
	  let nh2, lc2, nv2 = normalize_h_formula_dn auxf h2 in
	  let h = CF.ConjConj({CF.h_formula_conjconj_h1 = nh1;
	  CF.h_formula_conjconj_h2 = nh2;
	  CF.h_formula_conjconj_pos = pos}) in
          (h, lc1@lc2, nv1@nv2)
    | CF.Phase({CF.h_formula_phase_rd = h1;
      CF.h_formula_phase_rw = h2;
      CF.h_formula_phase_pos = pos}) ->
	  let nh1,lc1,nv1 = normalize_h_formula_dn auxf h1 in
	  let nh2,lc2,nv2 = normalize_h_formula_dn auxf h2 in
	  let h = CF.Phase({CF.h_formula_phase_rd = nh1;
	  CF.h_formula_phase_rw = nh2;
	  CF.h_formula_phase_pos = pos}) in 
          (h, lc1@lc2, nv1@nv2)
    | CF.DataNode hn -> auxf h 
    | _ -> (h,[],[])

let rec normalize_formula_dn aux_f (f : formula): formula = match f with
  | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) ->
	let rf1 = normalize_formula_dn aux_f f1 in
	let rf2 = normalize_formula_dn aux_f f2 in
	let resform = mkOr rf1 rf2 pos in
	resform
  | Base f1 ->
        let f1_heap, f1_constr, nv = normalize_h_formula_dn aux_f f1.formula_base_heap in
        Base({f1 with formula_base_heap = f1_heap})
  | Exists f1 ->
        let f1_heap, f1_constr, nv = normalize_h_formula_dn aux_f f1.formula_exists_heap in
        Exists({f1 with formula_exists_heap = f1_heap})

let merge_imm_ann ann1 ann2 = 
  match ann1, ann2 with
    | CP.ConstAnn(Mutable), ann
    | ann, CP.ConstAnn(Mutable) -> (ann, [], [])
    | CP.ConstAnn(Accs), _
    | _, CP.ConstAnn(Accs)    -> (CP.ConstAnn(Accs), [], [])
    | CP.PolyAnn sv, ann
    | ann, CP.PolyAnn sv   -> 
          let fresh_v = "ann_" ^ (fresh_name ()) in
          let fresh_sv = (CP.SpecVar(AnnT, fresh_v, Unprimed)) in
          let fresh_var = CP.Var(fresh_sv, no_pos) in
          let poly_ann = CP.mkPolyAnn fresh_sv in
          let constr1 = CP.mkSubAnn (CP.mkExpAnnSymb ann no_pos) fresh_var in
          let constr2 = CP.mkSubAnn (CP.Var(sv, no_pos)) fresh_var in
          (poly_ann, constr1::[constr2], [(fresh_v, Unprimed)])
    | ann_n, _ -> let ann = if (subtype_ann 2  ann_n  ann2 ) then ann2 else  ann1 in
      (ann, [], [])

let push_node_imm_to_field_imm_x (h: CF.h_formula):  CF.h_formula  * (CP.formula list) * ((Globals.ident * Globals.primed) list) =
  match h with
    | CF.DataNode dn -> 
          let ann_node = dn.CF.h_formula_data_imm in
          let new_ann_param, constr, new_vars = List.fold_left (fun (params, constr, vars) p_ann ->
              let new_p_ann,nc,nv = merge_imm_ann ann_node p_ann in
              (params@[new_p_ann], nc@constr, nv@vars)
          ) ([],[],[]) dn.CF.h_formula_data_param_imm in  
          let new_ann_node =  if (List.length  dn.CF.h_formula_data_param_imm > 0) then CP.ConstAnn(Mutable) else ann_node in
          let n_dn = CF.DataNode{dn with  CF.h_formula_data_imm = new_ann_node;
 	      CF.h_formula_data_param_imm = new_ann_param;} in
          (n_dn, constr, new_vars)
    | _ -> (h, [], [])

let push_node_imm_to_field_imm caller (h:CF.h_formula) : CF.h_formula * (CP.formula list) * ((Globals.ident * Globals.primed) list) =
  let pr = Cprinter.string_of_h_formula in
  let pr_out = pr_triple Cprinter.string_of_h_formula pr_none pr_none in
  Debug.no_1_num caller "push_node_imm_to_field_imm" pr pr_out push_node_imm_to_field_imm_x h 

let normalize_field_ann_heap_node_x (h:CF.h_formula): CF.h_formula  * (CP.formula list) * ((Globals.ident * Globals.primed) list) =
  if (!Globals.allow_field_ann) then
  (* if false then *)
    let h, constr, new_vars = normalize_h_formula_dn (push_node_imm_to_field_imm 1) h in
    (h,constr,new_vars)
  else (h,[],[])

let normalize_field_ann_heap_node (h:CF.h_formula): CF.h_formula * (CP.formula list) * ((Globals.ident * Globals.primed) list) =
  let pr = Cprinter.string_of_h_formula in
  let pr_out = pr_triple Cprinter.string_of_h_formula pr_none pr_none in
  Debug.no_1 "normalize_field_ann_heap_node" pr pr_out normalize_field_ann_heap_node_x h

let normalize_field_ann_formula_x (h:CF.formula): CF.formula =
  if (!Globals.allow_field_ann) then
  (* if (false) then *)
    normalize_formula_dn (push_node_imm_to_field_imm 2) h
  else h

let normalize_field_ann_formula (h:CF.formula): CF.formula =
  let pr = Cprinter.string_of_formula in
  Debug.no_1 "normalize_field_ann_formula" pr pr normalize_field_ann_formula_x h


let get_strongest_imm  (ann_lst: CP.ann list): CP.ann = 
  let rec helper ann ann_lst = 
    match ann_lst with
      | []   -> ann
      | (CP.ConstAnn(Mutable)) :: t -> (CP.ConstAnn(Mutable))
      | x::t -> if subtype_ann 3 x ann then helper x t else helper ann t
  in helper (CP.ConstAnn(Accs)) ann_lst

let get_weakest_imm  (ann_lst: CP.ann list): CP.ann = 
  let rec helper ann ann_lst = 
    match ann_lst with
      | []   -> ann
      | (CP.ConstAnn(Accs)) :: t -> (CP.ConstAnn(Accs))
      | x::t -> if subtype_ann 4 ann x then helper x t else helper ann t
  in helper (CP.ConstAnn(Mutable)) ann_lst

let update_read_write_ann (ann_from: CP.ann) (ann_to: CP.ann): CP.ann  =
  match ann_from with
    | CP.ConstAnn(Mutable)	-> ann_from
    | CP.ConstAnn(Accs)    -> ann_to
    | CP.ConstAnn(Imm)
    | CP.ConstAnn(Lend)
    | CP.TempAnn _
    | CP.PolyAnn(_)        -> if subtype_ann 5 ann_from ann_to then ann_from else ann_to
    | CP.TempRes _         -> ann_to

let read_write_exp_analysis (ex: C.exp)  (field_ann_lst: (ident * CP.ann) list) =
  let rec helper ex field_ann_lst  =
    match ex with
      | C.Block {C.exp_block_body = e} 
      | C.Catch { C.exp_catch_body = e} (* ->         helper cb field_ann_lst *)
      | C.Cast {C.exp_cast_body = e }
      | C.Label {C.exp_label_exp = e}  (* > helper e field_ann_lst *)
          -> helper e field_ann_lst
      | C.Assert {
            C.exp_assert_asserted_formula = assert_f_o;
            C.exp_assert_assumed_formula = assume_f_o } ->
            (* check assert_f_o and assume_f_o *)
            field_ann_lst
      | C.Assign  {
            C.exp_assign_lhs = lhs;
            C.exp_assign_rhs = rhs  } ->
            let field_ann_lst = 
              List.map (fun (f, ann) -> if (lhs == f) then (f, update_read_write_ann ann (CP.ConstAnn(Mutable))) else (f,ann) ) field_ann_lst in
            helper rhs field_ann_lst
      | C.Bind {
            C.exp_bind_bound_var = v;
            C.exp_bind_fields = vs;
            C.exp_bind_body = e } ->
            (* andreeac TODO: nested binds ---> is it supported? *)
            field_ann_lst
      | C.ICall {
            C.exp_icall_arguments = args } ->
            List.map (fun (f, ann) -> if (List.mem f args) then (f, update_read_write_ann ann (CP.ConstAnn(Lend))) else (f,ann) ) field_ann_lst
      | C.SCall {
            C.exp_scall_arguments = args } ->
            List.map (fun (f, ann) -> if (List.mem f args) then (f, update_read_write_ann ann (CP.ConstAnn(Lend))) else (f,ann) ) field_ann_lst
      | C.Cond {
            C.exp_cond_condition = cond;
            C.exp_cond_then_arm = e1;
            C.exp_cond_else_arm = e2 } ->
            let field_ann_lst = List.map (fun (f, ann) -> if (f == cond) then (f, update_read_write_ann ann (CP.ConstAnn(Lend))) else (f,ann) ) field_ann_lst in
            let field_ann_lst = helper e1 field_ann_lst in
            helper e2 field_ann_lst
      | C.New { C.exp_new_arguments = args } ->
            let args = List.map (fun (t, v) -> v) args in
            List.map (fun (f, ann) -> if (List.mem f args) then (f, update_read_write_ann ann (CP.ConstAnn(Lend))) else (f,ann) ) field_ann_lst
      | C.Try { C.exp_try_body = e1; C.exp_catch_clause = e2}
      | C.Seq { C.exp_seq_exp1 = e1; C.exp_seq_exp2 = e2 }->
            let field_ann_lst = helper e1 field_ann_lst in
            helper e2 field_ann_lst
      | C.Var { C.exp_var_name = v } ->
            List.map (fun (f, ann) -> if (f == v) then (f, update_read_write_ann ann (CP.ConstAnn(Lend))) else (f,ann) ) field_ann_lst
      | C.While{
            C.exp_while_condition = cond;
            C.exp_while_body = body } ->
            let field_ann_lst = List.map (fun (f, ann) -> if (f == cond) then (f, update_read_write_ann ann (CP.ConstAnn(Lend))) else (f,ann) ) field_ann_lst in
            helper body field_ann_lst
      | _  -> field_ann_lst
    
  in helper ex field_ann_lst
