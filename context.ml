
open Cformula
open Cast


type match_res = (h_formula (* lhs formula - contains holes in place of matched immutable nodes/views *)
		* h_formula (* node from the extracted formula *)                                                                                          
		* (h_formula * int) list (* imm node/view that have been replaced in lhs together with their corresponding hole id *)
		* match_type (* indicator of what type of matching *)
	       )
    

(*
type context = (h_formula (* frame with a hole *)
		* h_formula (* formula from the hole *)
		* int (* hole identifier*)
		* h_formula (* node from the extracted formula *)                                                                                          
		* match_type (* indicator of what type of macthing *)
		* h_formula (* context - reading phase prior to hole *)
		* (int * h_formula) list (* multiple holes with immutable terms extracted *)
	       )
*)

(*
and phase_type = 
  | Spatial
  | Classic
*)
and match_type =
  | Root
  | MaterializedArg
  | WArg
(*
and ctx_type = 
  | SpatialImm
  | SpatialMutable
  | ConjImm
  | ConjMutable
*)
(* 
   returns a list of tuples: (rest, matching node, flag, phase, ctx)
   The flag associated with each node lets us know if the match is at the root pointer, materialized arg, arg.
*)

(*  (resth1, anode, r_flag, phase, ctx) *)   
let rec choose_context prog lhs_h lhs_p (p : CP.spec_var) (imm : bool) rhs_info pos :  match_res list =
  (* let _ = print_string("choose ctx: lhs_h = " ^ (Cprinter.string_of_h_formula lhs_h) ^ "\n") in *)
  let lhs_fv = (h_fv lhs_h) @ (MCP.mfv lhs_p) in
	let eqns' = MCP.ptr_equations_without_null lhs_p in
  let r_eqns = match rhs_info with
    | Some (f,v)-> 
      let eqns = MCP.ptr_equations_without_null f in
      let r_asets = alias eqns in
      let a_vars = lhs_fv @ v in
      let fltr = List.map (fun c-> Gen.BList.intersect_eq (=) c a_vars) r_asets in
      let colaps l = List.fold_left (fun a c -> match a with 
                                                  | [] -> [(c,c)]
                                                  | h::_-> (c,(fst h))::a) [] l in
      List.concat (List.map colaps fltr) 
    | None -> [] in
	let eqns = (p, p) :: eqns' in
	let asets = alias (eqns@r_eqns) in
	let paset = get_aset asets p in (* find the alias set containing p *)


    if Gen.is_empty paset then 
      begin 
	(* no alias *)
	failwith ("choose_context: Error in getting aliases for " ^ (Cprinter.string_of_spec_var p))
      end 
    else
      begin
	if not(CP.mem p lhs_fv) || (!Globals.enable_syn_base_case && (CP.mem CP.null_var paset))
	then begin
	  Debug.devel_pprint ("choose_context: " ^ (Cprinter.string_of_spec_var p) ^ " is not mentioned in lhs\n\n") pos;
	  []
	end
	else 
	  (* before: let anodes = context_get_aliased_node prog lhs_h paset in *)
	  (* choose the type of context *)
	  let anodes = (spatial_ctx_extract prog lhs_h paset imm) 
          in		  
	    anodes
      end	

(*
spatial context
*)
    
and spatial_ctx_extract_debug p f a i = Gen.Debug.ho_4 "spatial_context_extract " (fun _ -> "?") 
(Cprinter.string_of_h_formula) 
(fun _ -> "?") 
(string_of_bool)
(fun _ -> "?")
(*(fun l -> List.fold_left (fun x (a,b,c,d,e,f,g) -> x ^ "frame: " ^ (Cprinter.string_of_h_formula a) ^ "\n; rest_heap__lhs: " ^ (Cprinter.string_of_h_formula b) ^ "\n; anode = " ^ (Cprinter.string_of_h_formula d)) "" l)*)
spatial_ctx_extract p f a i


and spatial_ctx_extract prog (f0 : h_formula) (aset : CP.spec_var list) (imm : bool) : match_res list  =
  (* let _ = print_string("spatial_ctx_extract with f0 = " ^ (Cprinter.string_of_h_formula f0) ^ "\n") in  *)
  let rec helper f = match f with
    | HTrue 
    | HFalse -> []
    | Hole _ -> []
    | DataNode ({h_formula_data_node = p1; 
		 h_formula_data_imm = imm1}) ->
	if ((CP.mem p1 aset) && (subtype imm imm1)) then 
	  if imm then
	    let hole_no = Globals.fresh_int() in 
	      [((Hole hole_no), f, [(f, hole_no)], Root)]
	  else
	    [(HTrue, f, [], Root)]
	else 
	  []
    | ViewNode ({h_formula_view_node = p1;
		 h_formula_view_imm = imm1;
		 h_formula_view_arguments = vs1;
		 h_formula_view_name = c}) ->
	  if (subtype imm imm1) then
	    (if (CP.mem p1 aset)  then
	      if imm then
	       let hole_no = Globals.fresh_int() in
		(*[(Hole hole_no, matched_node, hole_no, f, Root, HTrue, [])]*)
		[(Hole hole_no, f, [(f, hole_no)], Root)]
	      else
		[(HTrue, f, [], Root)]
	    else
	      let vdef = look_up_view_def_raw prog.prog_view_decls c in
	      let mvs = CP.subst_var_list_avoid_capture vdef.view_vars vs1
		vdef.view_materialized_vars
	      in
		if List.exists (fun v -> ((CP.mem v aset) && (subtype imm imm1))) mvs then
		  if imm then
		    let hole_no = Globals.fresh_int() in
		      [(Hole hole_no, f, [(f, hole_no)], MaterializedArg)]
		  else
		    [(HTrue, f, [], MaterializedArg)]
		else if List.exists (fun v -> ((CP.mem v aset) && (subtype imm imm1))) vs1 then
		  if imm then
		    let hole_no = Globals.fresh_int() in 
		      [(Hole hole_no, f, [(f, hole_no)], WArg)]
		  else
		    [(HTrue, f, [], WArg)]
		else
		  []
	    )
	  else []
    | Star ({h_formula_star_h1 = f1;
	     h_formula_star_h2 = f2;
	     h_formula_star_pos = pos}) ->
	let l1 = helper f1 in
	let res1 = List.map (fun (lhs1, node1, hole1, match1) -> (mkStarH lhs1 f2 pos, node1, hole1, match1)) l1 in  

	let l2 = helper f2 in
	let res2 = List.map (fun (lhs2, node2, hole2, match2) -> (mkStarH f1 lhs2 pos, node2, hole2, match2)) l2 in
	  res1 @ res2
    | _ -> let _ = print_string("[context.ml]: There should be no conj/phase in the lhs at this level; lhs = " ^ (Cprinter.string_of_h_formula f) ^ "\n") in failwith("[context.ml]: There should be no conj/phase in the lhs at this level\n")



 (*| Conj ({h_formula_conj_h1 = f1;
	     h_formula_conj_h2 = f2;
	     h_formula_conj_pos = pos}) -> (* [] *)
	let l1 = helper f1 in
	let res1 = List.map (fun (ctx1, hole1, hole_no1, node1, match1, no_read_ctx1, imm_marks1) -> (mkConjH ctx1 f2 pos, hole1, hole_no1, node1, match1, no_read_ctx1, imm_marks1)) l1 in  

	let l2 = helper f2 in
	let res2 = List.map (fun (ctx2, hole2, hole_no2, node2, match2, no_read_ctx2, imm_marks2) -> (mkConjH f1 ctx2 pos, hole2, hole_no2, node2, match2, no_read_ctx2, imm_marks2)) l2 in
	  res1 @ res2

    | Phase ({h_formula_phase_rd = f1;
	     h_formula_phase_rw = f2;
	     h_formula_phase_pos = pos}) ->
	(* let _ = print_string("in phase with f1 = " ^ (Cprinter.string_of_h_formula f1) ^ "\n") in *)
	(* let _ = print_string("and f2 = " ^ (Cprinter.string_of_h_formula f2) ^ "\n") in *)
	let l1 = helper f1 in		
	let res1 = List.map (fun (ctx1, hole1, hole_no1, node1, match1, no_read_ctx1, imm_marks1) -> (mkPhaseH ctx1 f2 pos, hole1, hole_no1, node1, match1, no_read_ctx1, imm_marks1)) l1 in  

	let l2 = helper f2 in
	let res2 = 
	  if not(imm) && (List.length l2) > 0 then
	    (* drop read phase *)
	    List.map (fun (ctx2, hole2, hole_no2, node2, match2, no_read_ctx2, imm_marks2) -> (ctx2, hole2, hole_no2, node2, match2, no_read_ctx2, imm_marks2)) l2
	  else
	    List.map (fun (ctx2, hole2, hole_no2, node2, match2, no_read_ctx2, imm_marks2) -> (mkPhaseH f1 ctx2 pos, hole2, hole_no2, node2, match2, no_read_ctx2, imm_marks2)) l2
	in
	  res1 @ res2
(*	  
	let l2 = helper f2 in
	  (*List.map (fun (ctx2, hole2, hole_no2, node2, match2, no_read_ctx2, imm_marks2) -> ((*mkPhaseH f1 ctx2 pos*)ctx2, hole2, hole_no2, node2, match2, no_read_ctx2, imm_marks2)) l2*)
	List.map (fun (ctx2, hole2, hole_no2, node2, match2, no_read_ctx2, imm_marks2) -> (mkPhaseH f1 ctx2 pos, hole2, hole_no2, node2, match2, no_read_ctx2, imm_marks2)) l2  
*)
 *)
  in
    (helper f0)

and input_formula_in2_frame (frame, id_hole) (to_input : formula) : formula =
  match to_input with
    | Base (fb) ->
	Base{fb with formula_base_heap = input_h_formula_in2_frame (frame, id_hole) fb.formula_base_heap;}
    | Or ({formula_or_f1 = f1;
	   formula_or_f2 = f2;
	   formula_or_pos = pos}) -> 
	Or({formula_or_f1 = (input_formula_in2_frame (frame, id_hole) f1);
	    formula_or_f2 = (input_formula_in2_frame (frame, id_hole) f2);
	    formula_or_pos = pos})
    | Exists(fe) ->
	Exists{fe with formula_exists_heap = input_h_formula_in2_frame (frame, id_hole) fe.formula_exists_heap;}


and input_h_formula_in2_frame (frame, id_hole) (to_input : h_formula) : h_formula = 
  match frame with
    | Hole id ->
	if id = id_hole then to_input
	else frame
    | Star ({h_formula_star_h1 = f1;
	     h_formula_star_h2 = f2;
	     h_formula_star_pos = pos}) -> 
	let new_f1 = input_h_formula_in2_frame (f1, id_hole) to_input in 
	let new_f2 = input_h_formula_in2_frame (f2, id_hole) to_input in
	  Star ({h_formula_star_h1 = new_f1;
		 h_formula_star_h2 = new_f2;
		 h_formula_star_pos = pos})  
    | Conj ({h_formula_conj_h1 = f1;
	     h_formula_conj_h2 = f2;
	     h_formula_conj_pos = pos}) -> 
	let new_f1 = input_h_formula_in2_frame (f1, id_hole) to_input in 
	let new_f2 = input_h_formula_in2_frame (f2, id_hole) to_input in
	  Conj ({h_formula_conj_h1 = new_f1;
		 h_formula_conj_h2 = new_f2;
		 h_formula_conj_pos = pos})  
    | Phase ({h_formula_phase_rd = f1;
	     h_formula_phase_rw = f2;
	     h_formula_phase_pos = pos}) -> 
	let new_f1 = input_h_formula_in2_frame (f1, id_hole) to_input in 
	let new_f2 = input_h_formula_in2_frame (f2, id_hole) to_input in
	  Phase ({h_formula_phase_rd = new_f1;
		 h_formula_phase_rw = new_f2;
		 h_formula_phase_pos = pos})  
    | DataNode _ 
    | ViewNode _
    | HTrue | HFalse -> frame
  

(* 
and input_ctx_frame (ctx : Cformula.context) : Cformula.context =
    match ctx with
      | Ctx(es) ->
	  Ctx {es with es_formula = input_formula_in2_frame es.es_frame es.es_formula; es_frame = [];}
      | OCtx(c1, c2) -> OCtx((input_ctx_frame c1), (input_ctx_frame c2))

and input_list_ctx_frame (ctx : Cformula.list_context) : Cformula.list_context =
  match ctx with
      | FailCtx _ -> ctx
      | SuccCtx (cl) -> SuccCtx(List.map input_ctx_frame cl)
*)
(* create an empty context *)
(*and mk_empty_frame (id_hole : int) : h_formula = Hole(id_hole)*)
(*
and mk_empty_frame (): (h_formula * int) = 
  let hole_id = Globals.fresh_int () in
    (Hole(hole_id), hole_id)

(* check whether a context is empty *)
and is_empty_frame (frame : formula) : bool = match frame with 
  | Base ({formula_base_heap = fb_h;}) -> is_hole_heap_frame fb_h
  | _  -> failwith "context.ml, is_empty_ctx: check this\n" (* todo: check this *)

and is_hole_heap_frame (frame_h : h_formula) : bool = match frame_h with
  | Hole _ -> true
  | _ -> false

*)
(*------	
and update_ctx_frame ctx0 (frame, hole_id) = 
  match ctx0 with
    | Ctx(es) -> Ctx{es with es_frame = (frame, hole_id)}
    | OCtx(c1, c2) -> 
	let update_c1 = update_ctx_frame c1 (frame, hole_id) in
	let update_c2 = update_ctx_frame c2 (frame, hole_id) in
	  OCtx(update_c1, update_c2)

and update_list_ctx_frame ctx0 (frame, hole_id) = 
  match ctx0 with
    | FailCtx _ -> let _ = print_string("fail with frame " ^ (Cprinter.string_of_h_formula frame) ^ "\n") in ctx0
    | SuccCtx (cl) -> SuccCtx(List.map (fun x -> update_ctx_frame x (frame, hole_id))cl) 
-----*)
and update_ctx_es_formula ctx0 f = 
  match ctx0 with
    | Ctx(es) -> Ctx{es with es_formula = f}
    | OCtx(c1, c2) -> 
	let update_c1 = update_ctx_es_formula c1 f in
	let update_c2 = update_ctx_es_formula c2 f in
	  OCtx(update_c1, update_c2)

and update_ctx_es_orig_conseq ctx new_conseq = 
  match ctx with
    | Ctx(es) -> Ctx{es with es_orig_conseq = new_conseq}
    | OCtx(c1, c2) -> 
	let update_c1 = update_ctx_es_orig_conseq c1 new_conseq in
	let update_c2 = update_ctx_es_orig_conseq c2 new_conseq in
	  OCtx(update_c1, update_c2)

(* computes must-alias sets from equalities, maintains the invariant *)
(* that these sets form a partition. *)
and alias (ptr_eqs : (CP.spec_var * CP.spec_var) list) : CP.spec_var list list = match ptr_eqs with
  | (v1, v2) :: rest -> begin
	  let rest_sets = alias rest in
	  let search (v : CP.spec_var) (asets : CP.spec_var list list) = List.partition (fun aset -> CP.mem v aset) asets in
	  let av1, rest1 = search v1 rest_sets in
	  let av2, rest2 = search v2 rest1 in
	  let v1v2_set = CP.remove_dups_svl (List.concat ([v1; v2] :: (av1 @ av2))) in
		v1v2_set :: rest2
	end
  | [] -> []

and get_aset (aset : CP.spec_var list list) (v : CP.spec_var) : CP.spec_var list =
  let tmp = List.filter (fun a -> CP.mem v a) aset in
	match tmp with
	  | [] -> []
	  | [s] -> s
	  | _ -> failwith ((Cprinter.string_of_spec_var v) ^ " appears in more than one alias sets")

(* I <: M *)
(* return true if imm1 <: imm2 *)	
and subtype (imm1 : bool) (imm2 : bool) : bool = not(imm2) or imm1

  
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
      | [] -> (HTrue, [])
  in
    (crt_cont, 
     {  es with
          es_cont = cont;
     })

(* utilities for handling lhs holes *)
(* push *)
and push_crt_holes_list_ctx (ctx : list_context) (holes : (h_formula * int) list) : list_context = 
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
    | Phase({h_formula_phase_rd = h1;
	   h_formula_phase_rw = h2;
	   h_formula_phase_pos = pos}) ->
	let nh1 = apply_subs_h_formula crt_holes h1 in
	let nh2 = apply_subs_h_formula crt_holes h2 in
	  Phase({h_formula_phase_rd = nh1;
	       h_formula_phase_rw = nh2;
	       h_formula_phase_pos = pos})
    | _ -> h

