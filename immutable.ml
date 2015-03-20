#include "xdebug.cppo"
open VarGen
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
module I  = Iast


(* let rec split_phase_debug_lhs h = Debug.no_1 "split_phase(lhs)" *)
(*   Cprinter.string_of_h_formula  *)
(*   (fun (a,b,c) -> "RD = " ^ (Cprinter.string_of_h_formula a) ^ "; WR = " ^ (Cprinter.string_of_h_formula b) ^ "; NEXT = " ^ (Cprinter.string_of_h_formula c) ^ "\n")  *)
(*   split_phase h *)

(* and split_phase_debug_rhs h = Debug.no_1 "split_phase(rhs)" *)
(*   Cprinter.string_of_h_formula  *)
(*   (fun (a,b,c) -> "RD = " ^ (Cprinter.string_of_h_formula a) ^ "; WR = " ^ (Cprinter.string_of_h_formula b) ^ "; NEXT = " ^ (Cprinter.string_of_h_formula c) ^ "\n")  *)
(*   split_phase 0 h *)

let isAccs = CP.isAccs 
let isLend = CP.isLend 
let isImm = CP.isImm 
let isMutable = CP.isMutable

let isAccsList (al : CP.ann list) : bool = List.for_all isAccs al
let isMutList (al : CP.ann list) : bool = List.for_all isMutable al

let isExistsLendList (al : CP.ann list) : bool = List.exists isLend al
let isExistsMutList (al : CP.ann list) : bool = List.exists isMutable al

              
(* result: res:bool * (ann constraint = relation between lhs_ann and rhs_ann) *)
let rec subtype_ann_pair_x (imm1 : CP.ann) (imm2 : CP.ann) : bool * ((CP.exp * CP.exp) option) =
  match imm1 with
    | CP.PolyAnn v1 ->
          (match imm2 with
            | CP.PolyAnn v2 -> (true, Some (CP.Var(v1, no_pos), CP.Var(v2, no_pos)))
            | CP.ConstAnn k2 -> 
                  (true, Some (CP.Var(v1,no_pos), CP.AConst(k2,no_pos)))
            | CP.TempAnn _ | CP.NoAnn -> (subtype_ann_pair_x imm1 (CP.ConstAnn(Accs)))
            | CP.TempRes (al,ar) -> (subtype_ann_pair_x imm1 ar)  (* andreeac should it be Accs? *)
          )
    | CP.ConstAnn k1 ->
          (match imm2 with
            | CP.PolyAnn v2 -> (true, Some (CP.AConst(k1,no_pos), CP.Var(v2,no_pos)))
            | CP.ConstAnn k2 -> ((int_of_heap_ann k1)<=(int_of_heap_ann k2),None) 
            | CP.TempAnn _ | CP.NoAnn -> (subtype_ann_pair_x imm1 (CP.ConstAnn(Accs)))
            | CP.TempRes (al,ar) -> (subtype_ann_pair_x imm1 ar)  (* andreeac should it be Accs? *)
          ) 
    | CP.TempAnn _ | CP.NoAnn -> (subtype_ann_pair_x (CP.ConstAnn(Accs)) imm2) 
    | CP.TempRes (l,ar) -> (subtype_ann_pair_x (CP.ConstAnn(Accs)) imm2)  (* andreeac should it be ar-al? or Accs? *)
          
let subtype_ann_pair (imm1 : CP.ann) (imm2 : CP.ann) : bool * ((CP.exp * CP.exp) option) =
  let pr_imm = Cprinter.string_of_imm in
  let pr1 (imm1,imm2) =  (pr_imm imm1) ^ " <: " ^ (pr_imm imm2) ^ "?" in
  let pr_exp = CP.ArithNormalizer.string_of_exp in
  let pr_out = pr_pair string_of_bool (pr_option (pr_pair (add_str "l(subtype)" pr_exp) (add_str "r(subtype_" pr_exp)) ) in
  Debug.no_1 "subtype_ann_pair" pr1 pr_out (fun _ -> subtype_ann_pair_x imm1 imm2) (imm1,imm2)

(* bool denotes possible subyping *)
(* return true if imm1 <: imm2 *)	
(* M <: I <: L <: A*)
let subtype_ann_x (imm1 : CP.ann) (imm2 : CP.ann) : bool =
  let (r,op) = subtype_ann_pair imm1 imm2 in r

(* return true if imm1 <: imm2 *)	
(* M <: I <: L <: A*)
let subtype_ann caller (imm1 : CP.ann) (imm2 : CP.ann) : bool = 
  let pr_imm = Cprinter.string_of_imm in
  let pr1 (imm1,imm2) =  (pr_imm imm1) ^ " <: " ^ (pr_imm imm2) ^ "?" in
  Debug.no_1_num caller "subtype_ann"  pr1 string_of_bool (fun _ -> subtype_ann_x imm1 imm2) (imm1,imm2)

let subtype_ann_gen_x impl_vars evars (imm1 : CP.ann) (imm2 : CP.ann): 
  bool * (CP.formula list) * (CP.formula list) * (CP.formula list) =
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

let subtype_ann_gen impl_vars evars (imm1 : CP.ann) (imm2 : CP.ann): 
  bool * (CP.formula list) * (CP.formula list) * (CP.formula list) =
  let pr1 = !CP.print_svl in
  let pr2 = (Cprinter.string_of_imm)  in
  let pr2a = pr_list !CP.print_formula in
  let prlst =  (pr_pair (pr_list Cprinter.string_of_spec_var) (pr_list Cprinter.string_of_spec_var)) in
  let pr3 = pr_quad string_of_bool pr2a pr2a pr2a  in
  Debug.no_4 "subtype_ann_gen" pr1 pr1 pr2 pr2 pr3 
    subtype_ann_gen_x impl_vars evars (imm1 : CP.ann) (imm2 : CP.ann) 

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

let rec remove_true_rd_phase (h : h_formula) : h_formula = 
  match h with
    | Phase ({h_formula_phase_rd = h1;
	  h_formula_phase_rw = h2;
	  h_formula_phase_pos = pos
	 }) -> 
      if (h1 == HEmp) then h2
      else if (h2 == HEmp) then h1
      else h
    | Star ({h_formula_star_h1 = h1;
	  h_formula_star_h2 = h2;
	  h_formula_star_pos = pos
	 }) -> 
      let h1r = remove_true_rd_phase h1 in
      let h2r = remove_true_rd_phase h2 in
      mkStarH h1r h2r pos
    | _ -> h


let rec split_wr_phase (h : h_formula) : (h_formula * h_formula) = 
  match h with 
    | Star ({h_formula_star_h1 = h1;
	  h_formula_star_h2 = h2;
	  h_formula_star_pos = pos}) -> 
      (* let () = print_string("[cris]: split star " ^ (Cprinter.string_of_h_formula h) ^ "\n") in *)
	      (match h2 with
	        | Phase _ -> (h1, h2)
	        | Star ({h_formula_star_h1 = sh1;
		      h_formula_star_h2 = sh2;
		      h_formula_star_pos = spos}) ->
		          split_wr_phase (CF.mkStarH (CF.mkStarH h1 sh1 pos ) sh2 pos )
                (* | Conj _ ->  *)
                (*       if(!Globals.allow_field_ann) then  *)
                (*         split_wr_phase h2 *)
                (*       else *)
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
  | DataNode (h1) -> 
        if (!Globals.allow_field_ann) then (isExistsMutList h1.h_formula_data_param_imm)
        else
          ((CP.isMutable h1.h_formula_data_imm) || (CP.isImm h1.h_formula_data_imm))
  | ViewNode (h1) -> 
        if (!Globals.allow_field_ann) then (isExistsMutList (CP.annot_arg_to_imm_ann_list_no_pos h1.h_formula_view_annot_arg))
        else
          ((CP.isMutable h1.h_formula_view_imm) || (CP.isImm h1.h_formula_view_imm))
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
	h_formula_star_pos = pos}) -> (consume_heap_h_formula h1) || (consume_heap_h_formula h2)
  | _ -> false


let rec consume_heap (f : formula) : bool =  match f with
  | Base(bf) -> consume_heap_h_formula bf.formula_base_heap
  | Exists(ef) -> consume_heap_h_formula ef.formula_exists_heap
  | Or({formula_or_f1 = f1;
    formula_or_f2 = f2;
    formula_or_pos = pos}) ->
        (consume_heap f1) || (consume_heap f2)

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
    (* | Conj({h_formula_conj_h1 = h1; *)
    (*   h_formula_conj_h2 = h2}) -> *)
    (*       if !Globals.allow_field_ann then *)
    (*         let h3, h4 = split_wr_phase h2 in *)
    (*         (h1, h3, h4) *)
    (*       else 	       *)
    (*         if (consume_heap_h_formula h) then *)
    (*           (HEmp, h, HEmp) *)
    (*         else *)
    (*           (h, HEmp, HEmp) *)
    | _ ->
	      if (consume_heap_h_formula h) then
	        (HEmp, h, HEmp)
	      else
	        (h, HEmp, HEmp)

let split_phase i (h : h_formula) : (h_formula * h_formula * h_formula )= 
  let pr = Cprinter.string_of_h_formula in
  let pr2 = pr_triple pr pr pr in
  Debug.no_1_num i "split_phase" pr pr2 split_phase_x h


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
            if (isAccs node_imm) && (!Globals.remove_abs) then HEmp 
            else if !Globals.allow_field_ann &&  (isAccsList param_imm) && (!Globals.remove_abs) then HEmp else h
            (* match !Globals.allow_field_ann, !Globals.allow_imm with *)
            (*   | true, _     -> if (isAccsList param_imm) then HEmp else h *)
            (*   | false, true -> if (isAccs node_imm) then HEmp else h *)
            (*   | _,_         -> if (isAccs node_imm) then HEmp else h *)
          in new_h
    | CF.ViewNode vn ->  
          let node_imm = vn.CF.h_formula_view_imm in
          if (isAccs node_imm)  && (!Globals.remove_abs) then HEmp else h 
          (* let param_imm = CP.annot_arg_to_imm_ann_list vn.CF.h_formula_view_annot_arg in *)
          (* let new_h =  *)
          (*   match !Globals.allow_field_ann, !Globals.allow_imm with *)
          (*     | true, _     -> if (isAccsList param_imm) then HEmp else h *)
          (*     | false, true -> if (isAccs node_imm) then HEmp else h *)
          (*     | _,_         -> HEmp *)
          (* in new_h *)
    | _ -> h


(* let maybe_replace_w_empty h = *)
(*   match h with *)
(*     | CF.DataNode dn ->  *)
(*           let node_imm = dn.CF.h_formula_data_imm in *)
(*           let param_imm = dn.CF.h_formula_data_param_imm in *)
(*           let new_h, xpure =  *)
(*             match !Globals.allow_field_ann, !Globals.allow_imm with *)
(*               | true, _     -> if (isAccsList param_imm) then (HEmp, Some (xpure) ) else (h,None) *)
(*               | false, true -> if (isAccs node_imm) then (HEmp, Some (xpure)) else (h,None) *)
(*               | _,_         -> (h, None) *)
(*           in new_h *)
(*     | CF.ViewNode vn -> h  *)
(*           (\* let node_imm = vn.CF.h_formula_view_imm in *\) *)
(*           (\* let param_imm = CP.annot_arg_to_imm_ann_list vn.CF.h_formula_view_annot_arg in *\) *)
(*           (\* let new_h =  *\) *)
(*           (\*   match !Globals.allow_field_ann, !Globals.allow_imm with *\) *)
(*           (\*     | true, _     -> if (isAccsList param_imm) then HEmp else h *\) *)
(*           (\*     | false, true -> if (isAccs node_imm) then HEmp else h *\) *)
(*           (\*     | _,_         -> HEmp *\) *)
(*           (\* in new_h *\) *)
(*     | _ -> h *)


let ann_opt_to_ann (ann_opt: Ipure.ann option) (default_ann: Ipure.ann): Ipure.ann = 
  match ann_opt with
    | Some ann0 -> ann0
    | None      -> default_ann

let rec ann_opt_to_ann_lst (ann_opt_lst: Ipure.ann option list) (default_ann: Ipure.ann): Ipure.ann list = 
  match ann_opt_lst with
    | [] -> []
    | ann0 :: t -> (ann_opt_to_ann ann0 default_ann) :: (ann_opt_to_ann_lst t default_ann)

let iformula_ann_to_cformula_ann (iann : Ipure.ann) : CP.ann = 
  match iann with
    | Ipure.ConstAnn(x) -> CP.ConstAnn(x)
    | Ipure.PolyAnn((id,p), l) -> 
          CP.PolyAnn(CP.SpecVar (AnnT, id, p))

let iformula_ann_to_cformula_ann_lst (iann_lst : Ipure.ann list) : CP.ann list = 
  List.map iformula_ann_to_cformula_ann iann_lst

let iformula_ann_opt_to_cformula_ann_lst (iann_lst : Ipure.ann option list) : CP.ann list = 
  List.map iformula_ann_to_cformula_ann (ann_opt_to_ann_lst iann_lst  (Ipure.ConstAnn(Mutable)))

(* check lending property (@L) in classic reasoning. Hole is treated like @L *)
let rec is_classic_lending_hformula (f: h_formula) : bool =
  match f with
  | DataNode dn -> isLend dn.h_formula_data_imm
  | ViewNode vn -> isLend vn.h_formula_view_imm
  | Hole _ | FrmHole _ -> true      (* a Hole behaves like @L *)
  | Conj ({h_formula_conj_h1 = h1;
           h_formula_conj_h2 = h2})
  | ConjStar ({h_formula_conjstar_h1 = h1;
               h_formula_conjstar_h2 = h2})
  | ConjConj ({h_formula_conjconj_h1 = h1;
               h_formula_conjconj_h2 = h2})
  | Phase ({h_formula_phase_rd = h1;
            h_formula_phase_rw = h2})
  | Star ({h_formula_star_h1 = h1;
           h_formula_star_h2 = h2}) ->
      ((is_classic_lending_hformula h1) && (is_classic_lending_hformula h2))
  | _ -> false

let rec is_lend_h_formula (f : h_formula) : bool =  match f with
  | DataNode (h1) -> 
        if (isLend h1.h_formula_data_imm) then
          (* let () = print_string("true for h = " ^ (!print_h_formula f) ^ "\n\n")  in *) true
        else
          false
  | ViewNode (h1) ->
        if (isLend h1.h_formula_view_imm) then
          (* let () = print_string("true for h = " ^ (!print_h_formula f) ^ "\n\n") in *) true
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
	h_formula_star_pos = pos}) -> (is_lend_h_formula h1) || (is_lend_h_formula h2)
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
        (is_lend f1) || (is_lend f2)

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
          if (wr_phase) && ((!Globals.allow_mem) || (!Globals.allow_field_ann) || (!Globals.allow_ramify)) then h else
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
        (contains_phase h1) || (contains_phase h2)
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

and propagate_imm_struc_formula sf view_name (imm : CP.ann)  (imm_p: (CP.annot_arg * CP.annot_arg) list) =
  let res = 
    match sf with
      | EBase f   -> EBase {f with 
            formula_struc_base = propagate_imm_formula f.formula_struc_base view_name imm imm_p }
      | EList l   -> EList  (map_l_snd (fun c->  propagate_imm_struc_formula c view_name imm imm_p) l)
      | ECase f   -> ECase {f with formula_case_branches = map_l_snd (fun c->  propagate_imm_struc_formula c view_name imm imm_p) f.formula_case_branches;}
      | EAssume f -> EAssume {f with
	    formula_assume_simpl = propagate_imm_formula f.formula_assume_simpl view_name imm imm_p;
	    formula_assume_struc = propagate_imm_struc_formula  f.formula_assume_struc view_name imm imm_p;}
      | EInfer f  -> EInfer {f with formula_inf_continuation = propagate_imm_struc_formula f.formula_inf_continuation view_name imm imm_p} 
  in res

and propagate_imm_formula_x (f : formula) (view_name: ident) (imm : CP.ann) (imm_p: (CP.annot_arg * CP.annot_arg) list): formula = match f with
  | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) ->
	let rf1 = propagate_imm_formula_x f1 view_name imm imm_p in
	let rf2 = propagate_imm_formula_x f2 view_name imm imm_p in
	let resform = mkOr rf1 rf2 pos in
	resform
  | Base f1 ->
        let emap = build_eset_of_conj_formula (MCP.pure_of_mix  f1.CF.formula_base_pure) in
        let f1_heap = propagate_imm_h_formula f1.formula_base_heap view_name imm imm_p emap in
        Base({f1 with formula_base_heap = f1_heap})
  | Exists f1 ->
        let emap = build_eset_of_conj_formula (MCP.pure_of_mix  f1.CF.formula_exists_pure) in
        let f1_heap = propagate_imm_h_formula f1.formula_exists_heap view_name imm imm_p emap in
        Exists({f1 with formula_exists_heap = f1_heap})

(* !!currently works just for view_name and self data nodes!! *)
and propagate_imm_formula (f : formula) (view_name: ident) (imm : CP.ann) (imm_p: (CP.annot_arg * CP.annot_arg) list): formula =
   Debug.no_4 "propagate_imm_formula" 
      (add_str "formula" (Cprinter.string_of_formula)) 
      (add_str "view_name" pr_id) 
      (add_str "imm" (Cprinter.string_of_imm_ann)) 
      (add_str "map" (pr_list (pr_pair Cprinter.string_of_annot_arg Cprinter.string_of_annot_arg ))) 
      (Cprinter.string_of_formula) 
       propagate_imm_formula_x f view_name imm imm_p

(* andreeac TODOIMM: to replace below so that it uses emap *)
and replace_imm imm map emap=
  match imm with
    | CP.ConstAnn _ -> imm
    | CP.PolyAnn sv -> 
          begin
            let new_imm = List.fold_left (fun acc (fr,t) ->
                if ( Gen.BList.mem_eq CP.eq_ann imm [CP.annot_arg_to_imm_ann fr]) 
                then [get_weakest_imm ((CP.annot_arg_to_imm_ann fr)::[(CP.annot_arg_to_imm_ann t)]) ] 
                else acc) [] map in
            match new_imm with
              | []   -> imm
              | h::_ -> h
          end
    | _ -> imm                          (* replace temp as well *)

(* andreeac TODOIMM: propagate for fields in view defs must be modified to behave as below:
   pred p(a) = ... self<_@a>@b;
   unfold(pred(@c)@d) = ... self<_@weakest(a,b,c,d)>
*)
and propagate_imm_h_formula_x (f : h_formula) view_name (imm : CP.ann)  (imm_p: (CP.annot_arg * CP.annot_arg) list) emap : h_formula = 
  match f with
    | ViewNode f1 -> 
          if not (f1.CF.h_formula_view_name = view_name) then
			(*Cristian: this causes a bug in the folding, e.g. when trying to prove a @L view node the system ends up trying to prove @M
			nodes, which obviously fail. I believe that all the unfolded nodes need to take the original annotation not only the root.
			e.g. bellow must succeed: 
					pred p1<> ==  self::node<c>* c::t1<> .
					pred t1<> == self::node<_>.
					checkentail c::node2<cc>@L* cc::t1<>@L  |-  c::p1<>@L.
			It should behave similar to the datanode...
			*)
			(*f*)
			ViewNode({f1 with h_formula_view_imm = get_weakest_imm (imm::[f1.CF.h_formula_view_imm]);})
          else
            let new_node_imm = imm in
            let new_args_imm = List.fold_left (fun acc (fr,t) ->
                if (Gen.BList.mem_eq CP.eq_annot_arg fr (CF.get_node_annot_args f)) then acc@[t] else acc) []  imm_p in
            (* andreeac: why was below needed? *)
          (* match f1.Cformula.h_formula_view_imm with *)
	  (*   | CP.ConstAnn _ -> imm *)
	  (*   | _ ->  *)
	  (*         begin *)
	  (*           match imm with  *)
	  (*             | CP.ConstAnn _ -> imm *)
	  (*             | _ -> f1.Cformula.h_formula_view_imm  *)
	  (*         end *)
          ViewNode({f1 with h_formula_view_imm = get_weakest_imm (imm::[f1.CF.h_formula_view_imm]);(* new_node_imm; <--- andreeac: this is not correct when field-ann is enabled, to adjust *)
              h_formula_view_annot_arg = CP.update_positions_for_annot_view_params new_args_imm f1.h_formula_view_annot_arg;
          })
    | DataNode f1 -> 
          (* if not(CP.is_self_spec_var f1.CF.h_formula_data_node) then f *)
          (* else *)
            let new_param_imm = List.map (fun a -> replace_imm a imm_p emap) f1.CF.h_formula_data_param_imm in
            DataNode({f1 with h_formula_data_imm =  get_weakest_imm (imm::[f1.CF.h_formula_data_imm]);
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
	  let h1 = propagate_imm_h_formula f1.h_formula_star_h1 view_name imm imm_p emap in
	  let h2 = propagate_imm_h_formula f1.h_formula_star_h2 view_name imm imm_p emap in
	  mkStarH h1 h2 f1.h_formula_star_pos 
    | Conj f1 ->
	  let h1 = propagate_imm_h_formula f1.h_formula_conj_h1 view_name imm imm_p emap in
	  let h2 = propagate_imm_h_formula f1.h_formula_conj_h2 view_name imm imm_p emap in
	  mkConjH h1 h2 f1.h_formula_conj_pos
    | ConjStar f1 ->
	  let h1 = propagate_imm_h_formula f1.h_formula_conjstar_h1 view_name imm imm_p emap in
	  let h2 = propagate_imm_h_formula f1.h_formula_conjstar_h2 view_name imm imm_p emap in
	  mkConjStarH h1 h2 f1.h_formula_conjstar_pos
    | ConjConj f1 ->
	  let h1 = propagate_imm_h_formula f1.h_formula_conjconj_h1 view_name imm imm_p emap in
	  let h2 = propagate_imm_h_formula f1.h_formula_conjconj_h2 view_name imm imm_p emap in
	  mkConjConjH h1 h2 f1.h_formula_conjconj_pos	      	      
    | Phase f1 ->
	  let h1 = propagate_imm_h_formula f1.h_formula_phase_rd view_name imm imm_p emap in
	  let h2 = propagate_imm_h_formula f1.h_formula_phase_rw view_name imm imm_p emap in
	  mkPhaseH h1 h2 f1.h_formula_phase_pos
    | _ -> f

and propagate_imm_h_formula (f : h_formula) view_name (imm : CP.ann)  (map: (CP.annot_arg * CP.annot_arg) list) emap: h_formula = 
  Debug.no_4 "propagate_imm_h_formula" 
      (Cprinter.string_of_h_formula) 
      (add_str "view_name" pr_id) 
      (add_str "imm" (Cprinter.string_of_imm)) 
      (add_str "map" (pr_list (pr_pair Cprinter.string_of_annot_arg Cprinter.string_of_annot_arg ))) 
      (Cprinter.string_of_h_formula) 
      (fun _ _ _ _ -> propagate_imm_h_formula_x f view_name imm map emap) f view_name imm map

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
    | CP.TempAnn _ | CP.NoAnn
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

and replace_list_ann i (ann_lst_l: CP.ann list) (ann_lst_r: CP.ann list) es =
  let pr lst = "[" ^ (List.fold_left (fun y x-> (Cprinter.string_of_imm x) ^ ", " ^ y) "" lst) ^ "]; " in
  let pr_p =  pr_pair pr pr in 
  let pr_out = pr_triple pr_p pr_none pr_none in
  Debug.no_2_num i "replace_list_ann" pr pr pr_out (fun _ _-> replace_list_ann_x ann_lst_l ann_lst_r es) ann_lst_l ann_lst_r

and replace_list_ann_mem (ann_lst_l: CP.ann list) (ann_lst_r: CP.ann list) impl_vars expl_vars evars =
  let n_ann_lst, niv, constr = List.fold_left (fun ((res_ann_acc,cons_ann_acc), n_iv, (to_lhsl, to_rhsl, to_rhs_exl)) (ann_l,ann_r) -> 
      let (resid_ann, cons_ann), niv, ((to_lhs, to_rhs, to_rhs_ex),_) = subtract_ann ann_l ann_r impl_vars expl_vars evars true in 
      ((res_ann_acc@[resid_ann], cons_ann_acc@[cons_ann]), niv@n_iv, (to_lhs@to_lhsl, to_rhs@to_rhsl, to_rhs_ex@to_rhs_exl))
  ) (([],[]), [], ([],[],[])) (List.combine ann_lst_l ann_lst_r ) in
  n_ann_lst, niv, constr 

and consumed_ann (ann_l: CP.ann) (ann_r: CP.ann): CP.ann = 
  match ann_r with
    | CP.ConstAnn(Accs)    
    | CP.TempAnn _ | CP.NoAnn
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
  x_tinfo_hp (add_str "conjs bef:" (pr_list Cprinter.string_of_pure_formula)) conjs no_pos;
  (* keep only Eq formulae of form var = AConst, where var is in lst *)
  let conjs = List.filter (fun f -> 
      (CP.is_eq_with_aconst f) && not(CP.disjoint (CP.fv f) lst )) conjs in
 x_tinfo_hp (add_str "conjs:" (pr_list Cprinter.string_of_pure_formula)) conjs no_pos;
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
    x_tinfo_hp (add_str "pure:" (Cprinter.string_of_pure_formula)) pure no_pos;
    (* x_tinfo_hp (add_str "pairs:" (pr_list (pr_pair Cprinter.string_of_spec_var Cprinter.string_of_spec_var))) pairs no_pos; *)
    let conjs = CP.split_conjunctions pure in
    x_tinfo_hp (add_str "conjs:" (pr_list Cprinter.string_of_pure_formula)) conjs no_pos;
    let ann_r0 = collect_ann_info_from_formula annr conjs pure in
    let ann_l0 = collect_ann_info_from_formula annl conjs pure in
    x_tinfo_hp (add_str "annr:" (pr_opt string_of_heap_ann)) ann_r0 no_pos;
    x_tinfo_hp (add_str "annl:" (pr_opt string_of_heap_ann)) ann_l0 no_pos;
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
                    (* x_tinfo_hp (add_str "CP.TempRes:" (Cprinter.string_of_imm)) ann_l no_pos; *)
                    (* x_tinfo_hp (add_str "pure0:" (Cprinter.string_of_mix_formula)) pure0 no_pos; *)
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
  (* if (!Globals.allow_imm) || (!Globals.allow_field_ann) then *)
    let rec helper ctx = 
      match ctx with
        | Ctx(es) -> Ctx(restore_tmp_ann_es es)
        | OCtx(c1, c2) ->
	      let nc1 = helper c1 in
	      let nc2 = helper c2 in
	      OCtx(nc1, nc2)
    in helper ctx
  (* else ctx *)

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
          let new_pimm = apply_f_to_annot_arg f (List.map fst h.CF.h_formula_view_annot_arg) in 
          let new_f = CF.ViewNode {h with h_formula_view_imm = List.hd (restore_tmp_ann [h.CF.h_formula_view_imm] pure0);
              h_formula_view_annot_arg = CP.update_positions_for_annot_view_params new_pimm h.CF.h_formula_view_annot_arg} in
          let new_f = maybe_replace_w_empty new_f in
          new_f
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

and restore_tmp_ann_struc_formula sf = 
  let rec helper sf  = 
    match sf with
      | EBase f   -> EBase {f with formula_struc_base = restore_tmp_ann_formula f.formula_struc_base }
      | EList l   -> EList (map_l_snd helper l)
      | ECase c   -> ECase {c with formula_case_branches = List.map (fun (c1,c2)-> (c1, helper c2)) c.formula_case_branches;}
      | EAssume b -> EAssume {b with
	    formula_assume_simpl = restore_tmp_ann_formula b.formula_assume_simpl;
	    formula_assume_struc = helper b.formula_assume_struc;}
      | EInfer b  -> EInfer {b with  formula_inf_continuation = helper b.formula_inf_continuation}
  in helper sf

(* substitute *)
and subs_crt_holes_list_ctx (ctx : list_context) : list_context = 
  match ctx with
    | FailCtx _ -> ctx
    | SuccCtx(cl) ->
	  SuccCtx(List.map (subs_crt_holes_ctx 12 ) cl)

and subs_crt_holes_list_failesc_ctx ctx = 
  transform_list_failesc_context (idf, idf, (fun es -> Ctx (subs_holes_es es))) ctx

and subs_crt_holes_ctx_x (ctx : context) : context = 
  match ctx with
    | Ctx(es) -> Ctx(subs_holes_es es)
    | OCtx(c1, c2) ->
	  let nc1 = subs_crt_holes_ctx_x c1 in
	  let nc2 = subs_crt_holes_ctx_x c2 in
	  OCtx(nc1, nc2)

and subs_crt_holes_ctx i (ctx : context) : context = 
  let pr = Cprinter.string_of_context in
  Debug.no_1_num i "subs_crt_holes_ctx" pr pr subs_crt_holes_ctx_x ctx

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

let rec normalize_h_formula_dn auxf (h : CF.h_formula) : CF.h_formula * (CP.formula list) * ((Globals.ident * VarGen.primed) list) = 
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

let push_node_imm_to_field_imm_x (h: CF.h_formula):  CF.h_formula  * (CP.formula list) * ((Globals.ident * VarGen.primed) list) =
  match h with
    | CF.DataNode dn -> 
          let ann_node = dn.CF.h_formula_data_imm in
          let new_ann_param, constr, new_vars =
            if (List.length  dn.CF.h_formula_data_param_imm == List.length  dn.CF.h_formula_data_arguments) then
              List.fold_left (fun (params, constr, vars) p_ann ->
                  let new_p_ann,nc,nv = merge_imm_ann ann_node p_ann in
                  (params@[new_p_ann], nc@constr, nv@vars)
              ) ([],[],[]) dn.CF.h_formula_data_param_imm
            else
              let () = report_warning no_pos ("data field imm not set. Setting it now to be the same as node lvl imm. ") in
              let new_ann_param = List.map (fun _ -> ann_node) dn.CF.h_formula_data_arguments in
              (new_ann_param, [], [])
          in 
          let new_ann_node =  if (List.length  dn.CF.h_formula_data_param_imm > 0) then CP.ConstAnn(Mutable) else ann_node in
          let n_dn = CF.DataNode{dn with  CF.h_formula_data_imm = new_ann_node;
 	      CF.h_formula_data_param_imm = new_ann_param;} in
          (n_dn, constr, new_vars)
    | _ -> (h, [], [])

let push_node_imm_to_field_imm caller (h:CF.h_formula) : CF.h_formula * (CP.formula list) * ((Globals.ident * VarGen.primed) list) =
  let pr = Cprinter.string_of_h_formula in
  let pr_out = pr_triple Cprinter.string_of_h_formula pr_none pr_none in
  Debug.no_1_num caller "push_node_imm_to_field_imm" pr pr_out push_node_imm_to_field_imm_x h 

let normalize_field_ann_heap_node_x (h:CF.h_formula): CF.h_formula  * (CP.formula list) * ((Globals.ident * VarGen.primed) list) =
  if (!Globals.allow_field_ann) then
  (* if false then *)
    let h, constr, new_vars = normalize_h_formula_dn (push_node_imm_to_field_imm 1) h in
    (h,constr,new_vars)
  else (h,[],[])

let normalize_field_ann_heap_node (h:CF.h_formula): CF.h_formula * (CP.formula list) * ((Globals.ident * VarGen.primed) list) =
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

let normalize_field_ann_struc_formula_x (sf:CF.struc_formula): CF.struc_formula =
  if (!Globals.allow_field_ann) then
  (* if (false) then *)
    let rec helper sf = 
    match sf with
      | EBase f   -> EBase {f with 
            formula_struc_base = normalize_field_ann_formula f.formula_struc_base  }
      | EList l   -> EList  (map_l_snd (fun c->  helper c ) l)
      | ECase f   -> ECase {f with formula_case_branches = map_l_snd (fun c->  helper c) f.formula_case_branches;}
      | EAssume f -> EAssume {f with
	    formula_assume_simpl = normalize_field_ann_formula f.formula_assume_simpl;
	    formula_assume_struc = helper f.formula_assume_struc;}
      | EInfer f  -> EInfer {f with formula_inf_continuation = helper f.formula_inf_continuation } 
    in helper sf
  else sf

let normalize_field_ann_struc_formula (h:CF.struc_formula): CF.struc_formula =
  let pr = Cprinter.string_of_struc_formula in
  Debug.no_1 "normalize_field_ann_struc_formula" pr pr normalize_field_ann_struc_formula_x h

let update_read_write_ann (ann_from: CP.ann) (ann_to: CP.ann): CP.ann  =
  match ann_from with
    | CP.ConstAnn(Mutable)	-> ann_from
    | CP.ConstAnn(Accs)    -> ann_to
    | CP.ConstAnn(Imm)
    | CP.ConstAnn(Lend)
    | CP.TempAnn _
    | CP.PolyAnn(_)        -> 
          if subtype_ann 5 ann_from ann_to then ann_from else ann_to
    | CP.TempRes _ | CP.NoAnn     -> ann_to

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

let merge_imm_for_view eq a1l a2l =
  match a1l,a2l with
    | [], []      -> []
    | [], t::_    -> a2l
    | t::_, []    -> a1l
    | t1::_,t2::_ -> if eq a1l a2l then a1l 
      else failwith "Imm: view should preserve the same imm map"

let update_arg_imm_for_view fimm dimm param_ann emap =
  let param_ann = List.fold_left (fun acc a -> acc@(CP.fv_ann a)) [] param_ann in
  match fimm with
    | CP.ConstAnn _ -> 
          let imm = 
            match dimm with
              | CP.PolyAnn _ -> dimm
              | _            -> fimm in 
          imm
    | CP.PolyAnn sv ->
            if (Gen.BList.mem_eq CP.eq_spec_var sv param_ann) then fimm
            else 
              let elist = sv::(CP.EMapSV.find_equiv_all sv emap) in 
              let plst  = Gen.BList.intersect_eq CP.eq_spec_var param_ann elist in
              if not (Gen.is_empty plst) then CP.mkPolyAnn (List.hd plst)
              else fimm
    | _ -> fimm

let collect_view_imm_from_h_formula f param_ann data_name emap = (* param_ann *)
  let rec helper  f param_ann data_name emap =
    match f with
      | CF.DataNode {h_formula_data_param_imm = pimm; h_formula_data_imm = imm; h_formula_data_name = name}-> 
            if name = data_name then
              List.map (fun p -> update_arg_imm_for_view p imm param_ann emap) pimm
            else []
      | CF.ViewNode h -> []
      | CF.Star {h_formula_star_h1 = h1; h_formula_star_h2 = h2}
      | CF.Conj {h_formula_conj_h1 = h1; h_formula_conj_h2 = h2}
      | CF.ConjStar {h_formula_conjstar_h1 = h1; h_formula_conjstar_h2 = h2}
      | CF.ConjConj {h_formula_conjconj_h1 = h1; h_formula_conjconj_h2 = h2}
      | CF.Phase    {h_formula_phase_rd = h1; h_formula_phase_rw = h2}
          -> 
            let a1 = helper h1 param_ann data_name emap in
            let a2 = helper h2 param_ann data_name emap in
            merge_imm_for_view CP.eq_ann_list a1 a2
      | _ -> []
  in  helper f param_ann data_name emap


let collect_view_imm_from_formula f param_ann data_name = (* param_ann *)
  let rec helper  f param_ann data_name = 
    match f with 
      | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) ->
	    let a1 = helper f1 param_ann data_name in
	    let a2 = helper f2 param_ann data_name in
	    let anns = merge_imm_for_view CP.eq_ann_list a1 a2 in
            anns
      | Base   ({formula_base_heap   = h; formula_base_pure   = p})
      | Exists ({formula_exists_heap = h; formula_exists_pure = p}) ->
            let emap = build_eset_of_conj_formula (MCP.pure_of_mix p) in
            let anns = collect_view_imm_from_h_formula h param_ann data_name emap in
            anns
  in helper f param_ann data_name

let collect_view_imm_from_struc_formula sf param_ann data_name = 
  let rec helper sf param_ann data_name = 
    match sf with
      | EBase f   -> collect_view_imm_from_formula (f.formula_struc_base) param_ann data_name
      | EList l   -> List.fold_left (fun acc l ->  merge_imm_for_view CP.eq_ann_list acc l) [] (map_snd_only (fun c->  helper c param_ann data_name) l)
      | ECase f   -> List.fold_left (fun acc l ->  merge_imm_for_view CP.eq_ann_list acc l) [] (map_snd_only (fun c->  helper c param_ann data_name)  f.formula_case_branches)
      | EAssume f ->
            let v_imm_lst = collect_view_imm_from_formula f.formula_assume_simpl param_ann data_name in
            merge_imm_for_view CP.eq_ann_list [] (helper  f.formula_assume_struc param_ann data_name);
      | EInfer f  -> helper f.formula_inf_continuation param_ann data_name
  in helper sf param_ann data_name 

let collect_view_imm_from_case_struc_formula sf param_ann data_name def_ann = (* def_ann *)
  let f_lst = snd (List.split (sf.CF.formula_case_branches)) in
  let final_data_ann = List.fold_left (fun acc f->
      let data_ann = collect_view_imm_from_struc_formula f param_ann data_name in
      merge_imm_for_view CP.eq_ann_list acc data_ann
  ) [] f_lst in
  final_data_ann

(* andreeac TODOIMM use wrapper below *)
let collect_annot_imm_info_in_formula annot_args f data_name ddefs =
  let ddef = I.look_up_data_def_raw ddefs data_name in
  let def_ann  = List.map (fun f -> CP.imm_ann_bot ) ddef.I.data_fields in
  let ann_final = 
    if not (!Globals.allow_field_ann) then def_ann
    else
      let ann_params = CP.annot_arg_to_imm_ann_list annot_args in
      let ann_params = collect_view_imm_from_struc_formula f ann_params data_name (* def_ann *) in
      ann_params
  in
  let annot_args = CP.imm_ann_to_annot_arg_list  ann_final in
  annot_args

let initialize_positions_for_args (aa: CP.annot_arg list) (wa: CP.view_arg list) cf data_name ddefs =
  let wa_pos = CP.initialize_positions_for_view_params wa in
  let aa = collect_annot_imm_info_in_formula aa cf data_name ddefs in
  let aa_pos = CP.update_positions_for_view_params_x aa wa_pos in
  aa_pos, wa_pos

(* let collect_view_imm_from_h_iformula f param_ann data_name emap = (\* param_ann *\) *)
(*   let rec helper  f param_ann data_name emap = *)
(*     match f with *)
(*       | IF.HeapNode2 {IF.h_formula_data_imm_param = pimm; IF.h_formula_heap_imm = imm; IF.h_formula_heap_name = name}->  *)
(*       | IF.HeapNode  {IF.h_formula_data_imm_param = pimm; IF.h_formula_heap_imm = imm; IF.h_formula_heap_name = name}->  *)
(*             if name = data_name then *)
(*               List.map (fun p -> update_arg_imm_for_view p imm param_ann emap) pimm *)
(*             else [] *)
(*       | IF.Star {IF.h_formula_star_h1 = h1; IF.h_formula_star_h2 = h2} *)
(*       | IF.Conj {IF.h_formula_conj_h1 = h1; IF.h_formula_conj_h2 = h2} *)
(*       | IF.ConjStar {IF.h_formula_conjstar_h1 = h1; IF.h_formula_conjstar_h2 = h2} *)
(*       | IF.ConjConj {IF.h_formula_conjconj_h1 = h1; IF.h_formula_conjconj_h2 = h2} *)
(*       | IF.Phase    {IF.h_formula_phase_rd = h1; IF.h_formula_phase_rw = h2} *)
(*           ->  *)
(*             let a1 = helper h1 param_ann data_name emap in *)
(*             let a2 = helper h2 param_ann data_name emap in *)
(*             merge_imm_for_view a1 a2 *)
(*       | _ -> [] *)
(*   in  helper f param_ann data_name emap *)


(* let collect_view_imm_from_iformula f param_ann data_name = (\* param_ann *\) *)
(*   let rec helper  f param_ann data_name =  *)
(*     match f with  *)
(*       | IF.Or ({IF.formula_or_f1 = f1; IF.formula_or_f2 = f2; IF.formula_or_pos = pos}) -> *)
(* 	    let a1 = helper f1 param_ann data_name in *)
(* 	    let a2 = helper f2 param_ann data_name in *)
(* 	    let anns = merge_imm_for_view a1 a2 in *)
(*             anns *)
(*       | IF.Base   ({IF.formula_base_heap   = h; IF.formula_base_pure   = p}) *)
(*       | IF.Exists ({IF.formula_exists_heap = h; IF.formula_exists_pure = p}) -> *)
(*             let emap = build_eset_of_conj_formula (MCP.pure_of_mix p) in *)
(*             let anns = collect_view_imm_from_h_iformula h param_ann data_name emap in *)
(*             anns *)
(*   in helper f param_ann data_name *)

(* let collect_view_imm_from_struc_iformula sf param_ann data_name =  *)
(*   let rec helper sf param_ann data_name =  *)
(*     match sf with *)
(*       | IF.EBase f   -> collect_view_imm_from_iformula (f.IF.formula_struc_base) param_ann data_name *)
(*       | IF.EList l   -> List.fold_left (fun acc l ->  merge_imm_for_view acc l) [] (map_snd_only (fun c->  helper c param_ann data_name) l) *)
(*       | IF.ECase f   -> List.fold_left (fun acc l ->  merge_imm_for_view acc l) [] (map_snd_only (fun c->  helper c param_ann data_name)  f.IF.formula_case_branches) *)
(*       | IF.EAssume f -> *)
(*             let v_imm_lst = collect_view_imm_from_iformula f.IF.formula_assume_simpl param_ann data_name in *)
(*             merge_imm_for_view [] (helper  f.IF.formula_assume_struc param_ann data_name); *)
(*       | IF.EInfer f  -> helper f.IF.formula_inf_continuation param_ann data_name *)
(*   in helper sf param_ann data_name  *)

(* andreeac TODOIMM use wrapper below *)
(* let collect_annot_imm_info_in_iformula annot_args f data_name ddefs = *)
(*   let ddef = I.look_up_data_def_raw ddefs data_name in *)
(*   let def_ann  = List.map (fun f -> CP.imm_ann_bot ) ddef.I.data_fields in *)
(*   let ann_final = *)
(*     if not (!Globals.allow_field_ann) then def_ann *)
(*     else *)
(*       let ann_params = CP.annot_arg_to_imm_ann_list annot_args in *)
(*       let ann_params = collect_view_imm_from_struc_iformula f ann_params data_name (\* def_ann *\) in *)
(*       ann_params *)
(*   in *)
(*   let annot_args = CP.imm_ann_to_annot_arg_list  ann_final in *)
(*   annot_args *)

let collect_view_imm_from_h_iformula h  data_name = (* [] *)
  let rec helper  f data_name =
    match f with
      | IF.HeapNode2 {IF.h_formula_heap2_imm_param = pimm; (* IF.h_formula_heap_imm = imm; *) IF.h_formula_heap2_name = name}
      | IF.HeapNode  {IF. h_formula_heap_imm_param = pimm; (* IF.h_formula_heap_imm = imm; *) IF.h_formula_heap_name = name}->
            if name = data_name then (ann_opt_to_ann_lst pimm Ipure.imm_ann_bot)
              (* List.map (fun p -> update_arg_imm_for_view p imm param_ann emap) pimm *)
            else []
      | IF.Star {IF.h_formula_star_h1 = h1; IF.h_formula_star_h2 = h2}
      | IF.Conj {IF.h_formula_conj_h1 = h1; IF.h_formula_conj_h2 = h2}
      | IF.ConjStar {IF.h_formula_conjstar_h1 = h1; IF.h_formula_conjstar_h2 = h2}
      | IF.ConjConj {IF.h_formula_conjconj_h1 = h1; IF.h_formula_conjconj_h2 = h2}
      | IF.Phase    {IF.h_formula_phase_rd = h1; IF.h_formula_phase_rw = h2}
          ->
            let a1 = helper h1 data_name in
            let a2 = helper h2 data_name in
            merge_imm_for_view Ipure.eq_ann_list a1 a2
      | _ -> []
  in  helper h data_name 

let collect_view_imm_from_iformula f data_name = 
  let rec helper  f data_name =
    match f with
      | IF.Or ({IF.formula_or_f1 = f1; IF.formula_or_f2 = f2; IF.formula_or_pos = pos}) ->
            let a1 = helper f1 data_name in
            let a2 = helper f2 data_name in
            let anns = merge_imm_for_view  Ipure.eq_ann_list a1 a2 in
            anns
      | IF.Base   ({IF.formula_base_heap   = h; IF.formula_base_pure   = p})
      | IF.Exists ({IF.formula_exists_heap = h; IF.formula_exists_pure = p}) ->
            (* let emap = build_eset_of_conj_formula (MCP.pure_of_mix p) in *)
            let anns = collect_view_imm_from_h_iformula h data_name in
            anns
  in helper f data_name

let collect_imm_from_struc_iformula sf data_name =
  let rec helper sf data_name =
    match sf with
      | IF.EBase f   -> collect_view_imm_from_iformula (f.IF.formula_struc_base) data_name
      | IF.EList l   -> List.fold_left (fun acc l ->  merge_imm_for_view Ipure.eq_ann_list acc l) [] (map_snd_only (fun c->  helper c data_name) l)
      | IF.ECase f   -> List.fold_left (fun acc l ->  merge_imm_for_view Ipure.eq_ann_list acc l) [] (map_snd_only (fun c->  helper c data_name)  f.IF.formula_case_branches)
      | IF.EAssume f ->
            let v_imm_lst = collect_view_imm_from_iformula f.IF.formula_assume_simpl data_name in
            merge_imm_for_view Ipure.eq_ann_list [] (helper  f.IF.formula_assume_struc data_name);
      | IF.EInfer f  -> helper f.IF.formula_inf_continuation data_name
  in helper sf data_name

let add_position_to_imm_ann (a: Ipure.ann) (vp_pos: (ident * int) list) = 
  let a_pos = 
    match a with
      | Ipure.ConstAnn _        -> (a,0)
      | Ipure.PolyAnn ((v,_),_) -> 
            let ff p = if (String.compare (fst p) v == 0) then Some (a,snd p) else None in
            let found = Gen.BList.list_find ff vp_pos in
            match found with
              | Some p -> p
              | None   -> (a,0)
  in
  a_pos

let icollect_imm f vparam data_name ddefs =
  try
    let ddef = I.look_up_data_def_raw ddefs data_name in
    let def_ann  = List.map (fun f -> (Ipure.imm_ann_bot, 0) ) ddef.I.data_fields in
    let ann_final =
      if not (!Globals.allow_field_ann) then def_ann
      else
        let ann_params = collect_imm_from_struc_iformula f data_name (* def_ann *) in
        let vp_pos = CP.initialize_positions_for_view_params vparam in
        let ann_pos = List.map (fun a ->  add_position_to_imm_ann a vp_pos) ann_params in
        ann_pos
    in
    ann_final
  with Not_found -> [] (* this is for prim pred *)

let icollect_imm f vparam data_name ddefs =
  Debug.no_3 "icollect_imm" Iprinter.string_of_struc_formula 
      (pr_list pr_id) pr_id (pr_list (pr_pair Iprinter.string_of_imm string_of_int)) (fun _ _ _ -> icollect_imm f vparam data_name ddefs) f vparam data_name

let split_view_args view_args vdef:  CP.spec_var list * 'a list * (CP.annot_arg * int) list * (CP.view_arg * int) list  =
  (* TODO: normalize the unused ann consts  *)
  (* retrieve imm_map from I.view_decl *)
  (* let view_vars_gen = CP.sv_to_view_arg_list sv in *)
  let view_arg_lbl =  try (List.combine view_args (fst vdef.I.view_labels))
  with  Invalid_argument _ -> failwith "Immutable.ml, split_view_args: error while combining view args with labels 1" in
  let ann_map_pos = vdef.I.view_imm_map in
  let () = x_tinfo_hp (add_str "imm_map:" (pr_list (pr_pair Iprinter.string_of_imm string_of_int))) ann_map_pos no_pos in
  (* create list of view_arg*pos  *)
  let vp_pos = CP.initialize_positions_for_view_params view_arg_lbl in
  let view_args_pos = List.map (fun ((va,_),pos) -> (va,pos)) vp_pos in
  let annot_arg, vp_pos = List.partition (fun (vp,pos) -> List.exists (fun (_,p) -> p == pos ) ann_map_pos) vp_pos in
  let vp_lbl, _ = List.split vp_pos in  (* get rid of positions *)
  let vp, lbl   = List.split vp_lbl in  (* separate lbl from args *)
  let svp = CP.view_arg_to_sv_list vp in 
  let annot_arg_pos = List.map (fun ((a, _), pos) -> (a, pos)) annot_arg in (* get rid of lbl *)
  let annot_arg,pos = List.split annot_arg_pos in
  let imm_arg = CP.view_arg_to_imm_ann_list annot_arg in 
  let imm_arg_pos = try
    let imm_arg = 
      if imm_arg = [] then List.map (fun _ -> CP.ConstAnn Mutable) pos
      else imm_arg
    in
    List.combine imm_arg pos 
  with  Invalid_argument _ -> failwith "Immutable.ml, split_view_args: error while combining imm_arg with pos" in
  (* create an imm list following the imm_map, updated with proper values from the list of params *)
  let anns_pos = List.map (fun (a, pos) -> 
      try  List.find (fun (_, vpos) -> vpos == pos) imm_arg_pos
      with Not_found -> (iformula_ann_to_cformula_ann a, pos) )  ann_map_pos in
  let anns, pos = List.split anns_pos in
  let annot_arg = CP.imm_ann_to_annot_arg_list anns in
  let annot_args_pos = try List.combine annot_arg pos 
  with  Invalid_argument _ -> failwith "Immutable.ml, split_view_args: error while combining annot_arg with pos 2" in
  svp, lbl, annot_args_pos, view_args_pos

let split_view_args view_args vdef:  CP.spec_var list * 'a list * (CP.annot_arg * int) list * (CP.view_arg * int) list  =
  let pr = pr_quad  Cprinter.string_of_spec_var_list pr_none (pr_list (pr_pair Cprinter.string_of_annot_arg string_of_int)) (pr_list (pr_pair Cprinter.string_of_view_arg string_of_int)) in 
  Debug.no_1 "split_view_args" Cprinter.string_of_view_arg_list pr (fun _ -> split_view_args view_args vdef) view_args

let split_sv sv vdef:  CP.spec_var list * 'a list * (CP.annot_arg * int) list * (CP.view_arg * int) list  =
  (* retrieve imm_map from I.view_decl *)
  let view_vars_gen = CP.sv_to_view_arg_list sv in
  split_view_args view_vars_gen vdef

let split_sv sv vdef:  CP.spec_var list * 'a list * (CP.annot_arg * int) list * (CP.view_arg * int) list  =
  let pr = pr_quad  Cprinter.string_of_spec_var_list pr_none (pr_list (pr_pair Cprinter.string_of_annot_arg string_of_int)) (pr_list (pr_pair Cprinter.string_of_view_arg string_of_int)) in 
  Debug.no_1 "split_sv" Cprinter.string_of_spec_var_list pr (fun _ -> split_sv sv vdef) sv

let initialize_imm_args args =
  List.map (fun _ -> Some (Ipure.ConstAnn(Mutable))) args

let propagate_imm_formula sf view_name (imm : CP.ann)  (imm_p: (CP.annot_arg * CP.annot_arg) list) =
  let res = propagate_imm_formula sf view_name imm imm_p in
  normalize_field_ann_formula res

let propagate_imm sf view_name (imm : CP.ann)  (imm_p: (CP.annot_arg * CP.annot_arg) list) =
  let res = propagate_imm_struc_formula sf view_name imm imm_p in
  normalize_field_ann_struc_formula res

(* ===============================  below is for merging aliased nodes ================================= *)
(* ================== ex: x::node<a,y>@A * y::node<b,z> & x=y ----> y::node<b,z> & x=y ================= *)

let crop_incompatible_disjuncts unfolded_f dn emap =
  let rec helper f = 
    match f with
      | Base   ({formula_base_heap = h; formula_base_pure = p; })
      | Exists ({formula_exists_heap = h; formula_exists_pure = p; }) ->
            let (subs,_) = CP.get_all_vv_eqs (MCP.pure_of_mix p) in
            let emap2 = CP.EMapSV.build_eset subs in
            let emap  = CP.EMapSV.merge_eset emap emap2 in
            let sv, ident = dn.h_formula_data_node, dn.h_formula_data_name in
            let aset  = sv::(CP.EMapSV.find_equiv_all sv emap) in
            if  h_formula_contains_node h aset ident then Some f
            else None
      | Or orf ->
            let f1 = helper orf.formula_or_f1 in
            let f2 = helper orf.formula_or_f2 in
            match f1,f2 with
              | Some f1, Some f2 -> Some (Or {orf with formula_or_f1 = f1; formula_or_f2 = f2})
              | Some f, None
              | None, Some f -> Some f
              | None, None   -> None

  in helper unfolded_f

let unfold_and_norm vn vh dn emap unfold_fun qvars emap =
  let v =  vn.h_formula_view_node in
  let aset = v::(CP.EMapSV.find_equiv_all v emap) in           
  let uf = 0 in               (* is 0 ok or can it cause infinite unroll? *)
  let unfolded_f = unfold_fun vh aset v uf in
  let ret_f = push_exists qvars unfolded_f in
  let ret_f = crop_incompatible_disjuncts unfolded_f dn emap in
  ret_f

(* return (compatible_flag, to_keep_node) *)
let compatible_at_field_lvl imm1 imm2 h1 h2 unfold_fun qvars emap = 
  let comp, ret_h, unfold_f =
    match h1, h2 with
      | DataNode dn1, DataNode dn2 ->
            let p1 = List.combine dn1.h_formula_data_arguments dn1.h_formula_data_param_imm in
            let p2 = List.combine dn2.h_formula_data_arguments dn2.h_formula_data_param_imm in
            let imm = List.combine p1 p2 in
            let (comp, updated_elements) = List.fold_left (fun (comp,lst) ((a1,i1), (a2,i2)) ->
                match i1, i2 with
                  | CP.ConstAnn(Accs), a -> (true && comp, lst@[(a2,i2)])
                  | a, CP.ConstAnn(Accs) -> (true && comp, lst@[(a1,i1)])
                  | _, _ ->
                        Debug.print_info "Warning: " "possible unsoundess (* between overlapping heaps) " no_pos;
                        (false && comp, lst)
            ) (true,[]) imm in
            let args, pimm = List.split updated_elements in
            (* !!!! Andreea: to check how to safely merge two data nodes. Origins and Original info (and other info) abt dn2 is lost *)
            let dn = DataNode {dn1 with h_formula_data_arguments = args; h_formula_data_param_imm = pimm;} in
            (comp, dn, None)
      | ViewNode vn1, ViewNode vn2 -> Debug.print_info "Warning: " "combining two views not yet implemented" no_pos;
            (true, h1, None)
      | DataNode dn, ((ViewNode vn) as vh)
      | ((ViewNode vn) as vh), DataNode dn ->
            let pimm = CP.annot_arg_to_imm_ann_list_no_pos vn.h_formula_view_annot_arg in
            let comp = 
              if (List.length dn.h_formula_data_param_imm == List.length (pimm) ) then 
                let imm = List.combine dn.h_formula_data_param_imm pimm in
                let comp = List.fold_left (fun acc (i1,i2) -> 
                    match i1, i2 with
                      | CP.ConstAnn(Accs), a -> true && acc
                      | a, CP.ConstAnn(Accs) -> true && acc
                      | _, _ -> false
                ) true imm in
                comp
              else false in
            let () = x_binfo_hp (add_str "compatible for merging:" string_of_bool) comp no_pos in
            if comp then
              let ret_f = unfold_and_norm vn vh dn emap unfold_fun qvars emap in
              (comp, h1, ret_f)
            (* incompatible for merging *)
            else (comp, h1, None)
      | _, _ -> 
            Debug.print_info "Warning: " "combining different kind of nodes not yet implemented" no_pos; 
            (false, h1, None)
  in (comp, ret_h, unfold_f)

let compatible_at_field_lvl imm1 imm2 h1 h2 unfold_fun qvars emap = 
  let pr = Cprinter.string_of_h_formula in
  let pr_out3 = pr_opt Cprinter.string_of_formula in
  Debug.no_2 "compatible_at_field_lvl" pr pr (pr_triple string_of_bool pr pr_out3) (fun _ _ -> compatible_at_field_lvl imm1 imm2 h1 h2 unfold_fun qvars emap) h1 h2 


(* return (compatible_flag, to_keep_node) *)
let compatible_at_node_lvl prog imm1 imm2 h1 h2 unfold_fun qvars emap =
  let comp, ret_h =
    if (isAccs imm2) then (true, h1)
    else  if (isAccs imm1) then (true, h2)
    else (false, h1) in
  let compatible, keep_h, struc =
    (match h1, h2 with
      | DataNode _, DataNode _
      | ViewNode _, ViewNode _ -> (comp, ret_h, None)
      | ((DataNode dn) as dh), ((ViewNode vn) as vh)
      | ((ViewNode vn) as vh), ((DataNode dn) as dh) ->
            if comp then
              let ret_f = unfold_and_norm vn vh dn emap unfold_fun qvars emap in
              (comp, dh, ret_f)
              (* (comp, dh, None) *)
            else (comp, ret_h, None)
      | _, _ -> (comp, ret_h, None)) in
  (compatible, keep_h, struc)

let compatible_nodes prog imm1 imm2 h1 h2 unfold_fun qvars emap = 
  if (!Globals.allow_field_ann) then compatible_at_field_lvl imm1 imm2 h1 h2 unfold_fun qvars emap
  else compatible_at_node_lvl prog imm1 imm2 h1 h2 unfold_fun qvars emap

let compatible_nodes prog imm1 imm2 h1 h2 unfold_fun qvars emap =
  let pr = Cprinter.string_of_h_formula in
  let pr_out3 = pr_opt Cprinter.string_of_formula in
  Debug.no_2 "compatible_nodes" pr pr (pr_triple string_of_bool pr pr_out3) (fun _ _ ->  compatible_nodes prog imm1 imm2 h1 h2 unfold_fun qvars emap ) h1 h2

let partition_eqs_subs lst1 lst2 quantif =
  let eqs_lst = List.combine lst1 lst2 in
  let eqs_lst = List.map (fun (a,b) -> 
      if Gen.BList.mem_eq CP.eq_spec_var a quantif then (a,b)
      else if Gen.BList.mem_eq CP.eq_spec_var b quantif then (b,a)
      else (a,b) ) eqs_lst in
  let eqs_lst = List.fold_left (fun acc (a,b) -> if CP.eq_spec_var a b then acc else acc@[(a,b)]) [] eqs_lst in
  let subs, eqs_lst = List.partition (fun (a,b) ->
      Gen.BList.mem_eq CP.eq_spec_var a quantif ||  Gen.BList.mem_eq CP.eq_spec_var b quantif 
  ) eqs_lst in 
  (* let eqs = List.map (fun (a,b) -> CP.mkEqVar a b no_pos) eqs_lst in *)
  (eqs_lst, subs)

let norm_abs_node h p xpure =
  if (isAccs (get_imm h)) then
    let xpured, _, _ = x_add xpure h p 0 in (* 0 or 1? *)(* !!!! add the xpure to pure *)
    (HEmp, Some (MCP.pure_of_mix xpured))
  else
    (h, None)  

(* assume nodes are aliased *)
let merge_two_view_nodes prog vn1 vn2 h1 h2 prog quantif unfold_fun qvars emap =
  let comp, ret_h, _ = compatible_nodes prog vn1.h_formula_view_imm vn2.h_formula_view_imm h1 h2 unfold_fun qvars emap in
  let same_view = (String.compare vn1.h_formula_view_name vn2.h_formula_view_name = 0) in
  let comp_view =  same_view &&  not(Cfutil.is_view_node_segmented vn1 prog) in
  (* comp_view ---> true when views are compatible (same view def + view def is not segmented) *)
  if comp  && comp_view then
    let (eqs, subs) = partition_eqs_subs vn1.h_formula_view_arguments vn2.h_formula_view_arguments quantif in
    ([ret_h], eqs, subs, [])                      (* should I also add the pure of merged (@A) node? *)
    (* ([], []) *)
  else
    (* let xpure1 =  *)
    (* remove node annotated with @A if it's not compatible for merging *)
    if (isAccs vn1.h_formula_view_imm) then  ([h2], [], [], [])
    else if (isAccs vn2.h_formula_view_imm) then  ([h1], [], [], [])
    else ([h1;h2], [], [], [])

(* assume nodes are aliased *)
let merge_data_node_w_view_node prog dn1 vn2 h1 h2 quantif unfold_fun qvars emap =
  let comp, ret_h, struc = compatible_nodes prog dn1.h_formula_data_imm vn2.h_formula_view_imm h1 h2 unfold_fun qvars emap in
  if comp then
    (* let (eqs, subs) = partition_eqs_subs dn1.h_formula_data_arguments vn2.h_formula_view_arguments quantif in *)
    (* add here merge code *)
    match struc with
      | None   -> ([ret_h], [], [],[])  
      | Some s -> ([ret_h], [], [],[s])  
  else
    if (isAccs dn1.h_formula_data_imm) then  ([h2], [], [], [])
    else if (isAccs vn2.h_formula_view_imm) then  ([h1], [], [], [])
    else ([h1;h2], [], [], [])

let merge_data_node_w_view_node prog dn1 vn2 h1 h2 quantif unfold_fun qvars emap =
  let pr3 = Cprinter.string_of_h_formula in
  let pr1 d = pr3 (DataNode dn1) in
  let pr2 v = pr3 (ViewNode vn2) in
  let pr_out = pr_quad (pr_list pr3) pr_none pr_none pr_none in
  Debug.no_4 "merge_data_node_w_view_node" pr1 pr2 pr3 pr3 pr_out (fun _ _ _ _ -> merge_data_node_w_view_node prog dn1 vn2 h1 h2 quantif unfold_fun qvars emap) dn1 vn2 h1 h2

(* assume nodes are aliased *)
let merge_two_data_nodes prog dn1 dn2 h1 h2 quantif unfold_fun qvars emap =
  let comp, ret_h, _ = compatible_nodes prog dn1.h_formula_data_imm dn2.h_formula_data_imm h1 h2 unfold_fun qvars emap in
  let comp_data = comp && (String.compare dn1.h_formula_data_name dn2.h_formula_data_name = 0) in
  if comp_data then
    let (eqs, subs) = partition_eqs_subs dn1.h_formula_data_arguments dn2.h_formula_data_arguments quantif in
    ([ret_h], eqs, subs, [])
  else
    if (isAccs dn1.h_formula_data_imm) then  ([h2], [], [], [])
    else if (isAccs dn2.h_formula_data_imm) then  ([h1], [], [], [])
    else ([h1;h2], [], [], [])

(* merged two nodes and return merged node and resulted equalities. *)
let merge_two_nodes h1 h2 prog quantif unfold_fun qvars emap =
  match h1, h2 with
    | [(DataNode dn1) as h1], DataNode dn2  -> merge_two_data_nodes prog dn1 dn2 h1 h2 quantif unfold_fun qvars emap
    | [(ViewNode vn) as h2], ((DataNode dn) as h1)
    | [(DataNode dn) as h1], ((ViewNode vn) as h2) ->  merge_data_node_w_view_node prog dn vn h1 h2 quantif unfold_fun qvars emap (* ([h1;h2], []) *)
    | [(ViewNode vn1) as h1], ViewNode vn2 -> merge_two_view_nodes prog vn1 vn2 h1 h2 prog quantif unfold_fun qvars emap
(* ([h1;h2], []) *)
    | _, _ -> (h1@[h2], [], [], [])

(* let get_node_var h =  *)

let defined_node h1 = 
  match h1 with
    | DataNode _
    | ViewNode _
    | ThreadNode _ -> true
    | _ -> false

let aliased_nodes h1 h2 emap =
  if (defined_node h1) && (defined_node h2) then
    CP.EMapSV.is_equiv emap (get_node_var h1) (get_node_var h2)
  else
    false                               (* assume that if node is undefined, it does not have an aliased *)

let merge_list_w_node node lst emap prog quantif unfold_fun qvars = 
  let aliases, disj = List.partition (fun n -> aliased_nodes node n emap) lst in 
  let new_h, eqs, subs, structs = List.fold_left (fun (a, e, s, structs) n -> 
      let merged, eqs, subs, struc =  merge_two_nodes a n prog quantif unfold_fun qvars emap in
      (merged, e@eqs, subs@s, struc@structs)
  ) ([node],[], [], []) aliases in (* here!! *)
  (new_h, disj, eqs, subs, structs)

let merge_alias_nodes_h_formula_helper prog p lst emap quantif xpure unfold_fun qvars =
  let rec helper lst emap = 
    match lst with 
      | []   -> ([], [], [], true, [])
      (* | [h]  -> let new_h, pure = norm_abs_node h p xpure in  *)
      (*   ([new_h], (opt_to_list pure)) *)  (* andreeac: uncomment this 2 lines if you wnat to replace @A node with HEmp & xpure*)
      | h::t ->
            let updated_head, updated_tail, eqs_lst, subs_lst, struc_lst = merge_list_w_node h t emap prog quantif unfold_fun qvars in
            let (fixpoint, emap) = List.fold_left 
              ( fun (fixpoint,emap) (a,b) -> 
                  if CP.EMapSV.is_equiv emap a b then (fixpoint&&true,emap)
                  else (fixpoint&&false, CP.EMapSV.add_equiv emap a b) 
              ) (true, emap) eqs_lst in
            let fixpoint = fixpoint && (is_empty subs_lst) in
            let merged_tail, eqs_lst_tail, subs_lst_tail, fixpoint_tail, struc_tail = helper updated_tail emap  in
            (updated_head@merged_tail, eqs_lst@eqs_lst_tail, subs_lst@subs_lst_tail, fixpoint&&fixpoint_tail, struc_lst@struc_tail) in
  helper lst emap

(* merge aliased nodes 
 * return merged node and resulted qualities. *)
let merge_alias_nodes_h_formula prog f p emap quantif xpure unfold_fun qvars = (* f *)
  match f with
    | Star _ ->
          let node_lst = split_star_h f in
          let node_lst, eqs, subs, fixpoint, struc = merge_alias_nodes_h_formula_helper prog p node_lst emap quantif xpure unfold_fun qvars in
          let updated_f = combine_star_h node_lst in
          let eqs = List.map (fun (a,b) -> CP.mkEqVar a b no_pos) eqs in
          let aux_pure  = CP.join_conjunctions eqs in
          (* substitute non-global variables in conseq *)
          let fr, t = List.split subs in
          let updated_f = subst_avoid_capture_h fr t updated_f in
          let new_pure = MCP.memoise_add_pure p aux_pure in
          let new_pure = MCP.subst_avoid_capture_memo fr t new_pure in
          (updated_f, new_pure, fixpoint, struc)
              (* | DataNode _ | ViewNode _ -> norm_abs_node f p xpure *) (* andreeac: uncommnet this line if you wnat to replace @A node with HEmp & xpure*)
    | _ -> (f, p, true, [])

let merge_alias_nodes_h_formula prog f p emap quantif xpure unfold_fun qvars = 
  let pr1 = Cprinter.string_of_h_formula in
  let pr2 = Cprinter.string_of_mix_formula in
  Debug.no_2 "merge_alias_nodes_h_formula"  pr1 pr2 (pr_quad (add_str "heap" pr1) (add_str "pure" pr2) string_of_bool pr_none) (fun _ _ -> merge_alias_nodes_h_formula prog f p emap quantif xpure unfold_fun qvars) f p

let merge_alias_nodes_formula_helper prog heapf puref quantif xpure unfold_fun qvars =
  let rec helper heapf puref = 
    let (subs,_) = CP.get_all_vv_eqs (MCP.pure_of_mix puref) in
    let emap = CP.EMapSV.build_eset subs in
    let new_f, new_p, fixpoint, struc = merge_alias_nodes_h_formula prog heapf puref emap quantif xpure unfold_fun qvars in
    (* let new_p = *)
    (*   match new_p with *)
    (*     | Some p -> MCP.memoise_add_pure puref p *)
    (*     | None   -> puref in *)
    if not fixpoint then helper new_f new_p
    else (new_f, new_p, struc)
  in helper heapf puref
      
let merge_and_combine prog f heap pure quantif xpure unfold_fun qvars mk_new_f rec_fun =
  let fl  = flow_formula_of_formula f in 
  let pos = pos_of_formula f in
  let new_f, new_p, unfold_f_lst = merge_alias_nodes_formula_helper prog heap pure quantif xpure (unfold_fun fl) qvars in
  let new_f =  mk_new_f new_f new_p in
  let ret_f = match unfold_f_lst with
    | [] -> new_f
    | _  ->
          let f = List.fold_left (fun acc f-> normalize_combine_star acc f pos) new_f unfold_f_lst in
          rec_fun f
  in ret_f 
  

let merge_alias_nodes_formula prog f quantif xpure unfold_fun =
  let rec helper f =
    let fl  = flow_formula_of_formula f in 
    let pos = pos_of_formula f in
    match f with
      | Base bf ->
            let mk_base f p = Base { bf with formula_base_heap = f;  formula_base_pure = p; } in
            merge_and_combine prog f bf.formula_base_heap bf.formula_base_pure quantif xpure unfold_fun [] mk_base helper
      | Exists ef ->
            let qvars = ef.formula_exists_qvars in
            let mk_exists f p =  Exists{ef with formula_exists_heap = f;  formula_exists_pure = p; } in
            merge_and_combine prog f ef.formula_exists_heap ef.formula_exists_pure quantif xpure unfold_fun qvars mk_exists helper
      | Or orf -> 
            Or {orf with formula_or_f1 = helper orf.formula_or_f1;  formula_or_f2 = helper orf.formula_or_f2;}
  in
  if not (!Globals.imm_merge) then f
  else helper f

let merge_alias_nodes_formula prog f quantif xpure unfold_fun =
  let pr = Cprinter.string_of_formula in
  Debug.no_1 "merge_alias_nodes_formula" pr pr (fun _ -> merge_alias_nodes_formula prog f quantif xpure unfold_fun) f

let rec merge_alias_nodes_struc_formula prog f xpure conseq unfold_fun =
  let res =
    match f with
      | EBase f ->
            let (ee, ei) = (f.formula_struc_exists, f.formula_struc_explicit_inst) in
            let quantif = if conseq then ee@ei@f.formula_struc_implicit_inst else [] in
            EBase {f with
                formula_struc_base =  merge_alias_nodes_formula prog f.formula_struc_base quantif xpure unfold_fun}
      | EList l   -> EList  (map_l_snd (fun c-> merge_alias_nodes_struc_formula prog c xpure conseq unfold_fun) l)
      | ECase f   -> ECase {f with formula_case_branches = map_l_snd (fun c-> merge_alias_nodes_struc_formula prog c xpure conseq unfold_fun) f.formula_case_branches;}
      | EAssume f -> 
            EAssume {f with
	    formula_assume_simpl = merge_alias_nodes_formula prog f.formula_assume_simpl [] xpure unfold_fun;
	    formula_assume_struc = merge_alias_nodes_struc_formula prog f.formula_assume_struc xpure conseq unfold_fun;}
      | EInfer f  -> EInfer {f with formula_inf_continuation = merge_alias_nodes_struc_formula prog f.formula_inf_continuation xpure conseq unfold_fun }
  in if not (!Globals.imm_merge) then f
  else res

let merge_alias_nodes_struc_formula prog f xpure conseq  unfold_fun =
  let pr = Cprinter.string_of_struc_formula in
  Debug.no_1 "merge_alias_nodes_struc_formula" pr pr (fun _ -> merge_alias_nodes_struc_formula prog f xpure conseq  unfold_fun) f

(* ===============================  end - merging aliased nodes ================================= *)
