(*
  Call FixBag for multi-set domain
*)

open Globals
open Gen
open Exc.GTable
open Perm
open Cpure
open Context
module M = Lexer.Make(Token.Token)
module DD = Debug

module Pr = Cprinter
module CP = Cpure
module CF= Cformula
module MCP = Mcpure
module TP = Tpdispatcher

(******************************************************************************)

(* Operators *)
let op_lt = "<" 
let op_lte = "<=" 
let op_gt = ">" 
let op_gte = ">=" 
let op_eq = "=" 
let op_neq = "!=" 
let op_and = " && "
let op_or = " || "
let op_add = "+"
let op_sub = "-"

(******************************************************************************)

let rec string_of_elems elems string_of sep = match elems with 
  | [] -> ""
  | h::[] -> string_of h 
  | h::t -> (string_of h) ^ sep ^ (string_of_elems t string_of sep)

(******************************************************************************)

let fixbag_of_spec_var x = match x with
(*  | CP.SpecVar (Named _, id, Unprimed) -> "NOD" ^ id*)
(*  | CP.SpecVar (Named _, id, Primed) -> "NODPRI" ^ id*)
(*  | CP.SpecVar (_, id, Unprimed) -> id*)
(*  | CP.SpecVar (_, id, Primed) -> "PRI" ^ id*)
  | CP.SpecVar (_, id, _) -> 
    if is_anon_var x && not (is_bag_typ x) then "v_" ^ id else id

let rec fixbag_of_exp e = match e with
  | CP.Null _ -> "null"
  | CP.Var (x, _) -> fixbag_of_spec_var x
  | CP.IConst (i, _) -> string_of_int i
(*  | CP.FConst (f, _) -> string_of_float f*)
  | CP.Add (e1, e2, _) -> fixbag_of_exp e1 ^ op_add ^ fixbag_of_exp e2 
  | CP.Subtract (e1, e2, _) -> fixbag_of_exp e2
  | CP.Bag (es, _) -> "{" ^ (string_of_elems es fixbag_of_exp ",") ^ "}"
  | CP.BagUnion (es, _) -> string_of_elems es fixbag_of_exp "+"
  | CP.BagIntersect (es, _) -> string_of_elems es fixbag_of_exp "."
  | CP.BagDiff (e1, e2, _) -> fixbag_of_exp e1 ^ op_sub ^ fixbag_of_exp e2 
  | _ -> illegal_format ("Fixbag.fixbag_of_exp: Not supported expression")

let rec fixbag_of_b_formula b =
  let (pf, _) = b in
  match pf with
    | CP.BConst (b,_) -> "{}={}"
    | CP.BVar (x, _) -> fixbag_of_spec_var x
    | CP.Lt (e1, e2, _) -> "{}={}"
    | CP.Lte (e1, e2, _) -> "{}={}"
    | CP.Gt (e1, e2, _) -> "{}={}"
    | CP.Gte (e1, e2, _) -> "{}={}"
    | CP.Eq (e1, e2, _) -> if CP.is_null e2 && not (is_bag e1) then fixbag_of_exp e1 ^op_lte^"0"
      else if CP.is_null e1 && not(is_bag e2) then fixbag_of_exp e2 ^op_lte^"0"
      else fixbag_of_exp e1 ^ op_eq ^ fixbag_of_exp e2
    | CP.Neq (e1, e2, _) -> 
      if CP.is_null e2 && not (is_bag e1) then fixbag_of_exp e1 ^op_gt^"0"
      else if CP.is_null e1 && not(is_bag e2) then fixbag_of_exp e2 ^op_gt^"0"
      else if (* !allow_pred_spec *) not !dis_ps && (List.exists is_bag_typ (CP.bfv b) || is_bag e1 || is_bag e2) then "{}={}"
      else
      if List.exists is_int_typ (CP.bfv b) then fixbag_of_exp e1 ^ op_neq ^ fixbag_of_exp e2
      else "!(" ^ fixbag_of_exp e1 ^ op_eq ^ fixbag_of_exp e2 ^ ")"
    | CP.RelForm (id,args,_) -> (fixbag_of_spec_var id) ^ "(" ^ (string_of_elems args fixbag_of_exp ",") ^ ")"
(*    | BagIn (sv, e, _) ->*)
(*    | BagNotIn (sv, e, _) -> *)
    | CP.BagSub (e1, e2, _) -> fixbag_of_exp e1 ^ op_lte ^ fixbag_of_exp e2
(*    | BagMin (sv1, sv2, _) ->*)
(*    | BagMax (sv1, sv2, _) ->*)
    | _ -> illegal_format ("Fixbag.fixbag_of_b_formula: Do not support list or boolean vars")

let rec fixbag_of_pure_formula f = match f with
  | CP.BForm ((CP.BVar (x,_),_),_) -> "$" ^ fixbag_of_spec_var x
  | CP.BForm (b,_) -> fixbag_of_b_formula b
  | CP.And (p1, p2, _) ->
    "(" ^ fixbag_of_pure_formula p1 ^ op_and ^ fixbag_of_pure_formula p2 ^ ")"
  | CP.Or (p1, p2,_ , _) ->
    "(" ^ fixbag_of_pure_formula p1 ^ op_or ^ fixbag_of_pure_formula p2 ^ ")"
  | CP.Not (p,_ , _) -> 
    begin
    match p with
    | CP.BForm ((CP.BVar (x,_),_),_) -> "!$" ^ fixbag_of_spec_var x
    | _ -> "!(" ^ fixbag_of_pure_formula p ^ ")"
    end
  | CP.Forall (sv, p,_ , _) -> illegal_format ("Fixbag.fixbag_of_pure_formula: Do not support forall")
  | CP.Exists (sv, p,_ , _) ->
    " (exists " ^ fixbag_of_spec_var sv ^ ":" ^ fixbag_of_pure_formula p ^ ") "
  | CP.AndList b -> "(" ^ String.concat op_and (List.map (fun (_,c)-> fixbag_of_pure_formula c) b) ^ ")"

let rec fixbag_of_h_formula f = match f with
  | CF.Star {CF.h_formula_star_h1 = h1; CF.h_formula_star_h2 = h2} -> 
    "(" ^ fixbag_of_h_formula h1 ^ op_and ^ fixbag_of_h_formula h2 ^ ")"
  | CF.Phase _ -> illegal_format ("Fixbag.fixbag_of_h_formula: Not supported Phase-formula")
  | CF.Conj {CF.h_formula_conj_h1 = h1; CF.h_formula_conj_h2 = h2} -> 
    "(" ^ fixbag_of_h_formula h1 ^ op_or ^ fixbag_of_h_formula h2 ^ ")"
  | CF.DataNode {CF.h_formula_data_node = sv; CF.h_formula_data_name = c;CF.h_formula_data_arguments = svs} -> 
    if CP.is_self_spec_var sv then self ^ op_gt ^ "0"
    else c ^ "(" ^ (fixbag_of_spec_var sv) ^ "," ^ (string_of_elems svs fixbag_of_spec_var ",") ^ ")"
  | CF.ViewNode {CF.h_formula_view_node = sv; CF.h_formula_view_name = c; CF.h_formula_view_arguments = svs} ->
    if CP.is_self_spec_var sv then self ^ op_gt ^ "0"
    else c ^ "(" ^  (fixbag_of_spec_var sv)  ^","^ (string_of_elems svs fixbag_of_spec_var ",")^","^ res_name ^ ")"
  | CF.HTrue -> "HTrue"
  | CF.HFalse -> "HFalse"
  | CF.HEmp -> "{}={}"
  | CF.HRel _ -> "HTrue"
  | CF.Hole _ -> illegal_format ("Fixbag.fixbag_of_h_formula: Not supported Hole-formula")
  | _ -> illegal_format("Fixbag.fixbag_of_h_formula: Not Suppoted")

let fixbag_of_mix_formula (f,l) = match f with
  | MCP.MemoF _ -> ""
  | MCP.OnePF pf -> fixbag_of_pure_formula pf

let rec fixbag_of_formula e = match e with
  | CF.Or _ -> illegal_format ("Fixbag.fixbag_of_formula: Not supported Or-formula")
  | CF.Base {CF.formula_base_heap = h; CF.formula_base_pure = p; CF.formula_base_label = b} ->
    "(" ^ fixbag_of_h_formula h ^ op_and ^ fixbag_of_mix_formula (p,b) ^ ")"
  | CF.Exists {CF.formula_exists_qvars = svs; CF.formula_exists_heap = h; 
    CF.formula_exists_pure = p; CF.formula_exists_label = b} ->  
    "(exists " ^ (string_of_elems svs fixbag_of_spec_var ",") ^ ": " ^ 
    fixbag_of_h_formula h ^ op_and ^ fixbag_of_mix_formula (p,b) ^ ")"


(******************************************************************************)

let fixbag = "fixbag4"

let syscall cmd =
  let ic, oc = Unix.open_process cmd in
  let buf = Buffer.create 16 in
  (try
     while true do
       Buffer.add_channel buf ic 1
     done
   with End_of_file -> ());
  let _ = Unix.close_process (ic, oc) in
  (Buffer.contents buf)
   
(******************************************************************************)
let rec remove_paren s n = if n=0 then "" else match s.[0] with
  | '(' -> remove_paren (String.sub s 1 (n-1)) (n-1)
  | ')' -> remove_paren (String.sub s 1 (n-1)) (n-1)
  | _ -> (String.sub s 0 1) ^ (remove_paren (String.sub s 1 (n-1)) (n-1))

let compute_inv name vars fml pf no_of_disjs =
  if not !Globals.do_infer_inv then pf
  else
    let rhs = string_of_elems fml (fun (c,_) ->fixbag_of_formula c) op_or in
    let no = string_of_int no_of_disjs in
    let input_fixbag = 
      try
      name ^ "(" ^"self," ^ (string_of_elems vars fixbag_of_spec_var ",") ^ " -> "
        ^ res_name ^ ") := " 
        ^ rhs
      with _ -> report_error no_pos "Error in translating the input for fixbag"
     in
      (*print_endline ("\nINPUT: " ^ input_fixbag);*)
      DD.info_pprint ">>>>>> compute_fixpoint <<<<<<" no_pos;
      DD.info_pprint ("Input of fixbag: " ^ input_fixbag) no_pos;
(*      let output_of_sleek = "fixbag.inf" in*)
(*      let oc = open_out output_of_sleek in*)
(*      Printf.fprintf oc "%s" input_fixbag;*)
(*      flush oc;*)
(*      close_out oc;*)
      let res = syscall (fixbag ^ " \'" ^ input_fixbag ^ "\' \'" ^ no ^ "\'") in
      let res = remove_paren res (String.length res) in
      (*print_endline ("RES: " ^ res);*)
      DD.info_pprint ("Result of fixbag: " ^ res) no_pos;
      let new_pf = List.hd (Parse_fixbag.parse_fix res) in
      let _ = DD.devel_hprint (add_str "Result of fixbag (parsed): "  !CP.print_formula) new_pf no_pos in
    let check_imply = Omega.imply new_pf pf "1" 100.0 in
    if check_imply then (
      Pr.fmt_string "INV:  ";
      Pr.pr_angle name (fun x -> Pr.fmt_string (Pr.string_of_typed_spec_var x)) vars;
      Pr.fmt_string ("\nOLD: " ^ (Pr.string_of_pure_formula pf) ^
                     "\nNEW: " ^ (Pr.string_of_pure_formula new_pf) ^ "\n\n");			
      new_pf)
    else pf



(******************************************************************************)

let rec is_rec pf = match pf with
  | CP.BForm (bf,_) -> CP.is_RelForm pf
  | CP.And (f1,f2,_) -> is_rec f1 || is_rec f2
  | CP.Or (f1,f2,_,_) -> is_rec f1 || is_rec f2
  | CP.Not (f,_,_) -> is_rec f
  | CP.Forall (_,f,_,_) -> is_rec f
  | CP.Exists (_,f,_,_) -> is_rec f
  | CP.AndList b -> exists_l_snd is_rec b

let rec get_rel_vars pf = match pf with
  | CP.BForm (bf,_) -> if CP.is_RelForm pf then CP.get_rel_args pf else []
  | CP.And (f1,f2,_) -> get_rel_vars f1 @ get_rel_vars f2
  | CP.Or (f1,f2,_,_) -> get_rel_vars f1 @ get_rel_vars f2
  | CP.Not (f,_,_) -> get_rel_vars f
  | CP.Forall (_,f,_,_) -> get_rel_vars f
  | CP.Exists (_,f,_,_) -> get_rel_vars f
  | CP.AndList b -> fold_l_snd get_rel_vars b

let rec remove_red_cnts (f:formula) : formula = match f with
  | BForm ((p_fml,l),p) -> BForm ((remove_red_cnts_p p_fml,l),p)
  | And (f1,f2,p) -> 
    let g1 = remove_red_cnts f1 in
    let g2 = remove_red_cnts f2 in
    mkAnd g1 g2 p
  | AndList b -> AndList (map_l_snd remove_red_cnts b)
  | Or (f1,f2,l,p) ->
    let g1 = remove_red_cnts f1 in
    let g2 = remove_red_cnts f2 in
    mkOr g1 g2 l p
  | _ -> f

and remove_red_cnts_p f = match f with  
  | Eq (Var(sv,_),Bag(es,p),_)
  | Eq (Bag(es,p),Var(sv,_),_) 
  | Eq (Var(sv,_),BagUnion(es,p),_)
  | Eq (BagUnion(es,p),Var(sv,_),_) -> 
    if name_of_spec_var sv = CP.name_of_exp (Bag(es,p)) 
    then BConst(true,no_pos) else f
  | Eq (e1,e2,l) -> 
    let r = eqExp_f eq_spec_var e1 e2 in 
    if r then BConst (true,no_pos) else f
  | _ -> f

let rec is_red_num_exp e = match e with
  | IConst _ -> true
  | Add (e1,e2,_) -> is_red_num_exp e1 || is_red_num_exp e2
  | _ -> false

let rec is_non_zero_exp e = match e with
  | IConst (0,_) -> false
  | IConst _ -> true
  | Add (e1,e2,_) -> is_non_zero_exp e1 || is_non_zero_exp e2
  | _ -> false

let get_red_num_pf pf = match pf with
  | Lt (e1,e2,_)
  | Lte (e1,e2,_)
  | Gt (e1,e2,_)
  | Gte (e1,e2,_)
  | Neq (e1,e2,_) -> 
    if is_red_num_exp e1 || is_red_num_exp e2 then 
      let r = afv e1 @ afv e2 in
      (r,[]) 
    else ([],[])
  | Eq (e1,e2,_) -> 
    begin
    match e1,e2 with
    | Var _, BagUnion _ 
    | BagUnion _, Var _ -> ([], List.filter is_int_typ (afv e1 @ afv e2))
    | _ -> 
      if is_non_zero_exp e1 || is_non_zero_exp e2 then 
        let r = afv e1 @ afv e2 in
        (r,[]) 
      else 
      if is_red_num_exp e1 || is_red_num_exp e2 then 
        (afv e1 @ afv e2,[]) 
      else ([],[])
    end
  | _ -> ([],[])

let rec get_red_num_var f = match f with
  | BForm ((pf,_),_) -> get_red_num_pf pf
  | And (f1,f2,_) -> 
    let (r11,r12) = get_red_num_var f1 in
    let (r21,r22) = get_red_num_var f2 in
    (r11@r21,r12@r22)
  | Or (f1,f2,_,_) ->
    let (r11,r12) = get_red_num_var f1 in
    let (r21,r22) = get_red_num_var f2 in
    (r11@r21,r12@r22)
  | Not (f,_,_) -> get_red_num_var f
  | Forall (_,f,_,_) -> get_red_num_var f
  | Exists (_,f,_,_) -> get_red_num_var f
  | AndList _ -> report_error no_pos "to handle AndList"

let rec create_alias_tbl keep_vars all_vars aset = 
  (* TODO: remove duplicate *)
  let f = fun v ->
    let alias_lst = List.filter (fun x -> not(List.mem x keep_vars)) 
      (CP.EMapSV.find_equiv_all v aset) 
    in v::alias_lst
  in
  let res_k = List.map f keep_vars in
  let other_vars = CP.diff_svl all_vars (List.concat res_k) in
  res_k @ (List.map f other_vars)

let is_important_var sv = match sv with
  | SpecVar (Named t,_,_) -> t="ubi" || t="bi" || t="eb"
  | _ -> false

let rewrite_fml pure keep_vars = 
  let als = MCP.ptr_bag_equations_without_null (MCP.mix_of_pure pure) 
            (keep_vars@[SpecVar(Named "eb","{}",Unprimed)]) in
(*  DD.info_hprint (add_str "ALS: " (pr_list (pr_pair !print_sv !print_sv))) als no_pos;*)
  let aset = CP.EMapSV.build_eset als in
  let lst1,lst2 = List.split als in
  let ivars = List.filter is_important_var (CP.remove_dups_svl (lst1@lst2)) in
(*  DD.info_hprint (add_str "IVARS: " !print_svl) ivars no_pos;*)
  let rec_vars = CP.remove_dups_svl (get_rel_vars pure) in
  let all_keep_vars = keep_vars@rec_vars@ivars in
  let alias = create_alias_tbl all_keep_vars (CP.fv pure) aset in
  let subst_lst = List.concat (
    List.map (fun vars -> 
      if vars = [] then [] 
      else let hd = List.hd vars in List.map (fun v -> (v,hd)) (List.tl vars)
    ) alias) in
(*  DD.info_hprint (add_str "SUBST: " (pr_list (pr_pair !print_sv !print_sv))) subst_lst no_pos;*)
  let pure = CP.subst subst_lst pure in
  pure

let rec elim_disj p flag = match p with
  | BForm ((Neq(_,Bag([],_),_),_),_)
  | BForm ((Neq(Bag([],_),_,_),_),_) -> CP.mkTrue no_pos
  | BForm ((Eq(_,_,_),_),_) -> 
    let fv_p = CP.fv p in
    if flag && List.exists is_bag_typ fv_p && not(List.exists is_rel_typ fv_p) 
    then CP.mkTrue no_pos else p
  | Or (f1,f2,_,_) -> 
    let f1 = elim_disj f1 true in
    let f2 = elim_disj f2 true in
    let disjs = CP.list_of_disjs (CP.mkOr f1 f2 None no_pos) in
    let disjs = Gen.BList.remove_dups_eq CP.equalFormula disjs in
    Solver.normalize_to_CNF_new (CP.disj_of_list disjs no_pos) no_pos
  | BForm _ -> p
  | And (f1,f2,_) -> CP.mkAnd (elim_disj f1 flag) (elim_disj f2 flag) no_pos
  | Not (f,_,_) -> CP.mkNot_s (elim_disj f flag)
  | Forall (v,f,o,p) -> Forall (v,elim_disj f flag,o,p)
  | Exists (v,f,o,p) -> Exists (v,elim_disj f flag,o,p)
  | AndList l -> AndList (map_l_snd (fun x -> elim_disj x flag) l)

let rec elim_ex p = match p with
  | Exists (_,f,_,_) -> elim_ex f
  | BForm _ -> p
  | And (f1,f2,pos) -> CP.mkAnd (elim_ex f1) (elim_ex f2) pos
  | Or (f1,f2,o,pos) -> CP.mkOr (elim_ex f1) (elim_ex f2) o pos
  | Not (f,o,pos) -> Not (elim_ex f,o,pos)
  | Forall (_,f,_,_) -> p
  | AndList _ -> report_error no_pos "to handle AndList"

let rec elim_red p =
  let p = elim_ex p in
  let node_vars = List.filter CP.is_node_typ (CP.fv p) in
  let num_vars, others = get_red_num_var p in
  let red_num_vars = CP.diff_svl num_vars others in
  CP.remove_cnts (node_vars @ red_num_vars) p

let transform fml fv_rel new_v = match fml with
  | BForm ((Eq (v1, BagUnion ([v2;Bag([Var (v,_)],_)],_), _), _),_)
  | BForm ((Eq (v1, BagUnion ([Bag([Var (v,_)],_);v2],_), _), _),_)
  | BForm ((Eq (BagUnion ([Bag([Var (v,_)],_);v2],_), v1, _), _),_)
  | BForm ((Eq (BagUnion ([v2;Bag([Var (v,_)],_)],_), v1, _), _),_) -> 
    if diff_svl (fv fml) fv_rel != [] || List.length new_v != 1 then fml
    else
      let vars = afv v2 in
      let new_vars = List.map (fun x -> CP.fresh_spec_var_prefix "FB" x) vars in
      let pairs = List.combine (vars@[v]) (new_vars@new_v) in
      let als_lst = List.map (fun (x,y) -> CP.mkEqVar x y no_pos) pairs in
      let fml_new = CP.subst pairs fml in        
      conj_of_list (fml_new::als_lst) no_pos
  | _ -> fml

let transform fml fv_rel new_v =
  let pr0 = !CP.print_formula in
  let pr1 = !CP.print_svl in
  Debug.no_3 "transform" pr0 pr1 pr1 pr0
      (fun _ _ _ -> transform fml fv_rel new_v) fml fv_rel new_v

let simplify pf fv_rel =
(*  let _ = DD.info_hprint (add_str "PURE1: " !CP.print_formula) pf no_pos in*)
  let pf = elim_red pf in
(*  let _ = DD.info_hprint (add_str "PURE2: " !CP.print_formula) pf no_pos in*)
  let pf = elim_disj pf false in
  let pf = elim_disj pf false in
(*  let _ = DD.info_hprint (add_str "PURE3: " !CP.print_formula) pf no_pos in*)
  (* TODO: use fixpoint instead *)
  let pf = rewrite_fml pf fv_rel in
  let pf = rewrite_fml pf fv_rel in
(*  let _ = DD.info_hprint (add_str "PURE4: " !CP.print_formula) pf no_pos in*)
  pf

let update_rec_call rel rel_def ante_vars = match (rel,rel_def) with
  | (CP.BForm ((CP.RelForm (id,args,p), o1), o2), 
    CP.BForm ((CP.RelForm (id_def,args_def,_),_),_)) -> 
    if id = id_def then 
      let new_args_def = 
        let pre_args, post_args = List.partition 
          (fun e -> Gen.BList.subset_eq CP.eq_spec_var 
                    (CP.afv e) ante_vars) args_def in
        pre_args @ post_args 
      in
      let pairs = List.combine args_def args in
      let new_args = List.map (fun a -> List.assoc a pairs) new_args_def in
      let id = match id with | CP.SpecVar (t,n,p) -> CP.SpecVar (t,"fixbag" ^ n,p) in
      CP.BForm ((CP.RelForm (id,new_args,p), o1), o2)
    else report_error no_pos "Not supported mutual recursion in FixBag"
  | _ -> report_error no_pos "Expecting relation formulae"

let rewrite_to_neq fml = match fml with
  | Or (f1,f2,_,_) ->
    (match f1,f2 with
    | (BForm ((pf1,o1),o2), BForm ((pf2,_),_)) -> 
      (match pf1,pf2 with
      | (Lt (Var (v1,p1), Var (v2,p2), p), Lt (Var (v3,_), Var (v4,_), _))
      | (Gt (Var (v1,p1), Var (v2,p2), p), Gt (Var (v3,_), Var (v4,_), _)) -> 
        if eq_spec_var v1 v4 && eq_spec_var v2 v3 then
          BForm ((Neq(Var(v1,p1),Var(v2,p2),p),o1),o2)
        else fml
      | (Lt (Var (v1,p1), Var (v2,p2), p), Gt (Var (v3,_), Var (v4,_), _))
      | (Gt (Var (v1,p1), Var (v2,p2), p), Lt (Var (v3,_), Var (v4,_), _)) -> 
        if eq_spec_var v1 v3 && eq_spec_var v2 v4 then
          BForm ((Neq(Var(v1,p1),Var(v2,p2),p),o1),o2)
        else fml
      | _ -> fml)
    | _ -> fml)
  | _ -> fml

let elim_red_rec vars fmls =
  List.filter (fun f ->
    let vs = List.filter (fun x -> CP.is_bag_typ x || CP.is_bool_typ x) (CP.fv f) in
    CP.subset vs vars
  ) fmls

let rec filter_var f vars = 
  match f with
  | CP.Or (f1,f2,l,p) -> CP.mkOr (filter_var f1 vars) (filter_var f2 vars) l p
  | _ -> CP.filter_var f vars

let handle_base base fv_rel rcase_vars = 
(*  let _ = DD.info_hprint (add_str "BASE: " !CP.print_formula) base no_pos in*)
  let base = remove_red_cnts (filter_var base fv_rel) in
  let base_conjs = Gen.BList.remove_dups_eq (CP.equalFormula) (CP.list_of_conjs base) in
  let base =
    if List.length base_conjs == 1 then
      let base_hd = List.hd base_conjs in
      transform base_hd fv_rel rcase_vars
    else CP.conj_of_list base_conjs no_pos 
  in base

let handle_rec rcase_orig rel rel_vars ante_vars =
(*  let _ = DD.info_hprint (add_str "REC: " !CP.print_formula) rcase_orig no_pos in*)
  let rec_vars = CP.remove_dups_svl (get_rel_vars rcase_orig) in
  let all_rel_vars = rel_vars @ rec_vars in
  let rcase = CP.drop_rel_formula rcase_orig in
  let rcase = remove_red_cnts (filter_var rcase all_rel_vars) in
  let rcase_conjs = elim_red_rec all_rel_vars (CP.list_of_conjs rcase) in
  let rels = List.map (fun x -> update_rec_call x rel ante_vars) 
    (Gen.BList.remove_dups_eq (CP.equalFormula) (CP.get_RelForm rcase_orig)) in
  let rcase_conjs = List.map (fun x -> rewrite_to_neq x) rcase_conjs in
  CP.conj_of_list (rcase_conjs @ rels) no_pos

let helper (rel,pfs) ante_vars = 
  let fv_rel = CP.get_rel_args rel in
  let pfs = List.map (fun x -> simplify x fv_rel) pfs in
(*  let _ = DD.info_hprint (add_str "input_pairs2: " *)
(*    (pr_pair !CP.print_formula (pr_list !CP.print_formula))) (rel,pfs) no_pos in*)

  let (rcases, bcases) = List.partition is_rec pfs in
  let rcases = List.map (fun x -> handle_rec x rel fv_rel ante_vars) rcases in
  let rcases_vars = diff_svl (List.filter is_int_typ (List.concat (List.map CP.fv rcases))) fv_rel in
  let bcases = List.map (fun x -> handle_base x fv_rel rcases_vars) bcases in
  let pfs = bcases @ rcases in

(*  let pfs = List.map elim_quan pfs in*)
(*  let pfs = propagate_rec pfs rel ante_vars in*)

  let is_special_typ x = match x with 
    | CP.SpecVar (Named t, _, _) -> t="eb"||t="ub"||t="b"||t="bi"||t="ubi"
    | _ -> false 
  in
  let mk_exists_no_simp vs pure o p = List.fold_left (fun f v -> Exists (v,f,o,p)) pure vs in
(*  let _ = DD.info_hprint (add_str "input_pairs3: " *)
(*    (pr_pair !CP.print_formula (pr_list !CP.print_formula))) (rel,pfs) no_pos in*)
  let pfs = List.map (fun p -> 
    let exists_vars = 
      CP.diff_svl 
        (List.filter (fun x -> not(CP.is_bag_typ x 
        || CP.is_rel_typ x || is_special_typ x)) (CP.fv p)) fv_rel 
    in mk_exists_no_simp exists_vars p None no_pos) pfs in
  match pfs with
  | [] -> []
  | _ -> [(rel, List.fold_left (fun p1 p2 -> 
          CP.mkOr p1 p2 None no_pos) (CP.mkFalse no_pos) pfs)]

let compute_fixpoint_aux rel_fml pf ante_vars = 
  let (name,vars) = match rel_fml with
    | CP.BForm ((CP.RelForm (name,args,_),_),_) -> 
      (CP.name_of_spec_var name, List.concat (List.map CP.afv args))
    | _ -> report_error no_pos "Wrong format"
  in
  let pre_vars, post_vars = List.partition (fun v -> List.mem v ante_vars) vars in

  try
    let rhs = fixbag_of_pure_formula pf in
    let no = string_of_int !Globals.fixcalc_disj in
    let input_fixbag =  "fixbag" ^ name ^ "(" 
      ^ (string_of_elems pre_vars fixbag_of_spec_var ",") ^ " -> "
      ^ (string_of_elems post_vars fixbag_of_spec_var ",") ^ ") := " 
      ^ rhs
    in
    DD.devel_pprint ">>>>>> compute_fixpoint <<<<<<" no_pos;
    DD.devel_pprint ("Input of fixbag: " ^ input_fixbag) no_pos;
    DD.devel_pprint ("Number of disjs: " ^ no) no_pos;
    let res = syscall (fixbag ^ " \'" ^ input_fixbag ^ "\' \'" ^ no ^ "\'") in
    let res = remove_paren res (String.length res) in
    DD.devel_pprint ("Result of fixbag: " ^ res) no_pos;
    let fixpoint = Parse_fixbag.parse_fix res in
    DD.devel_hprint (add_str "Result of fixbag (parsed): " 
      (pr_list !CP.print_formula)) fixpoint no_pos;
    match fixpoint with
      | [post] -> (rel_fml, post)
      | _ -> report_error no_pos "Expecting a postcondition"
  with _ -> 
    report_error no_pos "Unexpected error in computing fixpoint by FixBag"

let rec unify_rels rel a_rel = match rel, a_rel with
  | (f1,CP.BForm ((CP.RelForm (name1,args1,p1),p2),p3)), 
    (f2,CP.BForm ((CP.RelForm (name2,args2,_ ),_ ),_ )) ->
    let subst_arg = List.combine (List.map CP.exp_to_spec_var args2) 
                                 (List.map CP.exp_to_spec_var args1) in
    let f2 = CP.subst subst_arg f2 in
    f2
  | _ -> report_error no_pos ("unify_rels: Expected a relation, " ^ 
        (pr_pair !CP.print_formula !CP.print_formula) (snd rel, snd a_rel))

let rec preprocess pairs = match pairs with
  | [] -> []
  | r::rs -> 
    let rel = snd r in
    let name = CP.name_of_rel_form rel in
    let same_rels, diff_rels = 
      List.partition (fun r0 -> 
        CP.eq_spec_var (CP.name_of_rel_form (snd r0)) name) rs in
    let unified_rels = 
      if same_rels == [] then [(rel, [fst r])]
      else 
        let res = List.map (fun r0 -> 
                    if CP.equalFormula rel (snd r0) then (fst r0)
                    else unify_rels r r0) same_rels in
        [(rel, (fst r) :: res)]
    in
    unified_rels @ (preprocess diff_rels)

let compute_fixpoint input_pairs ante_vars =
(*  let _ = DD.info_hprint (add_str "input_pairs1: " *)
(*    (pr_list (pr_pair !CP.print_formula !CP.print_formula))) input_pairs no_pos in*)

  let pairs = preprocess input_pairs in

  let pairs = List.concat (List.map (fun x -> helper x ante_vars) pairs) in

(*  let _ = DD.info_hprint (add_str "input_pairs2: " *)
(*    (pr_list (pr_pair !CP.print_formula !CP.print_formula))) pairs no_pos in*)

  List.map (fun (rel_fml,pf) -> 
    if CP.isConstFalse pf then (rel_fml, CP.mkFalse no_pos)
    else 
    if CP.isConstTrue pf then (rel_fml, CP.mkTrue no_pos)
    else 
(*    if not(is_rec pf) then *)
(*      let _ = DD.devel_hprint (add_str "Input: " !CP.print_formula) pf no_pos in*)
(*      let exists_vars = CP.diff_svl (CP.fv_wo_rel pf) (CP.fv rel_fml) in *)
(*      let pf = TP.simplify_exists_raw exists_vars pf in*)
(*      (rel_fml, remove_subtract pf)*)
(*    else *)
      compute_fixpoint_aux rel_fml pf ante_vars) pairs

let compute_fixpoint (i:int) input_pairs ante_vars =
  let pr0 = !CP.print_formula in
  let pr1 = pr_list (pr_pair pr0 pr0) in
  let pr2 = !CP.print_svl in
  Debug.no_2_num i "compute_fixpoint" pr1 pr2 (pr_list (pr_pair pr0 pr0)) 
      (fun _ _ -> compute_fixpoint input_pairs ante_vars) input_pairs ante_vars



