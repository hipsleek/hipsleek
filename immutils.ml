open Globals
open VarGen
open Gen.Basic
open Cpure

let int_imm_to_exp i loc = 
  mkExpAnnSymb (mkConstAnn (heap_ann_of_int i)) loc

let ann_sv_lst  = (name_for_imm_sv Mutable):: (name_for_imm_sv Imm):: (name_for_imm_sv Lend)::[(name_for_imm_sv Accs)]

let is_ann_const_sv sv = 
  match sv with
  | SpecVar(AnnT,a,_) -> List.exists (fun an -> an = a ) ann_sv_lst
  | _                 -> false

let helper_is_const_ann_sv em sv test =
  let imm_const_sv = mkAnnSVar test in
  if not (is_ann_typ sv) then false
  else if eq_spec_var sv imm_const_sv then true
  else EMapSV.is_equiv em sv imm_const_sv 

let is_mut_sv ?emap:(em=[])  sv = helper_is_const_ann_sv em sv Mutable 

let is_imm_sv ?emap:(em=[])  sv = helper_is_const_ann_sv em sv Imm

let is_lend_sv ?emap:(em=[]) sv = helper_is_const_ann_sv em sv Lend

let is_abs_sv ?emap:(em=[])  sv = helper_is_const_ann_sv em sv Accs

let is_imm_const_sv ?emap:(em=[])  sv = 
  (is_abs_sv ~emap:em sv) ||   (is_mut_sv ~emap:em sv) ||   (is_lend_sv ~emap:em sv) ||   (is_imm_sv ~emap:em sv)

let get_imm_list ?loc:(l=no_pos) list =
  let elem_const = (mkAnnSVar Mutable)::(mkAnnSVar Imm)::(mkAnnSVar Lend)::[(mkAnnSVar Accs)] in
  let anns_ann =  (ConstAnn(Mutable))::(ConstAnn(Imm))::(ConstAnn(Lend))::[(ConstAnn(Accs))] in
  let anns_exp =  (AConst(Mutable,l))::(AConst(Imm,l))::(AConst(Lend,l))::[(AConst(Accs,l))] in
  let anns = List.combine anns_ann anns_exp in
  let lst = List.combine elem_const anns in
  let imm = 
    try
      Some (snd (List.find (fun (a,_) -> EMapSV.mem a list  ) lst ) )
    with Not_found -> None
  in imm

let get_imm_emap ?loc:(l=no_pos) sv emap =
  let aliases = EMapSV.find_equiv_all sv emap in
  get_imm_list ~loc:l aliases

let get_imm_emap_exp_opt  ?loc:(l=no_pos) sv emap : exp option = map_opt snd (get_imm_emap ~loc:l sv emap)

let get_imm_emap_exp  ?loc:(l=no_pos) sv emap : exp  = 
  map_opt_def (mkVar sv l) (fun x -> x) (get_imm_emap_exp_opt ~loc:l sv emap)

let get_imm_emap_ann_opt  ?loc:(l=no_pos) sv emap : ann option = map_opt fst (get_imm_emap ~loc:l sv emap)

let eq_const_ann const_imm em sv = 
  match const_imm with
  | Mutable -> is_mut_sv ~emap:em sv
  | Imm     -> is_imm_sv ~emap:em sv
  | Lend    -> is_lend_sv ~emap:em sv
  | Accs    -> is_abs_sv ~emap:em sv

let helper_is_const_imm em (imm:ann) const_imm = 
  match imm with
  | ConstAnn a -> a == const_imm
  | PolyAnn sv -> eq_const_ann const_imm em sv 
  | _ -> false

(* below functions take into account the alias information while checking if imm is a certain const. *)
let is_abs ?emap:(em=[]) (imm:ann) = helper_is_const_imm em imm Accs

let is_abs_list ?emap:(em=[]) imm_list = List.for_all (is_abs ~emap:em) imm_list

let is_mutable ?emap:(em=[]) (imm:ann) = helper_is_const_imm em imm Mutable 

let is_mutable_list ?emap:(em=[]) imm_list =  List.for_all (is_mutable ~emap:em) imm_list

let is_immutable ?emap:(em=[]) (imm:ann) = helper_is_const_imm em imm Imm

let is_immutable_list ?emap:(em=[]) imm_list =  List.for_all (is_immutable ~emap:em) imm_list

let is_lend ?emap:(em=[]) (imm:ann) = helper_is_const_imm em imm Lend

let is_lend_list ?emap:(em=[]) imm_list =  List.for_all (is_lend ~emap:em) imm_list

let isAccs (a : ann) : bool = is_abs a

let isLend(a : ann) : bool = is_lend a

let isMutable(a : ann) : bool = is_mutable a

let isImm(a : ann) : bool = is_immutable a

let isPoly(a : ann) : bool = 
  match a with
  | PolyAnn v -> true
  | _ -> false

let is_const_imm ?emap:(em=[]) (a:ann) : bool =
  match a with
  | ConstAnn _ -> true
  | PolyAnn sv -> (is_mutable ~emap:em a) || (is_immutable ~emap:em a) || (is_lend ~emap:em a) || (is_abs ~emap:em a)
  | _ -> false

let is_const_imm_list ?emap:(em=[]) (alst:ann list) : bool =
  List.for_all (is_const_imm ~emap:em) alst

(* end imm utilities *)

let contains_imm (f:formula) =
  let f_e e =  Some (is_ann_type (get_exp_type e)) in
  fold_formula f (nonef,nonef, f_e)  (List.exists (fun b -> b) )

let contains_imm (f:formula) =
  Debug.no_1 "contains_imm" !print_formula string_of_bool contains_imm f

(* assumption: f is in CNF *)
let build_eset_of_imm_formula f =
  let lst = split_conjunctions f in
  let emap = List.fold_left (fun acc f -> match f with
      | BForm (bf,_) ->
        (match bf with
         | (Eq (Var (v1,_), Var (v2,_), _),_) -> 
           if (is_bag_typ v1) then acc
           else EMapSV.add_equiv acc v1 v2
         | (Eq (ex, Var (v1,_), _),_) 
         | (Eq (Var (v1,_), ex, _),_) -> 
           (match conv_ann_exp_to_var ex with
            | Some (v2,_) -> EMapSV.add_equiv acc v1 v2
            | None -> acc)
         | (SubAnn (Var (v1,_), (AConst(Mutable,_) as exp), _),_) -> (* bot *)
           let v2 = mkAnnSVar Mutable in EMapSV.add_equiv acc v1 v2
         | (SubAnn(AConst(Accs,_) as exp, Var (v1,_), _),_) -> (* top *)
           let v2 = mkAnnSVar Accs in EMapSV.add_equiv acc v1 v2
         | _ -> acc)
      | _ -> acc
    ) EMapSV.mkEmpty lst in emap

let build_eset_of_imm_formula f =
  let pr = !print_formula in
  let pr_out = EMapSV.string_of in
  Debug.no_1 "build_eset_of_imm_formula" pr pr_out build_eset_of_imm_formula f

(* pre norm *)
let simplify_imm_adddition (f:formula) =
  let fixpt = ref true in
  let f_e emap e =
    match e with
    | Var(sv,l) -> if is_ann_typ sv then get_imm_emap_exp ~loc:l sv emap else e
    | _ -> e
  in
  let f_b emap fb =
    (* need a helper because of local var emap *)
    let f_b_helper bf =
      let (p_f, lbl) = bf in
      match p_f with
      | Eq (Var(sv,lv), Add(e1,e2,la), l) ->
        if is_ann_typ sv then 
          let new_pf = (Eq (Var(sv,lv), Add(f_e emap e1, f_e emap e2,la), l)) in
          Some (new_pf, lbl)
        else None
      | _ -> None
    in 
    let fb = transform_b_formula (f_b_helper, somef) fb in
    fb
  in

  let f_f f =
    match f with
    | BForm (b1,b2) -> let emap = build_eset_of_imm_formula f in Some (BForm (f_b emap b1, b2))
    | _ -> None
  in
  let fncs = (nonef, nonef, f_f, somef, somef) in
  transform_formula fncs f

