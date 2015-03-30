#include "xdebug.cppo"
open VarGen
open Globals
open Gen.Basic
open Exc.GTable
module LO=Label_only.LOne
open Label
open Cpure

let min_max_one = "__min_max_one__"

(********************************************************)
       (*****************DERIVE********************)
(********************************************************)
let extract_inner_e e0 root val_extns rec_args=
  let rec initial_helper exps v=
    match exps with
      | [] -> if v then
            if is_bag_typ root then
              Bag ([],no_pos)
            else IConst (0, no_pos) (*todo: should improve here*)
          else report_error no_pos "cpure.extract_inner_e: why is it empty?"
      | e:: rest ->
          let svl1 = afv e in
          if svl1 = []  then
            e
          else
            let valid=(diff_svl svl1 val_extns = [] && intersect_svl svl1 rec_args = []) in
            initial_helper rest (v||valid)
  in
  let rec helper e=
    match e with
      | Add (e1, e2,_)
      | Subtract (e1, e2,_)
      | Mult (e1, e2, _)
      | Div (e1, e2, _)
      | Max (e1, e2, _)
      | Min (e1, e2, _) ->
          let svl1 = afv e1 in
          let first_e =  initial_helper [e2;e1] false in
          let res= (e, first_e)
            (* if svl1 = [] then *)
            (* (\*e1 should be a const*\) *)
            (*   (e, e1) *)
            (* else if diff_svl svl1 val_extns = [] then *)
            (*   (e, e1) *)
            (* else (e, e2) *)
          in
          (false, res)
	  (* bag expressions *)
      | Bag (exps,p) ->  (true, ( Bag ([],p), initial_helper exps false))
      | BagUnion (exps,p) -> (true, (BagUnion ([],p), initial_helper exps false))
      | BagIntersect (exps,p) -> (true, (BagIntersect ([],p), initial_helper exps false))
      | _ -> report_error no_pos "cpure.extract_inner_e: not handle yet"
  in
  helper e0

let extract_outer_inner_p pf0 root_args val_extns rec_args=
  let is_root e=
    let sv = afv e in
    diff_svl sv root_args = []
  in
  let rec find_initial exps v=
    match exps with
      | [] -> if v then
            if is_bag_typ (List.hd root_args) then
              Bag ([],no_pos)
            else IConst (0, no_pos) (*todo: should improve here*)
          else
            (*min/max*)
            let r = List.hd root_args in
            Var (SpecVar (type_of_spec_var r, min_max_one, primed_of_spec_var r), no_pos)
      (* report_error no_pos "cpure.extract_outer_inner_p: why is it empty?" *)
      | e:: rest ->
          let svl1 = afv e in
          if svl1 = [] (* || (diff_svl svl1 val_extns = [] && intersect_svl svl1 rec_args = []) *) then
            e
          else
            let valid =(diff_svl svl1 val_extns = [] && intersect_svl svl1 rec_args = []) in
            find_initial rest (v||valid)
  in
  let rec helper pf=
    match pf with
      | Lt (e1, e2,_)
      | Lte (e1, e2, _)
      | Gt (e1, e2 , _)
      | Gte (e1, e2, _)
      | Eq (e1, e2, _)
      | Neq (e1, e2, _) -> begin
          let b1= is_root e1 in
          let b2= is_root e2 in
          match b1,b2 with
            | true,false ->
                let is_bag, (inner_e,first_e) = extract_inner_e e2 (List.hd root_args) val_extns rec_args in
                (is_bag,(pf,e1), (inner_e,first_e))
            | false,true ->
                 let is_bag, (inner_e,first_e) = extract_inner_e e1 (List.hd root_args) val_extns rec_args in
                (is_bag, (pf,e2), (inner_e,first_e))
            | _ -> report_error no_pos "cpure.extract_outer_inner_p: wrong?"
      end
      |  EqMin (e1, e2, e3,p) (* first is min of second and third *) ->
          (* let () =  Debug.info_pprint ("  EqMin: " ^ (!print_p_formula pf)) no_pos in *)
          (*find initial value: e2 or e3*)
          let e_i = find_initial [e2;e3] false in
          (false, (Eq (e1,e2,p), e1), (Min (e2,e3,no_pos),e_i))
      |  EqMax (e1, e2, e3,p) (* first is max of second and third *) ->
          (* let () =  Debug.info_pprint ("  EqMax: " ^ (!print_p_formula pf)) no_pos in *)
          (*find initial value: e2 or e3*)
          let e_i = find_initial [e2;e3] false in
          (false, (Eq (e1,e2,p), e1), (Max (e2,e3,no_pos),e_i))
      | _ -> report_error no_pos "cpure.extract_outer_inner_p: not handle yet"
  in
  helper pf0

let extract_outer_inner_f p0 args val_extns rec_args=
  let rec helper p ex_quans irr_ps=
    match p with
      | BForm ((pf,_),_) ->
          (extract_outer_inner_p pf args val_extns rec_args,ex_quans, irr_ps)
      | And (p1,p2,_) -> begin
          let svl1 = fv p1 in
          let svl2 = fv p2 in
          let b1 = intersect_svl svl1 rec_args = [] in
          let b2 = intersect_svl svl2 rec_args = [] in
          match b1,b2 with
            | true,false -> helper p2 ex_quans (irr_ps@[p1])
            | false,true -> helper p1 ex_quans (irr_ps@[p2])
            | _ -> report_error no_pos "cpure.extract_outer_inner_f: not handle yet 1"
      end
      | Exists (sv, p1, _, _) -> helper p1 (ex_quans@[sv]) irr_ps
      | _ -> report_error no_pos "cpure.extract_outer_inner_f: not handle yet 2"
  in
  helper p0 [] []

let extract_outer_inner_x f args val_extns rec_args=
  extract_outer_inner_f f args val_extns rec_args

let extract_outer_inner p args val_extns rec_args=
  let pr0 = !print_svl in
  let pr1 = !print_p_formula in
  (* let pr2 = ArithNormalizer.string_of_exp in *)
  let pr2 = !print_exp in
  let pr3 = pr_triple string_of_bool (pr_pair pr1 pr2) (pr_pair pr2 pr2) in
  let pr4 = !print_formula in
  let pr5 = pr_triple pr3 pr0 (pr_list pr4) in
  Debug.no_5 "extract_outer_inner" pr4 pr0 pr0 pr0 pr0 pr5
      (fun _ _ _ _ _ -> extract_outer_inner_x p args val_extns rec_args)
      p args val_extns val_extns rec_args

(* let check_null_var e= *)
(*   match e with *)
(*     | Var ((SpecVar (t,id,_)),p) -> *)
(*         if String.compare id null_sv = 0 then *)
(*           begin *)
(*               match t with *)
(*                 | Int -> IConst (1,p) *)
(*                 | BagT _ -> Bag ([], p) *)
(*                 | _ -> e *)
(*           end *)
(*         else e *)
(*     | _ -> e *)

let is_zero e=
  match e with
    | IConst (n, _) -> (n=0)
    | _ -> false

let is_bag_empty e=
  match e with
    | Bag (exps,_) -> (exps =[])
    | _ -> false

let is_node_sv e=
  match e with
    | Var (sv,_) -> is_node_typ sv
    | _ -> false

(*non-bag constrs*)
let mk_exp_from_non_bag_tmpl tmpl e1 e2 p=
  let preprocess e01 e02=
    if is_zero e02 || is_node_sv e02 then (Some e01)
    else if is_zero e01 || is_node_sv e01 then Some e02 else None
  in
  let e11 = (* check_null_var *) e1 in
  let e22 = (* check_null_var *) e2 in
  match tmpl with
    | Add (_, _,_) ->
        (* if is_zero e22 || is_node_sv e22 then e11 *)
        (* else if is_zero e11 || is_node_sv e11 then e22 else *)
        let r = preprocess e11 e22 in
        begin
            match r with
              | Some e -> e
              | None -> Add (e11,e22,p)
        end
    | Subtract (_, _,_) -> Subtract (e11, e22,p)
    | Mult (_, _, _) ->  Mult (e11, e22, p)
    | Div (_, _, _) -> Div (e11, e22, p)
    | Max (_, _, _) ->
        let r = preprocess e11 e22 in
        begin
            match r with
              | Some e -> e
              | None -> mkMax e11 e22 p
        end
    | Min (_, _, _) ->
       let r = preprocess e11 e22 in
        begin
            match r with
              | Some e -> e
              | None -> mkMin e11 e22 p
        end
    | _ -> report_error no_pos "cpure.extract_inner_e: not handle yet"

(*bag constrs (* bag expressions *)*)
let mk_exp_from_bag_tmpl tmpl e1 e2 p=
  match tmpl with
    | Bag (_,_) -> Bag ( [e1;e2],p)
    | BagUnion (_,_) ->
        if is_bag_empty e1 || is_node_sv e1 then e2 else
          if is_bag_empty e2 || is_node_sv e2 then e1 else
            BagUnion ([e1;e2],p)
    | BagIntersect (_,_) -> BagIntersect ([e1;e2],p)
    | _ -> report_error no_pos "cpure.extract_inner_e: not handle yet"

let mk_pformula_from_tmpl tmpl e1 e2 p=
  match tmpl with
    | Lt (_, _,_) -> mkLt e1 e2 p
    | Lte (_, _, _) -> mkLte e1 e2 p
    | Gt (_, _ , _) -> mkGt e1 e2 p
    | Gte (_, _, _) -> mkGte e1 e2 p
    | Eq (_, _, _) -> mkEq e1 e2 p
    | Neq (_, _, _) -> mkNeq e1 e2 p
    | _ -> report_error no_pos "cpure.extract_outer_inner_p: not handle yet"

(************* NORM MIN/MAX**********************)
(********************************************************)
   (********************** NORM********************)
(********************************************************)
(*
  x=min(a,b,c) = Ex d: x=min(a,d) & d=min(b,c)
*)
(*assume that this is a list of all min or all max*)
(*
 k=-1: not init
 k=0: max
 k=1: min
*)
let extract_list_exp_min_max_exp_x e k0=
  (**)
  let rec helper e0 k=
    match e0 with
      | Var _ -> ([e0],k)
      | Max (e1,e2,_) ->
          let k1=
            if k = -1 then 0 else if k<>0 then
                  report_error no_pos "cpure.extract_list_exp_min_max_exp: sth wrong 1"
                else 0
          in
          let svl2,k2 = helper e1 k1 in
          let svl3,k3 = helper e2 k1 in
          if (k2=0 && k3=0) then (svl2@svl3,0) else
            report_error no_pos "cpure.extract_list_exp_min_max_exp: sth wrong 2"
      | Min (e1,e2,_) ->
           let k1=
            if k = -1 then 1 else if k<>1 then
                  report_error no_pos "cpure.extract_list_exp_min_max_exp: sth wrong"
                else 1
          in
           let svl2,k2 = helper e1 k1 in
          let svl3,k3 = helper e2 k1 in
          if (k2=1 && k3=1) then (svl2@svl3,1) else
            report_error no_pos "cpure.extract_list_exp_min_max_exp: sth wrong 3"
      | _ -> raise Not_found
  in
  try
      helper e k0
  with Not_found -> ([],-1)

(*
 k=-1: not init
 k=0: max
 k=1: min
*)
let extract_list_exp_min_max_exp e k=
  (* let pr1 = ArithNormalizer.string_of_exp in *)
  let pr1 = !print_exp in
  Debug.no_1 "extract_list_exp_min_max_exp" pr1 (pr_pair (pr_list pr1) string_of_int)
      (fun _ -> extract_list_exp_min_max_exp_x e k) e

let norm_exp_min_max_p pf=
  let get_two_last svl=
    let rev_svl = List.rev svl in
    let sv2 = List.hd rev_svl in
    let rest2 = List.tl rev_svl in
    let sv1 = List.hd rest2 in
    let rest = List.rev (List.tl rest2) in
    (sv1,sv2,rest)
  in
  let check_min_max_one e=
    match e with
      | Var (sv,_) -> String.compare (name_of_spec_var sv) min_max_one = 0
      | _ -> false
  in
(*
 k=-1: not init
 k=0: max
 k=1: min
*)
  let mk_min_max_helper k e exps p=
    let sv= match e with
      | Var (sv,_) -> sv
      | _ -> report_error no_pos "cpure.norm_exp_min_max_p: 1"
    in
    let rec helper exps0 ps quans=
      let v1,v2,rest= get_two_last exps0 in
      let fr_sv =  (fresh_spec_var sv) in
      let fr_var = (Var (fr_sv,no_pos)) in
      let pf1= if k=0 then (EqMax (fr_var, v1, v2, no_pos)) else
            (EqMin (fr_var, v1, v2, no_pos))
      in
      let np = BForm ((pf1,None),None) in
      let n_rest = rest@[fr_var] in
      if (List.length n_rest<=2) then
        begin
            let pf11=
              let v11,v22,_ = get_two_last n_rest in
              if check_min_max_one v11 then
                mkEq e v22 no_pos
              else if check_min_max_one v22 then
                mkEq e v11 no_pos
              else (*check x=max(v,V) -> x=V*)
                if (eqExp_f eq_spec_var) v11 v22 then (mkEq e v11 no_pos)
              else
                if k=0 then (EqMax (e,v11, v22, no_pos)) else
                  (EqMin (e, v11, v22, no_pos))
            in
            (pf11, ps@[np], (quans@[fr_sv]))
        end
        else
        helper n_rest (ps@[np]) (quans@[fr_sv])
    in
    helper exps [] []
  in
  let norm_list_min_max e1 init_exps e2 pos k=
    let exps0,k = extract_list_exp_min_max_exp e2 k in
    if k = -1 then (pf,[],[]) else
      let exps1 = exps0@init_exps in
      if List.length exps1 <=2 then
        (*check x=max(v,V) -> x=V*)
        let v11,v22,_ = get_two_last exps1 in
         if (eqExp_f eq_spec_var) v11 v22 then ((mkEq e1 v11 no_pos),[],[]) else
           (pf,[],[])
      else
        mk_min_max_helper k e1 exps1 pos
  in
  match pf with
    | Eq (e1,e2,l) -> begin
        let b1 = is_var e1 in
        let b2= is_var e2 in
        match b1,b2 with
          | true,false -> norm_list_min_max e1 [] e2 l (-1)
          | false,true -> norm_list_min_max e2 [] e1 l (-1)
          | _ -> pf,[],[]
    end
    | EqMin (e1,e2,e3,l) -> begin
        (* let () =  Debug.info_pprint ("   EqMin: ") no_pos in *)
        let b2 = is_var e2 in
        let b3= is_var e3 in
        match b2,b3 with
          | true,false -> norm_list_min_max e1 [e2] e3 l 1
          | false,true -> norm_list_min_max e1 [e3] e2 l 1
          | true,true -> if (eqExp_f eq_spec_var) e2 e3 then
                (mkEq e1 e2 l,[],[])
              else pf,[],[]
          | _ -> pf,[],[]
    end
    | EqMax (e1,e2,e3,l) -> begin
        (* let () =  Debug.info_pprint ("   EqMax: ") no_pos in *)
        let b2 = is_var e2 in
        let b3= is_var e3 in
        match b2,b3 with
          | true,false -> norm_list_min_max e1 [e2] e3 l 0
          | false,true -> norm_list_min_max e1 [e3] e2 l 0
          | true,true -> if (eqExp_f eq_spec_var) e2 e3 then
                (mkEq e1 e2 l,[], [])
              else pf,[],[]
          | _ -> pf,[],[]
    end
    | _ -> pf,[],[]

let norm_exp_min_max f =
  match f with
    | BForm ((pf,pann),fl) ->
        let npf,ps, quans = norm_exp_min_max_p pf in
        if ps = [] then
          (BForm ((npf, pann),fl), [])
        else
          let np =  BForm ((npf, pann),fl) in
          let cmb_f = List.fold_left (fun p1 p2 -> mkAnd p1 p2 no_pos) np ps in
          (cmb_f,quans)
    | _ -> (f,[])

let min_max_sv = SpecVar (NUM, "min_max", Unprimed) 

let norm_exp_min_max2 p =
  let quant = new Gen.stack in
  let f_f p = None in
  let f_bf (p, bann) = None in
  let f_e e = 
    match e with
    | Max(_,_,l) 
    | Min(_,_,l) ->
          let nv = fresh_spec_var  min_max_sv in
          quant # push (nv,e);
          Some (Var (nv,l))
    | _ -> None 
  in
  let f = map_formula p (f_f,f_bf,f_e) in
  (f, quant # get_stk)

let norm_exp_min_max2 p =
  let pr1 = !print_formula in
  let pr2 = pr_list (pr_pair !print_sv !print_exp) in
  Debug.no_1 "norm_exp_min_max2" pr1 (pr_pair pr1 pr2)
      (fun _ -> norm_exp_min_max2 p) p

let norm_exp_min_max p=
  let pr1 = !print_formula in
  (* let () = norm_exp_min_max2 p in *)
  Debug.no_1 "norm_exp_min_max" pr1 (pr_pair pr1 !print_svl)
      (fun _ -> norm_exp_min_max p) p
(********************************************************)
   (********************END NORM********************)
(********************************************************)
let mk_formula_from_tmp_x outer n_root_e n_inner_e ex_quans irr_ps p=
  let n_outer = mk_pformula_from_tmpl outer n_root_e n_inner_e p in
  let n_p = (BForm ((n_outer, None), None)) in
  let n_p1,quans = norm_exp_min_max n_p in
  let p1 = List.fold_left (fun p1 p2 -> mkAnd p1 p2 no_pos) n_p1
    irr_ps in
  let new_f = if ex_quans = [] then p1 else
    mkExists_with_simpl elim_exists ex_quans p1 None p
  in
  (new_f,quans)

let mk_formula_from_tmp outer n_root_e n_inner_e ex_quans irr_ps p=
  let pr1 = !print_svl in
  let pr2 = !print_formula in
  let pr3 = !print_p_formula in
  Debug.no_3 "mk_formula_from_tmp" pr3 pr1 (pr_list pr2) (pr_pair pr2 pr1)
      (fun _ _ _ -> mk_formula_from_tmp_x outer n_root_e n_inner_e
          ex_quans irr_ps p) outer ex_quans irr_ps

(********************************************************)
       (*****************END DERIVE*****************)
(********************************************************)
