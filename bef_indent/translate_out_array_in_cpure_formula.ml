open Cpure
open Globals
open Debug
open VarGen
(* Translate out array in cpure formula  *)

(* array_transform_info contains 2 fields. *target_array* denotes the array element expression to be translated, while *new_name* denoting the new expression *)
type array_transform_info =
    {
        target_array:exp;
        new_name:exp
    }
;;

type array_transform_return =
    {
        imply_ante: b_formula;
        imply_conseq: b_formula;
        array_to_var: b_formula;
    }
;;

let print_pure = ref (fun (c:formula) -> "printing not initialized");;
let print_p_formula = ref (fun (p:p_formula) -> "printing not initialized");;
let string_of_array_transform_info
      (a:array_transform_info):string=
  "array_transform: { target_array = "^(ArithNormalizer.string_of_exp a.target_array)^"; new_name = "^(ArithNormalizer.string_of_exp a.new_name)^" }"
;;

let get_array_name
      (e:exp):(spec_var)=
  match e with
    | ArrayAt (sv,_,_) -> sv
    | _ -> failwith "get_array_name: Invalid input"
;;

let get_array_at_index
      (e:exp):exp=
  match e with
    | ArrayAt (sv,elst,_)->
          begin
            match elst with
              | [index] -> index
              | _ -> failwith "get_array_at_index: Fail to handle multi-dimension array"
          end
    | _ -> failwith "get_array_at_index: Invalid input"
;;

let is_same_sv
      (sv1:spec_var) (sv2:spec_var):bool=
  match sv1,sv2 with
    | SpecVar (t1,i1,p1), SpecVar (t2,i2,p2)->
          begin
            match p1,p2 with
              | Primed,Primed
              | Unprimed,Unprimed ->
                    if (cmp_typ t1 t2) && (i1=i2) then true else false
              | _,_-> false
          end
;;

let is_same_var
      (v1:exp) (v2:exp):bool =
  match v1, v2 with
    | Var (sv1,_), Var (sv2,_)->
          is_same_sv sv1 sv2
    | Var _, IConst _
    | IConst _, Var _ ->
          false
    | _ -> failwith ("is_same_var:"^(ArithNormalizer.string_of_exp v1)^" "^(ArithNormalizer.string_of_exp v2)^" Invalid input")
;;

let rec is_same_exp
      (e1:exp) (e2:exp):bool=
  match e1,e2 with
  | Null _,Null _ -> true
  | Var (sv1,_), Var (sv2,_)
  | Level (sv1,_),Level (sv2,_) ->
        is_same_sv sv1 sv2
  | IConst (i1,_), IConst (i2,_)->
        i1=i2
  | FConst (i1,_), FConst (i2,_)->
        i1 = i2
  | ListHead (e1,_), ListHead (e2,_)
  | ListTail (e1,_), ListTail (e2,_)
  | ListLength (e1,_),ListLength (e2,_)
  | ListReverse (e1,_),ListReverse (e2,_) ->
        is_same_exp e1 e2
  | Tup2 ((e11,e12),_),Tup2((e21,e22),_)
  | Add (e11,e12,_),Add (e21,e22,_)
  | Subtract (e11,e12,_), Subtract (e21,e22,_)
  | Mult (e11,e12,_), Mult (e21,e22,_)
  | Div (e11,e12,_),Div (e21,e22,_)
  | Max (e11,e12,_),Max (e21,e22,_)
  | Min (e11,e12,_),Min (e21,e22,_)
  | BagDiff (e11,e12,_),BagDiff (e21,e22,_)
  | ListCons (e11,e12,_), ListCons (e21,e22,_) ->
        (is_same_exp e11 e21) && (is_same_exp e12 e22)
  | ListAppend (elst1,_), ListAppend (elst2,_)
  | Bag (elst1,_), Bag (elst2,_)
  | BagUnion (elst1,_), BagUnion (elst2,_)
  | List (elst1,_), List (elst2,_) ->
        List.fold_left2 (fun b e1 e2 -> b && (is_same_exp e1 e2)) true elst1 elst2
  | ArrayAt (sv1,elst1,_), ArrayAt (sv2,elst2,_)
  | Func (sv1,elst1,_), Func (sv2,elst2,_)->
        (is_same_sv sv1 sv2) && (List.fold_left2 (fun b e1 e2 -> b && (is_same_exp e1 e2)) true elst1 elst2)
  | _ -> false
;;

let is_same_array
      (e1:exp) (e2:exp):bool=
  match e1,e2 with
    | ArrayAt (sv1,elst1,_), ArrayAt (sv2,elst2,_) ->
          if is_same_sv sv1 sv2 then true else false
    | _,_ -> failwith "is_same_array: Invalid Input"
;;

(* It may not work properly for not-constant cases because the implementation of is_same_exp *)
let is_same_array_at
      (e1:exp) (e2:exp):bool=
  let is_same_exp_list
        (elst1:exp list) (elst2:exp list):bool=
    List.fold_left2 (fun b e1 e2 -> b && (is_same_exp e1 e2)) true elst1 elst2
  in
  match e1,e2 with
    | ArrayAt (sv1,elst1,_), ArrayAt (sv2,elst2,_) ->
          if (is_same_sv sv1 sv2) && (is_same_exp_list elst1 elst2) then true else false
    | _,_ -> failwith "is_same_array_at: Invalid Input"
;;

let rec remove_dupl_spec_var_list
      (svlst:spec_var list):(spec_var list) =
  let rec helper
        (sv:spec_var) (svlst:spec_var list):(spec_var list) =
    match svlst with
      | h::rest -> if is_same_sv sv h then helper sv rest else h::(helper sv rest)
      | [] -> []
  in
  match svlst with
    | h::rest -> h::(helper h (remove_dupl_spec_var_list rest))
    | [] -> []
;;

let remove_dupl_spec_var_list svlst =
  Debug.no_1 "remove_dupl_spec_var_list" (pr_list string_of_spec_var) (pr_list string_of_spec_var) (fun svlst ->remove_dupl_spec_var_list svlst) svlst
;;

let mk_imply
      (ante:formula) (conseq:formula):formula=
  Or (Not (ante,None,no_pos),conseq,None,no_pos)
;;

let mk_array_new_name_spec_var
      (sv:spec_var) (e:exp):spec_var =
  match sv with
    | SpecVar (typ,id,primed)->
          begin
            match typ with
              | Array (atyp,_)->
                    begin
                      match primed with
                        | Primed ->
                              (*Var( SpecVar (atyp,(id)^"_"^"primed_"^(ArithNormalizer.string_of_exp e),primed),no_pos)*)
                              SpecVar (atyp,(id)^"___"^(ArithNormalizer.string_of_exp e)^"___",primed)
                        | _ -> SpecVar (atyp,(id)^"___"^(ArithNormalizer.string_of_exp e)^"___",primed)
                    end
              | _ -> failwith "mk_array_new_name: Not array type"
          end
;;

let mk_array_new_name_wrapper_for_array
      (e:exp):spec_var =
  match e with
    | ArrayAt (sv,[ne],_) ->
          mk_array_new_name_spec_var sv ne
    | _ ->
          failwith "mk_array_new_name_wrapper_for_array: Invalid input"
;;

let mk_array_new_name
        (sv:spec_var) (e:exp):exp=
    match sv with
      | SpecVar (typ,id,primed)->
            begin
              match typ with
                | Array (atyp,_)->
                      begin
                        match primed with
                          | Primed ->
                                (*Var( SpecVar (atyp,(id)^"_"^"primed_"^(ArithNormalizer.string_of_exp e),primed),no_pos)*)
                                Var( SpecVar (atyp,(id)^"___"^(ArithNormalizer.string_of_exp e)^"___",primed),no_pos)
                          | _ -> Var( SpecVar (atyp,(id)^"___"^(ArithNormalizer.string_of_exp e)^"___",primed),no_pos)
                      end
                | _ -> failwith "mk_array_new_name: Not array type"
            end
;;

let mk_array_new_name
      (sv:spec_var) (e:exp):exp=
  let psv = string_of_spec_var in
  let pe = ArithNormalizer.string_of_exp in
  Debug.no_2 "mk_array_new_name" psv pe pe (fun sv e-> mk_array_new_name sv e) sv e
;;

let rec mk_and_list
      (flst:formula list):formula=
  match flst with
    | [h] -> h
    | h::rest -> And (h,mk_and_list rest,no_pos)
    | [] -> mkTrue no_pos
    (*| [] -> failwith "mk_and_list: Invalid input"*)
;;

let rec mk_or_list
      (flst:formula list):formula=
  match flst with
    | [h] -> h
    | h::rest -> Or (h,mk_or_list rest,None,no_pos)
    | [] -> failwith "mk_and_list: Invalid input"
;;

let rec contain_array
      (f:formula):bool=
  let rec contain_array_exp
        (e:exp):bool=
    match e with
      | ArrayAt _
          -> true
      | Tup2 ((e1,e2),loc)
      | Add (e1,e2,loc)
      | Subtract (e1,e2,loc)
      | Mult (e1,e2,loc)
      | Div (e1,e2,loc)
      | Max (e1,e2,loc)
      | Min (e1,e2,loc)
      | BagDiff (e1,e2,loc)
      | ListCons (e1,e2,loc)->
            ((contain_array_exp e1) or (contain_array_exp e2))
      | TypeCast (_,e1,loc)
      | ListHead (e1,loc)
      | ListTail (e1,loc)
      | ListLength (e1,loc)
      | ListReverse (e1,loc)->
            contain_array_exp e1
      | Null _|Var _|Level _|IConst _|FConst _|AConst _|InfConst _|Tsconst _|Bptriple _|ListAppend _|Template _
      | Func _
      | List _
      | Bag _
      | BagUnion _
      | BagIntersect _
          -> false
      | _ -> failwith "Unexpected case"
  in
  let contain_array_b_formula
        ((p,ba):b_formula):bool=
    match p with
      | Frm _
      | XPure _
      | LexVar _
      | BConst _
      | BVar _
      | BagMin _
      | BagMax _
      (*| VarPerm _*)
      | RelForm _ ->
            false
      | BagIn (sv,e1,loc)
      | BagNotIn (sv,e1,loc)->
            contain_array_exp e1
      | Lt (e1,e2,loc)
      | Lte (e1,e2,loc)
      | Gt (e1,e2,loc)
      | Gte (e1,e2,loc)
      | SubAnn (e1,e2,loc)
      | Eq (e1,e2,loc)
      | Neq (e1,e2,loc)
      | ListIn (e1,e2,loc)
      | ListNotIn (e1,e2,loc)
      | ListAllN (e1,e2,loc)
      | ListPerm (e1,e2,loc)->
            (contain_array_exp e1) || (contain_array_exp e2)
      | EqMax (e1,e2,e3,loc)
      | EqMin (e1,e2,e3,loc)->
            (contain_array_exp e1) || (contain_array_exp e2) || (contain_array_exp e3)
      | _ -> false
  in
  match f with
    | BForm (b,fl)->
          contain_array_b_formula b
    | And (f1,f2,loc)->
          (contain_array f1) || (contain_array f2)
    | AndList lst->
          failwith "contain_array: To Be Implemented"
    | Or (f1,f2,fl,loc)->
          (contain_array f1) || (contain_array f2)
    | Not (not_f,fl,loc)->
          contain_array not_f
    | Forall (sv,f1,fl,loc)->
          contain_array f1
    | Exists (sv,f1,fl,loc)->
          contain_array f1
;;

let contain_array
      (f:formula):bool =
  Debug.no_1 "contain_array" !print_pure string_of_bool (fun f->contain_array f
) f
;;

(* ----------------------------------------------------------------------------------- *)

let rec normalize_not
      (f:formula):formula =
  match f with
    | BForm (b,fl)->
          f
    | And (f1,f2,l)->
          let nf1 = normalize_not f1 in
          let nf2 = normalize_not f2 in
          And (nf1,nf2,l)
    | AndList lst->
          failwith "normalize_not: To Be Implemented"
    | Or (f1,f2,fl,l)->
          let nf1 = normalize_not f1 in
          let nf2 = normalize_not f2 in
          Or (nf1,nf2,fl,l)
    | Not (not_f,fl,l)->
          begin
            match not_f with
              | BForm _ ->
                    f
              | And (f1,f2,l)->
                    let nf1 = normalize_not (Not (f1,None,no_pos)) in
                    let nf2 = normalize_not (Not (f1,None,no_pos)) in
                    Or (nf1,nf2,None,no_pos)
              | Or (f1,f2,fl,l)->
                    let nf1 = normalize_not (Not (f1,None,no_pos)) in
                    let nf2 = normalize_not (Not (f1,None,no_pos)) in
                    And (nf1,nf2,no_pos)
              | AndList _ ->
                    failwith "normalize_not: To Be Implemented"
              | Not (not_f1,fl1,l1) ->
                    not_f1
              | _ ->
                    f
          end
    | Forall _
    | Exists _->
          f
;;

let normalize_not
      (f:formula):formula =
  Debug.no_1 "normalize_not" !print_pure !print_pure (fun f -> normalize_not f) f
;;

let rec normalize_or
      (f:formula):(formula list) =
  match f with
    | BForm (b,fl)->
          [f]
    | And (f1,f2,l)->
          let flst1 = normalize_or f1 in
          let flst2 = normalize_or f2 in
          List.fold_left (
              fun result tmp_f1 -> result @ (List.map (fun tmp_f2 -> And (tmp_f1,tmp_f2,no_pos)) flst2)) [] flst1
    | AndList lst->
          failwith "normalize_or: To Be Implemented"
    | Or (f1,f2,fl,l)->
          let flst1 = normalize_or f1 in
          let flst2 = normalize_or f2 in
          flst1@flst2
    | Not (not_f,fl,l)->
          [f]
    | Forall _
    | Exists _->
          [f]
;;

let normalize_or
      (f:formula):(formula list)=
  let pflst = fun flst -> List.fold_left (fun s f -> s^" "^(!print_pure f)) "" flst in
  Debug.no_1 "normalize_or" !print_pure pflst (fun f -> normalize_or f) f
;;

let print_flst
      (flst:(formula list)):string =
  let helper
        (flst:(formula list)):string =
    List.fold_left (fun s f-> s^" "^(!print_pure f)) "" flst
  in
  "["^(helper flst)^"]"
;;

let print_flstlst
      (flstlst:((formula list) list)):string =
  let helper
        (flstlst:((formula list) list)):string =
    List.fold_left (fun s flst -> s^" "^(print_flst flst)) "" flstlst
  in
  "["^(helper flstlst)^"]"
;;

let rec normalize_to_lst
      (f:formula):((formula list) list) =
  let helper
        (f:formula):((formula list) list) =
    match f with
      | BForm (b,fl)->
            [[f]]
      | And (f1,f2,l)->
            let flst1 = normalize_to_lst f1 in
            let flst2 = normalize_to_lst f2 in
            List.fold_left (
                fun result tmp_f1 -> result @ (List.map (fun tmp_f2 -> tmp_f1@tmp_f2) flst2)) [] flst1
      | AndList lst->
            failwith "normalize_to_lst: To Be Implemented"
      | Or (f1,f2,fl,l)->
            let flst1 = normalize_to_lst f1 in
            let flst2 = normalize_to_lst f2 in
            flst1@flst2
      | Not (not_f,fl,l)->
            [[f]]
      | Forall _
      | Exists _->
            [[f]]
  in
  helper (normalize_not f)
;;

let normalize_to_lst
      (f:formula):((formula list) list) =
  Debug.no_1 "normalize_to_lst" !print_pure print_flstlst (fun f-> normalize_to_lst f) f
;;

let split_for_process
      (f:formula) (cond:formula->bool) :(((formula list) list) * ((formula list) list)) =
  let rec helper_for_lst
        (flstlst:((formula list) list)):(((formula list) list) * ((formula list) list)) =
    match flstlst with
      | h::rest ->
            let (keep,throw) = helper_for_one h in
            let (rest_keep,rest_throw) = helper_for_lst rest in
            (keep::rest_keep,throw::rest_throw)
      | [] -> ([],[])
  and helper_for_one
        (flst:(formula list)):((formula list)*(formula list)) =
    match flst with
      | h::rest ->
            let (rest_k,rest_t) = helper_for_one rest in
            if cond h
            then (h::rest_k,rest_t)
            else (rest_k,h::rest_t)
      | [] ->
            ([],[])
  in
  helper_for_lst (normalize_to_lst f)
;;

let split_for_process
      (f:formula) (cond:formula->bool) : (((formula list) list) * ((formula list) list)) =
  let print_flstlst_pair =
    function
      | (flst1,flst2) -> "("^(print_flstlst flst1)^","^(print_flstlst flst2)^")"
  in
  Debug.no_1 "split_for_process" !print_pure print_flstlst_pair (fun _ -> split_for_process f cond) f
;;

let split_and_process
      (f:formula) (cond:formula->bool) (processor:formula->formula):formula =
  let rec combine
        (flst1:(formula list) list) (flst2:(formula list) list) :((formula list) list) =
    match flst1, flst2 with
      | h1::rest1,h2::rest2 ->
            (h1@h2)::(combine rest1 rest2)
      | [],[]->[]
      | _,_ -> failwith "split_and_process: Invalid input"
  in
  let (keeplst,throwlst) = split_for_process f cond in
  let nkeeplst = List.map (fun flst -> [processor (mk_and_list flst)]) keeplst in
  let n_flst = combine nkeeplst throwlst in
  mk_or_list (List.map (fun flst -> mk_and_list flst) n_flst)
;;

let split_and_process
      (f:formula) (cond:formula->bool) (processor:formula->formula):formula =
  Debug.no_1 "split_and_process" !print_pure !print_pure (fun _ -> split_and_process f cond processor) f
;;

let rec can_be_simplify
      (f:formula) : bool =
  let rec is_valid_forall_helper_b_formula
        ((p,ba):b_formula) (sv:spec_var):bool =
    let rec is_valid_forall_helper_exp
          (e:exp) (sv:spec_var) :bool =
      match e with
        | ArrayAt (arr,[index],loc) ->
              if is_same_sv arr sv
              then false
              else
                begin
                  match index with
                    | Var (i_sv,_) ->
                          not (is_same_sv i_sv sv)
                    | IConst _ ->
                          true
                    | _ ->
                          false
                end
        | ArrayAt _ ->
              false
        | Add (e1,e2,loc)
        | Subtract (e1,e2,loc)
        | Mult (e1,e2,loc)
        | Div (e1,e2,loc)->
              (is_valid_forall_helper_exp e1 sv) && (is_valid_forall_helper_exp e2 sv)
        | Var _
        | IConst _ ->
              true
        | _ -> failwith "is_valid_forall_helper_exp: To Be Implemented"
    in
    let is_valid_forall_helper_p_formula
          (p:p_formula) (sv:spec_var):bool =
      match p with
        | BConst _
        | BVar _
        | Frm _
        | XPure _
        | LexVar _
        | RelForm _ ->
              true
        | Lt (e1,e2,loc)
        | Lte (e1,e2,loc)
        | Gt (e1,e2,loc)
        | Gte (e1,e2,loc)
        | Eq (e1,e2,loc)
        | Neq (e1,e2,loc) ->
              (is_valid_forall_helper_exp e1 sv) && (is_valid_forall_helper_exp e2 sv)
        | _ ->
              failwith "is_valid_forall_helper_p_formula: To Be Implemented"
    in
    is_valid_forall_helper_p_formula p sv
  in
  let rec is_valid_forall
        (f1:formula) (sv:spec_var) : bool =
    match f1 with
      | BForm (b,fl)->
            is_valid_forall_helper_b_formula b sv
      | And (f1,f2,_)
      | Or (f1,f2,_,_)->
            (is_valid_forall f1 sv) && (is_valid_forall f2 sv)
      | AndList lst ->
            failwith "is_valid_forall: To Be Implemented"
      | Not (not_f,fl,loc)->
            (is_valid_forall not_f sv)
      (* | Forall (sv,f1,fl,loc) -> *)
      (*       false *)
      (* | Exists _ -> *)
      (*       false *)
      | Forall (nsv,nf,fl,loc) ->
            is_valid_forall nf nsv
      | Exists (nsv,nf,fl,loc) ->
            is_valid_forall nf nsv
  in
  let is_valid_forall
        (f1:formula) (sv:spec_var) : bool =
    Debug.no_2 "is_valid_forall" !print_pure string_of_spec_var string_of_bool (fun f sv-> is_valid_forall f sv) f1 sv
  in
  match f with
    | BForm (b,fl)->
          true
    | And _
    | AndList _
    | Or _->
          failwith ("can_be_simplify:"^(!print_pure f)^" Invalid Input")
    | Not (not_f,fl,loc)->
          (can_be_simplify not_f) || (not (contain_array not_f))
    | Forall (sv,f1,fl,loc) ->
          (is_valid_forall f1 sv) || (not (contain_array f1))
    | Exists (sv,f1,fl,loc) ->
          (is_valid_forall f1 sv) || (not (contain_array f1))
;;

let can_be_simplify
      (f:formula):bool =
  Debug.no_1 "can_be_simplify" !print_pure string_of_bool (fun f->can_be_simplify f) f
;;

(* let array_simplify *)
(*       (f:formula) (processor:formula->formula):formula = *)
(*   split_and_process f can_be_simplify processor *)
(* ;; *)

(* -------------------------------------------------------------------------------------------- *)
(* apply index replacement to array formula using quantifiers. If fail to replace, return None. *)

let rec process_quantifier
      (f:formula) :(formula)=
  let  get_array_index_replacement (* The input can be any form *)
        (f:formula) (sv:spec_var):(exp option) =
    let rec get_array_index_replacement_helper (* only pick up forms like !(i=c) *)
          (flst:formula list) (sv:spec_var):(exp option) =
      match flst with
        | h::rest ->
              begin
                match h with
                  | Not (BForm ((Eq(e1,e2,_),_),_),_,_)
                  | BForm((Neq (e1,e2,_),_),_)->
                        begin
                          match e1,e2 with
                            | Var (sv1,_),Var (sv2,_) ->
                                  if is_same_sv sv1 sv
                                  then Some (Var (sv2,no_pos))
                                  else
                                    if is_same_sv sv2 sv
                                    then Some (Var (sv1,no_pos))
                                    else
                                      get_array_index_replacement_helper rest sv
                            | Var (sv1,_), IConst i
                            | IConst i, Var (sv1,_) ->
                                  if is_same_sv sv1 sv
                                  then Some (IConst i)
                                  else get_array_index_replacement_helper rest sv
                            | _, _ ->
                                  get_array_index_replacement_helper rest sv
                        end
                  | _ -> get_array_index_replacement_helper rest sv
              end
        | [] ->
              None
    in
    let flst = normalize_or (normalize_not f) in
    get_array_index_replacement_helper flst sv
  in
  let get_array_index_replacement
        (f:formula) (sv:spec_var):(exp option) =
    let peo = function
      | Some e -> ArithNormalizer.string_of_exp e
      | None -> "None"
    in
    Debug.no_2 "get_array_index_replacement" !print_pure string_of_spec_var peo (fun f sv -> get_array_index_replacement f sv) f sv
  in
  (* let rec replace_index *)
  (*       (f:formula) (sv:spec_var) (r:exp option):(formula) = *)
  (*   let rec replace_helper *)
  (*         ((p,ba):b_formula) (sv:spec_var) (r:exp option):(b_formula) = *)
  (*     let rec replace_helper_exp *)
  (*           (e:exp) (sv:spec_var) (r:exp option):(exp) = *)
  (*       match e with *)
  (*         | ArrayAt (arr,[index],loc) -> *)
  (*               begin *)
  (*                 match index with *)
  (*                   | Var (i_sv,_) -> *)
  (*                         if is_same_sv i_sv sv *)
  (*                         then *)
  (*                           begin *)
  (*                             match r with *)
  (*                               | Some n_index -> ArrayAt (arr,[n_index],loc) *)
  (*                               | None -> e *)
  (*                           end *)
  (*                         else *)
  (*                           e *)
  (*                   | _ -> e *)
  (*               end *)
  (*         | ArrayAt _ -> *)
  (*               failwith "replace_helper_exp: Fail to handle multi-dimension array" *)
  (*         | Add (e1,e2,loc) *)
  (*         | Subtract (e1,e2,loc) *)
  (*         | Mult (e1,e2,loc) *)
  (*         | Div (e1,e2,loc)-> *)
  (*               let (ne1,ne2) = (replace_helper_exp e1 sv r, replace_helper_exp e2 sv r) in *)
  (*               begin *)
  (*                 match e with *)
  (*                   | Add _ -> Add (ne1,ne2,loc) *)
  (*                   | Subtract _ -> Subtract (ne1,ne2,loc) *)
  (*                   | Mult _ -> Mult (ne1,ne2,loc) *)
  (*                   | Div _ -> Div (ne1,ne2,loc) *)
  (*                   | _ -> failwith "replace_helper_exp: Invalid Input" *)
  (*               end *)
  (*         | Var _ *)
  (*         | IConst _ -> *)
  (*               e *)
  (*         | _ -> failwith "replace_helper_exp: To Be Implemented" *)
  (*     in *)
  (*     let replace_helper_p *)
  (*           (p:p_formula) (sv:spec_var) (r:exp option): (p_formula) = *)
  (*       match p with *)
  (*         | BConst _ *)
  (*         | BVar _ -> *)
  (*               p *)
  (*         | Lt (e1,e2,loc) *)
  (*         | Lte (e1,e2,loc) *)
  (*         | Gt (e1,e2,loc) *)
  (*         | Gte (e1,e2,loc) *)
  (*         | Eq (e1,e2,loc) *)
  (*         | Neq (e1,e2,loc) -> *)
  (*               let (ne1,ne2) = ( replace_helper_exp e1 sv r, replace_helper_exp e2 sv r ) in *)
  (*               begin *)
  (*                 match p with *)
  (*                   | Lt _ -> *)
  (*                         Lt (ne1,ne2,loc) *)
  (*                   | Lte _ -> *)
  (*                         Lte (ne1,ne2,loc) *)
  (*                   | Gt _ -> *)
  (*                         Gt (ne1,ne2,loc) *)
  (*                   | Gte _ -> *)
  (*                         Gte (ne1,ne2,loc) *)
  (*                   | Eq _ -> *)
  (*                         Eq (ne1,ne2,loc) *)
  (*                   | Neq _ -> *)
  (*                         Neq (ne1,ne2,loc) *)
  (*                   | _ -> failwith "replace_helper_p: Invalid Input" *)
  (*               end *)
  (*         | _ -> *)
  (*               failwith "replace_helper_p: To Be Implemented" *)
  (*     in *)
  (*     (replace_helper_p p sv r,None) *)
  (*   in *)
  (*   match f with *)
  (*     | BForm (b,fl)-> *)
  (*           BForm (replace_helper b sv r,fl) *)
  (*     | And (f1,f2,loc)-> *)
  (*           And (replace_index f1 sv r, replace_index f2 sv r,loc) *)
  (*     | AndList lst-> *)
  (*           failwith "replace_index: To Be Implemented" *)
  (*     | Or (f1,f2,fl,loc)-> *)
  (*           Or (replace_index f1 sv r, replace_index f2 sv r,fl,loc) *)
  (*     | Not (not_f,fl,loc)-> *)
  (*           Not (replace_index not_f sv r,fl,loc) *)
  (*     | Forall _ *)
  (*     | Exists _ -> *)
  (*           failwith "replace_index: nested quantifiers" *)
  (* in *)
  (* let replace_index *)
  (*       (f:formula) (sv:spec_var) (r:exp option):(formula) = *)
  (*   let peo = function *)
  (*     | Some e -> ArithNormalizer.string_of_exp e *)
  (*     | None -> "None" *)
  (*   in *)
  (*   let pfo = function *)
  (*     | Some f -> !print_pure f *)
  (*     | None -> "None" *)
  (*   in *)
  (*   Debug.no_3 "replace_index" !print_pure string_of_spec_var peo !print_pure (fun f sv r -> replace_index f sv r) f sv r *)
  (* in *)
  let replace
        ((p,ba):b_formula) (ctx:((spec_var * exp) list)):b_formula =
    let rec find_replace
          (sv:spec_var) (ctx:((spec_var * exp) list)): (exp option) =
      match ctx with
        | (nsv,ne)::rest ->
              if is_same_sv nsv sv
              then Some ne
              else find_replace sv rest
        | [] ->
              None
    in
    let replace_exp
          (e:exp) (ctx:((spec_var * exp) list)):exp =
      match e with
        | ArrayAt (arr,[index],loc) ->
              begin
                match index with
                  | Var (sv,_)->
                        begin
                          match find_replace sv ctx with
                            | Some rep ->
                                  ArrayAt (arr, [rep], loc)
                            | None ->
                                  e
                        end
                  | IConst _ ->
                        e
                  | _ ->
                        failwith ("replace_exp: Invalid index form "^(ArithNormalizer.string_of_exp e))
              end
        | ArrayAt _ ->
              failwith "replace_exp: cannot handle multi-dimensional array"
        | _ ->
              e
    in
    match p with
      | Lt (e1, e2, loc)->
            (Lt (replace_exp e1 ctx, replace_exp e2 ctx, loc),ba)
      | Lte (e1, e2, loc)->
            (Lte (replace_exp e1 ctx, replace_exp e2 ctx, loc),ba)
      | Gt (e1, e2, loc)->
            (Gt (replace_exp e1 ctx, replace_exp e2 ctx, loc),ba)
      | Gte (e1, e2, loc)->
            (Gte (replace_exp e1 ctx, replace_exp e2 ctx, loc),ba)
      | SubAnn (e1, e2, loc)->
            (SubAnn (replace_exp e1 ctx, replace_exp e2 ctx, loc),ba)
      | Eq (e1, e2, loc)->
            (Eq (replace_exp e1 ctx, replace_exp e2 ctx, loc),ba)
      | Neq (e1, e2, loc)->
            (Neq (replace_exp e1 ctx, replace_exp e2 ctx, loc),ba)
      | BConst _
      | BVar _
      | Frm _
      | XPure _
      | LexVar _
      | RelForm _->
            (p,ba)
      | _ -> failwith ("replace: "^(!print_p_formula p)^" To Be Implemented")
  in
  let rec process_helper
        (f:formula) (ctx:((spec_var * exp) list)) :(formula)=
    match f with
      | BForm (b,fl)->
            BForm (replace b ctx,fl)
      | And (f1,f2,loc)->
            And (process_helper f1 ctx, process_helper f2 ctx,loc)
      | AndList lst->
            failwith ("process_helper: "^(!print_pure f)^" To Be Implemented")
      | Or (f1,f2,fl,loc)->
            Or (process_helper f1 ctx,process_helper f2 ctx,fl,loc)
      | Not (not_f,fl,loc)->
            Not (process_helper not_f ctx,fl,loc)
      | Forall (sv,f1,fl,loc)->
            let r = get_array_index_replacement f1 sv in
            begin
              match r with
                | Some re ->
                      Forall (sv,process_helper f1 ((sv,re)::ctx),fl,loc)
                | None ->
                      Forall (sv,f1,fl,loc)
            end
      | Exists (sv,f1,fl,loc)->
            let r = get_array_index_replacement (Not (f1,None,no_pos)) sv in
            begin
              match r with
                | Some re ->
                      Exists (sv,process_helper f1 ((sv,re)::ctx),fl,loc)
                | None ->
                      Exists (sv,f1,fl,loc)
            end
  in
  process_helper f []
;;

let process_quantifier
      (f:formula) : (formula) =
  let pfo = function
    | Some fo -> !print_pure fo
    | None -> "None"
  in
  Debug.no_1 "process_quantifier" !print_pure !print_pure (fun f -> process_quantifier f) f
;;


(* ---------------------------------------------------------------------------------------------------- *)

let name_counter = ref 0;;
let rec standarize_array_formula
      (f:formula):(formula * (formula list) * (spec_var list))=
  (* the (spec_var list) type return value is not used here *)

  let mk_new_name ():spec_var =
    let _ = name_counter:= !name_counter + 1 in
    mk_typed_spec_var Int ("tarrvar"^(string_of_int (!name_counter)))
  in
  let rec mk_index_form
        (e:exp):(exp * ((exp * exp) list) * (spec_var list))=
    match e with
      | ArrayAt (sv,elst,loc) ->
            let nsv = mk_new_name () in
            let nname = Var (nsv,no_pos) in
            let (ne,eelst,svlst) = standarize_exp e in
            (nname,(nname,ne)::eelst,nsv::svlst)
      | Add (e1,e2,loc)
      | Subtract (e1,e2,loc)
      | Mult (e1,e2,loc)
      | Div (e1,e2,loc)->
            let nsv = mk_new_name () in
            let nname = Var (nsv,no_pos) in
            let (ne1,eelst1,svlst1) = standarize_exp e1 in
            let (ne2,eelst2,svlst2) = standarize_exp e2 in
            let neelst =
              begin
                match e with
                  | Add _ ->(nname,Add (ne1,ne2,no_pos))::(eelst1@eelst2)
                  | Subtract _ ->(nname,Subtract (ne1,ne2,no_pos))::(eelst1@eelst2)
                  | Mult _ -> (nname,Mult (ne1,ne2,no_pos))::(eelst1@eelst2)
                  | Div _ ->(nname,Div (ne1,ne2,no_pos))::(eelst1@eelst2)
                  | _ -> failwith "standarize_exp: Invalid Input"
              end
            in
            (nname,neelst, (nsv::(svlst1@svlst2)))
      | Var _
      | IConst _ ->
            (e,[],[])
      | _ -> failwith "mk_index_form: Invalid case of index"
  and standarize_exp
        (e:exp):(exp * ((exp * exp) list) * (spec_var list))=
    match e with
      | ArrayAt (sv,elst,loc) ->
            begin
              match elst with
                | [h] ->
                      let (nindex,eelst,svlst) = mk_index_form h in
                      (ArrayAt (sv,[nindex],loc),eelst,svlst)
                | _ -> failwith "standarize_exp: Fail to handle multi-dimension array"
            end
      | Add (e1,e2,loc)->
            let (ne1,eelst1,svlst1) = standarize_exp e1 in
            let (ne2,eelst2,svlst2) = standarize_exp e2 in
            (Add (ne1,ne2,loc),eelst1@eelst2,svlst1@svlst2)
      | Subtract (e1,e2,loc)->
            let (ne1,eelst1,svlst1) = standarize_exp e1 in
            let (ne2,eelst2,svlst2) = standarize_exp e2 in
            (Subtract (ne1,ne2,loc),eelst1@eelst2,svlst1@svlst2)
      | Mult (e1,e2,loc)->
            let (ne1,eelst1,svlst1) = standarize_exp e1 in
            let (ne2,eelst2,svlst2) = standarize_exp e2 in
            (Mult (ne1,ne2,loc),eelst1@eelst2,svlst1@svlst2)
      | Div (e1,e2,loc)->
            let (ne1,eelst1,svlst1) = standarize_exp e1 in
            let (ne2,eelst2,svlst2) = standarize_exp e2 in
            (Div (ne1,ne2,loc),eelst1@eelst2,svlst1@svlst2)
      | IConst _
      | Var _
      | Null _ ->
            (e,[],[])
      | _ -> failwith ("standarzie_exp: "^(ArithNormalizer.string_of_exp e)^" To Be Implemented")
  in
  let standarize_p_formula
        (p:p_formula):(p_formula * (p_formula list) * (spec_var list))=
    let rec mk_p_formula_from_eelst
          (eelst: ( (exp * exp) list)):(p_formula list)=
      match eelst with
        | (e1,e2)::rest ->
              (Eq (e1,e2,no_pos))::(mk_p_formula_from_eelst rest)
        | [] -> []
    in
    match p with
      | Lt (e1, e2, loc)->
            let (ne1,eelst1,svlst1) = standarize_exp e1 in
            let (ne2,eelst2,svlst2) = standarize_exp e2 in
            (Lt (ne1,ne2,loc),mk_p_formula_from_eelst (eelst1@eelst2),svlst1@svlst2)
      | Lte (e1, e2, loc)->
           let (ne1,eelst1,svlst1) = standarize_exp e1 in
            let (ne2,eelst2,svlst2) = standarize_exp e2 in
            (Lte (ne1,ne2,loc),mk_p_formula_from_eelst (eelst1@eelst2),svlst1@svlst2)
      | Gt (e1, e2, loc)->
           let (ne1,eelst1,svlst1) = standarize_exp e1 in
            let (ne2,eelst2,svlst2) = standarize_exp e2 in
            (Gt (ne1,ne2,loc),mk_p_formula_from_eelst (eelst1@eelst2),svlst1@svlst2)
      | Gte (e1, e2, loc)->
           let (ne1,eelst1,svlst1) = standarize_exp e1 in
            let (ne2,eelst2,svlst2) = standarize_exp e2 in
            (Gte (ne1,ne2,loc),mk_p_formula_from_eelst (eelst1@eelst2),svlst1@svlst2)
      | SubAnn (e1, e2, loc)->
           let (ne1,eelst1,svlst1) = standarize_exp e1 in
            let (ne2,eelst2,svlst2) = standarize_exp e2 in
            (SubAnn (ne1,ne2,loc),mk_p_formula_from_eelst (eelst1@eelst2),svlst1@svlst2)
      | Eq (e1, e2, loc)->
           let (ne1,eelst1,svlst1) = standarize_exp e1 in
            let (ne2,eelst2,svlst2) = standarize_exp e2 in
            (Eq (ne1,ne2,loc),mk_p_formula_from_eelst (eelst1@eelst2),svlst1@svlst2)
      | Neq (e1, e2, loc)->
            let (ne1,eelst1,svlst1) = standarize_exp e1 in
            let (ne2,eelst2,svlst2) = standarize_exp e2 in
            (Neq (ne1,ne2,loc),mk_p_formula_from_eelst (eelst1@eelst2),svlst1@svlst2)
      | BConst _
      | BVar _
      | Frm _
      | XPure _
      | LexVar _
      | RelForm _->
            (p,[],[])
      | BagSub _
      | ListIn _
      | ListNotIn _
      | ListAllN _
      | ListPerm _
      | EqMax _
      | EqMin _
      | BagIn _
      | BagNotIn _
      | BagMin _
      | BagMax _ ->
      (*| VarPerm _ ->*)
            failwith ("standarize_p_formula 1: "^(!print_p_formula p)^" To Be Implemented")
      (* | RelForm _ -> *)
      (*       failwith ("standarize_p_formula 2: "^(!print_p_formula p)^" To Be Implemented") *)
  in
  match f with
    | BForm ((p,_),fl)->
          let (np,plst,svlst) = standarize_p_formula p in
          let flst = List.map (fun p -> BForm((p,None),None)) plst in
          (BForm ((np,None),None),flst,svlst)
    | And (f1,f2,l)->
          let (nf1,flst1,svlst1) = standarize_array_formula f1 in
          let (nf2,flst2,svlst2) = standarize_array_formula f2 in
          (And (nf1,nf2,l),flst1@flst2,svlst1@svlst2)
    | AndList lst->
          (* let (flst,flstlst) = *)
          (*   (List.split (List.map (fun (t,f) -> let (nf,nflst) = (standarize_array_formula f) in ((t,nf),nflst)) lst)) in *)
          (* let nflst = List.fold_left (fun result l -> result@l) [] flstlst in *)
          (* (AndList flst,nflst) *)
          failwith "standarize_array_formula: AndList To Be Implemented"
    | Or (f1,f2,fl,l)->
          let (nf1,flst1,svlst1) = standarize_array_formula f1 in
          let (nf2,flst2,svlst2) = standarize_array_formula f2 in
          (Or (nf1,nf2,fl,l),flst1@flst2,svlst1@svlst2)
    | Not (f,fl,l)->
          let (nf1,flst1,svlst) = standarize_array_formula f in
          (Not (nf1,fl,l),flst1,svlst)
    | Forall (sv,f,fl,l)->
          let (nf1,flst1,svlst) = standarize_array_formula f in
          (Forall (sv,nf1,fl,l),flst1,svlst)
    | Exists (sv,f,fl,l)->
          let (nf1,flst1,svlst) = standarize_array_formula f in
          (Exists (sv,nf1,fl,l),flst1,svlst)
;;

let rec standarize_one_formula
      (f:formula):formula=
  let helper
        (f:formula):formula=
    match f with
      | BForm (b,fl)->
            let (nf,flst,svlst) = standarize_array_formula f in
            let fbody = mk_and_list (nf::flst) in
            if List.length svlst = 0
            then fbody
            else
              (* let fbase = Exists (List.hd svlst,fbody,None,no_pos) in *)
              (* List.fold_left (fun nf sv -> Exists (sv,nf,None,no_pos)) fbase (List.tl svlst) *)
              fbody
      | And (f1,f2,l)->
            And (standarize_one_formula f1,standarize_one_formula f2,l)
      | AndList lst->
            AndList (List.map (fun (t,f)->(t,standarize_one_formula f)) lst)
      | Or (f1,f2,fl,l)->
            Or (standarize_one_formula f1,standarize_one_formula f2,fl,l)
      | Not (f,fl,l)->
            Not (standarize_one_formula f,fl,l)
      | Forall (sv,f,fl,l)->
            Forall (sv,standarize_one_formula f,fl,l)
      | Exists (sv,f,fl,l)->
            Exists (sv,standarize_one_formula f,fl,l)
  in
  (helper f)
;;

let standarize_one_formula
      (f:formula):formula=
  let pf = !print_pure in
  Debug.no_1 "standarize_one_formula" pf pf (fun f-> standarize_one_formula f) f
;;

(* let standarize_array_imply *)
(*       (ante:formula) (conseq:formula):(formula * formula)= *)
(*   let (n_conseq,flst,svlst) = standarize_array_formula conseq in *)
(*   let ante = mk_and_list (ante::flst) in *)
(*   let n_ante = standarize_one_formula ante in *)
(*   (n_ante,n_conseq) *)
(* ;; *)

let standarize_array_imply
      (ante:formula) (conseq:formula):(formula * formula)=
  let (n_ante,flst1,_) = standarize_array_formula ante in
  let (n_conseq,flst2,_) = standarize_array_formula conseq in
  let n_ante = mk_and_list (n_ante::(flst1@flst2)) in
  (n_ante,n_conseq)
;;

let standarize_array_imply
      (ante:formula) (conseq:formula):(formula * formula) =
  let pf = !print_pure in
  let pr =
    function
      |(a,b) -> "("^(!print_pure a)^", "^(!print_pure b)^")"
  in
  Debug.no_2 "standarize_array_imply" pf pf pr (fun ante conseq -> standarize_array_imply ante conseq) ante conseq
;;


(* ------------------------------------------------------------------- *)
(* For update_array_1d *)
let rec translate_array_relation
      (f:formula):formula=
  let translate_array_relation_in_b_formula
        ((p,ba):b_formula):formula option=
    let helper
          (p:p_formula):formula option=
      match p with
        | RelForm (SpecVar (_,id,_),elst,loc) ->
              if id="update_array_1d"
              then
                begin
                  match (List.nth elst 0), (List.nth elst 1) with
                    | Var (SpecVar (t0,id0,p0) as old_array_sv,_), Var (SpecVar (t1,id1,p1) as new_array_sv,_) ->
                          let new_array_at = ArrayAt (SpecVar (Array (t1,1000),id1,p1),[List.nth elst 3],no_pos) in
                          let new_eq = BForm ((Eq (new_array_at,List.nth elst 2,no_pos),None),None )in
                          let new_q = mk_spec_var "i" in
                          let new_ante = BForm((Neq (Var (new_q,no_pos), List.nth elst 3,no_pos),None),None) in
                          let new_conseq = BForm((Eq (ArrayAt (SpecVar (Array (t1,1000),id1,p1),[Var (new_q,no_pos)],no_pos), ArrayAt (SpecVar (Array (t0,1000),id0,p0),[Var (new_q,no_pos)],no_pos),no_pos),None),None) in
                          let new_forall = Forall(new_q,mk_imply new_ante new_conseq,None,no_pos) in
                          Some (And (new_eq,new_forall,no_pos))
                    | _ -> failwith "translate_array_relation: Not Var"
                end
              else
                None
        | _ -> None
    in
    helper p
  in
  match f with
    | BForm (b,fl)->
          begin
            match translate_array_relation_in_b_formula b with
              | Some nf -> nf
              | None -> f
          end
    | And (f1,f2,loc)->
          And (translate_array_relation f1,translate_array_relation f2,loc)
    | AndList lst->
          AndList (List.map (fun (t,f)-> (t,translate_array_relation f)) lst)
    | Or (f1,f2,fl,loc)->
          Or (translate_array_relation f1,translate_array_relation f2,fl,loc)
    | Not (f,fl,loc)->
          Not (translate_array_relation f,fl,loc)
    | Forall (sv,f,fl,loc)->
          Forall (sv,translate_array_relation f,fl,loc)
    | Exists (sv,f,fl,loc)->
          Exists (sv,translate_array_relation f,fl,loc)
;;

let translate_array_relation
      (f:formula):formula=
  let pf = !print_pure in
  Debug.no_1 "translate_array_relation" pf pf (fun f-> translate_array_relation f) f
;;
(* ------------------------------------------------------------------- *)
let translate_array_equality
      (f:formula) (scheme:((spec_var * (exp list)) list)):(formula option)=
  let produce_equality
        (sv1:spec_var) (sv2:spec_var) (indexlst: (exp list)):(formula list) =
    List.map (fun index -> BForm ((Eq (mk_array_new_name sv1 index,mk_array_new_name sv2 index,no_pos),None),None) ) indexlst
  in
  let rec find_match
        (scheme:((spec_var * (exp list)) list)) (sv:spec_var) : ((exp list) option) =
    match scheme with
      | (nsv,elst)::rest ->
            if is_same_sv nsv sv
            then Some elst
            else
              find_match rest sv
      | [] -> None
  in
  let helper_b_formula
        ((p,ba):b_formula) (scheme:((spec_var * (exp list)) list)):(formula list) =
    match p with
      | Eq (Var (sv1,_), Var (sv2,_),loc) ->
            if is_same_sv sv1 sv2
            then []
            else
               begin
                 match find_match scheme sv1, find_match scheme sv2 with
                   | Some indexlst1, Some indexlst2 ->
                         (produce_equality sv1 sv2 indexlst1)@(produce_equality sv1 sv2 indexlst2)
                   | Some indexlst,_
                   | _,Some indexlst ->
                         produce_equality sv1 sv2 indexlst
                   | _,_ -> []
               end
       | _ -> []
   in
   let rec helper
         (f:formula) (scheme:((spec_var * (exp list)) list)):formula list=
     match f with
       | BForm (b,fl)->
             helper_b_formula b scheme
       | And (f1,f2,loc)->
             (helper f1 scheme) @ (helper f2 scheme)
       | AndList lst->
             failwith "translate_array_equality: AndList To Be Implemented"
       | Or (f1,f2,fl,loc)->
             (helper f1 scheme) @ (helper f2 scheme)
       | Not (f,fl,loc)->
             helper f scheme
       | Forall (sv,f,fl,loc)->
             []
       | Exists (sv,f,fl,loc)->
             []
   in
   match helper f scheme with
     | [] -> None
     | lst -> Some (mk_and_list lst)
;;

let translate_array_equality
      (f:formula) (scheme: ((spec_var * (exp list)) list)):(formula option) =
  let string_of_translate_scheme
        (ts:((spec_var * (exp list)) list)):string=
    let string_of_item
          ((arr,indexlst):(spec_var * (exp list))):string=
      let string_of_indexlst = List.fold_left (fun s e -> s^" "^(ArithNormalizer.string_of_exp e)^" ") "" indexlst in
      "array: "^(string_of_spec_var arr)^" { "^(string_of_indexlst)^"}"
    in
    List.fold_left (fun s item -> (string_of_item item)^" "^s) "" ts
  in
  let pfo = function
    | Some f -> !print_pure f
    | None -> "None"
  in
  Debug.no_2 "translate_array_equality" !print_pure string_of_translate_scheme pfo (fun f scheme -> translate_array_equality f scheme) f scheme
;;
(* ------------------------------------------------------------------- *)

let f_hole_name = ref 0;;
let rec split_formula
      (f:formula) (cond:formula -> bool):(formula * ((formula * spec_var) list)) =
  match f with
    | BForm (b,fl)->
          if cond f
          then (f,[])
          else
            let nname = "f___hole_"^(string_of_int !f_hole_name) in
            let _ = f_hole_name :=!f_hole_name + 1 in
            let nsv = mk_spec_var nname in
            let hole = BVar (nsv,no_pos) in
            let nf = BForm ((hole,None),fl) in
            (nf,[(f,nsv)])
    | And (f1,f2,loc)->
          let (nf1,sv2p1) = split_formula f1 cond in
          let (nf2,sv2p2) = split_formula f2 cond in
          (And (nf1,nf2,loc),sv2p1@sv2p2)
    | AndList lst->
          failwith "split_formula: AndList To Be Implemented"
    | Or (f1,f2,fl,loc)->
          let (nf1,sv2p1) = split_formula f1 cond in
          let (nf2,sv2p2) = split_formula f2 cond in
          (Or (nf1,nf2,fl,loc),sv2p1@sv2p2)
    | Not (not_f,fl,loc)->
          let (nnot_f,sv2p) = split_formula not_f cond in
          (Not (nnot_f,fl,loc),sv2p)
    | Forall (sv,f1,fl,loc)->
          if cond f
          then (f,[])
          else
            let nname = "f___hole_"^(string_of_int !f_hole_name) in
            let _ = f_hole_name := !f_hole_name + 1 in
            let nsv = mk_spec_var nname in
            let hole = BVar (nsv,no_pos) in
            let nf = BForm ((hole,None),fl) in
            (nf,[(f,nsv)])
    | Exists (sv,f1,fl,loc)->
          if cond f
          then (f,[])
          else
            let nname = "f___hole_"^(string_of_int !f_hole_name) in
            let _ = f_hole_name := !f_hole_name + 1 in
            let nsv = mk_spec_var nname in
            let hole = BVar (nsv,no_pos) in
            let nf = BForm ((hole,None),fl) in
            (nf,[(f,nsv)])
          (* failwith "exists!!!!" *)
;;

let split_formula
      (f:formula) (cond:formula -> bool):(formula * ((formula * spec_var) list)) =
  let psv2f = List.fold_left (fun s (f,sv) -> (s^"("^(!print_pure f)^","^(string_of_spec_var sv)^")")) "" in
  let presult = function
    | (f,sv2f) -> "new f:"^(!print_pure f)^" sv2f:"^(psv2f sv2f)
  in
  Debug.no_1 "split_formula" !print_pure presult (fun _ -> split_formula f cond) f
;;

let rec combine_formula
      (f:formula) (sv2f:((formula * spec_var) list)):formula =
  let rec find_match
        (holesv:spec_var) (sv2f:((formula * spec_var) list)):formula option =
    match sv2f with
      | (f,sv)::rest ->
        if is_same_sv sv holesv
        then Some f
        else find_match holesv rest
      | [] -> None
  in
  let contain
        ((p,ba):b_formula) (sv2f:((formula * spec_var) list)):formula option =
    match p with
      | BVar (holesv,_) ->
            find_match holesv sv2f
      | Lt (e1, e2, loc)
      | Lte (e1, e2, loc)
      | Gt (e1, e2, loc)
      | Gte (e1, e2, loc)
      | SubAnn (e1, e2, loc)
      | Eq (e1, e2, loc)
      | Neq (e1, e2, loc)
      | BagSub (e1, e2, loc)
      | ListIn (e1, e2, loc)
      | ListNotIn (e1, e2, loc)
      | ListAllN (e1, e2, loc)
      | ListPerm (e1, e2, loc)->
            begin
              match e1,e2 with
                | Var (holesv1,_),_
                | _,Var (holesv1,_) ->
                      find_match holesv1 sv2f
                | _ -> None
            end
      | _ -> None
  in
  match f with
    | BForm (b,fl)->
          begin
            match contain b sv2f with
              | Some nf-> nf
              | None -> f
          end
    | And (f1,f2,loc)->
          And (combine_formula f1 sv2f,combine_formula f2 sv2f,loc)
    | AndList lst->
          failwith "split_formula: AndList To Be Implemented"
    | Or (f1,f2,fl,loc)->
          Or (combine_formula f1 sv2f,combine_formula f2 sv2f,fl,loc)
    | Not (not_f,fl,loc)->
          Not (combine_formula not_f sv2f,fl,loc)
    | Forall (sv,f1,fl,loc)->
          f
    | Exists (sv,f1,fl,loc)->
          f
;;

let combine_formula
      (f:formula) (sv2f:((formula * spec_var) list)):formula =
  let psv2f = List.fold_left (fun s (f,sv) -> s^"("^(!print_pure f)^","^(string_of_spec_var sv)^")") "" in
  Debug.no_2 "combine_formula" !print_pure psv2f !print_pure (fun f sv2f -> combine_formula f sv2f) f sv2f
;;

let split_and_combine
      (processor:formula -> formula) (cond:formula->bool) (f:formula):formula =
  let (keep,sv2f) = split_formula f cond in
  combine_formula (processor keep) sv2f
;;

let split_and_combine
      (processor:formula -> formula) (cond:formula->bool) (f:formula):formula =
  if !Globals.array_translate
  then split_and_combine processor cond f
  else processor f
;;

(* let weaken_array_in_imply_LHS *)
(*       (processor:formula -> formula -> 'a) (ante:formula) (conseq:formula):'a = *)
(*   let nante = new_translate_out_array_in_one_formula *)

(* ------------------------------------------------------------------- *)
(* !!!!! let extract_scheme_for_quantifier *)
(*       (f:formula):(spec_var option) = *)
(*   if can_be_simplify f *)
(*   then None *)
(*   else *)
(*     match f with *)
(*       | Forall (sv,f1,fl,l) -> *)
(*             helper f1 sv *)
(*       | _ -> *)


(* let weaken_quantifier *)
(*       (f:formula) (scheme: ((spec_var * (exp list)) list)):(formula * (formula option)) = *)
(*   if can_be_simplify f *)
(*   then (f,None) *)
(*   else *)
(*     match f with *)
(*       | Forall (sv,f1,fl,l)-> *)
(*             let  *)



(* ------------------------------------------------------------------- *)
module Index=
    struct
      type t = exp
      let compare e1 e2=
        match e1,e2 with
          | Var (sv1,_), Var (sv2,_)->
                if is_same_sv sv1 sv2
                then 0
                else 1
          | IConst (i1,_), IConst (i2,_)->
                if i1=i2
                then 0
                else 1
          | _ , _ -> 1
    end
;;

module IndexSet = Set.Make(Index);;

let extract_translate_scheme
      (f:formula):((spec_var * (exp list)) list)=
  let translate_scheme = Hashtbl.create 10000 in (* sv -> IndexSet *)
  let rec helper_exp
        (e:exp) (nfsv:spec_var option)=
    match e with
      | Var _
      | IConst _
      | Null _ ->
            ()
      | Add (e1,e2,loc)
      | Subtract (e1,e2,loc)
      | Mult (e1,e2,loc)
      | Div (e1,e2,loc)->
            begin
              helper_exp e1 nfsv;
              helper_exp e2 nfsv;
            end
      | ArrayAt (sv,elst,loc)->
            begin
              match elst with
                | [index] ->
                      begin
                        match index, nfsv with
                          | Var (indexsv,_), Some nnfsv ->
                                if is_same_sv indexsv nnfsv
                                then ()
                                else
                                  let indexset =
                                    try
                                      Hashtbl.find translate_scheme sv
                                    with
                                        Not_found ->
                                            IndexSet.empty
                                  in
                                  Hashtbl.replace translate_scheme sv (IndexSet.add index indexset)
                          | _,_ ->
                                let indexset =
                                  try
                                    Hashtbl.find translate_scheme sv
                                  with
                                      Not_found ->
                                          IndexSet.empty
                                in
                                Hashtbl.replace translate_scheme sv (IndexSet.add index indexset)
                      end
                | _ -> failwith "extract_translate_scheme: Fail to deal with multi-dimensional array"
            end
      | _ ->
            failwith ("Translate_out_array_in_cpure_formula.extract_translate_scheme: "^(ArithNormalizer.string_of_exp e)^" To Be Implemented")
  in
  let helper_b_formula
        ((p,ba):b_formula) (nfsv:spec_var option)=
    match p with
      | Lt (e1, e2, loc)
      | Lte (e1, e2, loc)
      | Gt (e1, e2, loc)
      | Gte (e1, e2, loc)
      | SubAnn (e1, e2, loc)
      | Eq (e1, e2, loc)
      | Neq (e1, e2, loc)
      | BagSub (e1, e2, loc)
      | ListIn (e1, e2, loc)
      | ListNotIn (e1, e2, loc)
      | ListAllN (e1, e2, loc)
      | ListPerm (e1, e2, loc)->
            begin
              helper_exp e1 nfsv;
              helper_exp e2 nfsv
            end
      | RelForm (sv,elst,loc) ->
            List.iter (fun re -> helper_exp re nfsv) elst
      | BConst _
      | XPure _
      | BVar _
      | LexVar _
      | Frm _->
            ()
      | EqMax _
      | EqMin _
      | BagIn _
      | BagNotIn _
      | BagMin _
      | BagMax _ ->
      (*| VarPerm _ ->*)
            failwith ("extract_translate_scheme: "^(!print_p_formula p)^" To Be Implemented")
  in
  let rec helper (* Still working on the Hashtbl *)
        (f:formula) (nfsv:spec_var option):unit=
    match f with
      | BForm (b,fl)->
            helper_b_formula b nfsv
      | And (f1,f2,l)->
            begin
              helper f1 nfsv;
              helper f2 nfsv
            end
      | AndList lst->
            List.iter (fun (t,f) -> helper f nfsv) lst
      | Or (f1,f2,fl,l)->
            begin
              helper f1 nfsv;
              helper f2 nfsv;
            end
      | Not (f,fl,l)->
            helper f nfsv
      | Forall (sv,f,fl,l)->
            helper f (Some sv)
      | Exists (sv,f,fl,l)->
            helper f (Some sv)
  in
  (* Very Dangerous!!! *)
  let _ = helper f None in (* create and fullfil the hashtbl *)
  Hashtbl.fold
      (fun arr indexset result ->
          let indexlst = IndexSet.fold (fun i ilst -> i::ilst) indexset [] in
          (arr,indexlst)::result) translate_scheme []
;;

let extract_translate_scheme
      (f:formula):((spec_var * (exp list)) list)=
  let string_of_translate_scheme
        (ts:((spec_var * (exp list)) list)):string=
    let string_of_item
          ((arr,indexlst):(spec_var * (exp list))):string=
      let string_of_indexlst = List.fold_left (fun s e -> s^" "^(ArithNormalizer.string_of_exp e)^" ") "" indexlst in
      "array: "^(string_of_spec_var arr)^" { "^(string_of_indexlst)^"}"
    in
    List.fold_left (fun s item -> (string_of_item item)^" "^s) "" ts
  in
  Debug.no_1 "extract_translate_scheme" !print_pure string_of_translate_scheme (fun f -> extract_translate_scheme f) f
;;



let rec mk_array_free_formula
      (f:formula):formula=
  let rec mk_array_free_exp
        (e:exp):exp=
    match e with
      | ArrayAt (sv,[exp],loc) ->
            mk_array_new_name sv exp
      | Add (e1,e2,loc)->
            Add (mk_array_free_exp e1, mk_array_free_exp e2,loc)
      | Subtract (e1,e2,loc)->
            Subtract (mk_array_free_exp e1, mk_array_free_exp e2,loc)
      | Mult (e1,e2,loc)->
            Mult (mk_array_free_exp e1, mk_array_free_exp e2,loc)
      | Div (e1,e2,loc)->
            Div (mk_array_free_exp e1, mk_array_free_exp e2,loc)
      | IConst _
      | Var _
      | Null _->
            e
      | _ -> failwith ("mk_array_free_exp: "^(ArithNormalizer.string_of_exp e)^" To Be Implemented")
  in
  let mk_array_free_b_formula
        ((p,ba):b_formula):b_formula=
    let mk_array_free_p_formula
          (p:p_formula):p_formula=
      match p with
        | Lt (e1, e2, loc)->
              Lt (mk_array_free_exp e1, mk_array_free_exp e2, loc)
        | Lte (e1, e2, loc)->
              Lte (mk_array_free_exp e1, mk_array_free_exp e2, loc)
        | Gt (e1, e2, loc)->
              Gt (mk_array_free_exp e1, mk_array_free_exp e2, loc)
        | Gte (e1, e2, loc)->
              Gte (mk_array_free_exp e1, mk_array_free_exp e2, loc)
        | SubAnn (e1, e2, loc)->
              SubAnn (mk_array_free_exp e1, mk_array_free_exp e2, loc)
        | Eq (e1, e2, loc)->
              Eq (mk_array_free_exp e1, mk_array_free_exp e2, loc)
        | Neq (e1, e2, loc)->
              Neq (mk_array_free_exp e1, mk_array_free_exp e2, loc)
        | BagSub (e1, e2, loc)->
              BagSub (mk_array_free_exp e1, mk_array_free_exp e2, loc)
        | ListIn (e1, e2, loc)->
              ListIn (mk_array_free_exp e1, mk_array_free_exp e2, loc)
        | ListNotIn (e1, e2, loc)->
              ListNotIn (mk_array_free_exp e1, mk_array_free_exp e2, loc)
        | ListAllN (e1, e2, loc)->
              ListAllN (mk_array_free_exp e1, mk_array_free_exp e2, loc)
        | ListPerm (e1, e2, loc)->
              ListPerm (mk_array_free_exp e1, mk_array_free_exp e2, loc)
        | EqMax (e1, e2, e3, loc)->
              EqMax (mk_array_free_exp e1, mk_array_free_exp e2, mk_array_free_exp e3, loc)
        | EqMin (e1, e2, e3, loc)->
              EqMin (mk_array_free_exp e1, mk_array_free_exp e2, mk_array_free_exp e3, loc)
        | BagIn (sv,e1,loc)->
              BagIn (sv, mk_array_free_exp e1, loc)
        | BagNotIn (sv,e1,loc)->
              BagNotIn (sv, mk_array_free_exp e1, loc)
        | BConst _
        | Frm _
        | LexVar _
        | BVar _
        | XPure _ ->
              p
        | RelForm (sv,elst,loc) ->
              RelForm (sv, List.map (fun re -> mk_array_free_exp re) elst,loc)
        | BagMin _
        | BagMax _->
        (*| VarPerm _->*)
              failwith ("mk_array_free_p_formula: 2"^(!print_p_formula p)^" To Be Implemented")
    in
    (mk_array_free_p_formula p,None)
  in
  match f with
    | BForm (b,fl)->
          BForm (mk_array_free_b_formula b,fl)
    | And (f1,f2,l)->
          And (mk_array_free_formula f1, mk_array_free_formula f2,l)
    | AndList lst->
          AndList (List.map (fun (t,f) -> (t,mk_array_free_formula f)) lst)
    | Or (f1,f2,fl,l)->
          Or (mk_array_free_formula f1, mk_array_free_formula f2, fl, l)
    | Not (f,fl,l)->
          Not (mk_array_free_formula f,fl,l)
    | Forall (sv,f,fl,l)->
          Forall (sv,mk_array_free_formula f,fl,l)
    | Exists (sv,f,fl,l)->
          Exists (sv,mk_array_free_formula f,fl,l)
;;

let mk_array_free_formula
      (f:formula):formula=
  let pr = !print_pure in
  Debug.no_1 "mk_array_free_formula" pr pr (fun f-> mk_array_free_formula f) f
;;

let mk_array_free_formula_split
      (f:formula):formula=
  split_and_process f can_be_simplify mk_array_free_formula
;;


let mk_array_free_formula_split
      (f:formula):formula=
  let pr = !print_pure in
  Debug.no_1 "mk_array_free_formula_split" pr pr (fun f-> mk_array_free_formula_split f) f
;;

let mk_aux_formula
      (index1:exp) (index2:exp) (arr:spec_var):formula=
  let ante = BForm ((Eq (index1, index2, no_pos),None),None) in
  let conseq = BForm ((Eq (mk_array_new_name arr index1, mk_array_new_name arr index2, no_pos),None),None) in
  mk_imply ante conseq
;;

(* ------------------------------------------- *)
let rec get_array_element_in_f
        (f:formula) (sv:spec_var):(exp list) =
    let rec get_array_element_in_exp
          (e:exp) (sv:spec_var):(exp list) =
      match e with
        | Var _
        | IConst _
        | Null _ ->
              []
        | Add (e1,e2,loc)
        | Subtract (e1,e2,loc)
        | Mult (e1,e2,loc)
        | Div (e1,e2,loc)->
              (get_array_element_in_exp e1 sv) @ (get_array_element_in_exp e2 sv)
        | ArrayAt (nsv,elst,loc)->
              if (is_same_sv nsv sv)
              then [e]
              else []
        | _ ->
              failwith ("Translate_out_array_in_cpure_formula.extract_translate_scheme: "^(ArithNormalizer.string_of_exp e)^" To Be Implemented")
    in
    let get_array_element_in_b_formula
          ((p,ba):b_formula) (sv:spec_var):(exp list) =
      match p with
        | Lt (e1, e2, loc)
        | Lte (e1, e2, loc)
        | Gt (e1, e2, loc)
        | Gte (e1, e2, loc)
        | SubAnn (e1, e2, loc)
        | Eq (e1, e2, loc)
        | Neq (e1, e2, loc)
        | BagSub (e1, e2, loc)
        | ListIn (e1, e2, loc)
        | ListNotIn (e1, e2, loc)
        | ListAllN (e1, e2, loc)
        | ListPerm (e1, e2, loc)->
              (get_array_element_in_exp e1 sv) @ (get_array_element_in_exp e2 sv)
        | RelForm (sv,elst,loc) ->
              List.fold_left (fun r e -> (get_array_element_in_exp e sv)@r) [] elst
        | BConst _
        | XPure _
        | BVar _
        | LexVar _
        | Frm _->
              []
        | EqMax _
        | EqMin _
        | BagIn _
        | BagNotIn _
        | BagMin _
        | BagMax _ ->
        (* | VarPerm _ -> *)
              failwith ("extract_translate_scheme: "^(!print_p_formula p)^" To Be Implemented")
    in
    match f with
      | BForm (b,fl)->
            get_array_element_in_b_formula b sv
      | And (f1,f2,l)->
            (get_array_element_in_f f1 sv)@(get_array_element_in_f f2 sv)
      | AndList lst->
            failwith ("get_array_element_in_f: AndList To Be Implemented")
      | Or (f1,f2,fl,l)->
            (get_array_element_in_f f1 sv)@(get_array_element_in_f f2 sv)
      | Not (nf,fl,l)->
            get_array_element_in_f nf sv
      | Forall (nsv,nf,fl,l)->
            get_array_element_in_f nf sv
      | Exists (nsv,nf,fl,l)->
            get_array_element_in_f nf sv
;;

let get_array_element_as_spec_var_list
      (f:formula) (sv:spec_var) :(spec_var list) =
  let elst = get_array_element_in_f f sv in
  List.map (fun e -> mk_array_new_name_wrapper_for_array e) elst
;;

let get_array_element_as_spec_var_list
      (f:formula) (sv:spec_var) :(spec_var list) =
  Debug.no_2 "get_array_element_as_spec_var_list" !print_pure string_of_spec_var (pr_list string_of_spec_var) (fun f sv -> get_array_element_as_spec_var_list f sv) f sv
;;

let rec expand_array_variable
      (f:formula) (svlst:spec_var list) :(spec_var list) =
  let expand f sv =
    let array_element = get_array_element_as_spec_var_list f sv in
    match array_element with
      | [] -> [sv]
      | _ -> array_element
  in
  let helper f svlst =
    match svlst with
      | h::rest -> (expand f h)@(expand_array_variable f rest)
      | [] -> []
  in
  remove_dupl_spec_var_list (helper f svlst)
;;

let rec process_exists_array
      (f:formula):formula =
  match f with
    | BForm (b,fl)->
          f
    | And (f1,f2,l)->
          And (process_exists_array f1, process_exists_array f2,l)
    | AndList lst->
          failwith "process_exists_array: AndList To Be Implemented"
    | Or (f1,f2,fl,l)->
          Or (process_exists_array f1,process_exists_array f2,fl,l)
    | Not (f,fl,l)->
          Not (process_exists_array f,fl,l)
    | Forall (sv,nf,fl,l)->
          Forall (sv,process_exists_array nf,fl,l)
    | Exists (SpecVar (typ,id,primed) as sv,nf,fl,l)->
          let nqlst =
            begin
              match typ with
                | Array _ ->
                      get_array_element_in_f f sv
                | _ -> []
            end
          in
          if List.length nqlst == 0
          then f
          else
            let mk_new_name_helper
                  (e:exp) : spec_var =
              match e with
                | ArrayAt (SpecVar (typ,id,primed),[e],_)->
                      begin
                        match typ with
                          | Array (atyp,_ ) ->
                                begin
                                  match primed with
                                    | Primed ->
                                          SpecVar (atyp,(id)^"___"^(ArithNormalizer.string_of_exp e)^"___",primed)
                                    | _ ->
                                          SpecVar (atyp,(id)^"___"^(ArithNormalizer.string_of_exp e)^"___",primed)
                                end
                          | _ -> failwith "mk_new_name_helper: Not array type"
                      end
                | _ -> failwith "mk_new_name_helper: Invalid input"
            in
            List.fold_left (fun r nq -> Exists(mk_new_name_helper nq,r,None,no_pos)) nf nqlst
;;

let process_exists_array
      (f:formula):formula =
  Debug.no_1 "process_exists_array" !print_pure !print_pure (fun f -> process_exists_array f) f
;;

(* ------------------------------------------- *)
let rec drop_array_formula
      (f:formula):formula=
  let rec contain_array_exp
        (e:exp):bool=
    match e with
      | ArrayAt _
          -> true
      | Tup2 ((e1,e2),loc)
      | Add (e1,e2,loc)
      | Subtract (e1,e2,loc)
      | Mult (e1,e2,loc)
      | Div (e1,e2,loc)
      | Max (e1,e2,loc)
      | Min (e1,e2,loc)
      | BagDiff (e1,e2,loc)
      | ListCons (e1,e2,loc)->
            ((contain_array_exp e1) or (contain_array_exp e2))
      | TypeCast (_,e1,loc)
      | ListHead (e1,loc)
      | ListTail (e1,loc)
      | ListLength (e1,loc)
      | ListReverse (e1,loc)->
            contain_array_exp e1
      | Null _|Var _|Level _|IConst _|FConst _|AConst _|InfConst _|Tsconst _|Bptriple _|ListAppend _|Template _
      | Func _
      | List _
      | Bag _
      | BagUnion _
      | BagIntersect _
          -> false
      | _ -> failwith "drop_array_formula: Unexpected case"
  in
  let contain_array_b_formula
        ((p,ba):b_formula):bool=
    match p with
      | Frm _
      | XPure _
      | LexVar _
      | BConst _
      | BVar _
      | BagMin _
      | BagMax _
      (* | VarPerm _ *)
      | RelForm _ ->
            false
      | BagIn (sv,e1,loc)
      | BagNotIn (sv,e1,loc)->
            contain_array_exp e1
      | Lt (e1,e2,loc)
      | Lte (e1,e2,loc)
      | Gt (e1,e2,loc)
      | Gte (e1,e2,loc)
      | SubAnn (e1,e2,loc)
      | Eq (e1,e2,loc)
      | Neq (e1,e2,loc)
      | ListIn (e1,e2,loc)
      | ListNotIn (e1,e2,loc)
      | ListAllN (e1,e2,loc)
      | ListPerm (e1,e2,loc)->
            (contain_array_exp e1) || (contain_array_exp e2)
      | EqMax (e1,e2,e3,loc)
      | EqMin (e1,e2,e3,loc)->
            (contain_array_exp e1) || (contain_array_exp e2) || (contain_array_exp e3)
      | _ -> false
  in
  match f with
    | BForm (b,fl)->
          if contain_array_b_formula b then mkTrue no_pos else f
    | And (f1,f2,loc)->
          And (drop_array_formula f1,drop_array_formula f2,loc)
    | AndList lst->
          AndList (List.map (fun (t,f)-> (t,drop_array_formula f)) lst)
    | Or (f1,f2,fl,loc)->
          Or (drop_array_formula f1,drop_array_formula f2,fl,loc)
    | Not (f,fl,loc)->
          Not (drop_array_formula f,fl,loc)
    | Forall (sv,f,fl,loc)->
          Forall (sv,drop_array_formula f,fl,loc)
    | Exists (sv,f,fl,loc)->
          Exists (sv,drop_array_formula f,fl,loc)
;;

let drop_array_formula
      (f:formula):formula =
  if !Globals.array_translate
  then drop_array_formula f
  else f

let drop_array_formula
      (f:formula):formula=
  let pr = !print_pure in
  Debug.no_1 "drop_array_formula" pr pr (fun fo->drop_array_formula fo) f
;;
(* --------------------------------------------------------- *)

let rec drop_array_quantifier
      (f:formula):formula =
  match f with
    | BForm (b,fl)->
          f
    | And (f1,f2,loc)->
          And(drop_array_quantifier f1,drop_array_quantifier f2,loc)
    | AndList lst->
          failwith "drop_array_quantifier: AndList To Be Implemented"
    | Or (f1,f2,fl,loc)->
          Or (drop_array_quantifier f1,drop_array_quantifier f2,fl,loc)
    | Not (f,fl,loc)->
          Not (drop_array_quantifier f,fl,loc)
    | Forall (sv,f,fl,loc)->
          if contain_array f
          then mkTrue no_pos
          else Forall (sv,drop_array_quantifier f,fl,loc)
    | Exists (sv,f,fl,loc)->
          if contain_array f
          then mkTrue no_pos
          else Exists (sv,drop_array_quantifier f,fl,loc)
;;

let drop_array_quantifier
      (f:formula):formula =
  Debug.no_1 "drop_array_quantifier" !print_pure !print_pure (fun f -> drop_array_quantifier f) f
;;

let rec produce_aux_formula
      (translate_scheme:((spec_var * (exp list)) list)):(formula option)=
  let needed_to_produce
        (h:exp) (e:exp):bool=
    match h,e with
      | IConst _, IConst _ -> false
      | Var (sv1,_), Var (sv2,_)->
            not (is_same_sv sv1 sv2)
      | IConst _, Var _
      | Var _, IConst _->
            true
      | _,_-> failwith "needed_to_produce: Invalid input"
  in
  let rec produce_aux_formula_helper
        (translate_scheme:((spec_var * (exp list)) list)):(formula list)=
    let produce_aux_formula_one
          ((arr_name,indexlst):(spec_var * (exp list))): (formula list)=
      let rec iterator
            (lst1:exp list) (lst2:exp list) : (formula list)=
        let rec iterator_helper
              (e:exp) (l:exp list):(formula list)=
          match l with
            | h::rest ->
                  if needed_to_produce h e
                  then
                    (mk_aux_formula e h arr_name)::(iterator_helper e rest)
                  else
                    iterator_helper e rest
            | [] ->
                  []
        in
        match lst1, lst2 with
          | h1::rest1,h2::rest2 ->
                (iterator_helper h1 lst2)@(iterator rest1 rest2)
          | [],_
          | _,[]->
                []
      in
      iterator indexlst indexlst
    in
    match translate_scheme with
      | h::rest ->
            (produce_aux_formula_one h)@(produce_aux_formula_helper rest)
      | [] ->
            []
  in
  let aux_formula_lst = produce_aux_formula_helper translate_scheme in
  match aux_formula_lst with
    | []-> None
    | _ -> Some (mk_and_list aux_formula_lst)
;;

let produce_aux_formula
      (translate_scheme:((spec_var * (exp list)) list)):(formula option)=
  let string_of_translate_scheme
        (ts:((spec_var * (exp list)) list)):string=
    let string_of_item
          ((arr,indexlst):(spec_var * (exp list))):string=
      let string_of_indexlst = List.fold_left (fun s e -> s^" "^(ArithNormalizer.string_of_exp e)^" ") "" indexlst in
      "array: "^(string_of_spec_var arr)^" { "^(string_of_indexlst)^"}"
    in
    List.fold_left (fun s item -> (string_of_item item)^" "^s) "" ts
  in
  let pr_option =
    function
      | Some f-> (!print_pure f)
      | None-> "None"
  in
  Debug.no_1 "produce_aux_formula" string_of_translate_scheme pr_option (fun ts -> produce_aux_formula ts) translate_scheme
;;

(* let new_translate_out_array_in_formula *)
(*       (f:formula):formula= *)
(*   let array_free_formula = mk_array_free_formula f in *)
(*   let aux_formula = produce_aux_formula (extract_translate_scheme f) in *)
(*   match aux_formula with *)
(*     | None -> array_free_formula *)
(*     | Some af -> And (array_free_formula,af,no_pos) *)
(* ;; *)

(* let new_translate_out_array_in_formula *)
(*       (f:formula):formula= *)
(*   Debug.no_1 "new_translate_out_array_in_formula" !print_pure !print_pure (fun f -> new_translate_out_array_in_formula f) f *)
(* ;; *)


(* let new_translate_out_array_in_imply *)
(*       (ante:formula) (conseq:formula):(formula * formula) = *)
(*   let translate_scheme = (extract_translate_scheme (And (ante,conseq,no_pos))) in *)
(*   let n_ante = *)
(*     match produce_aux_formula translate_scheme with *)
(*       | Some aux_f -> And (mk_array_free_formula ante,aux_f,no_pos) *)
(*       | None -> mk_array_free_formula ante *)
(*   in *)
(*   (\*let _ = mk_array_free_formula_split ante in*\) *)
(*   let n_conseq = mk_array_free_formula conseq in *)
(*   (n_ante,n_conseq) *)
(* ;; *)

(* let new_translate_out_array_in_imply *)
(*       (ante:formula) (conseq:formula):(formula * formula) = *)
(*   let pr = !print_pure in *)
(*   let pr_pair = function *)
(*     | (a,b) -> "("^(pr a)^","^(pr b)^")" *)
(*   in *)
(*   Debug.no_2 "new_translate_out_array_in_imply" pr pr pr_pair (fun ante conseq -> new_translate_out_array_in_imply ante conseq) ante conseq *)
(* ;; *)

(* let new_translate_out_array_in_imply_full *)
(*       (ante:formula) (conseq:formula):(formula * formula) = *)
(*   let (an,con) = (process_quantifier ante,process_quantifier conseq) in *)
(*   let (s_ante,s_conseq) = standarize_array_imply an con in *)
(*   new_translate_out_array_in_imply s_ante s_conseq *)
(* ;; *)

let new_translate_out_array_in_imply_split
      (ante:formula) (conseq:formula):(formula * formula) =
  let translate_scheme = (extract_translate_scheme (And (ante,conseq,no_pos))) in
  let n_ante =
    match produce_aux_formula translate_scheme with
      | Some aux_f -> And (mk_array_free_formula_split ante,aux_f,no_pos)
      | None -> mk_array_free_formula_split ante
  in
  let n_ante_with_eq =
    match translate_array_equality ante translate_scheme with
      | None   -> n_ante
      | Some eq -> And (eq,n_ante,no_pos)
  in
  (*let _ = mk_array_free_formula_split ante in*)
  let n_conseq = mk_array_free_formula_split conseq in
  (n_ante_with_eq,n_conseq)
;;

let new_translate_out_array_in_imply_split
      (ante:formula) (conseq:formula):(formula * formula) =
  let (keep_ante,sv2f_ante) = split_formula ante can_be_simplify in
  let (keep_conseq,sv2f_conseq) = split_formula conseq can_be_simplify in
  let (nante,nconseq) = new_translate_out_array_in_imply_split keep_ante keep_conseq in
  (combine_formula nante sv2f_ante,combine_formula nconseq sv2f_conseq)
;;

let new_translate_out_array_in_imply_split
      (ante:formula) (conseq:formula):(formula * formula) =
  let pr = !print_pure in
  let pr_pair = function
    | (a,b) -> "("^(pr a)^","^(pr b)^")"
  in
  Debug.no_2 "new_translate_out_array_in_imply_split" pr pr pr_pair (fun ante conseq -> new_translate_out_array_in_imply_split ante conseq) ante conseq
;;

let new_translate_out_array_in_imply_split_full
      (ante:formula) (conseq:formula):(formula * formula) =
  let (an,con) = (translate_array_relation ante,translate_array_relation conseq) in
  let (an,con) = (process_quantifier an,process_quantifier con) in
  let (s_ante,s_conseq) = standarize_array_imply an con in
  new_translate_out_array_in_imply_split s_ante s_conseq
;;

let new_translate_out_array_in_imply_split_full
      (ante:formula) (conseq:formula):(formula * formula) =
  if !Globals.array_translate
  then new_translate_out_array_in_imply_split_full ante conseq
  else (ante,conseq)
;;

(* let new_translate_out_array_in_imply_split_full *)
(*       (ante:formula) (conseq:formula):(formula * formula) = *)
(*   if !Globals.array_translate *)
(*   then new_translate_out_array_in_imply_split_full ante conseq *)
(*   else (ante,conseq) *)
(* ;; *)

let new_translate_out_array_in_one_formula
      (f:formula):formula=
  let f = process_exists_array f in
  let array_free_formula = mk_array_free_formula f in
  let scheme = extract_translate_scheme f in
  let aux_formula = produce_aux_formula scheme in
  let new_f =
    match aux_formula with
      | None -> array_free_formula
      | Some af -> And (array_free_formula,af,no_pos)
  in
  match translate_array_equality f scheme with
    | None -> new_f
    | Some ef -> And (ef,new_f,no_pos)
;;

let new_translate_out_array_in_one_formula
      (f:formula):formula=
  Debug.no_1 "new_translate_out_array_in_one_formula" !print_pure !print_pure (fun f -> new_translate_out_array_in_one_formula f) f
;;

let new_translate_out_array_in_one_formula_full
      (f:formula):formula=
  let f = translate_array_relation f in
  let nf = process_quantifier f in
  (*let _ = mk_array_free_formula_split nf in*)
  let sf = standarize_one_formula nf in
  new_translate_out_array_in_one_formula sf
;;

(* let new_translate_out_array_in_one_formula_split *)
(*       (f:formula):formula = *)
(*   split_and_process (process_quantifier f) can_be_simplify new_translate_out_array_in_one_formula_full *)
(* ;; *)

let new_translate_out_array_in_one_formula_split
      (f:formula):formula =
  split_and_combine new_translate_out_array_in_one_formula_full can_be_simplify (process_quantifier (translate_array_relation f))
;;

let new_translate_out_array_in_one_formula_split
      (f:formula):formula =
  if !Globals.array_translate
  then new_translate_out_array_in_one_formula_split f
  else f
;;

let new_translate_out_array_in_one_formula_split
      (f:formula):formula =
  Debug.no_1 "new_translate_out_array_in_one_formula_split" !print_pure !print_pure (fun f -> new_translate_out_array_in_one_formula_split f) f
;;


(* Given a formula, replace all the occurance of a variable in the formula with another variable *)
(* index is the variable to be replaced, with new_index *)
(* let rec produce_new_index_predicate *)
(*       (fo:formula) (index:exp) (new_index:exp):formula = *)
(*   let rec helper_exp *)
(*         (e:exp) (index:exp) (new_index:exp):exp = *)
(*     match e with *)
(*       | Var (sv,loc)-> *)
(*             if is_same_var e index then new_index else e *)
(*       | IConst _ *)
(*       | ArrayAt _ -> *)
(*             e *)
(*       | Add (e1,e2,loc) -> *)
(*             Add (helper_exp e1 index new_index, helper_exp e2 index new_index, loc) *)
(*       | Subtract (e1,e2,loc)-> *)
(*             Subtract (helper_exp e1 index new_index, helper_exp e2 index new_index, loc) *)
(*       | Mult (e1,e2,loc)-> *)
(*             Mult (helper_exp e1 index new_index, helper_exp e2 index new_index, loc) *)
(*       | Div (e1,e2,loc) -> *)
(*             Div (helper_exp e1 index new_index, helper_exp e2 index new_index,loc) *)
(*       | _ -> *)
(*             failwith "Translate_out_array_in_cpure_formula.produce_new_index_predicate: To Be Implemented" *)
(*   in *)
(*   let helper_b_formula *)
(*         ((p,ba):b_formula) (index:exp) (new_index:exp):b_formula = *)
(*     let helper_p_formula *)
(*           (p:p_formula) (index:exp) (new_index:exp):p_formula = *)
(*       match p with *)
(*         | Lt (e1, e2, loc)-> *)
(*               Lt (helper_exp e1 index new_index, helper_exp e2 index new_index, loc) *)
(*         | Lte (e1, e2, loc)-> *)
(*               Lte (helper_exp e1 index new_index, helper_exp e2 index new_index, loc) *)
(*         | Gt (e1, e2, loc)-> *)
(*               Gt (helper_exp e1 index new_index, helper_exp e2 index new_index, loc) *)
(*         | Gte (e1, e2, loc)-> *)
(*               Gte (helper_exp e1 index new_index, helper_exp e2 index new_index, loc) *)
(*         | SubAnn (e1, e2, loc)-> *)
(*               SubAnn (helper_exp e1 index new_index, helper_exp e2 index new_index, loc) *)
(*         | Eq (e1, e2, loc)-> *)
(*               Eq (helper_exp e1 index new_index, helper_exp e2 index new_index, loc) *)
(*         | Neq (e1, e2, loc)-> *)
(*               Neq (helper_exp e1 index new_index, helper_exp e2 index new_index, loc) *)
(*         | BagSub (e1, e2, loc)-> *)
(*               BagSub (helper_exp e1 index new_index, helper_exp e2 index new_index, loc) *)
(*         | ListIn (e1, e2, loc)-> *)
(*               ListIn (helper_exp e1 index new_index, helper_exp e2 index new_index, loc) *)
(*         | ListNotIn (e1, e2, loc)-> *)
(*               ListNotIn (helper_exp e1 index new_index, helper_exp e2 index new_index, loc) *)
(*         | ListAllN (e1, e2, loc)-> *)
(*               ListAllN (helper_exp e1 index new_index, helper_exp e2 index new_index, loc) *)
(*         | ListPerm (e1, e2, loc)-> *)
(*               ListPerm (helper_exp e1 index new_index, helper_exp e2 index new_index, loc) *)
(*         | EqMax (e1, e2, e3, loc)-> *)
(*               EqMax (helper_exp e1 index new_index, helper_exp e2 index new_index, helper_exp e3 index new_index, loc) *)
(*         | EqMin (e1, e2, e3, loc)-> *)
(*               EqMin (helper_exp e1 index new_index, helper_exp e2 index new_index, helper_exp e3 index new_index, loc) *)
(*         | BagIn (sv,e1,loc)-> *)
(*               BagIn (sv, helper_exp e1 index new_index, loc) *)
(*         | BagNotIn (sv,e1,loc)-> *)
(*               BagNotIn (sv, helper_exp e1 index new_index, loc) *)
(*         | Frm _ *)
(*         | XPure _ *)
(*         | LexVar _ *)
(*         | BConst _ *)
(*         | BVar _ *)
(*         | BagMin _ *)
(*         | BagMax _ *)
(*         | VarPerm _ *)
(*         | RelForm _ -> *)
(*               failwith "produce_new_index_predicate: To Be Implemented" *)
(*     in *)
(*     (helper_p_formula p index new_index, None) *)
(*   in *)
(*   match fo with *)
(*     | BForm (b,fl)-> *)
(*           let n_b = helper_b_formula b index new_index in *)
(*           BForm (n_b,fl) *)
(*     | And (f1,f2,l)-> *)
(*           And (produce_new_index_predicate f1 index new_index,produce_new_index_predicate f2 index new_index,l) *)
(*     | AndList lst-> *)
(*           AndList (List.map (fun (t,f) -> (t,produce_new_index_predicate f index new_index)) lst) *)
(*     | Or (f1,f2,fl,l)-> *)
(*           Or (produce_new_index_predicate f1 index new_index,produce_new_index_predicate f2 index new_index,fl,l) *)
(*     | Not (f,fl,l)-> *)
(*           Not (produce_new_index_predicate f index new_index,fl,l) *)
(*     | Forall (sv,f,fl,l)-> *)
(*           Forall (sv,produce_new_index_predicate f index new_index,fl,l) *)
(*     | Exists (sv,f,fl,l)-> *)
(*           Exists (sv,produce_new_index_predicate f index new_index,fl,l) *)
(* ;; *)

(* let produce_new_index_predicate *)
(*       (f:formula) (index:exp) (new_index:exp):formula = *)
(*   let pf = !print_pure in *)
(*   let pe = ArithNormalizer.string_of_exp in *)
(*   Debug.no_3 "produce_new_index_predicate" pf pe pe pf (fun f i n -> produce_new_index_predicate f i n) f index new_index *)
(* ;; *)

(* let produce_new_index_predicate_wrapper *)
(*       (fo:formula option) (index:exp) (new_index:exp):formula = *)
(*   match fo with *)
(*     | Some f -> produce_new_index_predicate f index new_index *)
(*     | None -> BForm ((Eq (index,new_index,no_pos),None),None) *)
(* ;; *)

(* Given a formula, extract all the subformulas that is related to some variable *)
(* let rec extract_index_predicate *)
(*       (f:formula) (index:exp):(formula option) = *)
(*   let rec is_involved_exp *)
(*         (e:exp) (index:exp):bool = *)
(*     match e with *)
(*       | Var (sv,loc)-> *)
(*             is_same_var e index *)
(*       | Add (e1,e2,loc) *)
(*       | Subtract (e1,e2,loc) *)
(*       | Mult (e1,e2,loc) *)
(*       | Div (e1,e2,loc)-> *)
(*             (is_involved_exp e1 index)||(is_involved_exp e2 index) *)
(*       | ArrayAt _ *)
(*       | IConst _ -> *)
(*             false *)
(*       | _ -> *)
(*             failwith ("Translate_out_array_in_cpure_formula.extract_index_predicate: "^(ArithNormalizer.string_of_exp e)^" To Be Implemented") *)
(*   in *)
(*   let helper_b_formula *)
(*         ((p,ba):b_formula) (index:exp):(b_formula option) = *)
(*     let helper_p_formula *)
(*           (p:p_formula) (index:exp):(p_formula option) = *)
(*       match p with *)
(*         | Lt (e1, e2, loc) *)
(*         | Lte (e1, e2, loc) *)
(*         | Gt (e1, e2, loc) *)
(*         | Gte (e1, e2, loc) *)
(*         | SubAnn (e1, e2, loc) *)
(*         | Eq (e1, e2, loc) *)
(*         | Neq (e1, e2, loc) *)
(*         | BagSub (e1, e2, loc) *)
(*         | ListIn (e1, e2, loc) *)
(*         | ListNotIn (e1, e2, loc) *)
(*         | ListAllN (e1, e2, loc) *)
(*         | ListPerm (e1, e2, loc)-> *)
(*               if (is_involved_exp e1 index) || (is_involved_exp e2 index) *)
(*               then *)
(*                 Some p *)
(*               else *)
(*                 None *)
(*         | EqMax (e1, e2, e3, loc) *)
(*         | EqMin (e1, e2, e3, loc)-> *)
(*               if (is_involved_exp e1 index) || (is_involved_exp e2 index) || (is_involved_exp e3 index) *)
(*               then *)
(*                 Some p *)
(*               else *)
(*                 None *)
(*         | BagIn (sv,e1,loc) *)
(*         | BagNotIn (sv,e1,loc)-> *)
(*               if (is_involved_exp e1 index) *)
(*               then *)
(*                 Some p *)
(*               else *)
(*                 None *)
(*         | Frm _ *)
(*         | XPure _ *)
(*         | LexVar _ *)
(*         | BConst _ *)
(*         | BVar _ *)
(*         | BagMin _ *)
(*         | BagMax _ *)
(*         | VarPerm _ *)
(*         | RelForm _ -> *)
(*               failwith "extract_index_predicate: To Be Implemented" *)
(*     in *)
(*     match helper_p_formula p index with *)
(*       | Some pf -> *)
(*             Some (pf,None) *)
(*       | None -> *)
(*             None *)
(*   in *)
(*   let rec helper *)
(*         (f:formula) (index:exp): (formula option) = *)
(*     match f with *)
(*       | BForm (b,fl)-> *)
(*             begin *)
(*               match (helper_b_formula b index) with *)
(*                 | Some bp -> *)
(*                       Some (BForm (bp,fl)) *)
(*                 | None -> *)
(*                       None *)
(*             end *)
(*       | And (f1,f2,l)-> *)
(*             begin *)
(*               match helper f1 index, helper f2 index with *)
(*                 | None,None -> None *)
(*                 | Some nf,None *)
(*                 | None, Some nf -> Some nf *)
(*                 | Some nf1, Some nf2 -> Some (And (nf1,nf2,l)) *)
(*             end *)
(*       | AndList lst-> *)
(*             let flst = List.fold_left *)
(*               (fun result (t,inputf) -> *)
(*                   match helper inputf index with *)
(*                     | Some nf -> nf::result *)
(*                     | None -> result *)
(*               ) [] lst *)
(*             in *)
(*             if List.length flst = 0 *)
(*             then None *)
(*             else Some (mk_and_list flst) *)
(*       | Or (f1,f2,fl,l)-> *)
(*             begin *)
(*               match helper f1 index, helper f2 index with *)
(*                 | None, None -> None *)
(*                 | Some nf, None *)
(*                 | None, Some nf -> Some nf *)
(*                 | Some nf1, Some nf2 -> Some (Or (nf1,nf2,fl,l)) *)
(*             end *)
(*       | Not (f,fl,l)-> *)
(*             begin *)
(*               match helper f index with *)
(*                 | Some nf -> Some (Not (nf,fl,l)) *)
(*                 | None -> None *)
(*             end *)
(*       | Forall (sv,f,fl,l)-> *)
(*             begin *)
(*               match helper f index with *)
(*                 | Some nf -> Some (Forall (sv,nf,fl,l)) *)
(*                 | None -> None *)
(*             end *)
(*       | Exists (sv,f,fl,l)-> *)
(*             begin *)
(*               match helper f index with *)
(*                 | Some nf -> Some (Exists (sv,nf,fl,l)) *)
(*                 | None -> None *)
(*             end *)
(*   in *)
(*   helper f index *)
(* ;; *)

(* let extract_index_predicate *)
(*       (f:formula) (index:exp):(formula option) = *)
(*   let pf = !print_pure in *)
(*   let pfo = function *)
(*     | Some f -> pf f *)
(*     | None -> "Constant index" *)
(*   in *)
(*   Debug.no_2 "extract_index_predicate" pf ArithNormalizer.string_of_exp pfo (fun f i -> extract_index_predicate f i) f index *)
(* ;; *)

(* Get array transform information from cpure formula *)
(* Actually I don't have to translate the array out here. But due to some historical reason, the implementation is like this. *)
(* In later usage of this method, I only use the array_transform_info list. *)

(* let get_array_transform_info_lst *)
(*       (f:formula):((array_transform_info list) * formula)= *)
(*   let rec get_array_transform_info_lst_helper *)
(*         (f:formula):((array_transform_info list) * formula)= *)
(*     let mk_array_new_name *)
(*           (sv:spec_var) (e:exp):exp= *)
(*       match sv with *)
(*         | SpecVar (typ,id,primed)-> *)
(*               begin *)
(*                 match typ with *)
(*                   | Array (atyp,_)-> *)
(*                         begin *)
(*                           match primed with *)
(*                             | Primed -> *)
(*                                   (\*Var( SpecVar (atyp,(id)^"_"^"primed_"^(ArithNormalizer.string_of_exp e),primed),no_pos)*\) *)
(*                                   Var( SpecVar (atyp,(id)^"___"^(ArithNormalizer.string_of_exp e)^"___",primed),no_pos) *)
(*                             | _ -> Var( SpecVar (atyp,(id)^"___"^(ArithNormalizer.string_of_exp e)^"___",primed),no_pos) *)
(*                         end *)
(*                   | _ -> failwith "get_array_transform_info_lst: Not array type" *)
(*               end *)
(*     in *)
(*     (\* return a list of array_transform_info and an array-free expression *\) *)
(*     let rec get_array_transform_info_lst_from_exp *)
(*           (e:exp):((array_transform_info list) * exp)= *)
(*       match e with *)
(*         | ArrayAt (sv,elst,_)-> *)
(*               begin *)
(*                 match elst with *)
(*                   | [h] -> *)
(*                         let new_name = mk_array_new_name sv h in *)
(*                         let new_info = { target_array = e; new_name = new_name } in *)
(*                         ([new_info],new_name) *)
(*                   | h::rest -> failwith "get_array_transform_info_lst_from_exp: Fail to handle multi-dimensional array" *)
(*                   | [] -> failwith "get_array_transform_info_lst_from_exp: Impossible Case" *)
(*               end *)
(*         | Tup2 ((e1,e2),loc)-> *)
(*               let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in *)
(*               let (info2,ne2) = get_array_transform_info_lst_from_exp e2 in *)
(*               (info1@info2,Tup2 ((ne1,ne2),loc)) *)
(*         | Add (e1,e2,loc)-> *)
(*               let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in *)
(*               let (info2,ne2) = get_array_transform_info_lst_from_exp e2 in *)
(*               (info1@info2,Add (ne1,ne2,loc)) *)
(*         | Subtract (e1,e2,loc)-> *)
(*               let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in *)
(*               let (info2,ne2) = get_array_transform_info_lst_from_exp e2 in *)
(*               (info1@info2,Subtract (ne1,ne2,loc)) *)
(*         | Mult (e1,e2,loc)-> *)
(*               let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in *)
(*               let (info2,ne2) = get_array_transform_info_lst_from_exp e2 in *)
(*               (info1@info2,Mult (ne1,ne2,loc)) *)
(*         | Div (e1,e2,loc)-> *)
(*               let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in *)
(*               let (info2,ne2) = get_array_transform_info_lst_from_exp e2 in *)
(*               (info1@info2,Div (ne1,ne2,loc)) *)
(*         | Max (e1,e2,loc)-> *)
(*               let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in *)
(*               let (info2,ne2) = get_array_transform_info_lst_from_exp e2 in *)
(*               (info1@info2,Max (ne1,ne2,loc)) *)
(*         | Min (e1,e2,loc)-> *)
(*               let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in *)
(*               let (info2,ne2) = get_array_transform_info_lst_from_exp e2 in *)
(*               (info1@info2,Min (ne1,ne2,loc)) *)
(*         | BagDiff (e1,e2,loc)-> *)
(*               let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in *)
(*               let (info2,ne2) = get_array_transform_info_lst_from_exp e2 in *)
(*               (info1@info2,BagDiff (ne1,ne2,loc)) *)
(*         | ListCons (e1,e2,loc)-> *)
(*               let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in *)
(*               let (info2,ne2) = get_array_transform_info_lst_from_exp e2 in *)
(*               (info1@info2,ListCons (ne1,ne2,loc)) *)
(*         | TypeCast (typ,e1,loc)-> *)
(*               let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in *)
(*               (info1,TypeCast (typ,ne1,loc)) *)
(*         | ListHead (e1,loc)-> *)
(*               let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in *)
(*               (info1,ListHead (ne1,loc)) *)
(*         | ListTail (e1,loc)-> *)
(*               let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in *)
(*               (info1,ListTail (ne1,loc)) *)
(*         | ListLength (e1,loc)-> *)
(*               let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in *)
(*               (info1,ListLength (ne1,loc)) *)
(*         | ListReverse (e1,loc)-> *)
(*               let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in *)
(*               (info1,ListReverse (ne1,loc)) *)
(*         | Func _ -> failwith "get_array_transform_info_lst_from_exp: Func To Be Implemented" *)
(*         | List _ -> failwith "get_array_transform_info_lst_from_exp: List To Be Implemented" *)
(*         | Bag _ -> failwith "get_array_transform_info_lst_from_exp: Bag To Be Implemented" *)
(*         | BagUnion _ -> failwith "get_array_transform_info_lst_from_exp: BagUnion To Be Implemented" *)
(*         | BagIntersect _ -> failwith "get_array_transform_info_lst_from_exp: BagIntersect To Be Implemented" *)
(*         (\*| Var (sv,_) -> let _ = print_endline ("Var: sv = "^(string_of_spec_var sv)) in ([],e)*\) *)
(*         | _ -> ([],e) *)
(*     in *)
(*     let get_array_transform_info_lst_from_b_formula *)
(*           ((p,ba):b_formula):((array_transform_info list) * b_formula)= *)
(*       let helper *)
(*             (p:p_formula):((array_transform_info list) * p_formula)= *)
(*         match p with *)
(*           | Lt (e1, e2, loc)-> *)
(*                 let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in *)
(*                 let (info2,ne2) = get_array_transform_info_lst_from_exp e2 in *)
(*                 (info1@info2,Lt (ne1,ne2,loc)) *)
(*           | Lte (e1, e2, loc)-> *)
(*                 let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in *)
(*                 let (info2,ne2) = get_array_transform_info_lst_from_exp e2 in *)
(*                 (info1@info2,Lte (ne1,ne2,loc)) *)
(*           | Gt (e1, e2, loc)-> *)
(*                 let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in *)
(*                 let (info2,ne2) = get_array_transform_info_lst_from_exp e2 in *)
(*                 (info1@info2,Gt (ne1,ne2,loc)) *)
(*           | Gte (e1, e2, loc)-> *)
(*                 let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in *)
(*                 let (info2,ne2) = get_array_transform_info_lst_from_exp e2 in *)
(*                 (info1@info2,Gte (ne1,ne2,loc)) *)
(*           | SubAnn (e1, e2, loc)-> *)
(*                 let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in *)
(*                 let (info2,ne2) = get_array_transform_info_lst_from_exp e2 in *)
(*                 (info1@info2,SubAnn (ne1,ne2,loc)) *)
(*           | Eq (e1, e2, loc)-> *)
(*                 let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in *)
(*                 let (info2,ne2) = get_array_transform_info_lst_from_exp e2 in *)
(*                 (info1@info2,Eq (ne1,ne2,loc)) *)
(*           | Neq (e1, e2, loc)-> *)
(*                 let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in *)
(*                 let (info2,ne2) = get_array_transform_info_lst_from_exp e2 in *)
(*                 (info1@info2,Neq (ne1,ne2,loc)) *)
(*           | BagSub (e1, e2, loc)-> *)
(*                 let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in *)
(*                 let (info2,ne2) = get_array_transform_info_lst_from_exp e2 in *)
(*                 (info1@info2,BagSub (ne1,ne2,loc)) *)
(*           | ListIn (e1, e2, loc)-> *)
(*                 let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in *)
(*                 let (info2,ne2) = get_array_transform_info_lst_from_exp e2 in *)
(*                 (info1@info2,ListIn (ne1,ne2,loc)) *)
(*           | ListNotIn (e1, e2, loc)-> *)
(*                 let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in *)
(*                 let (info2,ne2) = get_array_transform_info_lst_from_exp e2 in *)
(*                 (info1@info2,ListNotIn (ne1,ne2,loc)) *)
(*           | ListAllN (e1, e2, loc)-> *)
(*                 let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in *)
(*                 let (info2,ne2) = get_array_transform_info_lst_from_exp e2 in *)
(*                 (info1@info2,ListAllN (ne1,ne2,loc)) *)
(*           | ListPerm (e1, e2, loc)-> *)
(*                 let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in *)
(*                 let (info2,ne2) = get_array_transform_info_lst_from_exp e2 in *)
(*                 (info1@info2,ListPerm (ne1,ne2,loc)) *)
(*           | EqMax (e1, e2, e3, loc)-> *)
(*                 let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in *)
(*                 let (info2,ne2) = get_array_transform_info_lst_from_exp e2 in *)
(*                 let (info3,ne3) = get_array_transform_info_lst_from_exp e3 in *)
(*                 ((info1@info2)@info3,EqMax (ne1,ne2,ne3,loc)) *)
(*           | EqMin (e1, e2, e3, loc)-> *)
(*                 let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in *)
(*                 let (info2,ne2) = get_array_transform_info_lst_from_exp e2 in *)
(*                 let (info3,ne3) = get_array_transform_info_lst_from_exp e3 in *)
(*                 ((info1@info2)@info3,EqMin (ne1,ne2,ne3,loc)) *)
(*           | BagIn (sv,e1,loc)-> *)
(*                 let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in *)
(*                 (info1,BagIn (sv,ne1,loc)) *)
(*           | BagNotIn (sv,e1,loc)-> *)
(*                 let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in *)
(*                 (info1,BagNotIn (sv,ne1,loc)) *)
(*           | Frm _ *)
(*           | XPure _ *)
(*           | LexVar _ *)
(*           | BConst _ *)
(*           | BVar _ *)
(*           | BagMin _ *)
(*           | BagMax _ *)
(*           | VarPerm _ *)
(*           | RelForm _ -> *)
(*                 ([],p) *)
(*       in *)
(*       let (info,np) = helper p in *)
(*       (info, (np,None)) *)
(*     in *)
(*     match f with *)
(*       | BForm (b,fl)-> *)
(*             let (info,nb) = get_array_transform_info_lst_from_b_formula b in *)
(*             (info,BForm (nb,fl)) *)
(*       | And (f1,f2,l)-> *)
(*             let (info1,nf1) = get_array_transform_info_lst_helper f1 in *)
(*             let (info2,nf2) = get_array_transform_info_lst_helper f2 in *)
(*             (info1@info2,And (nf1,nf2,l)) *)
(*       | AndList lst-> *)
(*             let (result_info,result_nfl) = List.fold_left (fun (infol,nfl) (t,and_fo)->let (info,nf) = get_array_transform_info_lst_helper and_fo in (infol@info,nfl@[(t,nf)])) ([],[]) lst in *)
(*             (result_info,AndList result_nfl) *)
(*       | Or (f1,f2,fl,l)-> *)
(*             let (info1,nf1) = get_array_transform_info_lst_helper f1 in *)
(*             let (info2,nf2) = get_array_transform_info_lst_helper f2 in *)
(*             (info1@info2,Or (nf1,nf2,fl,l)) *)
(*       | Not (f,fl,l)-> *)
(*             let (info1,nf1) = get_array_transform_info_lst_helper f in *)
(*             (info1,Not (nf1,fl,l)) *)
(*       | Forall (sv,f,fl,l)-> *)
(*             let (info1,nf1) = get_array_transform_info_lst_helper f in *)
(*             (info1,Forall (sv,nf1,fl,l)) *)
(*       | Exists (sv,f,fl,l)-> *)
(*             let (info1,nf1) = get_array_transform_info_lst_helper f in *)
(*             (info1,Exists (sv,nf1,fl,l)) *)
(*   in *)
(*   let rec no_duplicate_array_name *)
(*         (alst:array_transform_info list):array_transform_info list= *)
(*     let rec duplicate_array_at *)
(*           (a:array_transform_info) (alst:array_transform_info list):bool= *)
(*       match alst with *)
(*         | h::rest -> if is_same_array_at a.target_array h.target_array then true else duplicate_array_at a rest *)
(*         | [] -> false *)
(*     in *)
(*     match alst with *)
(*       | h::rest -> if duplicate_array_at h rest then no_duplicate_array_name rest else h::(no_duplicate_array_name rest) *)
(*       | [] -> [] *)
(*   in *)
(*   let (infolst,nf) = get_array_transform_info_lst_helper f in *)
(*   (no_duplicate_array_name infolst,nf) *)
(* ;; *)

let get_array_index
      (e:exp):exp=
  match e with
    | ArrayAt (_,elst,_)->
          begin
            match elst with
              |[h] -> h
              | _ -> failwith "get_array_index: Invalid index format"
          end
    | _ -> failwith "get_array_index: Invalid input"
;;

(* What is returned is a list of (A*B). A is a list of array_transform_info, indicating the mapping from an ArrayAt to a Var. B is a list of (exp*exp), indicating the relation between indexes *)
(* let constraint_generator *)
(*       (baselst:exp list) (infolst:array_transform_info list):((array_transform_info list) * ((exp * exp) list)) list= *)
(*   let rec iterate *)
(*         (baselst:exp list) (infolst:array_transform_info list) (whole_infolst:array_transform_info list) (translate_info:(exp * array_transform_info) list):((array_transform_info list) * ((exp * exp) list)) list= *)
(*     match baselst, infolst with *)
(*       | hb::restb,hi::resti -> *)
(*             if is_same_array hb hi.target_array *)
(*             then (iterate restb whole_infolst whole_infolst ((hb,hi)::translate_info)) @ (iterate baselst resti whole_infolst translate_info) *)
(*             else iterate baselst resti whole_infolst translate_info *)
(*       | [], _ -> *)
(*             let mk_result *)
(*                   ((e,info):(exp * array_transform_info)):(array_transform_info * (exp * exp))= *)
(*               let (index1,index2) = (get_array_index e,get_array_index info.target_array) in *)
(*               ({target_array = e; new_name = info.new_name},(index1,index2)) *)
(*             in *)
(*             [(List.split (List.fold_left (fun result (e,info) -> (mk_result (e,info))::result) [] translate_info))] *)
(*       | _, [] -> *)
(*             [] *)
(*   in *)
(*   iterate baselst infolst infolst [] *)
(* ;; *)

(* return a list of exp, indicating what ArrayAt is contained in a p_formula*)
(* let extract_translate_base *)
(*       (p:p_formula):(exp list)= *)
(*   let rec extract_translate_base_exp *)
(*         (e:exp):(exp list)= *)
(*     match e with *)
(*       | ArrayAt _ -> *)
(*             [e] *)
(*       | Add (e1,e2,loc) *)
(*       | Subtract (e1,e2,loc) *)
(*       | Mult (e1,e2,loc) *)
(*       | Div (e1,e2,loc) -> *)
(*             (extract_translate_base_exp e1)@(extract_translate_base_exp e2) *)
(*       | _ -> [] *)
(*   in *)
(*   let helper *)
(*         (p:p_formula):(exp list) = *)
(*     match p with *)
(*       | Frm _ *)
(*       | XPure _ *)
(*       | LexVar _ *)
(*       | BConst _ *)
(*       | BVar _ *)
(*       | BagMin _ *)
(*       | BagMax _ *)
(*       | VarPerm _ *)
(*       | RelForm _ -> *)
(*             [] *)
(*       | BagIn (sv,e1,loc) *)
(*       | BagNotIn (sv,e1,loc)-> *)
(*             extract_translate_base_exp e1 *)
(*       | Lt (e1,e2,loc) *)
(*       | Lte (e1,e2,loc) *)
(*       | Gt (e1,e2,loc) *)
(*       | Gte (e1,e2,loc) *)
(*       | SubAnn (e1,e2,loc) *)
(*       | Eq (e1,e2,loc) *)
(*       | Neq (e1,e2,loc) *)
(*       | ListIn (e1,e2,loc) *)
(*       | ListNotIn (e1,e2,loc) *)
(*       | ListAllN (e1,e2,loc) *)
(*       | ListPerm (e1,e2,loc)-> *)
(*             (extract_translate_base_exp e1)@(extract_translate_base_exp e2) *)
(*       | EqMax (e1,e2,e3,loc) *)
(*       | EqMin (e1,e2,e3,loc)-> *)
(*             (extract_translate_base_exp e1)@(extract_translate_base_exp e2)@(extract_translate_base_exp e3) *)
(*       | _ ->  [] *)
(*   in *)
(*   helper p *)
(* ;; *)

(* find_replace: find a new name for an array expression, return the new expression and the new transform information *)
(* The array expressions and the new variable expressions are mapped one to one *)
(* let find_replace *)
(*       (e:exp) (infolst:array_transform_info list):(exp * (array_transform_info list))= *)
(*   let rec helper *)
(*         (e:exp) (infolst:array_transform_info list):(exp * (array_transform_info list))= *)
(*     match infolst with *)
(*       | h::rest -> *)
(*             if is_same_array_at e h.target_array *)
(*             then (h.new_name, rest) *)
(*             else *)
(*               helper e rest *)
(*       | []-> failwith "find_replace: Fail to find a new name for array" *)
(*   in *)
(*   match e with *)
(*     | ArrayAt _ -> *)
(*           helper e infolst *)
(*     | _ -> failwith "find_replace: Invalid input" *)
(* ;; *)

(* let find_replace *)
(*       (e:exp) (infolst:array_transform_info list):(exp* (array_transform_info list))= *)
(*   let p_result = *)
(*     function *)
(*         (e,alst) -> "exp: "^(ArithNormalizer.string_of_exp e)^"\n array_transform_info list: "^(List.fold_left (fun r i -> r^(string_of_array_transform_info i)^"\n") "\n" alst) *)
(*   in *)
(*   let p_infolst = *)
(*     function *)
(*         h -> List.fold_left (fun r i -> r^(string_of_array_transform_info i)^"\n") "\n" h *)
(*   in *)
(*   let p_e = ArithNormalizer.string_of_exp in *)
(*   Debug.no_2 "find_replace" p_e p_infolst p_result (fun e i -> find_replace e i) e infolst *)
(* ;; *)
(* END of find_replace *)

(* let translate_array_formula_LHS_b_formula *)
(*       ((p,ba):b_formula) (infolst:array_transform_info list):(((exp * exp) list) * b_formula) list= *)
(*   let translate_base = extract_translate_base p in *)
(*   (\* translate_base is a list of exp, denoting all the ArrayAt in a p_formula *\) *)
(*   let translate_infolstlst = constraint_generator translate_base infolst in *)
(*   let rec mk_array_free_exp *)
(*         (e:exp) (infolst:array_transform_info list):(exp * (array_transform_info list))= *)
(*     match e with *)
(*       | ArrayAt _ -> *)
(*             find_replace e infolst *)
(*       | Add (e1,e2,loc)-> *)
(*             let (ne1,ninfolst) = mk_array_free_exp e1 infolst in *)
(*             let (ne2,ninfolst) = mk_array_free_exp e2 ninfolst in *)
(*             (Add (ne1,ne2,loc),ninfolst) *)
(*       | Subtract (e1,e2,loc)-> *)
(*             let (ne1,ninfolst) = mk_array_free_exp e1 infolst in *)
(*             let (ne2,ninfolst) = mk_array_free_exp e2 ninfolst in *)
(*             (Subtract (ne1,ne2,loc),ninfolst) *)
(*       | Mult (e1,e2,loc)-> *)
(*             let (ne1,ninfolst) = mk_array_free_exp e1 infolst in *)
(*             let (ne2,ninfolst) = mk_array_free_exp e2 ninfolst in *)
(*             (Mult (ne1,ne2,loc),ninfolst) *)
(*       | Div (e1,e2,loc)-> *)
(*             let (ne1,ninfolst) = mk_array_free_exp e1 infolst in *)
(*             let (ne2,ninfolst) = mk_array_free_exp e2 ninfolst in *)
(*             (Div (ne1,ne2,loc),ninfolst) *)
(*       | _ -> (e,infolst) *)
(*   in *)
(*   let mk_array_free_formula *)
(*         (p:p_formula) (infolst:array_transform_info list):p_formula= *)
(*     match p with *)
(*       | Frm _ *)
(*       | XPure _ *)
(*       | LexVar _ *)
(*       | BConst _ *)
(*       | BVar _ *)
(*       | BagMin _ *)
(*       | BagMax _ *)
(*       | VarPerm _ *)
(*       | RelForm _ -> *)
(*             p *)
(*       | BagIn (sv,e1,loc)-> *)
(*             let (ne,ninfolst) = mk_array_free_exp e1 infolst in *)
(*             if (List.length ninfolst)=0 *)
(*             then BagIn (sv,ne,loc) *)
(*             else failwith "mk_array_free_formula: Invalid replacement" *)
(*       | BagNotIn (sv,e1,loc)-> *)
(*             let (ne,ninfolst) = mk_array_free_exp e1 infolst in *)
(*             if (List.length ninfolst)=0 *)
(*             then BagNotIn (sv,ne,loc) *)
(*             else failwith "mk_array_free_formula: Invalid replacement" *)
(*       | Lt (e1,e2,loc) -> *)
(*             let (ne1,ninfolst) = mk_array_free_exp e1 infolst in *)
(*             let (ne2,ninfolst) = mk_array_free_exp e2 ninfolst in *)
(*             if (List.length ninfolst)=0 *)
(*             then *)
(*               Lt (ne1,ne2,loc) *)
(*             else *)
(*               failwith "mk_array_free_formula: Invalid replacement" *)
(*       | Lte (e1,e2,loc) -> *)
(*             let (ne1,ninfolst) = mk_array_free_exp e1 infolst in *)
(*             let (ne2,ninfolst) = mk_array_free_exp e2 ninfolst in *)
(*             if (List.length ninfolst)=0 *)
(*             then *)
(*               Lte (ne1,ne2,loc) *)
(*             else *)
(*               failwith "mk_array_free_formula: Invalid replacement" *)
(*       | Gt (e1,e2,loc) -> *)
(*             let (ne1,ninfolst) = mk_array_free_exp e1 infolst in *)
(*             let (ne2,ninfolst) = mk_array_free_exp e2 ninfolst in *)
(*             if (List.length ninfolst)=0 *)
(*             then *)
(*               Gt (ne1,ne2,loc) *)
(*             else *)
(*               failwith "mk_array_free_formula: Invalid replacement" *)
(*       | Gte (e1,e2,loc) -> *)
(*             let (ne1,ninfolst) = mk_array_free_exp e1 infolst in *)
(*             let (ne2,ninfolst) = mk_array_free_exp e2 ninfolst in *)
(*             if (List.length ninfolst)=0 *)
(*             then *)
(*               Gte (ne1,ne2,loc) *)
(*             else *)
(*               failwith "mk_array_free_formula: Invalid replacement" *)
(*       | SubAnn (e1,e2,loc) -> *)
(*             let (ne1,ninfolst) = mk_array_free_exp e1 infolst in *)
(*             let (ne2,ninfolst) = mk_array_free_exp e2 ninfolst in *)
(*             if (List.length ninfolst)=0 *)
(*             then *)
(*               SubAnn (ne1,ne2,loc) *)
(*             else *)
(*               failwith "mk_array_free_formula: Invalid replacement" *)
(*       | Eq (e1,e2,loc) -> *)
(*             let (ne1,ninfolst) = mk_array_free_exp e1 infolst in *)
(*             let (ne2,ninfolst) = mk_array_free_exp e2 ninfolst in *)
(*             if (List.length ninfolst)=0 *)
(*             then *)
(*               Eq (ne1,ne2,loc) *)
(*             else *)
(*               failwith "mk_array_free_formula: Invalid replacement" *)
(*       | Neq (e1,e2,loc) -> *)
(*             let (ne1,ninfolst) = mk_array_free_exp e1 infolst in *)
(*             let (ne2,ninfolst) = mk_array_free_exp e2 ninfolst in *)
(*             if (List.length ninfolst)=0 *)
(*             then *)
(*               Neq (ne1,ne2,loc) *)
(*             else *)
(*               failwith "mk_array_free_formula: Invalid replacement" *)
(*       | ListIn (e1,e2,loc) -> *)
(*             let (ne1,ninfolst) = mk_array_free_exp e1 infolst in *)
(*             let (ne2,ninfolst) = mk_array_free_exp e2 ninfolst in *)
(*             if (List.length ninfolst)=0 *)
(*             then *)
(*               ListIn (ne1,ne2,loc) *)
(*             else *)
(*               failwith "mk_array_free_formula: Invalid replacement" *)
(*       | ListNotIn (e1,e2,loc) -> *)
(*             let (ne1,ninfolst) = mk_array_free_exp e1 infolst in *)
(*             let (ne2,ninfolst) = mk_array_free_exp e2 ninfolst in *)
(*             if (List.length ninfolst)=0 *)
(*             then *)
(*               ListNotIn (ne1,ne2,loc) *)
(*             else *)
(*               failwith "mk_array_free_formula: Invalid replacement" *)
(*       | ListAllN (e1,e2,loc) -> *)
(*             let (ne1,ninfolst) = mk_array_free_exp e1 infolst in *)
(*             let (ne2,ninfolst) = mk_array_free_exp e2 ninfolst in *)
(*             if (List.length ninfolst)=0 *)
(*             then *)
(*               ListAllN (ne1,ne2,loc) *)
(*             else *)
(*               failwith "mk_array_free_formula: Invalid replacement" *)
(*       | ListPerm (e1,e2,loc)-> *)
(*             let (ne1,ninfolst) = mk_array_free_exp e1 infolst in *)
(*             let (ne2,ninfolst) = mk_array_free_exp e2 ninfolst in *)
(*             if (List.length ninfolst)=0 *)
(*             then *)
(*               ListPerm (ne1,ne2,loc) *)
(*             else *)
(*               failwith "mk_array_free_formula: Invalid replacement" *)
(*       | EqMax (e1,e2,e3,loc)-> *)
(*             let (ne1,ninfolst) = mk_array_free_exp e1 infolst in *)
(*             let (ne2,ninfolst) = mk_array_free_exp e2 ninfolst in *)
(*             let (ne3,ninfolst) = mk_array_free_exp e3 ninfolst in *)
(*             if (List.length ninfolst)=0 *)
(*             then *)
(*               EqMax (ne1,ne2,ne3,loc) *)
(*             else *)
(*               failwith "mk_array_free_formula: Invalid replacement" *)
(*       | EqMin (e1,e2,e3,loc)-> *)
(*             let (ne1,ninfolst) = mk_array_free_exp e1 infolst in *)
(*             let (ne2,ninfolst) = mk_array_free_exp e2 ninfolst in *)
(*             let (ne3,ninfolst) = mk_array_free_exp e3 ninfolst in *)
(*             if (List.length ninfolst)=0 *)
(*             then *)
(*               EqMin (ne1,ne2,ne3,loc) *)
(*             else *)
(*               failwith "mk_array_free_formula: Invalid replacement" *)
(*       | _ ->  p *)
(*   in *)
(*   let rec mk_array_free_formula_lst *)
(*         (\* (p:p_formula) (infolstlst:(((array_transform_info list) * ((exp * exp) list)) list)):(((p_formula list) * b_formula) list)= *\) *)
(*         (p:p_formula) (infolstlst:(((array_transform_info list) * ((exp * exp) list)) list)):((((exp * exp) list) * b_formula) list)= *)
(*     match infolstlst with *)
(*       | (alst,eelst)::rest -> *)
(*             (\* let plst = List.map (fun (e1,e2) -> Eq (e1,e2,no_pos)) eelst in *\) *)
(*             begin *)
(*               match eelst with *)
(*                 | [] -> mk_array_free_formula_lst p rest *)
(*                 | _ -> (eelst,(mk_array_free_formula p alst,None))::(mk_array_free_formula_lst p rest) *)
(*             end *)
(*       | [] -> [] *)
(*   in *)
(*   mk_array_free_formula_lst p translate_infolstlst *)
(* ;; *)

(* let rec translate_array_formula_LHS *)
(*       (f:formula) (infolst:array_transform_info list) (f_whole:formula):formula= *)
(*   match f with *)
(*     | BForm (b,fl)-> *)
(*           let rec helper *)
(*                 (\* (lhslst:((p_formula list) * b_formula) list):formula=*\) *)
(*                 (lhslst:((((exp * exp) list) * b_formula) list)) : formula = *)
(*             match lhslst with *)
(*               | [] -> f *)
(*               | (eelst,bformula)::rest -> *)
(*                     let ante = mk_and_list (List.map (fun (i, ni) -> produce_new_index_predicate_wrapper (extract_index_predicate f_whole i) i ni) eelst) in *)
(*                     (\* let ante = mk_and_list (List.map (fun p -> BForm ((p,None),None)) plst) in *\) *)
(*                     let imply = mk_imply ante (BForm (bformula,None)) in *)
(*                     And (imply,helper rest,no_pos) *)
(*           in *)
(*           let lhslst = translate_array_formula_LHS_b_formula b infolst in *)
(*           helper lhslst *)
(*     | And (f1,f2,l)-> *)
(*           And (translate_array_formula_LHS f1 infolst f_whole,translate_array_formula_LHS f2 infolst f_whole,l) *)
(*     | AndList lst-> *)
(*           AndList (List.map (fun (t,f)->(t,translate_array_formula_LHS f infolst f_whole)) lst) *)
(*     | Or (f1,f2,fl,l)-> *)
(*           Or (translate_array_formula_LHS f1 infolst f_whole,translate_array_formula_LHS f2 infolst f_whole,fl,l) *)
(*     | Not (f,fl,l)-> *)
(*           Not (translate_array_formula_LHS f infolst f_whole,fl,l) *)
(*     | Forall (sv,f,fl,l)-> *)
(*           Forall (sv,translate_array_formula_LHS f infolst f_whole,fl,l) *)
(*     | Exists (sv,f,fl,l)-> *)
(*           Exists (sv,translate_array_formula_LHS f infolst f_whole,fl,l) *)
(* ;; *)

(* let translate_array_formula_LHS *)
(*       (f:formula) (infolst:array_transform_info list):formula= *)
(*   translate_array_formula_LHS f infolst f *)
(* ;; *)

(* translating array equation *)
let mk_array_equal_formula
      (ante:formula) (infolst:array_transform_info list):formula option=
  let array_new_name_tbl = Hashtbl.create 10000 in
  let rec create_array_new_name_tbl
        (infolst:array_transform_info list)=
    match infolst with
      | h::rest ->
            let new_name_list =
              try
                Hashtbl.find array_new_name_tbl (get_array_name h.target_array)
              with
                  Not_found-> []
            in
            let _ = Hashtbl.replace array_new_name_tbl (get_array_name h.target_array) (((get_array_index h.target_array),h.new_name)::new_name_list) in
            create_array_new_name_tbl rest
      | [] -> ()
  in
  let rec match_two_name_list
        (namelst1:(exp * exp) list) (namelst2:(exp * exp) list):formula=
    let rec helper
          ((i1,n1):(exp * exp)) (namelst:(exp * exp) list):formula=
      match namelst with
        | [(i2,n2)] ->
              let index_formula = BForm ((Eq (i1,i2,no_pos),None),None) in
              let name_formula = BForm( (Eq (n1,n2,no_pos),None),None) in
              mk_imply index_formula name_formula
        | (i2,n2)::rest ->
              let index_formula = BForm ((Eq (i1,i2,no_pos),None),None) in
              let name_formula = BForm( (Eq (n1,n2,no_pos),None),None) in
              let imply = mk_imply index_formula name_formula in
              And (imply,helper (i1,n1) rest,no_pos)
        | [] -> failwith "mk_array_equal_formula: Invalid input"
    in
    match namelst1 with
      | [h] -> helper h namelst2
      | h::rest ->
            And (helper h namelst2,match_two_name_list rest namelst2,no_pos)
      | [] -> failwith "mk_array_equal_formula: Invalid input"
  in
  let rec mk_array_equal_formula_list
        (ante:formula):(formula list)=
    let mk_array_equal_formula_list_b_formula
          ((p,ba):b_formula):(formula list)=
      match p with
        | Eq (Var (sv1,_), Var (sv2,_), loc) ->
              begin
                try
                  let namelst1 = Hashtbl.find array_new_name_tbl sv1 in
                  let namelst2 = Hashtbl.find array_new_name_tbl sv2 in
                  [(match_two_name_list namelst1 namelst2)]
                with
                    Not_found -> []
              end
        | _ -> []
    in
    match ante with
      | BForm (b,fl)->
            mk_array_equal_formula_list_b_formula b
      | And (f1,f2,loc)->
          (mk_array_equal_formula_list f1)@(mk_array_equal_formula_list f2)
      | AndList lst->
            List.fold_left (fun result (_,f) -> result@(mk_array_equal_formula_list f)) [] lst
      | Or (f1,f2,fl,loc)->
            (mk_array_equal_formula_list f1)@(mk_array_equal_formula_list f2)
      | Not (f,fl,loc)->
            mk_array_equal_formula_list f
      | Forall (sv,f,fl,loc)->
            mk_array_equal_formula_list f
      | Exists (sv,f,fl,loc)->
            mk_array_equal_formula_list f
  in
  let _ = create_array_new_name_tbl infolst in
  let flst = mk_array_equal_formula_list ante in
  match flst with
    | [] -> None
    | _ -> Some (mk_and_list flst)
;;


let mk_array_equal_formula
      (ante:formula) (infolst:array_transform_info list):(formula option)=
  let pinfolst=
    function
      | l-> List.fold_left (fun r i -> r^(string_of_array_transform_info i)^"\n") "\n" l
  in
  let pf = !print_pure in
  let presult =
    function
      | Some f -> pf f
      | None -> "None"
  in
  Debug.no_2 "mk_array_equal_formula" pf pinfolst presult (fun ante infolst-> mk_array_equal_formula ante infolst) ante infolst
;;
(* END of translating array equation *)

(* let translate_out_array_in_imply *)
(*       (ante:formula) (conseq:formula) : (formula * formula) = *)
(*   let (ante,conseq) = standarize_array_imply ante conseq in *)
(*   let (info_lst,n_conseq) = get_array_transform_info_lst (And (conseq,ante,no_pos)) in *)
(*   let n_ante = translate_array_formula_LHS ante info_lst in *)
(*   let n_ante = *)
(*     match mk_array_equal_formula ante info_lst with *)
(*       | Some f -> And (f,n_ante,no_pos) *)
(*       | None -> n_ante *)
(*   in *)
(*   let (_,n_conseq) = get_array_transform_info_lst conseq in *)
(*   (n_ante,n_conseq) *)
(* ;; *)
(* (\*          *******************************         *\) *)



(* let array_new_name_tbl size= *)
(*   let tbl = Hashtbl.create size in *)
(*   let find *)
(*         (sv:specvar):exp list= *)
(*     try *)
(*       Hashtbl.find tbl sv *)
(*     with *)
(*       | Not_found->[] *)
(*   in *)
(*   let add *)
(*         (sv:specvar) (e:exp)= *)
(*     let r = find sv in *)
(*     Hashtbl.replace sv (e::r) *)
(*   in *)
(*   let dispatch *)
(*         (meth_name:string) *)



(* let translate_out_array_in_one_formula *)
(*       (f:formula):formula= *)
(*   let f = standarize_one_formula f in *)
(*   let (info_lst,_) = get_array_transform_info_lst f in *)
(*   let nf = translate_array_formula_LHS f info_lst in *)
(*   let nf = *)
(*     match mk_array_equal_formula f info_lst with *)
(*       | Some f -> And (f,nf,no_pos) *)
(*       | None -> nf *)
(*   in *)
(*   nf *)
(* ;; *)



(* translate the array back to the formula *)
let rec translate_back_array_in_one_formula
      (f:formula):formula=
  let rec translate_back_array_in_exp
        (e:exp):exp =
    match e with
      | Var (sv,_)->
            begin
              match sv with
                | SpecVar (t,i,p)->
                      let arr_var_regexp = Str.regexp ".*___.*___" in
                      if (Str.string_match arr_var_regexp i 0)
                      then
                        (*let i = String.sub i 8 ((String.length i) - 9) in*)
                        let splitter = Str.regexp "___" in
                        let name_list = Str.split splitter i in
                        let arr_name = List.nth name_list 0 in
                        let index = List.nth name_list 1 in
                        let n_sv = SpecVar (Array (t,1),arr_name,p) in
                        let n_exp =
                          try
                            let const = int_of_string index in
                            IConst (const,no_pos)
                          with
                              Failure "int_of_string" ->
                                  Var (SpecVar (Int,index,Unprimed),no_pos)
                        in
                        ArrayAt (n_sv,[n_exp],no_pos)
                      else
                        e
            end
      | Add (e1,e2,loc)->
            Add (translate_back_array_in_exp e1, translate_back_array_in_exp e2, loc)
      | Subtract (e1,e2,loc)->
            Subtract (translate_back_array_in_exp e1, translate_back_array_in_exp e2, loc)
      | Mult (e1,e2,loc)->
            Mult (translate_back_array_in_exp e1, translate_back_array_in_exp e2, loc)
      | Div (e1,e2,loc)->
            Div (translate_back_array_in_exp e1, translate_back_array_in_exp e2, loc)
      | _ -> e
  in
  let translate_back_array_in_b_formula
        ((p,ba):b_formula):b_formula =
    let helper
          (p:p_formula):p_formula =
      match p with
        | Frm _
        | XPure _
        | LexVar _
        | BConst _
        | BVar _
        | BagMin _
        | BagMax _
        (* | VarPerm _ *)
        | RelForm _ ->
              p
        | BagIn (sv,e1,loc)->
              p
        | BagNotIn (sv,e1,loc)->
              p
        | Lt (e1,e2,loc) ->
              Lt (translate_back_array_in_exp e1, translate_back_array_in_exp e2,loc)
        | Lte (e1,e2,loc) ->
              Lte (translate_back_array_in_exp e1, translate_back_array_in_exp e2,loc)
        | Gt (e1,e2,loc) ->
              Gt (translate_back_array_in_exp e1, translate_back_array_in_exp e2,loc)
        | Gte (e1,e2,loc) ->
              Gte (translate_back_array_in_exp e1, translate_back_array_in_exp e2,loc)
        | SubAnn (e1,e2,loc) ->
              SubAnn (translate_back_array_in_exp e1, translate_back_array_in_exp e2,loc)
        | Eq (e1,e2,loc) ->
              Eq (translate_back_array_in_exp e1, translate_back_array_in_exp e2,loc)
        | Neq (e1,e2,loc) ->
              Neq (translate_back_array_in_exp e1, translate_back_array_in_exp e2,loc)
        | ListIn (e1,e2,loc) ->
              ListIn (translate_back_array_in_exp e1, translate_back_array_in_exp e2,loc)
        | ListNotIn (e1,e2,loc) ->
              ListNotIn (translate_back_array_in_exp e1, translate_back_array_in_exp e2,loc)
        | ListAllN (e1,e2,loc) ->
              ListAllN (translate_back_array_in_exp e1, translate_back_array_in_exp e2,loc)
        | ListPerm (e1,e2,loc)->
              ListPerm (translate_back_array_in_exp e1, translate_back_array_in_exp e2,loc)
        | EqMax (e1,e2,e3,loc)->
              EqMax (translate_back_array_in_exp e1, translate_back_array_in_exp e2, translate_back_array_in_exp e3, loc)
        | EqMin (e1,e2,e3,loc)->
              EqMin (translate_back_array_in_exp e1, translate_back_array_in_exp e2,translate_back_array_in_exp e3,loc)
        | _ -> p
    in
    (helper p,ba)
  in
  match f with
    | BForm (b,fl)->
          BForm (translate_back_array_in_b_formula b,fl)
    | And (f1,f2,loc)->
          And (translate_back_array_in_one_formula f1,translate_back_array_in_one_formula f2,loc)
    | AndList lst->
          AndList (List.map (fun (t,f)-> (t,translate_back_array_in_one_formula f)) lst)
    | Or (f1,f2,fl,loc)->
          Or (translate_back_array_in_one_formula f1,translate_back_array_in_one_formula f2,fl,loc)
    | Not (f,fl,loc)->
          Not (translate_back_array_in_one_formula f,fl,loc)
    | Forall (sv,f,fl,loc)->
          Forall (sv,translate_back_array_in_one_formula f,fl,loc)
    | Exists (sv,f,fl,loc)->
          Exists (sv,translate_back_array_in_one_formula f,fl,loc)
;;


let translate_back_array_in_one_formula
      (f:formula):formula =
  if (!Globals.array_translate)
  then translate_back_array_in_one_formula f
  else f
;;

let translate_back_array_in_one_formula
      (f:formula):formula =
  let pf = !print_pure in
  Debug.no_1 "translate_back_array_in_one_formula" pf pf (fun f -> translate_back_array_in_one_formula f) f
;;
(* END of translating back the array to a formula *)


(* Controlled by Globals.array_translate *)
(* let translate_out_array_in_imply *)
(*       (ante:formula)(conseq:formula):(formula*formula)= *)
(*   if !Globals.array_translate then translate_out_array_in_imply ante conseq *)
(*   else (ante,conseq) *)

(* let drop_array_formula *)
(*       (f:formula):formula= *)
(*   if !Globals.array_translate then drop_array_formula f *)
(*   else f *)
(* ;; *)




(* let drop_array_formula *)
(*       (f:formula):formula= *)
(*   let pr = !print_pure in *)
(*   Debug.no_1 "drop_array_formula" pr pr (fun fo->drop_array_formula fo) f *)

(* let translate_out_array_in_imply *)
(*       (ante:formula)(conseq:formula):(formula*formula)= *)
(*   let p1 = !print_pure in *)
(*   let p2 (f1,f2) = "new ante: "^(p1 f1)^"\nnew conseq: "^(p1 f2) in *)
(*   Debug.no_2 "translate_out_array_in_imply" p1 p1 p2 (fun f1 f2-> translate_out_array_in_imply f1 f2) ante conseq *)



(* let translate_out_array_in_one_formula_full *)
(*       (f:formula):formula= *)
(*   let f = translate_array_relation f in *)
(*   let nf = translate_out_array_in_one_formula f in *)
(*   let dnf = drop_array_formula nf in *)
(*   dnf *)
(* ;; *)

(* let translate_out_array_in_one_formula_full *)
(*       (f:formula):formula= *)
(*   if !Globals.array_translate then translate_out_array_in_one_formula_full f *)
(*   else f *)
(* ;; *)

(* let translate_out_array_in_one_formula_full *)
(*       (f:formula):formula= *)
(*   let pf = !print_pure in *)
(*   Debug.no_1 "translate_out_array_in_one_formula_full" pf pf (fun f -> translate_out_array_in_one_formula_full f) f *)
(* ;; *)
