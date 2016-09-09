#include "xdebug.cppo"

open Cpure
open Globals
open Debug
open VarGen
(* Translate out array in cpure formula  *)

let global_unchanged_info = ref [];;
let string_of_exp = ArithNormalizer.string_of_exp;;



let plain_string_of_exp e0 =
  let need_parentheses e = match e with
    | Add _ | Subtract _ -> true
    | _ -> false
  in
  let wrap e =
       if need_parentheses e then "(" ^ (string_of_exp e) ^ ")"
       else (string_of_exp e)
  in
  let tmp_string_of_spec_var ?(print_typ=false) (sv: spec_var) =
    match sv with
    | SpecVar (t, v, p) ->
      if p==Primed
      then ("PRI"^v)
      else v
  in
  match e0 with
  | Null _ -> "null"
  | Var (v, _) -> tmp_string_of_spec_var v
  | IConst (i, _) -> string_of_int i
  | FConst (f, _) -> string_of_float f
  | AConst (f, _) -> string_of_heap_ann f
  | Tsconst (f,_) -> Tree_shares.Ts.string_of f
  | Add (e1, e2, _) -> (string_of_exp e1) ^ " + " ^ (string_of_exp e2)
  | Subtract (e1, e2, _) -> (string_of_exp e1) ^ " - " ^ (string_of_exp e2)
  | Mult (e1, e2, _) -> (wrap e1) ^ "*" ^ (wrap e2)
  | Div (e1, e2, _) -> (wrap e1) ^ "/" ^ (wrap e2)
  | Max (e1, e2, _) -> "max(" ^ (string_of_exp e1) ^ "," ^ (string_of_exp e2) ^ ")"
  | Min (e1, e2, _) -> "min(" ^ (string_of_exp e1) ^ "," ^ (string_of_exp e2) ^ ")"
  | TypeCast (ty, e1, _) -> "(" ^ (Globals.string_of_typ ty) ^ ") " ^ string_of_exp e1
  | ArrayAt (sv,elst,_)->
    let string_of_index_list
        (elst:exp list):string=
      List.fold_left (fun s e -> s ^"["^(string_of_exp e)^"]") "" elst
    in
    (string_of_spec_var sv)^(string_of_index_list elst) 
  | _ -> "???"
;;

let print_pure = ref (fun (c:formula) -> "printing not initialized");;
let print_p_formula = ref (fun (p:p_formula) -> "printing not initialized");;

let is_same_sv
    (sv1:spec_var) (sv2:spec_var):bool=
  (* let () = print_endline ((string_of_spec_var sv1)^" and "^(string_of_spec_var sv2)) in *)
  match sv1,sv2 with
  | SpecVar (t1,i1,p1), SpecVar (t2,i2,p2)->
    begin
      match p1,p2 with
      | Primed,Primed
      | Unprimed,Unprimed ->
        (* if (cmp_typ t1 t2) && (i1=i2) then true else false *)
        if (i1=i2) then true else false
      | _,_->
        (* let () = x_binfo_pp ("is_same_sv:different primed") no_pos in *)
        false
    end
;;

let rec remove_dupl equal lst =
  let rec helper item lst =
    match lst with
    | h::rest ->
      if equal item h then true
      else helper item rest
    | [] -> false
  in
  match lst with
  | h::rest ->
    if helper h rest
    then
      remove_dupl equal rest
    else
      h::(remove_dupl equal rest)
  | [] -> []
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

(* OrderTyped of expression *)
module OrderedExp =
  struct
    type t = Cpure.exp
    let compare e1 e2 =
      if is_same_exp e1 e2
      then 0
      else Pervasives.compare e1 e2
  end
;;

module ExpSet = Set.Make(OrderedExp);;

let string_of_expset s =
  "{ "^(ExpSet.fold (fun item r -> ((string_of_exp item)^" "^r)) s "")^"}"
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

let mk_array_new_name_sv
  sv e :spec_var =
  match sv with
  | SpecVar (typ,id,primed)->
    begin
      match typ with
      | Array (atyp,_)->
        SpecVar (atyp,(id)^"__"^(plain_string_of_exp e),primed)
      | _ -> failwith "mk_array_new_name: Not array type"
    end
;;


let mk_array_new_name
    (sv:spec_var) (e:exp):exp=
  Var (mk_array_new_name_sv sv e,no_pos)
;;

let mk_array_new_name
    (sv:spec_var) (e:exp):exp=
  let psv = string_of_spec_var in
  let pe = string_of_exp in
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
        then true
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
    (x_add_1 can_be_simplify not_f) || (not (contain_array not_f))
  | Forall (sv,f1,fl,loc) ->
    (is_valid_forall f1 sv) || (not (contain_array f1))
  | Exists (sv,f1,fl,loc) ->
    (is_valid_forall f1 sv) || (not (contain_array f1))
;;

let can_be_simplify
    (f:formula):bool =
  Debug.no_1 "can_be_simplify" !print_pure string_of_bool (fun f->can_be_simplify f) f
;;



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
      | Some e -> string_of_exp e
      | None -> "None"
    in
    Debug.no_2 "get_array_index_replacement" !print_pure string_of_spec_var peo (fun f sv -> get_array_index_replacement f sv) f sv
  in
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
    let rec replace_exp
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
            failwith ("replace_exp: Invalid index form "^(string_of_exp e))
        end
      | ArrayAt _ ->
        failwith "replace_exp: cannot handle multi-dimensional array"
      | Add (e1,e2,loc)->
        Add (replace_exp e1 ctx,replace_exp e2 ctx,loc)
      | Subtract (e1,e2,loc)->
        Subtract (replace_exp e1 ctx,replace_exp e2 ctx,loc)
      | Mult (e1,e2,loc)->
        Mult (replace_exp e1 ctx,replace_exp e2 ctx,loc)
      | Div (e1,e2,loc)->
        Div (replace_exp e1 ctx,replace_exp e2 ctx,loc)
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
          Exists (sv,process_helper f1 ctx,fl,loc)
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


(* This is actually problematic if there is disjunction inside *)
let constantize_ex_q f=
  let  get_array_index_replacement (* The input can be any form *)
        (f:formula) (sv:spec_var):(exp option) =
    let rec get_array_index_replacement_helper (* only pick up forms like (i=c) and !(i!=c) *)
          (f:formula) (sv:spec_var):(exp option) =
      (* let () = x_binfo_pp ("get_array_index_replacement_helper: "^(!print_pure f)) no_pos in *)
      match f with
        | Not (BForm ((Neq(e1,e2,_),_),_),_,_)
        | BForm((Eq (e1,e2,_),_),_)->
              begin
                match e1,e2 with
                  | Var (sv1,_),Var (sv2,_) ->
                        if is_same_sv sv1 sv
                        then Some (Var (sv2,no_pos))
                        else
                          if is_same_sv sv2 sv
                          then Some (Var (sv1,no_pos))
                          else
                            None
                  | Var (sv1,_), IConst i
                  | IConst i, Var (sv1,_) ->
                        if is_same_sv sv1 sv
                        then Some (IConst i)
                        else None
                  | _, _ ->
                        None
              end
        | And (f1,f2,loc)
        | Or (f1,f2,_,loc)->
              begin
                match get_array_index_replacement_helper f1 sv,get_array_index_replacement_helper f2 sv with
                  | None,None -> None
                  | Some r,_
                  | _,Some r ->
                        Some r
              end
        | Not (not_f,fl,loc)->
              get_array_index_replacement_helper not_f sv
        | AndList lst ->
              failwith ("process_helper: "^(!print_pure f)^" To Be Implemented")
        | _ ->
              None
    in
    (* let () = x_binfo_pp ("flst"^((pr_list !print_pure) flst)) no_pos in *)
    get_array_index_replacement_helper f sv
  in
  let get_array_index_replacement
        (f:formula) (sv:spec_var):(exp option) =
    let peo = function
      | Some e -> string_of_exp e
      | None -> "None"
    in
    Debug.no_2 "exists:get_array_index_replacement" !print_pure string_of_spec_var peo (fun f sv -> get_array_index_replacement f sv) f sv
  in
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
    let rec replace_exp
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
                        failwith ("replace_exp: Invalid index form "^(string_of_exp e))
              end
        | ArrayAt _ ->
              failwith "replace_exp: cannot handle multi-dimensional array"
        | Add (e1,e2,loc)->
              Add (replace_exp e1 ctx,replace_exp e2 ctx,loc)
        | Subtract (e1,e2,loc)->
              Subtract (replace_exp e1 ctx,replace_exp e2 ctx,loc)
        | Mult (e1,e2,loc)->
              Mult (replace_exp e1 ctx,replace_exp e2 ctx,loc)
        | Div (e1,e2,loc)->
              Div (replace_exp e1 ctx,replace_exp e2 ctx,loc)
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
            Forall (sv,process_helper f1 ctx,fl,loc)
      | Exists (sv,f1,fl,loc)->
            let r = get_array_index_replacement f1 sv in
            begin
              match r with
                | Some re ->
                      Exists (sv,process_helper f1 ((sv,re)::ctx),fl,loc)
                | None ->
                      Exists (sv,process_helper f1 ctx,fl,loc)
            end
  in
  process_helper f []
;;

(* ---------------------------------------------------------------------------------------------------- *)


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
    | _ -> failwith ("standarzie_exp: "^(string_of_exp e)^" To Be Implemented")
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
    | ImmRel _
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
  (* let (n_ante,flst1,_) = standarize_array_formula ante in *)
  (* let (n_conseq,flst2,_) = standarize_array_formula conseq in *)
  (* let n_ante = mk_and_list (n_ante::(flst1@flst2)) in *)
  (* (n_ante,n_conseq) *)
  let n_ante = standarize_one_formula ante in
  let (n_conseq,flst2,_) = standarize_array_formula conseq in
  let n_ante = mk_and_list (n_ante::(flst2)) in
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
(* For update_array_1d(a,a',v,i), translate it into forall(k:k!=i-->a[k]=a'[k]. *)

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
              let new_array_at = ArrayAt (SpecVar (t1,id1,p1),[List.nth elst 3],no_pos) in
              let new_eq = BForm ((Eq (new_array_at,List.nth elst 2,no_pos),None),None )in
              let new_q = mk_spec_var "i" in
              let new_ante = BForm((Neq (Var (new_q,no_pos), List.nth elst 3,no_pos),None),None) in
              let new_conseq = BForm((Eq (ArrayAt (SpecVar (t1,id1,p1),[Var (new_q,no_pos)],no_pos), ArrayAt (SpecVar (t0,id0,p0),[Var (new_q,no_pos)],no_pos),no_pos),None),None) in
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

let translate_array_relation f=
  if !Globals.array_translate
  then translate_array_relation f
  else f
;;

(* ------------------------------------------------------------------- *)

(* For a=a'*)

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
    (f:formula) (scheme:((spec_var * (exp list)) list)):(formula)=
  let produce_equality (* produce *)
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
      ((p,ba):b_formula) (scheme:((spec_var * (exp list)) list)):formula =
    match p with
    | Eq (Var (sv1,_), Var (sv2,_),loc) ->
      if is_same_sv sv1 sv2
      then BForm ((p,ba),None)
      else
        begin
          match find_match scheme sv1, find_match scheme sv2 with
          | Some indexlst1, Some indexlst2 ->
            mk_and_list ((produce_equality sv1 sv2 indexlst1)@(produce_equality sv1 sv2 indexlst2))
          | Some indexlst,_
          | _,Some indexlst ->
            mk_and_list (produce_equality sv1 sv2 indexlst)
          | _,_ -> BForm ((p,ba),None)
        end
    | _ ->
      BForm ((p,ba),None)
  in
  let rec helper
      (f:formula) (scheme:((spec_var * (exp list)) list)):formula=
    match f with
    | BForm (b,fl)->
      helper_b_formula b scheme
    | And (f1,f2,loc)->
      And ((helper f1 scheme) , (helper f2 scheme),loc)
    | AndList lst->
      failwith "translate_array_equality: AndList To Be Implemented"
    | Or (f1,f2,fl,loc)->
      f
    (*Or (helper f1 scheme,helper f2 scheme,fl,loc)*)
    (*failwith "translate_array_equality: To Be Normalized!"*)
    | Not (f,fl,loc)->
      Not (helper f scheme,fl,loc)
    | Forall _->
      f
    | Exists _->
      f
  in
  helper f scheme
;;

let translate_array_equality
    (f:formula) (scheme: ((spec_var * (exp list)) list)):(formula) =
  let string_of_translate_scheme
      (ts:((spec_var * (exp list)) list)):string=
    let string_of_item
        ((arr,indexlst):(spec_var * (exp list))):string=
      let string_of_indexlst = List.fold_left (fun s e -> s^" "^(string_of_exp e)^" ") "" indexlst in
      "array: "^(string_of_spec_var arr)^" { "^(string_of_indexlst)^"}"
    in
    List.fold_left (fun s item -> (string_of_item item)^" "^s) "" ts
  in
  let pfo = function
    | Some f -> !print_pure f
    | None -> "None"
  in
  Debug.no_2 "translate_array_equality" !print_pure string_of_translate_scheme !print_pure (fun f scheme -> translate_array_equality f scheme) f scheme
;;

(* ------------------------------------------------------------------- *)
let translate_array_equality_to_forall
    (f:formula) :(formula)=
  let helper_b_formula
      ((p,ba):b_formula):formula =
    match p with
    | Eq ((Var (SpecVar (Array _,arr1,_) as sv1,_)), (Var (SpecVar (Array _,arr2,_) as sv2,_)),_) ->
      if is_same_sv sv1 sv2
      then BForm ((p,ba),None)
      else
        let q = SpecVar (Int,"tmp_q",Unprimed) in
        let index = Var (q,no_pos) in
        let equation = BForm((Eq (ArrayAt (sv1,[index],no_pos),ArrayAt (sv2,[index],no_pos),no_pos),None),None) in
        let forall = Forall (q,equation,None,no_pos) in
        And (forall,BForm ((p,ba),None),no_pos)
    | _ ->
      BForm ((p,ba),None)
  in
  let rec helper
      (f:formula):formula=
    match f with
    | BForm (b,fl)->
      helper_b_formula b
    | And (f1,f2,loc)->
      And ((helper f1) , (helper f2),loc)
    | AndList lst->
      failwith "translate_array_equality: AndList To Be Implemented"
    | Or (f1,f2,fl,loc)->
      Or (helper f1,helper f2,fl,loc)
    (*Or (helper f1 scheme,helper f2 scheme,fl,loc)*)
    (*failwith "translate_array_equality: To Be Normalized!"*)
    | Not (f,fl,loc)->
      Not (helper f,fl,loc)
    | Forall (sv,nf,fl,loc)->
      Forall (sv,helper nf,fl,loc)
    | Exists (sv,nf,fl,loc)->
      Exists (sv,helper nf,fl,loc)
  in
  helper f
;;

let translate_array_equality_to_forall
    (f:formula) :(formula) =
  Debug.no_1 "translate_array_equality_to_forall" !print_pure !print_pure translate_array_equality_to_forall f
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
  if (* Globals.infer_const_obj # is_arr_as_var *)
    !Globals.array_translate
  then split_and_combine processor cond f
  else processor f
;;
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

    (* | ImmRel _ *)
(* Turn all the array element in f into normal variables *)
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
    | _ -> e
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
      | ImmRel _
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
  split_and_process f (x_add_1 can_be_simplify) mk_array_free_formula
;;


let mk_array_free_formula_split
    (f:formula):formula=
  let pr = !print_pure in
  Debug.no_1 "mk_array_free_formula_split" pr pr (fun f-> mk_array_free_formula_split f) f
;;

(* The result will be index1=index2 -> arr_index1=arr_index2 *)
let mk_aux_formula
    (index1:exp) (index2:exp) (arr:spec_var):formula=
  let ante = BForm ((Eq (index1, index2, no_pos),None),None) in
  let conseq = BForm ((Eq (mk_array_new_name arr index1, mk_array_new_name arr index2, no_pos),None),None) in
  mk_imply ante conseq
;;

let mk_aux_formula_from_one_to_many
      (new_index:exp) (old_index_lst:exp list) (arr:spec_var):formula option =
  let rec helper n olst =
    match olst with
      | h::rest ->
            (mk_aux_formula new_index h arr)::(helper new_index rest)
      | [] ->
            []
  in
  let af = helper new_index old_index_lst in
  match af with
    | [] -> None
    | _ -> Some (mk_and_list af)
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
      (* failwith ("Trans_arr.extract_translate_scheme: "^(ArithNormalizer.string_of_exp e)^" To Be Implemented") *)
      failwith ("Trans_arr.get_array_element_in_exp: "^(string_of_exp e)^" To Be Implemented")
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
    | RelForm (nsv,elst,loc) ->
      (* let () = x_binfo_pp ("get_array_element_in_b_formula: RelForm") no_pos in *)
      List.fold_left (fun r e -> (get_array_element_in_exp e sv)@r) [] elst
    | BConst _
    | XPure _
    | BVar _
    | LexVar _
    | ImmRel _
    | Frm _->
      []
    | EqMax _
    | EqMin _
    | BagIn _
    | BagNotIn _
    | BagMin _
    | BagMax _ ->
      (* | VarPerm _ -> *)
      failwith ("get_array_element_in_exp: "^(!print_p_formula p)^" To Be Implemented")
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

let get_array_element_in_f
    (f:formula) (sv:spec_var):(exp list) =
  Debug.no_2 "get_array_element_in_f" !print_pure string_of_spec_var (pr_list string_of_exp) (fun f sv -> get_array_element_in_f f sv) f sv
;;

let collect_free_array_index f:exp list =
  let rec helper_e e notfv =
    match e with
    | ArrayAt (arr,[index],loc) ->
      begin
        match index with
        | IConst _ ->
          [index]
        | Var (sv,_) ->
          if List.exists (fun s -> is_same_sv s sv) notfv
          then []
          else [index]
        | _ ->
          failwith "extend_env: Invalid input"
      end
    | ArrayAt _ ->
      failwith "extend_env_e: Invalid array format"
    | Add (e1,e2,loc)
    | Subtract (e1,e2,loc)
    | Mult (e1,e2,loc)
    | Div (e1,e2,loc)->
      (helper_e e1 notfv)@(helper_e e2 notfv)
    | Var _
    | IConst _ ->
      []
    | _ -> []
  in
  let helper_b (p,ba) notfv =
    match p with
    | BConst _
    | BVar _
    | Frm _
    | XPure _
    | LexVar _
    | RelForm _ ->
      []
    | Lt (e1,e2,loc)
    | Lte (e1,e2,loc)
    | Gt (e1,e2,loc)
    | Gte (e1,e2,loc)
    | Eq (e1,e2,loc)
    | Neq (e1,e2,loc) ->
      (helper_e e1 notfv)@(helper_e e2 notfv)
    | _ ->
      failwith "extend_env_b: To Be Implemented"
  in
  let rec helper f notfv =
  match f with
  | BForm (b,fl)->
    helper_b b notfv
  | And (f1,f2,_)
  | Or (f1,f2,_,_) ->
    (helper f1 notfv)@(helper f2 notfv)
  | AndList lst->
    failwith "extend_env: AndList To Be Implemented"
  | Not (sub_f,fl,loc)->
    helper sub_f notfv
  | Forall (sv,sub_f,fl,loc)
  | Exists (sv,sub_f,fl,loc)->
    helper sub_f (sv::notfv)
  in
  remove_dupl is_same_exp (helper f [])
;;

let collect_free_array_index f =
  Debug.no_1 "collect_free_array_index" !print_pure (pr_list string_of_exp) collect_free_array_index f
;;


(* The input formula for this process must be normalized *)
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
          remove_dupl is_same_exp (get_array_element_in_f nf sv)
        | _ -> []
      end
    in
    if List.length nqlst == 0
    then
      (* let () = x_binfo_pp ("process_exists_array: Nothing changed: "^(!print_pure f)) no_pos in *)
      let new_nf = process_exists_array nf in
      Exists (sv,new_nf,fl,l)
    else
      let mk_new_name_helper
          (e:exp) : spec_var =
        match e with
        | ArrayAt (arr,[e],_)->
          mk_array_new_name_sv arr e
        | _ -> failwith "mk_new_name_helper: Invalid input"
      in
      (* let () = x_binfo_pp ("f:"^(!print_pure f)) no_pos in *)
      (* let () = x_binfo_pp ("nqlst: "^((pr_list string_of_exp) nqlst)) no_pos in *)
      let new_nf = Exists (sv,process_exists_array nf,fl,l) in
      List.fold_left (fun r nq -> Exists(mk_new_name_helper nq,r,None,no_pos)) new_nf nqlst
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
    | ImmRel _
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
  if (* Globals.infer_const_obj # is_arr_as_var *)
    !Globals.array_translate
  then drop_array_formula f
  else f

let drop_array_formula
    (f:formula):formula=
  let pr = !print_pure in
  Debug.no_1 "drop_array_formula" pr pr (fun fo->drop_array_formula fo) f
;;
(* --------------------------------------------------------- *)


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
      let string_of_indexlst = List.fold_left (fun s e -> s^" "^(string_of_exp e)^" ") "" indexlst in
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

let rec contain_array_element f arr_sv index_sv:bool =
  let rec helper_e e arr_sv index:bool =
    match e with
      | ArrayAt (arr,[index],loc) ->
            if is_same_sv arr arr_sv
            then
              begin
                match index with
                  | IConst _ ->
                        false
                  | Var (sv,_) ->
                        if is_same_sv sv index_sv
                        then true
                        else false
                  | _ ->
                        failwith "contain_array_element: Invalid index"
              end
            else
              false
      | ArrayAt _ ->
            failwith "contain_array_element: Invalid array format"
      | Add (e1,e2,loc)
      | Subtract (e1,e2,loc)
      | Mult (e1,e2,loc)
      | Div (e1,e2,loc)->
            (helper_e e1 arr_sv index)||(helper_e e2 arr_sv index)
      | Var _
      | IConst _ ->
            false
      | _ -> failwith "is_valid_forall_helper_exp: To Be Implemented"
  in
  let helper_b ((p,ba):b_formula) arr_sv index =
    match p with
      | BConst _
      | BVar _
      | Frm _
      | XPure _
      | LexVar _
      | RelForm _ ->
            false
      | Lt (e1,e2,loc)
      | Lte (e1,e2,loc)
      | Gt (e1,e2,loc)
      | Gte (e1,e2,loc)
      | Eq (e1,e2,loc)
      | Neq (e1,e2,loc) ->
            (helper_e e1 arr_sv index)||(helper_e e2 arr_sv index)
      | _ ->
            failwith "extend_env_b: To Be Implemented"
  in
  match f with
    | BForm (b,fl)->
          helper_b b arr_sv index_sv
    | And (f1,f2,_)
    | Or (f1,f2,_,_) ->
          (contain_array_element f1 arr_sv index_sv)||(contain_array_element f2 arr_sv index_sv)
    | AndList lst->
          failwith "extend_env: AndList To Be Implemented"
    | Not (sub_f,fl,loc)->
          contain_array_element sub_f arr_sv index_sv
    | Forall (sv,sub_f,fl,loc)
    | Exists (sv,sub_f,fl,loc)->
          contain_array_element sub_f arr_sv index_sv
;;

(* For a formula and an index sv, produce the auxiliary formula that contains the information between the index sv to the other indexes *)
let produce_aux_formula_from_env f index_sv env =
  let new_index = Var (index_sv,no_pos) in
  let rec helper env =
    match env with
      | (arr_sv,indexlst)::rest ->
            if contain_array_element f arr_sv index_sv
            then
              begin
                let aux_1 = mk_aux_formula_from_one_to_many new_index indexlst arr_sv in
                match aux_1 with
                  | Some a ->
                        a::(helper rest)
                  | None -> helper rest
              end
            else
              helper rest
      | [] ->
            []
  in
  let aflst = helper env in
  match aflst with
    | [] -> None
    | _ -> Some (mk_and_list aflst)
;;



(* Assuming that the quantified variable can only be index or the array itself *)
type not_free_var = (spec_var list)
;;

let string_of_sv_lst = pr_list string_of_spec_var;;

let add_v  nfv sv:not_free_var =
  (sv::nfv)
;;



let not_free nfv sv =
  List.exists (fun ele -> is_same_sv ele sv) nfv
;;

(* (arr -> {sv list}) list *)
type arr2index_env = ((spec_var * (exp list)) list)
;;

let string_of_env env:string =
  let string_of_item
        ((arr,indexlst):(spec_var * (exp list))):string=
    let string_of_indexlst = List.fold_left (fun s e -> s^" "^(string_of_exp e)^" ") "" indexlst in
    "array: "^(string_of_spec_var arr)^" { "^(string_of_indexlst)^"}"
  in
  (pr_list string_of_item) env
;;

let produce_aux_formula_from_env f index_sv env =
  let pro = function
    | Some f -> !print_pure f
    | None -> "None"
  in
  Debug.no_3 "produce_aux_formula_from_env" !print_pure string_of_spec_var string_of_env pro produce_aux_formula_from_env f index_sv env
;;

let add_env (env:arr2index_env) (arr:spec_var) (index:exp) =
  let rec helper
        env arr index =
    match env with
      | (array,elst)::rest ->
            if is_same_sv array arr
            then
              if List.exists (fun ele -> is_same_exp ele index) elst
              then env
              else
                (array,index::elst)::rest
            else
              (array,elst)::(helper rest arr index)
      | [] ->
            [(arr,[index])]
  in
  match index with
    | IConst _
    | Var _ ->
            helper env arr index
    | _ -> failwith "add_env: Invalid format of array index"
;;

(* Collect all the free array element in f *)
let rec extend_env old_env (nfv:not_free_var) f:arr2index_env =
  let rec extend_env_e old_env nfv e =
    match e with
      | ArrayAt (arr,[index],loc) ->
            begin
              match index with
                | IConst _ ->
                      if (not_free nfv arr)
                      then
                        old_env
                      else
                        add_env old_env arr index
                | Var (sv,_) ->
                      if (not_free nfv arr) || (not_free nfv sv)
                      then
                        old_env
                      else
                        add_env old_env arr index
                | _ ->
                      failwith "extend_env: Invalid input"
            end
      | ArrayAt _ ->
            failwith "extend_env_e: Invalid array format"
      | Add (e1,e2,loc)
      | Subtract (e1,e2,loc)
      | Mult (e1,e2,loc)
      | Div (e1,e2,loc)->
            let new_env1 = extend_env_e old_env nfv e1 in
            let new_env2 = extend_env_e new_env1 nfv e2 in
            new_env2
      | Var _
      | IConst _ ->
            old_env
      | _ -> old_env
  in
  let extend_env_b old_env nfv ((p,ba):b_formula) =
    match p with
      | BConst _
      | BVar _
      | Frm _
      | XPure _
      | LexVar _
      | RelForm _ ->
            old_env
      | Lt (e1,e2,loc)
      | Lte (e1,e2,loc)
      | Gt (e1,e2,loc)
      | Gte (e1,e2,loc)
      | Eq (e1,e2,loc)
      | Neq (e1,e2,loc) ->
            let new_env1 = extend_env_e old_env nfv e1 in
            let new_env2 = extend_env_e new_env1 nfv e2 in
            new_env2
      | _ ->
            failwith "extend_env_b: To Be Implemented"
  in
  match f with
    | BForm (b,fl)->
          extend_env_b old_env nfv b
    | And (f1,f2,_)
    | Or (f1,f2,_,_) ->
          let new_env1 = extend_env old_env nfv f1 in
          let new_env2 = extend_env new_env1 nfv f2 in
          new_env2
    | AndList lst->
          failwith "extend_env: AndList To Be Implemented"
    | Not (sub_f,fl,loc)->
          extend_env old_env nfv sub_f
    | Forall (sv,sub_f,fl,loc)
    | Exists (sv,sub_f,fl,loc)->
          let new_env = extend_env old_env (add_v nfv sv) sub_f in
          new_env
;;

let extend_env old_env nfv f =
  Debug.no_3 "extend_env" string_of_env (pr_list string_of_spec_var) !print_pure string_of_env extend_env old_env nfv f
;;

let rec expand_array_variable
    (f:formula) (svlst:spec_var list) :(spec_var list) =
  let expand sv replace=
    match sv with
    | SpecVar (Array _,_,_) ->
      (List.map (
        fun i ->
          match mk_array_new_name sv i with
          | Var (nsv,_) ->
            nsv
          | _ -> sv
        ) replace)@[sv]
    | _ ->
      [sv]
  in
  let rec helper svlst replace=
    match svlst with
    | h::rest -> (expand h replace)@(helper rest replace)
    | [] -> []
  in
  let replace = collect_free_array_index f in
  (* let () = x_binfo_pp ("expand_array_variable: replace "^((pr_list string_of_exp) replace)) no_pos in *)
  remove_dupl_spec_var_list (helper svlst replace)
;;

let expand_array_variable f svlst =
  Debug.no_2 "expand_array_variable" !print_pure (pr_list string_of_spec_var) (pr_list string_of_spec_var) expand_array_variable f svlst
;;

let expand_array_variable
      (f:formula) (svlst:spec_var list): (spec_var list) =
  if !Globals.array_translate
  then expand_array_variable f svlst
  else svlst
;;


let expand_relation f =
  let string_of_replace replace =
      (pr_list string_of_exp) replace
   in
   let find_replace index_exp replace:exp list =
     (* given the name of an array, return the list of the array elements as replacement *)
     match index_exp with
      | Var (sv,_)->
        begin
          match sv with
          | SpecVar (Array _,id,_) ->
            List.map (fun i -> (ArrayAt (sv,[i],no_pos))) replace
          | _ ->
            []
        end
      | _ -> []
   in
   let find_replace index_exp replace =
     Debug.no_2 "find_replace" string_of_exp string_of_replace (pr_list string_of_exp)  find_replace index_exp replace
   in
   let replace_helper explst replace =
     let () = x_tinfo_pp ("replace: "^(string_of_replace replace)) no_pos in
     List.fold_left (fun nlst exp ->nlst@((find_replace exp replace)@[exp])) [] explst
   in
   let rec helper f replace =
     let helper_b ((p,ba):b_formula) replace =
       match p with
       | RelForm (SpecVar (_,id,_) as rel_name,explst,loc) ->
         if id = "update_array_1d"
         then
           (p,ba)
         else
           let new_explst = replace_helper explst replace in
           (RelForm (rel_name,new_explst,loc),ba)
       | _ ->
        (p,ba)
     in
     match f with
     | BForm (b,fl)->
       BForm (helper_b b replace,fl)
     | And (f1,f2,loc)->
       And (helper f1 replace,helper f2 replace,loc)
     | AndList lst->
       AndList (List.map (fun (t,f)-> (t,drop_array_formula f)) lst)
     | Or (f1,f2,fl,loc)->
       Or (helper f1 replace,helper f2 replace,fl,loc)
     | Not (f,fl,loc)->
       Not (helper f replace,fl,loc)
     | Forall (sv,nf,fl,loc)->
       Forall (sv,helper nf replace,fl,loc)
     | Exists (sv,nf,fl,loc)->
       Exists (sv,helper nf replace,fl,loc)
   in
   (* let replace = *)
   (*   let env = extend_env [] [] f in *)
   (*   let transform (arr,indexlst) = *)
   (*     (arr,List.map (fun index -> ArrayAt (arr,[index],no_pos)) indexlst) *)
   (*    in *)
   (*    (List.map transform env) *)
   (* in *)
   (* This one does not work because it only takes variables from free ones *)
   (* let replace = *)
   (*   let env = extend_env [] [] f in *)
   (*   let collect = List.fold_left (fun r (arr,ilst) -> ilst@r) [] env in *)
   (*   remove_dupl is_same_exp collect *)
   (* in *)
   (* let () = x_binfo_pp ("expand_relation: replace "^((pr_list string_of_exp) replace)) no_pos in*)
   let replace = collect_free_array_index f in
   helper f replace
;;

let expand_relation f =
  Debug.no_1 "expand_relation" !print_pure !print_pure expand_relation f
;;

let expand_relation f =
  if !Globals.array_translate
  then expand_relation f
  else f
;;

let expand_array rel_def rel_f prevlst postvlst =
  let construct_replace def_arglst raw_replace =
    let find_pos def_arglst one =
      let rec find_pos_helper def_arglst one pos =
        match def_arglst with
        | h::rest ->
          if is_same_exp h one
          then pos
          else find_pos_helper rest one (pos+1)
        | [] -> failwith "find_pos: Not found"
      in
      find_pos_helper def_arglst one 0
    in
    let rec helper raw_replace =
      match raw_replace with
      | (IConst c)::rest -> (Some (IConst c),None)::(helper rest)
      | (Var v)::rest -> (None,Some (find_pos def_arglst (Var v)))::(helper rest)
      | [] -> []
      | _ -> failwith "construct_replace: Invalid input"
    in
    helper raw_replace
  in
  let match_replace arglst replace =
    let match_helper one =
      match one with
      | (Some (IConst c),None) -> IConst c
      | (None, Some pos) -> List.nth arglst pos
      | _ -> failwith "match_helper: Invalid input"
    in
    let rec helper replace =
      match replace with
      | h::rest -> (match_helper h)::(helper rest)
      | [] -> []
    in
    helper replace
  in
  let expand_array_vlst vlst raw_replace =
    let find_replace index_exp replace:exp list =
      (* given the name of an array, return the list of the array elements as replacement *)
      match index_exp with
      | Var (sv,_)->
        begin
          match sv with
          | SpecVar (Array _,id,_) ->
            List.map (fun i -> (ArrayAt (sv,[i],no_pos))) replace
          | _ ->
            []
        end
      | _ -> []
    in
    let replace_helper explst replace =
      (* let () = x_tinfo_pp ("replace: "^(string_of_replace replace)) no_pos in *)
      List.fold_left (fun nlst exp ->nlst@((find_replace exp replace)@[exp])) [] explst
    in
    replace_helper vlst raw_replace
  in
  let expand_relation f replace =
    let rec helper f replace =
      let helper_b ((p,ba):b_formula) replace =
        match p with
        | RelForm (SpecVar (_,id,_) as rel_name,explst,loc) ->
          if id = "update_array_1d"
          then
           (p,ba)
          else
            let new_raw_replace = match_replace explst replace in
            let new_explst = expand_array_vlst explst new_raw_replace in
            (RelForm (rel_name,new_explst,loc),ba)
        | _ ->
          (p,ba)
      in
      match f with
      | BForm (b,fl)->
        BForm (helper_b b replace,fl)
      | And (f1,f2,loc)->
        And (helper f1 replace,helper f2 replace,loc)
      | AndList lst->
        AndList (List.map (fun (t,f)-> (t,drop_array_formula f)) lst)
      | Or (f1,f2,fl,loc)->
        Or (helper f1 replace,helper f2 replace,fl,loc)
      | Not (f,fl,loc)->
        Not (helper f replace,fl,loc)
      | Forall (sv,nf,fl,loc)->
        Forall (sv,helper nf replace,fl,loc)
      | Exists (sv,nf,fl,loc)->
        Exists (sv,helper nf replace,fl,loc)
    in
    helper f replace
  in
  let strip_exp_to_sv e =
    match e with
    | ArrayAt (arr,[index],loc) ->
      mk_array_new_name_sv arr index
    | Var (sv,_) ->
      sv
    | _ -> failwith "strip_exp_to_sv: Invalid input"
  in
  let raw_replace = collect_free_array_index rel_f in
  match rel_def with
  | BForm (((RelForm (_,def_arglst,_)),_),_)->
    let replace = construct_replace def_arglst raw_replace in
    let (new_pre_vlst,new_post_vlst) =
      let new_raw_replace = match_replace def_arglst replace in
      (List.map strip_exp_to_sv (expand_array_vlst prevlst new_raw_replace),List.map strip_exp_to_sv (expand_array_vlst postvlst new_raw_replace))
    in
    let new_f =
      expand_relation rel_f replace
    in
    (new_pre_vlst,new_post_vlst,new_f)
  | _ ->
    failwith "expand_array: Invalid expression, expecting RelForm"
;;
let expand_array rel_def rel_f prevlst postvlst =
  let pr (prelst,postlst,newf)=
    "(prelst: "^((pr_list string_of_spec_var) prelst)^",postlst"^((pr_list string_of_spec_var) postlst)^",newf:"^(!print_pure newf)
  in
  Debug.no_4 "expand_array" !print_pure !print_pure (pr_list string_of_exp) (pr_list string_of_exp) pr expand_array rel_def rel_f prevlst postvlst
;;

let expand_array_sv_wrapper rel_def rel_f pre_svlst post_svlst =
  let pre_vlst = List.map (fun sv -> Var (sv,no_pos)) pre_svlst in
  let post_vlst = List.map (fun sv -> Var (sv,no_pos)) post_svlst in
  expand_array rel_def rel_f pre_vlst post_vlst
;;


(* let expand_for_fixcalc f pre_vars post_vars = *)
(*   let replace =  *)


(* The returned formula must be forall-free *)
let instantiate_forall
      (f:formula):formula =
  let instantiate_with_one_sv
        (f:formula) sv env:formula =
    (* env : exp list *)
    let rec replace_helper_e (e:exp) (sv:spec_var) (index:exp) =
      (* replace sv with index in the expression exp *)
      match e with
        | ArrayAt (arr,[nindex],loc) ->
              ArrayAt (arr,[replace_helper_e nindex sv index],loc)
        | ArrayAt _ ->
              failwith "extend_env_e: Invalid array format"
        | Add (e1,e2,loc)->
              Add (replace_helper_e e1 sv index, replace_helper_e e2 sv index,loc)
        | Subtract (e1,e2,loc)->
              Subtract (replace_helper_e e1 sv index, replace_helper_e e2 sv index,loc)
        | Mult (e1,e2,loc)->
              Mult (replace_helper_e e1 sv index, replace_helper_e e2 sv index,loc)
        | Div (e1,e2,loc)->
              Div (replace_helper_e e1 sv index, replace_helper_e e2 sv index,loc)
        | Var (nsv,_) ->
              if is_same_sv nsv sv
              then index
              else
                e
        | IConst _
        | Null _ ->
          e
        | _ -> failwith "instantiate_forall: To Be Implemented"
    in
    let replace_helper_b ((p,ba):b_formula) (sv:spec_var) (index:exp)=
      match p with
        | BConst _
        | BVar _
        | Frm _
        | XPure _
        | LexVar _
        | RelForm _ ->
              (p,ba)
        | Lt (e1,e2,loc)->
              (Lt (replace_helper_e e1 sv index,replace_helper_e e2 sv index,loc),ba)
        | Lte (e1,e2,loc)->
              (Lte (replace_helper_e e1 sv index,replace_helper_e e2 sv index,loc),ba)
        | Gt (e1,e2,loc)->
              (Gt (replace_helper_e e1 sv index,replace_helper_e e2 sv index,loc),ba)
        | Gte (e1,e2,loc)->
              (Gte (replace_helper_e e1 sv index,replace_helper_e e2 sv index,loc),ba)
        | Eq (e1,e2,loc)->
              (Eq (replace_helper_e e1 sv index,replace_helper_e e2 sv index,loc),ba)
        | Neq (e1,e2,loc) ->
              (Neq (replace_helper_e e1 sv index,replace_helper_e e2 sv index,loc),ba)
        | _ ->
              failwith "replace_helper: To Be Implemented"
    in
    (* replace sv in the formula f with index *)
    let rec instantiate_with_one_sv_helper
          (f:formula) (sv:spec_var) (index:exp) :formula =
      match f with
        | BForm (b,fl)->
              BForm (replace_helper_b b sv index,fl)
        | And (f1,f2,loc)->
              And (instantiate_with_one_sv_helper f1 sv index,instantiate_with_one_sv_helper f2 sv index,loc)
        | AndList lst->
              failwith "instantiate_forall: AndList To Be Implemented"
        | Or (f1,f2,fl,loc)->
              Or (instantiate_with_one_sv_helper f1 sv index,instantiate_with_one_sv_helper f2 sv index,fl,loc)
        | Not (f,fl,loc)->
              Not (instantiate_with_one_sv_helper f sv index,fl,loc)
        | Forall (n_sv,sub_f,fl,loc)->
              Forall (n_sv,instantiate_with_one_sv_helper sub_f sv index,fl,loc)
        | Exists (n_sv,sub_f,fl,loc)->
              Exists(n_sv,instantiate_with_one_sv_helper sub_f sv index,fl,loc)
    in
    let contains_arr f arr=
      (* To Be Implemented *)
      true
    in
    mk_and_list (List.map (fun r -> instantiate_with_one_sv_helper f sv r) env)
  in
  let instantiate_with_one_sv f sv env =
    Debug.no_3 "instantiate_with_one_sv" !print_pure string_of_spec_var (pr_list string_of_exp)  !print_pure instantiate_with_one_sv f sv env
  in
  let rec instantiate_forall_helper
      (f:formula) env :formula =
    match f with
    | BForm (b,fl)->
      f
    | And (f1,f2,loc)->
      And (instantiate_forall_helper f1 env,instantiate_forall_helper f2 env,loc)
    | AndList lst->
      failwith "instantiate_forall: AndList To Be Implemented"
    | Or (f1,f2,fl,loc)->
      Or (instantiate_forall_helper f1 env,instantiate_forall_helper f2 env,fl,loc)
    | Not (f,fl,loc)->
      Not (instantiate_forall_helper f env,fl,loc)
    | Forall (sv,sub_f,fl,loc)->
      let new_env = remove_dupl is_same_exp ((collect_free_array_index sub_f)@env) in
      let new_sub_f = instantiate_forall_helper sub_f new_env in
      (try
         let instantiated_sub_f = instantiate_with_one_sv new_sub_f sv env in
         instantiated_sub_f
       with _ ->
         f
      )
    | Exists (sv,sub_f,fl,loc) ->
      let new_env = remove_dupl is_same_exp ((collect_free_array_index sub_f)@env) in
      let new_sub_f = instantiate_forall_helper sub_f new_env in
      Exists (sv,new_sub_f,fl,loc)
  in
  let instantiate_forall_helper f env =
    Debug.no_2 "instantiate_forall_helper" !print_pure  (pr_list string_of_exp)  !print_pure instantiate_forall_helper f env
  in
  let env = collect_free_array_index f in
  instantiate_forall_helper f env

;;

let instantiate_forall f=
  let pr = !print_pure in
  Debug.no_1 "instantiate_forall" pr pr instantiate_forall f
;;

let rec instantiate_exists f =
  match f with
    | BForm (b,fl)->
          f
    | And (f1,f2,loc)->
          And (instantiate_exists f1,instantiate_exists f2,loc)
    | AndList lst->
          failwith "instantiate_forall: AndList To Be Implemented"
    | Or (f1,f2,fl,loc)->
          Or (instantiate_exists f1,instantiate_exists f2,fl,loc)
    | Not (f,fl,loc)->
          Not (instantiate_exists f,fl,loc)
    | Forall (sv,sub_f,fl,loc)->
          Forall (sv,instantiate_exists sub_f,fl,loc)
    | Exists (sv,sub_f,fl,loc)->
          begin
            match sv with
              | SpecVar (Array _,_,_) ->
                    Exists (sv,instantiate_exists sub_f,fl,loc)
              | _ -> instantiate_exists sub_f
          end
;;

let instantiate_exists f=
  Debug.no_1 "instantiate_exists" !print_pure !print_pure instantiate_exists f
;;

let rec produce_aux_formula_for_exists
      (f:formula) env:formula =
  match f with
    | Exists (nsv,sub_f,fl,l) ->
          let af = produce_aux_formula_from_env sub_f nsv env in
          let new_env = extend_env env [] sub_f in
          let new_sub_f = produce_aux_formula_for_exists sub_f new_env in
          begin
            match af with
              | Some new_f ->
                    let new_sub_f = And (new_f,new_sub_f,no_pos) in
                      Exists (nsv,new_sub_f,fl,l)
              | None ->
                    Exists (nsv,new_sub_f,fl,l)
          end
    | And (f1,f2,loc) ->
          And (produce_aux_formula_for_exists f1 env,produce_aux_formula_for_exists f2 env,loc)
    | Or (f1,f2,fl,loc) ->
          Or (produce_aux_formula_for_exists f1 env,produce_aux_formula_for_exists f2 env,fl,loc)
    | AndList lst->
          failwith "produce_aux_formula_for_exists: AndList To Be Implemented"
    | Not (sub_f,fl,loc)->
          Not (produce_aux_formula_for_exists sub_f env,fl,loc)
    | Forall (sv,sub_f,fl,loc)->
          let new_env = extend_env env [] sub_f in
          let new_sub_f = produce_aux_formula_for_exists sub_f new_env in
          Forall (sv,new_sub_f,fl,loc)
    | BForm (b,fl) ->
          f
;;

let produce_aux_formula_for_exists f env =
  Debug.no_2 "produce_aux_formula_for_exists" !print_pure string_of_env !print_pure produce_aux_formula_for_exists f env
;;

let translate_array_one_formula
      (f:formula):formula =

  (* standarize index format *)
  let f = standarize_one_formula f in
  (* translate a=a' *)
  let f = translate_array_equality_to_forall f in
  (* translate update_array_1d *)
  let f = translate_array_relation f in
  (* Constantiate existential quantifier *)
  let f = constantize_ex_q f in

  let global_env = extend_env [] [] f in
  let f = instantiate_forall f in
  let f = process_exists_array f in

  let f = produce_aux_formula_for_exists f global_env in
  let array_free_formula = mk_array_free_formula f in
  let aux_formula = produce_aux_formula global_env in
  let new_f =
    match aux_formula with
      | None -> array_free_formula
      | Some af -> And (array_free_formula,af,no_pos)
  in
  new_f
;;

let translate_array_one_formula f =
  Debug.no_1 "#1translate_array_one_formula" !print_pure !print_pure translate_array_one_formula f
;;

let translate_array_one_formula f=
  if !Globals.array_translate
  then translate_array_one_formula f
  else f
;;

let translate_array_one_formula_for_validity
      (f:formula):formula =
  let f = translate_array_equality_to_forall f in
  let f = standarize_one_formula f in
  let f = translate_array_equality_to_forall f in
  let f = translate_array_relation f in
  let f = constantize_ex_q f in


  let global_env = extend_env [] [] f in
  let f = instantiate_forall f in
  let f = process_exists_array f in

  let f = produce_aux_formula_for_exists f global_env in
  let array_free_formula = mk_array_free_formula f in
  let aux_formula = produce_aux_formula global_env in
  let new_f =
    match aux_formula with
      | None -> array_free_formula
      | Some af -> Or (array_free_formula,Not (af,None,no_pos),None,no_pos)
  in
  new_f
;;

let translate_array_one_formula_for_validity f =
  Debug.no_1 "#1translate_array_one_formula_for_validity" !print_pure !print_pure translate_array_one_formula_for_validity f
;;

let translate_array_one_formula_for_validity f=
  if !Globals.array_translate
  then translate_array_one_formula_for_validity f
  else f
;;

let translate_array_imply ante conseq =
  (translate_array_one_formula ante, translate_array_one_formula conseq)
;;

let translate_preprocess_helper
     (translate_relation:bool) (f:formula):formula =
  let f =
    if translate_relation then
      translate_array_relation f
    else
      f
  in
  let f = standarize_one_formula f in
  let f = process_quantifier f in
  let f = process_exists_array f in
  f
;;

let translate_preprocess = translate_preprocess_helper true;;

let translate_preprocess f =
  Debug.no_1 "translate_preprocess" !print_pure !print_pure translate_preprocess f
;;

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

let simplify_array_equality f=
  let is_equal_arr_full eqlst arr1 arr2 =
    List.exists (fun (p1,p2) -> (is_same_sv p1 arr1 && is_same_sv p2 arr2)||(is_same_sv p1 arr2 && is_same_sv p2 arr1)) eqlst
  in
  let rec get_eqlst f =
    let get_eqlst_b (p,ba)=
      match p with
      | Eq (Var (SpecVar (Array _,_,_) as sv1,_), Var (SpecVar (Array _,_,_) as sv2,_),_) ->
        [(sv1,sv2)]
      | _ -> []
    in
    match f with
    | BForm (b,fl)->
      get_eqlst_b b
    | And (f1,f2,_)
    | Or (f1,f2,_,_)->
      (get_eqlst f1)@(get_eqlst f2)
    | AndList lst->
      failwith "get_eqlst: AndList To Be Implemented"
    | Not (sub_f,_,_)
    | Forall (_,sub_f,_,_)
    | Exists (_,sub_f,_,_)->
      get_eqlst sub_f
  in
  let is_equal_arr =
    is_equal_arr_full (get_eqlst f)
  in
  let helper_b (p,ba) =
    match p with
    | Eq (ArrayAt (arr1,[index1],_), ArrayAt (arr2,[index2],_) ,_)->
      if is_equal_arr arr1 arr2 && is_same_exp index1 index2
      then None
      else Some (p,ba)
    | _ -> Some (p,ba)
  in
  let rec simplify_helper f:formula option =
    match f with
    | BForm (b,fl)->
      begin
        match helper_b b with
        | Some new_b -> Some (BForm (new_b,fl))
        | None -> None
      end
    | And (f1,f2,loc)->
      begin
        match simplify_helper f1, simplify_helper f2 with
        | None,None -> None
        | Some new_f1,Some new_f2 -> Some (And (new_f1,new_f2,loc))
        | None, Some new_f2 -> Some new_f2
        | Some new_f1,None -> Some new_f1
      end
    | AndList lst->
      failwith "simplify_array_equality: AndList To Be Implemented"
    | Or (f1,f2,fl,loc)->
      begin
        match simplify_helper f1, simplify_helper f2 with
        | None,None -> None
        | Some new_f1,Some new_f2 -> Some (Or (new_f1,new_f2,fl,loc))
        | None, Some new_f2 -> Some new_f2
        | Some new_f1,None -> Some new_f1
      end
    | Not (nf,fl,loc)->
      begin
        match simplify_helper nf with
        | Some new_nf -> Some (Not (new_nf,fl,loc))
        | None -> None
      end
    | Forall (sv,nf,fl,loc)->
      begin
        match simplify_helper nf with
        | Some new_nf -> Some (Forall (sv,new_nf,fl,loc))
        | None -> None
      end
    | Exists (sv,nf,fl,loc)->
      begin
        match simplify_helper nf with
        | Some new_nf -> Some (Exists (sv,new_nf,fl,loc))
        | None -> None
      end
  in
  (* equal relation is a list of pairs *)
  match simplify_helper f with
  | Some new_f -> new_f
  | None -> mkTrue no_pos
;;

let simplify_array_equality f =
  Debug.no_1 "simplify_array_equality" !print_pure !print_pure simplify_array_equality f
;;

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
          let arr_var_regexp = Str.regexp ".*__.*" in
          if (Str.string_match arr_var_regexp i 0)
          then
            (*let i = String.sub i 8 ((String.length i) - 9) in*)
            let splitter = Str.regexp "__" in
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
                let prefix_regexp = Str.regexp "PRI.*" in
                if Str.string_match prefix_regexp index 0
                then
                  let sv = SpecVar (Int,(List.nth (Str.split (Str.regexp "PRI") index) 0),Primed) in
                  Var (sv,no_pos)
                  else
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
      | ImmRel _
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

let translate_back_array_in_one_formula f =
  let res = translate_back_array_in_one_formula f in
  let res = simplify_array_equality res in
  res
;;

let translate_back_array_in_one_formula
    (f:formula):formula =
  let pf = !print_pure in
  Debug.no_1 "translate_back_array_in_one_formula" pf pf (fun f -> translate_back_array_in_one_formula f) f
;;

let translate_back_array_in_one_formula
    (f:formula):formula =
  if (!Globals.array_translate)  (* (Globals.infer_const_obj # is_arr_as_var) *)
  then translate_back_array_in_one_formula f
  else f
;;
(* END of translating back the array to a formula *)

let string_of_unchanged_info (f,t,clst) =
  "("^(string_of_exp f)^","^(string_of_exp t)^","^((pr_list string_of_exp) clst)
;;

let clean_list lst af at =
  let equal_unchanged (f1,t1,clst1) (f2,t2,clst2) =
          (is_same_exp f1 f2)&&(is_same_exp t1 t2)
  in
  let drop lst =
    List.fold_left (fun r (f,t,clst) -> if is_same_exp f t then r else (f,t,clst)::r) [] lst
  in
  let expand lst =
    let expand_one_helper (f,t,clst) =
      List.fold_left (fun r (nf,nt,nclst) -> if is_same_exp t nf then (f,nt,clst@nclst)::r else r) [(f,t,clst)] lst
    in
    let rec expand_helper lst =
      match lst with
      | h::rest -> (expand_one_helper h)@(expand_helper rest)
      | [] -> []
    in
    let new_lst = ref [] in
    let rec iterator lst =
      let result = remove_dupl equal_unchanged (expand_helper lst) in
      (* let () = x_binfo_pp ("expand_helper result: "^((pr_list string_of_unchanged_info) result)) no_pos in *)
      if not (List.length result=List.length !new_lst)
      then
        (
          new_lst := result;
          iterator result
        )
      else
        ()
    in
    (
      iterator lst;
      !new_lst
    )
  in
  let clean lst af at =
    try
      Some (List.hd (List.fold_left (fun r (f,t,clst) -> if is_same_exp f af && is_same_exp t at then (f,t,remove_dupl is_same_exp clst)::r else r) [] lst))
    with _ -> None
  in
  (* let () = x_binfo_pp ("clean_list"^((pr_list string_of_unchanged_info) lst)) no_pos in *)
  clean (expand (drop lst)) af at
;;

let clean_list lst af at =
  let po = function
    | Some u -> string_of_unchanged_info u
    | None ->"None"
  in
  Debug.no_3 "clean_list" (pr_list string_of_unchanged_info) (string_of_exp) (string_of_exp) po clean_list lst af at
;;

let same_unordered_list cmp lst1 lst2=
    let rec same_helper one blst =
      match blst with
      | h::rest ->
        if cmp h one
        then (true,rest)
        else same_helper one rest
      | [] ->
        (false,[])
    in
    let rec same_helper_2 alst blst =
      match alst with
      | h::rest ->
        let (found,newlst) = same_helper h blst in
        if found
        then true&&(same_helper_2 rest newlst)
        else false
      | [] ->
        List.length blst = 0
    in
    same_helper_2 lst1 lst2
;;

let unchanged_fixpoint (rel:formula) (define:formula list) =
  (* rel is the name of the relation, define is a list of disjunction formula that defines this relation *)
  let basic = ref (fun af at -> []) in
  let calculator relname (arg1:exp) (arg2:exp) (define:formula list) basic=
    (* Return a function, that takes in two arrays and returns the list of array relations between them *)
    (* arg1 and arg2 say that how the arguments look like in the definition *)
    let new_fun flst =
      let new_fun_x (af:exp) (at:exp)=
        let rec new_fun_helper (f:formula):((exp*exp*(exp list)) list) list =
          match f with
          | BForm (((RelForm (SpecVar (_,id,_),explist,loc)),pa),_) ->
            let uop1=
              if is_same_exp (List.nth explist 0)  arg1 then af else List.nth explist 0
            in
            let uop2=
              if is_same_exp (List.nth explist 1)  arg2 then at else List.nth explist 1
            in
            if id = "update_array_1d"
            then
              (* Only one disjunction *)
              [ [(uop1,uop2,[(List.nth explist 3)])] ]
            else
            if id = relname
            then
              let basic_result = basic uop1 uop2 in
              let () = x_tinfo_pp ("basic_result args: "^(string_of_exp uop1)^" "^(string_of_exp uop2)) no_pos in
              let () = x_tinfo_pp ("basic_result "^((pr_list string_of_unchanged_info) basic_result)) no_pos in
              [basic_result]
            else
              []
          | BForm (((Eq ((Var (SpecVar (Array _,_,_),_) as v2),(Var (SpecVar (Array _,_,_),_) as v1),loc)),pa),_) ->
            let uop1=
              if is_same_exp v1  arg1 then af else v1
            in
            let uop2=
              if is_same_exp v2 arg2 then at else v2
            in
            [ [(uop1,uop2,[])] ]
          | And (f1,f2,loc) ->
            let dres1 = new_fun_helper f1 in
            let dres2 = new_fun_helper f2 in
            List.fold_left (fun result rlst1 -> (List.map (fun rlst2 -> rlst1@rlst2) dres2)@result) (dres1@dres2) dres1
          | _ -> []
        in
        let equal_unchanged (f1,t1,clst1) (f2,t2,clst2) =
          (is_same_exp f1 f2)&&(is_same_exp t1 t2)
        in
        let list_of_list = List.flatten (List.map new_fun_helper flst) in
        (List.fold_left
           (fun result flst ->
              match clean_list flst af at with
              | Some u -> u::result
              | None -> result
           ) [] list_of_list)
      in
      new_fun_x
    in
    new_fun define
  in
  let (relname,arg1,arg2) =
    match rel with
    | BForm (((RelForm (SpecVar (_,id,_),explist,loc)),pa),_) ->
      (id,List.nth explist 0,List.nth explist 1)
    | _ -> failwith "unchanged_fixpoint: Invalid rel"
  in
  let same_index_set = same_unordered_list is_same_exp in
  let same_unchanged_info (f1,t1,iset1) (f2,t2,iset2)=
    (is_same_exp f1 f2)&&(is_same_exp t1 t2)&&(same_index_set iset1 iset2)
  in
  let same_result = same_unordered_list same_unchanged_info in
  let rec iterator () =
    let old_result = !basic arg1 arg2 in
    (* let () = x_binfo_pp ("old_result "^((pr_list string_of_unchanged_info) old_result)) no_pos in *)
    let new_rel = calculator relname arg1 arg2 define !basic in
    let new_result = new_rel arg1 arg2 in
    let () = x_tinfo_pp ("new_result "^((pr_list string_of_unchanged_info) new_result)) no_pos in
    if (same_result new_result old_result)
    then
      new_rel
    else
      let () = basic := new_rel in
      iterator ()
  in
  iterator ()
;;

let unify_unchanged_fixpoint ulist =
  match ulist with
  | [] ->
    ulist
  | h::rest ->
    let result =
      List.fold_left (fun (rf,rt,rc) (nf,nt,nc) ->
          if not (((is_same_exp rf nf)&&(is_same_exp rt nt))||((is_same_exp rf nt)&&(is_same_exp rt nf)))
          then
            failwith "unify_unchanged_fixpoint: Invalid input"
          else
            (rf,rt,rc@nc)
        ) h rest
    in
    [result]
;;


module H_Unchanged =
  struct
    type t = (Cpure.exp * Cpure.exp)
    let equal (f1,t1) (f2,t2) =
      let result = ((is_same_exp f1 f2)&&(is_same_exp t1 t2))||((is_same_exp f1 t2)&&(is_same_exp t1 f2)) in
      let () = x_tinfo_pp ("hash equal: f1 "^(string_of_exp f1)^" t1 "^(string_of_exp t1)^" f2 "^(string_of_exp f2)^" t2 "^(string_of_exp t2)^" "^(string_of_bool result)) no_pos in
      result
    let hash (f,t)= (String.length (string_of_exp f))+(String.length (string_of_exp t))
  end
;;

module Unchanged_Htbl = Hashtbl.Make(H_Unchanged);;
let string_of_unchanged_tbl tbl=
  Unchanged_Htbl.fold (fun (f,t) s r -> "("^(string_of_exp f)^","^(string_of_exp t)^","^(string_of_expset s)^")"^r) tbl ""
;;

let string_of_unchanged ((f,t),s) =
  "("^(string_of_exp f)^","^(string_of_exp t)^" "^(string_of_expset s)^")"
;;

let clean_tbl tbl arglst =
  let merge_tbl tbl =
    let merge_helper (f,t) item =
      let itemlst = Unchanged_Htbl.find_all tbl (f,t) in
      (* let () = x_binfo_pp ("itemlst length: "^(string_of_int (List.length itemlst))) no_pos in *)
      let new_item = List.fold_left (fun r i -> let () = Unchanged_Htbl.remove tbl (f,t) in ExpSet.union i r) ExpSet.empty itemlst in
      Unchanged_Htbl.replace tbl (f,t) new_item
    in
    Unchanged_Htbl.iter merge_helper tbl
  in
  let expand_tbl tbl =
    let changed = ref false in
    let expand_helper (f,t) eset =
      Unchanged_Htbl.iter (
        fun (nf,nt) neset ->
          let new_key =
            if (is_same_exp f nf && (not (is_same_exp nt t)))
            then
              Some (nt,t)
            else
            if (is_same_exp f nt && (not (is_same_exp nf t)))
            then
              Some (nf,t)
            else
            if (is_same_exp t nt && (not (is_same_exp f nf)))
            then Some (f,nf)
            else
            if (is_same_exp t nf && (not (is_same_exp f nt)))
            then Some (f,nt)
            else
              None
          in
          match new_key with
          | None -> ()
          | Some ((kf,kt) as key) ->
            let () = x_tinfo_pp ("expand_tbl: Find some key!") no_pos in
            let () = x_tinfo_pp ("key: "^(string_of_exp kf)^" "^(string_of_exp kt)) no_pos in
            let ()=  x_tinfo_pp ("tbl: "^(string_of_unchanged_tbl tbl)) no_pos in
            let new_eset = ExpSet.union eset neset in
            try
              let exists_set = Unchanged_Htbl.find tbl key in
              if ExpSet.equal new_eset exists_set
              then ()
              else
                let () = changed := true in
                Unchanged_Htbl.replace tbl key (ExpSet.union new_eset exists_set)
            with
            Not_found ->
              let () = x_tinfo_pp ("Not_found") no_pos in
              Unchanged_Htbl.add tbl key new_eset
      ) tbl
    in
    let rec iterator () =
      let () = Unchanged_Htbl.iter expand_helper tbl in
      if !changed
      then
        let () = changed:=false in
        iterator ()
      else
        ()
    in
    iterator ()
  in
  let clean_fv tbl arglst =
    Unchanged_Htbl.iter (
      fun (f,t) _ ->
        if not ((List.exists (fun x -> is_same_exp x f) arglst)&&(List.exists (fun x -> is_same_exp x t) arglst))
        then Unchanged_Htbl.remove tbl (f,t)
        else ()
    ) tbl
  in
  (
    merge_tbl tbl;
    expand_tbl tbl;
    clean_fv tbl arglst;
    merge_tbl tbl
  )
;;


let substitute_unchanged (arglst,infolst) explst =
  let subs = List.combine arglst explst in
  let subs_helper ((f,t),s) subs =
    let nf =
      try
        let (_,nf) = List.find (fun (a,s)->is_same_exp a f) subs in
        nf
      with
      | Not_found -> f
    in
    let nt =
      try
        let (_,nt) = List.find (fun (a,s)->is_same_exp a t) subs in
        nt
      with
      | Not_found -> t
    in
    let ns =
      ExpSet.fold
        (fun item r ->
          let nitem =
            try
              let (_,nitem) = List.find (fun (a,s) -> is_same_exp a item) subs in
              nitem
            with
            | Not_found ->
              item
          in
          ExpSet.add nitem r) s ExpSet.empty
    in
    ((nf,nt),ns)
  in
  List.map (fun x -> subs_helper x subs) infolst
;;

let substitute_unchanged (arglst,infolst) explst :((Cpure.exp * Cpure.exp) * ExpSet.t) list=
  let pr1 (arglst,infolst)=
    "["^((pr_list string_of_exp) arglst)^"]::["^((pr_list string_of_unchanged) infolst)^"]"
  in
  let basic = (arglst,infolst) in
  Debug.no_2 "substitute_unchanged" pr1 (pr_list string_of_exp) (pr_list string_of_unchanged) substitute_unchanged basic explst
;;

let new_unchanged_fixpoint relname arglst definelst basic=
  let rec helper define =
    match define with
    | BForm (((RelForm (SpecVar (_,id,_),explist,loc)),pa),_) ->
      if id = "update_array_1d"
      then
        (* Only one disjunction *)
        [ ((List.nth explist 0,List.nth explist 1),ExpSet.singleton (List.nth explist 3)) ]
      else
      if id = relname
      then
        substitute_unchanged basic explist
      else
        []
    | BForm (((Eq ((Var (SpecVar (Array _,_,_),_) as v2),(Var (SpecVar (Array _,_,_),_) as v1),loc)),pa),_) ->
      [ ((v1,v2),ExpSet.empty) ]
    | And (f1,f2,loc) ->
      (helper f1)@(helper f2)
    | _ -> []
  in
  let list = List.flatten (List.map helper definelst) in
  let tbl = Unchanged_Htbl.create 100000 in
  let () = List.iter (fun ((f,t),s) -> Unchanged_Htbl.add tbl (f,t) s) list in
  let () = x_tinfo_pp ("clean_tbl tbl: "^(string_of_unchanged_tbl tbl)) no_pos in
  let () = x_tinfo_pp ("clean_tbl arglst: "^((pr_list string_of_exp) arglst)) no_pos in
  let () = clean_tbl tbl arglst in
  let () = x_tinfo_pp ("clean_tbl new tbl: "^(string_of_unchanged_tbl tbl)) no_pos in
  Unchanged_Htbl.fold (fun (f,t) item r-> (((f,t),item)::r)) tbl []
;;

let is_same_unchanged ((f1,t1),s1) ((f2,t2),s2) =
  (((is_same_exp f1 f2)&&(is_same_exp t1 t2))||((is_same_exp f1 t2)&&(is_same_exp t1 f2))) && (ExpSet.equal s1 s2)
;;

let new_get_unchanged_fixpoint rel definelst =
  let (relname,arglst) =
    match rel with
    | BForm (((RelForm (SpecVar (_,id,_),explist,loc)),pa),_) ->
      (id,explist)
    | _ -> failwith "get_unchanged_fixpoint: Invalid rel"
  in
  let basic = ref [] in
  let rec iterator () =
    let new_basic = new_unchanged_fixpoint relname arglst definelst (arglst,!basic) in
    if same_unordered_list is_same_unchanged new_basic !basic
    then !basic
    else
      let () = basic := new_basic in
      iterator ()
  in
  let wrapper ((f,t),s) =
    let slst = ExpSet.fold (fun item r -> item::r) s [] in
    (f,t,slst)
  in
  let unchange_result = iterator () in
  let unchange_result_new = List.map wrapper unchange_result in
  let () = global_unchanged_info:= unchange_result_new in
  unchange_result
;;

let new_get_unchanged_fixpoint rel definelst =
  Debug.no_2 "new_get_unchanged_fixpoint" !print_pure (pr_list !print_pure) (pr_list string_of_unchanged) new_get_unchanged_fixpoint rel definelst
;;


let get_unchanged_fixpoint rel define =
  let (relname,arg1,arg2) =
    match rel with
    | BForm (((RelForm (SpecVar (_,id,_),explist,loc)),pa),_) ->
      (id,List.nth explist 0,List.nth explist 1)
    | _ -> failwith "unchanged_fixpoint: Invalid rel"
  in
  let result = (unchanged_fixpoint rel define) arg1 arg2 in
  let () = global_unchanged_info:= unify_unchanged_fixpoint result in
  result
;;

let get_unchanged_fixpoint rel define =
  Debug.no_2 "get_unchanged_fixpoint" !print_pure (pr_list !print_pure) (pr_list string_of_unchanged_info) get_unchanged_fixpoint rel define
;;

let get_unchanged_fixpoint rel define =
  if !Globals.array_translate
  then get_unchanged_fixpoint rel define
  else []
;;

let rec add_unchanged_info_to_formula unchanged f =
  let rec has_array_equal f e1 e2 =
    (* only conjuction, see whether there is a=a' *)
    match f with
    | BForm (((Eq ((Var (SpecVar (Array _,_,_),_) as v2),(Var (SpecVar (Array _,_,_),_) as v1),loc)),pa),_) ->
      (is_same_exp e1 v2 && is_same_exp e2 v1)||(is_same_exp e1 v1 && is_same_exp e2 v2)
    | And (f1,f2,_)->
      has_array_equal f1 e1 e2 || has_array_equal f2 e1 e2
    | _ -> false
  in
  let produce_unchanged_formula unchanged =
    match unchanged with
    | [(((Var (SpecVar _ as svf,_)) as e1),((Var (SpecVar _ as svt,_)) as e2),clst)] ->
      let new_qi = SpecVar (Int,"i",Unprimed) in
      let new_qi_var = Var (new_qi,no_pos) in
      let equal_f = BForm ((Eq (ArrayAt (svf,[new_qi_var],no_pos),ArrayAt (svt,[new_qi_var],no_pos),no_pos),None),None) in
      begin
        match clst with
        | [] ->
          Some (Forall (new_qi,equal_f,None,no_pos), e1, e2)
        | h::rest ->
          let pre_f = List.fold_left (
              fun result e ->
                let index_f = BForm ((Eq (new_qi_var,e,no_pos),None),None) in
                let not_f = Not (index_f,None,no_pos) in
                And (not_f,result,no_pos)
            ) (Not (BForm ((Eq (new_qi_var,h,no_pos),None),None),None,no_pos)) rest
          in
          let sub_f = Or (pre_f,equal_f,None,no_pos) in
          Some (Forall (new_qi,sub_f,None,no_pos),e1,e2)
      end
    | _ -> None
  in
  let helper unchanged f=
    let unchanged_formula = produce_unchanged_formula unchanged in
    match unchanged_formula with
    | None -> f
    | Some (uf,e1,e2) ->
      if has_array_equal f e1 e2
      then f
      else
        And (f,uf,no_pos)
  in
  match f with
  | Or (f1,f2,fl,loc) ->
    let new_f1 = add_unchanged_info_to_formula unchanged f1 in
    let new_f2 = add_unchanged_info_to_formula unchanged f2 in
    Or (new_f1,new_f2,fl,loc)
  | _ -> helper unchanged f
;;

let add_unchanged_info_to_formula unchanged f =
  Debug.no_2 "add_unchanged_info_to_formula" (pr_list string_of_unchanged_info) !print_pure !print_pure add_unchanged_info_to_formula unchanged f
;;

let add_unchanged_info_to_formula_f f =
  add_unchanged_info_to_formula !global_unchanged_info f
;;
