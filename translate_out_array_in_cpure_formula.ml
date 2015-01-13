open Cpure
open Globals
open Debug
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

let mk_imply
      (ante:formula) (conseq:formula):formula=
  Or (Not (ante,None,no_pos),conseq,None,no_pos)
;;

let rec mk_and_list
      (flst:formula list):formula=
  match flst with
    | [h] -> h
    | h::rest -> And (h,mk_and_list rest,no_pos)
    | [] -> failwith "mk_and_list: Invalid input"
;;

let rec standarize_array_formula
      (f:formula):(formula*(formula list))=
  let name_counter = ref 0 in
  let mk_new_name ()=
    let _ = name_counter:= !name_counter + 1 in
    Var (mk_typed_spec_var Int ("tarrvar"^(string_of_int (!name_counter))),no_pos)
  in
  let rec standarize_exp
        (e:exp):(exp * ((exp * exp) list))=
    match e with
      | ArrayAt (sv,elst,loc) ->
            begin
              match elst with
                | [h] ->
                      begin
                        match h with
                          | Var _
                          | IConst _ ->
                                (e,[])
                          | Add (e1,e2,loc)
                          | Subtract (e1,e2,loc)
                          | Mult (e1,e2,loc)
                          | Div (e1,e2,loc)->
                                let nname = mk_new_name () in
                                let (ne1,eelst1) = standarize_exp e1 in
                                let (ne2,eelst2) = standarize_exp e2 in
                                let neelst =
                                  begin
                                    match h with
                                      | Add _ ->(nname,Add (ne1,ne2,no_pos))::(eelst1@eelst2)
                                      | Subtract _ ->(nname,Subtract (ne1,ne2,no_pos))::(eelst1@eelst2)
                                      | Mult _ -> (nname,Mult (ne1,ne2,no_pos))::(eelst1@eelst2)
                                      | Div _ ->(nname,Div (ne1,ne2,no_pos))::(eelst1@eelst2)
                                      | _ -> failwith "standarize_exp: Invalid Input"
                                  end
                                in
                                (ArrayAt (sv,[nname],loc), neelst)
                          | _ -> failwith "standarize_exp: Invalid case for index"
                      end
                | _ -> failwith "standarize_exp: Fail to handle multi-dimension array"
            end
      | Tup2 ((e1,e2),loc)->
            let (ne1,eelst1) = standarize_exp e1 in
            let (ne2,eelst2) = standarize_exp e2 in
            (Tup2 ((ne1,ne2),loc),eelst1@eelst2)
      | Add (e1,e2,loc)->
            let (ne1,eelst1) = standarize_exp e1 in
            let (ne2,eelst2) = standarize_exp e2 in
            (Add (ne1,ne2,loc),eelst1@eelst2)
      | Subtract (e1,e2,loc)->
            let (ne1,eelst1) = standarize_exp e1 in
            let (ne2,eelst2) = standarize_exp e2 in
            (Subtract (ne1,ne2,loc),eelst1@eelst2)
      | Mult (e1,e2,loc)->
            let (ne1,eelst1) = standarize_exp e1 in
            let (ne2,eelst2) = standarize_exp e2 in
            (Mult (ne1,ne2,loc),eelst1@eelst2)
      | Div (e1,e2,loc)->
            let (ne1,eelst1) = standarize_exp e1 in
            let (ne2,eelst2) = standarize_exp e2 in
            (Div (ne1,ne2,loc),eelst1@eelst2)
      | Max (e1,e2,loc)->
            let (ne1,eelst1) = standarize_exp e1 in
            let (ne2,eelst2) = standarize_exp e2 in
            (Max (ne1,ne2,loc),eelst1@eelst2)
      | Min (e1,e2,loc)->
            let (ne1,eelst1) = standarize_exp e1 in
            let (ne2,eelst2) = standarize_exp e2 in
            (Min (ne1,ne2,loc),eelst1@eelst2)
      | BagDiff (e1,e2,loc)->
            let (ne1,eelst1) = standarize_exp e1 in
            let (ne2,eelst2) = standarize_exp e2 in
            (BagDiff (ne1,ne2,loc),eelst1@eelst2)
      | ListCons (e1,e2,loc)->
            let (ne1,eelst1) = standarize_exp e1 in
            let (ne2,eelst2) = standarize_exp e2 in
            (ListCons (ne1,ne2,loc),eelst1@eelst2)
      | TypeCast (typ,e1,loc)->
            let (ne1,eelst1) = standarize_exp e1 in
            (TypeCast (typ,ne1,loc),eelst1)
      | ListHead (e1,loc)->
            let (ne1,eelst1) = standarize_exp e1 in
            (ListHead (ne1,loc),eelst1)
      | ListTail (e1,loc)->
            let (ne1,eelst1) = standarize_exp e1 in
            (ListTail (ne1,loc),eelst1)
      | ListLength (e1,loc)->
            let (ne1,eelst1) = standarize_exp e1 in
            (ListLength (ne1,loc),eelst1)
      | ListReverse (e1,loc)->
            let (ne1,eelst1) = standarize_exp e1 in
            (ListReverse (ne1,loc),eelst1)
      | Func _ -> failwith "standarize_exp: Func To Be Implemented"
      | List _ -> failwith "standarize_exp: List To Be Implemented"
      | Bag _ -> failwith "standarize_exp: Bag To Be Implemented"
      | BagUnion _ -> failwith "standarize_exp: BagUnion To Be Implemented"
      | BagIntersect _ -> failwith "standarize_exp: BagIntersect To Be Implemented"
      | _ -> (e,[])
  in
  let standarize_p_formula
        (p:p_formula):(p_formula * (p_formula list))=
    let rec mk_p_formula_from_eelst
          (eelst: ( (exp * exp) list)):(p_formula list)=
      match eelst with
        | (e1,e2)::rest ->
              (Eq (e1,e2,no_pos))::(mk_p_formula_from_eelst rest)
        | [] -> []
    in
    match p with
      | Lt (e1, e2, loc)->
            let (ne1,eelst1) = standarize_exp e1 in
            let (ne2,eelst2) = standarize_exp e2 in
            (Lt (ne1,ne2,loc),mk_p_formula_from_eelst (eelst1@eelst2))
      | Lte (e1, e2, loc)->
            let (ne1,eelst1) = standarize_exp e1 in
            let (ne2,eelst2) = standarize_exp e2 in
            (Lte (ne1,ne2,loc),mk_p_formula_from_eelst (eelst1@eelst2))
      | Gt (e1, e2, loc)->
            let (ne1,eelst1) = standarize_exp e1 in
            let (ne2,eelst2) = standarize_exp e2 in
            (Gt (ne1,ne2,loc),mk_p_formula_from_eelst (eelst1@eelst2))
      | Gte (e1, e2, loc)->
            let (ne1,eelst1) = standarize_exp e1 in
            let (ne2,eelst2) = standarize_exp e2 in
            (Gte (ne1,ne2,loc),mk_p_formula_from_eelst (eelst1@eelst2))
      | SubAnn (e1, e2, loc)->
            let (ne1,eelst1) = standarize_exp e1 in
            let (ne2,eelst2) = standarize_exp e2 in
            (SubAnn (ne1,ne2,loc),mk_p_formula_from_eelst (eelst1@eelst2))
      | Eq (e1, e2, loc)->
            let (ne1,eelst1) = standarize_exp e1 in
            let (ne2,eelst2) = standarize_exp e2 in
            (Eq (ne1,ne2,loc),mk_p_formula_from_eelst (eelst1@eelst2))
      | Neq (e1, e2, loc)->
            let (ne1,eelst1) = standarize_exp e1 in
            let (ne2,eelst2) = standarize_exp e2 in
            (Neq (ne1,ne2,loc),mk_p_formula_from_eelst (eelst1@eelst2))
      | BagSub (e1, e2, loc)->
            let (ne1,eelst1) = standarize_exp e1 in
            let (ne2,eelst2) = standarize_exp e2 in
            (BagSub (ne1,ne2,loc),mk_p_formula_from_eelst (eelst1@eelst2))
      | ListIn (e1, e2, loc)->
            let (ne1,eelst1) = standarize_exp e1 in
            let (ne2,eelst2) = standarize_exp e2 in
            (ListIn (ne1,ne2,loc),mk_p_formula_from_eelst (eelst1@eelst2))
      | ListNotIn (e1, e2, loc)->
            let (ne1,eelst1) = standarize_exp e1 in
            let (ne2,eelst2) = standarize_exp e2 in
            (ListNotIn (ne1,ne2,loc),mk_p_formula_from_eelst (eelst1@eelst2))
      | ListAllN (e1, e2, loc)->
            let (ne1,eelst1) = standarize_exp e1 in
            let (ne2,eelst2) = standarize_exp e2 in
            (ListAllN (ne1,ne2,loc),mk_p_formula_from_eelst (eelst1@eelst2))
      | ListPerm (e1, e2, loc)->
            let (ne1,eelst1) = standarize_exp e1 in
            let (ne2,eelst2) = standarize_exp e2 in
            (ListPerm (ne1,ne2,loc),mk_p_formula_from_eelst (eelst1@eelst2))
      | EqMax (e1, e2, e3, loc)->
            let (ne1,eelst1) = standarize_exp e1 in
            let (ne2,eelst2) = standarize_exp e2 in
            let (ne3,eelst3) = standarize_exp e3 in
            (EqMax (ne1,ne2,ne3,loc),mk_p_formula_from_eelst ((eelst1@eelst2)@eelst3))
      | EqMin (e1, e2, e3, loc)->
            let (ne1,eelst1) = standarize_exp e1 in
            let (ne2,eelst2) = standarize_exp e2 in
            let (ne3,eelst3) = standarize_exp e3 in
            (EqMin (ne1,ne2,ne3,loc),mk_p_formula_from_eelst ((eelst1@eelst2)@eelst3))
      | BagIn (sv,e1,loc)->
            let (ne1,eelst1) = standarize_exp e1 in
            (BagIn (sv,ne1,loc),mk_p_formula_from_eelst eelst1)
      | BagNotIn (sv,e1,loc)->
            let (ne1,eelst1) = standarize_exp e1 in
            (BagNotIn (sv,ne1,loc),mk_p_formula_from_eelst eelst1)
      | BConst _->
            (p,[])
      | Frm _
      | XPure _
      | LexVar _
      | BVar _
      | BagMin _
      | BagMax _
      | VarPerm _
      | RelForm _ ->
            failwith ("standarize_array_formula: To Be Implemented")
  in
  match f with
    | BForm ((p,_),fl)->
          let (np,plst) = standarize_p_formula p in
          let flst = List.map (fun p -> BForm((p,None),None)) plst in
          (BForm ((np,None),None),flst)
    | And (f1,f2,l)->
          let (nf1,flst1) = standarize_array_formula f1 in
          let (nf2,flst2) = standarize_array_formula f2 in
          (And (nf1,nf2,l),flst1@flst2)
    | AndList lst->
          let (flst,flstlst) =
            (List.split (List.map (fun (t,f) -> let (nf,nflst) = (standarize_array_formula f) in ((t,nf),nflst)) lst)) in
          let nflst = List.fold_left (fun result l -> result@l) [] flstlst in
          (AndList flst,nflst)
    | Or (f1,f2,fl,l)->
          let (nf1,flst1) = standarize_array_formula f1 in
          let (nf2,flst2) = standarize_array_formula f2 in
          (Or (nf1,nf2,fl,l),flst1@flst2)
    | Not (f,fl,l)->
          let (nf1,flst1) = standarize_array_formula f in
          (Not (nf1,fl,l),flst1)
    | Forall (sv,f,fl,l)->
          let (nf1,flst1) = standarize_array_formula f in
          (Forall (sv,nf1,fl,l),flst1)
    | Exists (sv,f,fl,l)->
          let (nf1,flst1) = standarize_array_formula f in
          (Exists (sv,nf1,fl,l),flst1)
;;

let rec standarize_one_formula
      (f:formula):formula=
  match f with
    | BForm (b,fl)->
          let (nf,flst) = standarize_array_formula f in
          mk_and_list (nf::flst)
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
;;

let standarize_one_formula
      (f:formula):formula=
  let pf = !print_pure in
  Debug.no_1 "standarize_one_formula" pf pf (fun f-> standarize_one_formula f) f
;;

let standarize_array_imply
      (ante:formula) (conseq:formula):(formula * formula)=
  let (n_conseq,flst) = standarize_array_formula conseq in
  let ante = mk_and_list (ante::flst) in
  let n_ante = standarize_one_formula ante in
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

(* Given a formula, replace all the occurance of a variable in the formula with another variable *)
(* index is the variable to be replaced, with new_index *)
let rec produce_new_index_predicate
      (fo:formula) (index:exp) (new_index:exp):formula =
  let rec helper_exp
        (e:exp) (index:exp) (new_index:exp):exp =
    match e with
      | Var (sv,loc)->
            if is_same_var e index then new_index else e
      | IConst _
      | ArrayAt _ ->
            e
      | Add (e1,e2,loc) ->
            Add (helper_exp e1 index new_index, helper_exp e2 index new_index, loc)
      | Subtract (e1,e2,loc)->
            Subtract (helper_exp e1 index new_index, helper_exp e2 index new_index, loc)
      | Mult (e1,e2,loc)->
            Mult (helper_exp e1 index new_index, helper_exp e2 index new_index, loc)
      | Div (e1,e2,loc) ->
            Div (helper_exp e1 index new_index, helper_exp e2 index new_index,loc)
      | _ ->
            failwith "Translate_out_array_in_cpure_formula.produce_new_index_predicate: To Be Implemented"
  in
  let helper_b_formula
        ((p,ba):b_formula) (index:exp) (new_index:exp):b_formula =
    let helper_p_formula
          (p:p_formula) (index:exp) (new_index:exp):p_formula =
      match p with
        | Lt (e1, e2, loc)->
              Lt (helper_exp e1 index new_index, helper_exp e2 index new_index, loc)
        | Lte (e1, e2, loc)->
              Lte (helper_exp e1 index new_index, helper_exp e2 index new_index, loc)
        | Gt (e1, e2, loc)->
              Gt (helper_exp e1 index new_index, helper_exp e2 index new_index, loc)
        | Gte (e1, e2, loc)->
              Gte (helper_exp e1 index new_index, helper_exp e2 index new_index, loc)
        | SubAnn (e1, e2, loc)->
              SubAnn (helper_exp e1 index new_index, helper_exp e2 index new_index, loc)
        | Eq (e1, e2, loc)->
              Eq (helper_exp e1 index new_index, helper_exp e2 index new_index, loc)
        | Neq (e1, e2, loc)->
              Neq (helper_exp e1 index new_index, helper_exp e2 index new_index, loc)
        | BagSub (e1, e2, loc)->
              BagSub (helper_exp e1 index new_index, helper_exp e2 index new_index, loc)
        | ListIn (e1, e2, loc)->
              ListIn (helper_exp e1 index new_index, helper_exp e2 index new_index, loc)
        | ListNotIn (e1, e2, loc)->
              ListNotIn (helper_exp e1 index new_index, helper_exp e2 index new_index, loc)
        | ListAllN (e1, e2, loc)->
              ListAllN (helper_exp e1 index new_index, helper_exp e2 index new_index, loc)
        | ListPerm (e1, e2, loc)->
              ListPerm (helper_exp e1 index new_index, helper_exp e2 index new_index, loc)
        | EqMax (e1, e2, e3, loc)->
              EqMax (helper_exp e1 index new_index, helper_exp e2 index new_index, helper_exp e3 index new_index, loc)
        | EqMin (e1, e2, e3, loc)->
              EqMin (helper_exp e1 index new_index, helper_exp e2 index new_index, helper_exp e3 index new_index, loc)
        | BagIn (sv,e1,loc)->
              BagIn (sv, helper_exp e1 index new_index, loc)
        | BagNotIn (sv,e1,loc)->
              BagNotIn (sv, helper_exp e1 index new_index, loc)
        | Frm _
        | XPure _
        | LexVar _
        | BConst _
        | BVar _
        | BagMin _
        | BagMax _
        | VarPerm _
        | RelForm _ ->
              failwith "produce_new_index_predicate: To Be Implemented"
    in
    (helper_p_formula p index new_index, None)
  in
  match fo with
    | BForm (b,fl)->
          let n_b = helper_b_formula b index new_index in
          BForm (n_b,fl)
    | And (f1,f2,l)->
          And (produce_new_index_predicate f1 index new_index,produce_new_index_predicate f2 index new_index,l)
    | AndList lst->
          AndList (List.map (fun (t,f) -> (t,produce_new_index_predicate f index new_index)) lst)
    | Or (f1,f2,fl,l)->
          Or (produce_new_index_predicate f1 index new_index,produce_new_index_predicate f2 index new_index,fl,l)
    | Not (f,fl,l)->
          Not (produce_new_index_predicate f index new_index,fl,l)
    | Forall (sv,f,fl,l)->
          Forall (sv,produce_new_index_predicate f index new_index,fl,l)
    | Exists (sv,f,fl,l)->
          Exists (sv,produce_new_index_predicate f index new_index,fl,l)
;;

let produce_new_index_predicate
      (f:formula) (index:exp) (new_index:exp):formula =
  let pf = !print_pure in
  let pe = ArithNormalizer.string_of_exp in
  Debug.no_3 "produce_new_index_predicate" pf pe pe pf (fun f i n -> produce_new_index_predicate f i n) f index new_index
;;

let produce_new_index_predicate_wrapper
      (fo:formula option) (index:exp) (new_index:exp):formula =
  match fo with
    | Some f -> produce_new_index_predicate f index new_index
    | None -> BForm ((Eq (index,new_index,no_pos),None),None)
;;

(* Given a formula, extract all the subformulas that is related to some variable *)
let rec extract_index_predicate
      (f:formula) (index:exp):(formula option) =
  let rec is_involved_exp
        (e:exp) (index:exp):bool =
    match e with
      | Var (sv,loc)->
            is_same_var e index
      | Add (e1,e2,loc)
      | Subtract (e1,e2,loc)
      | Mult (e1,e2,loc)
      | Div (e1,e2,loc)->
            (is_involved_exp e1 index)||(is_involved_exp e2 index)
      | ArrayAt _
      | IConst _ ->
            false
      | _ ->
            failwith ("Translate_out_array_in_cpure_formula.extract_index_predicate: "^(ArithNormalizer.string_of_exp e)^" To Be Implemented")
  in
  let helper_b_formula
        ((p,ba):b_formula) (index:exp):(b_formula option) =
    let helper_p_formula
          (p:p_formula) (index:exp):(p_formula option) =
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
              if (is_involved_exp e1 index) || (is_involved_exp e2 index)
              then
                Some p
              else
                None
        | EqMax (e1, e2, e3, loc)
        | EqMin (e1, e2, e3, loc)->
              if (is_involved_exp e1 index) || (is_involved_exp e2 index) || (is_involved_exp e3 index)
              then
                Some p
              else
                None
        | BagIn (sv,e1,loc)
        | BagNotIn (sv,e1,loc)->
              if (is_involved_exp e1 index)
              then
                Some p
              else
                None
        | Frm _
        | XPure _
        | LexVar _
        | BConst _
        | BVar _
        | BagMin _
        | BagMax _
        | VarPerm _
        | RelForm _ ->
              failwith "extract_index_predicate: To Be Implemented"
    in
    match helper_p_formula p index with
      | Some pf ->
            Some (pf,None)
      | None ->
            None
  in
  let rec helper
        (f:formula) (index:exp): (formula list) =
    match f with
      | BForm (b,fl)->
            begin
              match (helper_b_formula b index) with
                | Some bp ->
                      [BForm (bp,fl)]
                | None ->
                      []
            end
      | And (f1,f2,l)->
            (helper f1 index)@(helper f2 index)
      | AndList lst->
            List.fold_left (fun l (t,f) -> l@(helper f index)) [] lst
      | Or (f1,f2,fl,l)->
            (helper f1 index)@(helper f2 index)
      | Not (f,fl,l)->
            helper f index
      | Forall (sv,f,fl,l)->
            helper f index
      | Exists (sv,f,fl,l)->
            helper f index
  in
  let helper
        (f:formula) (index:exp) : (formula list)=
    let _ = print_endline (!print_pure f) in
    helper f index
  in
  match f with
    | BForm _
    | And _
    | AndList _->
          begin
            match (helper f index) with
              | [] ->
                    None
              | lst ->
                    Some (mk_and_list lst)
          end
    | Or (f1,f2,fl,l)->
          begin
            match helper f1 index, helper f2 index with
              | [],[]-> None
              | lst,[]
              | [],lst -> Some (mk_and_list lst)
              | lst1,lst2 ->
                    Some (Or (mk_and_list lst1,mk_and_list lst2,fl,l))
          end
    | Not (f,fl,l)->
          begin
            match helper f index with
              | [] -> None
              | lst -> Some (Not (mk_and_list lst,fl,l))
          end
    | Forall (sv,f,fl,l)->
          begin
            match helper f index with
              | [] -> None
              | lst -> Some (Forall (sv,mk_and_list lst,fl,l))
          end
    | Exists (sv,f,fl,l)->
          begin
            match helper f index with
              | [] -> None
              | lst -> Some (Exists (sv,mk_and_list lst,fl,l))
          end
;;

let extract_index_predicate
      (f:formula) (index:exp):(formula option) =
  let pf = !print_pure in
  let pfo = function
    | Some f -> pf f
    | None -> "Constant index"
  in
  Debug.no_2 "extract_index_predicate" pf ArithNormalizer.string_of_exp pfo (fun f i -> extract_index_predicate f i) f index
;;

(* Get array transform information from cpure formula *)
(* Actually I don't have to translate the array out here. But due to some historical reason, the implementation is like this. *)
(* In later usage of this method, I only use the array_transform_info list. *)

let get_array_transform_info_lst
      (f:formula):((array_transform_info list) * formula)=
  let rec get_array_transform_info_lst_helper
        (f:formula):((array_transform_info list) * formula)=
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
                  | _ -> failwith "get_array_transform_info_lst: Not array type"
              end
    in
    (* return a list of array_transform_info and an array-free expression *)
    let rec get_array_transform_info_lst_from_exp
          (e:exp):((array_transform_info list) * exp)=
      match e with
        | ArrayAt (sv,elst,_)->
              begin
                match elst with
                  | [h] ->
                        let new_name = mk_array_new_name sv h in
                        let new_info = { target_array = e; new_name = new_name } in
                        ([new_info],new_name)
                  | h::rest -> failwith "get_array_transform_info_lst_from_exp: Fail to handle multi-dimensional array"
                  | [] -> failwith "get_array_transform_info_lst_from_exp: Impossible Case"
              end
        | Tup2 ((e1,e2),loc)->
              let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in
              let (info2,ne2) = get_array_transform_info_lst_from_exp e2 in
              (info1@info2,Tup2 ((ne1,ne2),loc))
        | Add (e1,e2,loc)->
              let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in
              let (info2,ne2) = get_array_transform_info_lst_from_exp e2 in
              (info1@info2,Add (ne1,ne2,loc))
        | Subtract (e1,e2,loc)->
              let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in
              let (info2,ne2) = get_array_transform_info_lst_from_exp e2 in
              (info1@info2,Subtract (ne1,ne2,loc))
        | Mult (e1,e2,loc)->
              let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in
              let (info2,ne2) = get_array_transform_info_lst_from_exp e2 in
              (info1@info2,Mult (ne1,ne2,loc))
        | Div (e1,e2,loc)->
              let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in
              let (info2,ne2) = get_array_transform_info_lst_from_exp e2 in
              (info1@info2,Div (ne1,ne2,loc))
        | Max (e1,e2,loc)->
              let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in
              let (info2,ne2) = get_array_transform_info_lst_from_exp e2 in
              (info1@info2,Max (ne1,ne2,loc))
        | Min (e1,e2,loc)->
              let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in
              let (info2,ne2) = get_array_transform_info_lst_from_exp e2 in
              (info1@info2,Min (ne1,ne2,loc))
        | BagDiff (e1,e2,loc)->
              let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in
              let (info2,ne2) = get_array_transform_info_lst_from_exp e2 in
              (info1@info2,BagDiff (ne1,ne2,loc))
        | ListCons (e1,e2,loc)->
              let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in
              let (info2,ne2) = get_array_transform_info_lst_from_exp e2 in
              (info1@info2,ListCons (ne1,ne2,loc))
        | TypeCast (typ,e1,loc)->
              let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in
              (info1,TypeCast (typ,ne1,loc))
        | ListHead (e1,loc)->
              let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in
              (info1,ListHead (ne1,loc))
        | ListTail (e1,loc)->
              let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in
              (info1,ListTail (ne1,loc))
        | ListLength (e1,loc)->
              let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in
              (info1,ListLength (ne1,loc))
        | ListReverse (e1,loc)->
              let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in
              (info1,ListReverse (ne1,loc))
        | Func _ -> failwith "get_array_transform_info_lst_from_exp: Func To Be Implemented"
        | List _ -> failwith "get_array_transform_info_lst_from_exp: List To Be Implemented"
        | Bag _ -> failwith "get_array_transform_info_lst_from_exp: Bag To Be Implemented"
        | BagUnion _ -> failwith "get_array_transform_info_lst_from_exp: BagUnion To Be Implemented"
        | BagIntersect _ -> failwith "get_array_transform_info_lst_from_exp: BagIntersect To Be Implemented"
        (*| Var (sv,_) -> let _ = print_endline ("Var: sv = "^(string_of_spec_var sv)) in ([],e)*)
        | _ -> ([],e)
    in
    let get_array_transform_info_lst_from_b_formula
          ((p,ba):b_formula):((array_transform_info list) * b_formula)=
      let helper
            (p:p_formula):((array_transform_info list) * p_formula)=
        match p with
          | Lt (e1, e2, loc)->
                let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in
                let (info2,ne2) = get_array_transform_info_lst_from_exp e2 in
                (info1@info2,Lt (ne1,ne2,loc))
          | Lte (e1, e2, loc)->
                let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in
                let (info2,ne2) = get_array_transform_info_lst_from_exp e2 in
                (info1@info2,Lte (ne1,ne2,loc))
          | Gt (e1, e2, loc)->
                let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in
                let (info2,ne2) = get_array_transform_info_lst_from_exp e2 in
                (info1@info2,Gt (ne1,ne2,loc))
          | Gte (e1, e2, loc)->
                let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in
                let (info2,ne2) = get_array_transform_info_lst_from_exp e2 in
                (info1@info2,Gte (ne1,ne2,loc))
          | SubAnn (e1, e2, loc)->
                let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in
                let (info2,ne2) = get_array_transform_info_lst_from_exp e2 in
                (info1@info2,SubAnn (ne1,ne2,loc))
          | Eq (e1, e2, loc)->
                let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in
                let (info2,ne2) = get_array_transform_info_lst_from_exp e2 in
                (info1@info2,Eq (ne1,ne2,loc))
          | Neq (e1, e2, loc)->
                let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in
                let (info2,ne2) = get_array_transform_info_lst_from_exp e2 in
                (info1@info2,Neq (ne1,ne2,loc))
          | BagSub (e1, e2, loc)->
                let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in
                let (info2,ne2) = get_array_transform_info_lst_from_exp e2 in
                (info1@info2,BagSub (ne1,ne2,loc))
          | ListIn (e1, e2, loc)->
                let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in
                let (info2,ne2) = get_array_transform_info_lst_from_exp e2 in
                (info1@info2,ListIn (ne1,ne2,loc))
          | ListNotIn (e1, e2, loc)->
                let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in
                let (info2,ne2) = get_array_transform_info_lst_from_exp e2 in
                (info1@info2,ListNotIn (ne1,ne2,loc))
          | ListAllN (e1, e2, loc)->
                let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in
                let (info2,ne2) = get_array_transform_info_lst_from_exp e2 in
                (info1@info2,ListAllN (ne1,ne2,loc))
          | ListPerm (e1, e2, loc)->
                let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in
                let (info2,ne2) = get_array_transform_info_lst_from_exp e2 in
                (info1@info2,ListPerm (ne1,ne2,loc))
          | EqMax (e1, e2, e3, loc)->
                let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in
                let (info2,ne2) = get_array_transform_info_lst_from_exp e2 in
                let (info3,ne3) = get_array_transform_info_lst_from_exp e3 in
                ((info1@info2)@info3,EqMax (ne1,ne2,ne3,loc))
          | EqMin (e1, e2, e3, loc)->
                let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in
                let (info2,ne2) = get_array_transform_info_lst_from_exp e2 in
                let (info3,ne3) = get_array_transform_info_lst_from_exp e3 in
                ((info1@info2)@info3,EqMin (ne1,ne2,ne3,loc))
          | BagIn (sv,e1,loc)->
                let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in
                (info1,BagIn (sv,ne1,loc))
          | BagNotIn (sv,e1,loc)->
                let (info1,ne1) = get_array_transform_info_lst_from_exp e1 in
                (info1,BagNotIn (sv,ne1,loc)) 
          | Frm _
          | XPure _
          | LexVar _
          | BConst _
          | BVar _
          | BagMin _
          | BagMax _
          | VarPerm _
          | RelForm _ ->
                ([],p)
      in
      let (info,np) = helper p in
      (info, (np,None))
    in
    match f with
      | BForm (b,fl)->
            let (info,nb) = get_array_transform_info_lst_from_b_formula b in
            (info,BForm (nb,fl))
      | And (f1,f2,l)->
            let (info1,nf1) = get_array_transform_info_lst_helper f1 in
            let (info2,nf2) = get_array_transform_info_lst_helper f2 in
            (info1@info2,And (nf1,nf2,l))
      | AndList lst->
            let (result_info,result_nfl) = List.fold_left (fun (infol,nfl) (t,and_fo)->let (info,nf) = get_array_transform_info_lst_helper and_fo in (infol@info,nfl@[(t,nf)])) ([],[]) lst in
            (result_info,AndList result_nfl)
      | Or (f1,f2,fl,l)->
            let (info1,nf1) = get_array_transform_info_lst_helper f1 in
            let (info2,nf2) = get_array_transform_info_lst_helper f2 in
            (info1@info2,Or (nf1,nf2,fl,l))
      | Not (f,fl,l)->
            let (info1,nf1) = get_array_transform_info_lst_helper f in
            (info1,Not (nf1,fl,l))
      | Forall (sv,f,fl,l)->
            let (info1,nf1) = get_array_transform_info_lst_helper f in
            (info1,Forall (sv,nf1,fl,l))
      | Exists (sv,f,fl,l)->
            let (info1,nf1) = get_array_transform_info_lst_helper f in
            (info1,Exists (sv,nf1,fl,l))
  in
  let rec no_duplicate_array_name
        (alst:array_transform_info list):array_transform_info list=
    let rec duplicate_array_at
          (a:array_transform_info) (alst:array_transform_info list):bool=
      match alst with
        | h::rest -> if is_same_array_at a.target_array h.target_array then true else duplicate_array_at a rest
        | [] -> false
    in
    match alst with
      | h::rest -> if duplicate_array_at h rest then no_duplicate_array_name rest else h::(no_duplicate_array_name rest)
      | [] -> []
  in
  let (infolst,nf) = get_array_transform_info_lst_helper f in
  (no_duplicate_array_name infolst,nf)
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

(* What is returned is a list of (A*B). A is a list of array_transform_info, indicating the mapping from an ArrayAt to a Var. B is a list of (exp*exp), indicating the relation between indexes *)
let constraint_generator
      (baselst:exp list) (infolst:array_transform_info list):((array_transform_info list) * ((exp * exp) list)) list=
  let rec iterate
        (baselst:exp list) (infolst:array_transform_info list) (whole_infolst:array_transform_info list) (translate_info:(exp * array_transform_info) list):((array_transform_info list) * ((exp * exp) list)) list=
    match baselst, infolst with
      | hb::restb,hi::resti ->
            if is_same_array hb hi.target_array
            then (iterate restb whole_infolst whole_infolst ((hb,hi)::translate_info)) @ (iterate baselst resti whole_infolst translate_info)
            else iterate baselst resti whole_infolst translate_info
      | [], _ ->
            let mk_result
                  ((e,info):(exp * array_transform_info)):(array_transform_info * (exp * exp))=
              let (index1,index2) = (get_array_index e,get_array_index info.target_array) in
              ({target_array = e; new_name = info.new_name},(index1,index2))
            in
            [(List.split (List.fold_left (fun result (e,info) -> (mk_result (e,info))::result) [] translate_info))]
      | _, [] ->
            []
  in
  iterate baselst infolst infolst []
;;

(* return a list of exp, indicating what ArrayAt is contained in a p_formula*)
let extract_translate_base
      (p:p_formula):(exp list)=
  let rec extract_translate_base_exp
        (e:exp):(exp list)=
    match e with
      | ArrayAt _ ->
            [e]
      | Add (e1,e2,loc)
      | Subtract (e1,e2,loc)
      | Mult (e1,e2,loc)
      | Div (e1,e2,loc) ->
            (extract_translate_base_exp e1)@(extract_translate_base_exp e2)
      | _ -> []
  in
  let helper
        (p:p_formula):(exp list) =
    match p with
      | Frm _
      | XPure _
      | LexVar _
      | BConst _
      | BVar _
      | BagMin _
      | BagMax _
      | VarPerm _
      | RelForm _ ->
            []
      | BagIn (sv,e1,loc)
      | BagNotIn (sv,e1,loc)->
            extract_translate_base_exp e1
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
            (extract_translate_base_exp e1)@(extract_translate_base_exp e2)
      | EqMax (e1,e2,e3,loc)
      | EqMin (e1,e2,e3,loc)->
            (extract_translate_base_exp e1)@(extract_translate_base_exp e2)@(extract_translate_base_exp e3)
      | _ ->  []
  in
  helper p
;;

(* find_replace: find a new name for an array expression, return the new expression and the new transform information *)
(* The array expressions and the new variable expressions are mapped one to one *)
let find_replace
      (e:exp) (infolst:array_transform_info list):(exp * (array_transform_info list))=
  let rec helper
        (e:exp) (infolst:array_transform_info list):(exp * (array_transform_info list))=
    match infolst with
      | h::rest ->
            if is_same_array_at e h.target_array
            then (h.new_name, rest)
            else
              helper e rest
      | []-> failwith "find_replace: Fail to find a new name for array"
  in
  match e with
    | ArrayAt _ ->
          helper e infolst
    | _ -> failwith "find_replace: Invalid input"
;;

let find_replace
      (e:exp) (infolst:array_transform_info list):(exp* (array_transform_info list))=
  let p_result =
    function
        (e,alst) -> "exp: "^(ArithNormalizer.string_of_exp e)^"\n array_transform_info list: "^(List.fold_left (fun r i -> r^(string_of_array_transform_info i)^"\n") "\n" alst)
  in
  let p_infolst =
    function
        h -> List.fold_left (fun r i -> r^(string_of_array_transform_info i)^"\n") "\n" h
  in
  let p_e = ArithNormalizer.string_of_exp in
  Debug.no_2 "find_replace" p_e p_infolst p_result (fun e i -> find_replace e i) e infolst
;;
(* END of find_replace *)

let translate_array_formula_LHS_b_formula
      ((p,ba):b_formula) (infolst:array_transform_info list):(((exp * exp) list) * b_formula) list=
  let translate_base = extract_translate_base p in
  (* translate_base is a list of exp, denoting all the ArrayAt in a p_formula *)
  let translate_infolstlst = constraint_generator translate_base infolst in
  let rec mk_array_free_exp
        (e:exp) (infolst:array_transform_info list):(exp * (array_transform_info list))=
    match e with
      | ArrayAt _ ->
            find_replace e infolst
      | Add (e1,e2,loc)->
            let (ne1,ninfolst) = mk_array_free_exp e1 infolst in
            let (ne2,ninfolst) = mk_array_free_exp e2 ninfolst in
            (Add (ne1,ne2,loc),ninfolst)
      | Subtract (e1,e2,loc)->
            let (ne1,ninfolst) = mk_array_free_exp e1 infolst in
            let (ne2,ninfolst) = mk_array_free_exp e2 ninfolst in
            (Subtract (ne1,ne2,loc),ninfolst)
      | Mult (e1,e2,loc)->
            let (ne1,ninfolst) = mk_array_free_exp e1 infolst in
            let (ne2,ninfolst) = mk_array_free_exp e2 ninfolst in
            (Mult (ne1,ne2,loc),ninfolst)
      | Div (e1,e2,loc)->
            let (ne1,ninfolst) = mk_array_free_exp e1 infolst in
            let (ne2,ninfolst) = mk_array_free_exp e2 ninfolst in
            (Div (ne1,ne2,loc),ninfolst)
      | _ -> (e,infolst)
  in
  let mk_array_free_formula
        (p:p_formula) (infolst:array_transform_info list):p_formula=
    match p with
      | Frm _
      | XPure _
      | LexVar _
      | BConst _
      | BVar _
      | BagMin _
      | BagMax _
      | VarPerm _
      | RelForm _ ->
            p
      | BagIn (sv,e1,loc)->
            let (ne,ninfolst) = mk_array_free_exp e1 infolst in
            if (List.length ninfolst)=0
            then BagIn (sv,ne,loc)
            else failwith "mk_array_free_formula: Invalid replacement"
      | BagNotIn (sv,e1,loc)->
            let (ne,ninfolst) = mk_array_free_exp e1 infolst in
            if (List.length ninfolst)=0
            then BagNotIn (sv,ne,loc)
            else failwith "mk_array_free_formula: Invalid replacement"
      | Lt (e1,e2,loc) ->
            let (ne1,ninfolst) = mk_array_free_exp e1 infolst in
            let (ne2,ninfolst) = mk_array_free_exp e2 ninfolst in
            if (List.length ninfolst)=0
            then
              Lt (ne1,ne2,loc)
            else
              failwith "mk_array_free_formula: Invalid replacement"
      | Lte (e1,e2,loc) ->
            let (ne1,ninfolst) = mk_array_free_exp e1 infolst in
            let (ne2,ninfolst) = mk_array_free_exp e2 ninfolst in
            if (List.length ninfolst)=0
            then
              Lte (ne1,ne2,loc)
            else
              failwith "mk_array_free_formula: Invalid replacement"
      | Gt (e1,e2,loc) ->
            let (ne1,ninfolst) = mk_array_free_exp e1 infolst in
            let (ne2,ninfolst) = mk_array_free_exp e2 ninfolst in
            if (List.length ninfolst)=0
            then
              Gt (ne1,ne2,loc)
            else
              failwith "mk_array_free_formula: Invalid replacement"
      | Gte (e1,e2,loc) ->
            let (ne1,ninfolst) = mk_array_free_exp e1 infolst in
            let (ne2,ninfolst) = mk_array_free_exp e2 ninfolst in
            if (List.length ninfolst)=0
            then
              Gte (ne1,ne2,loc)
            else
              failwith "mk_array_free_formula: Invalid replacement"
      | SubAnn (e1,e2,loc) ->
            let (ne1,ninfolst) = mk_array_free_exp e1 infolst in
            let (ne2,ninfolst) = mk_array_free_exp e2 ninfolst in
            if (List.length ninfolst)=0
            then
              SubAnn (ne1,ne2,loc)
            else
              failwith "mk_array_free_formula: Invalid replacement"
      | Eq (e1,e2,loc) ->
            let (ne1,ninfolst) = mk_array_free_exp e1 infolst in
            let (ne2,ninfolst) = mk_array_free_exp e2 ninfolst in
            if (List.length ninfolst)=0
            then
              Eq (ne1,ne2,loc)
            else
              failwith "mk_array_free_formula: Invalid replacement"
      | Neq (e1,e2,loc) ->
            let (ne1,ninfolst) = mk_array_free_exp e1 infolst in
            let (ne2,ninfolst) = mk_array_free_exp e2 ninfolst in
            if (List.length ninfolst)=0
            then
              Neq (ne1,ne2,loc)
            else
              failwith "mk_array_free_formula: Invalid replacement"
      | ListIn (e1,e2,loc) ->
            let (ne1,ninfolst) = mk_array_free_exp e1 infolst in
            let (ne2,ninfolst) = mk_array_free_exp e2 ninfolst in
            if (List.length ninfolst)=0
            then
              ListIn (ne1,ne2,loc)
            else
              failwith "mk_array_free_formula: Invalid replacement"
      | ListNotIn (e1,e2,loc) ->
            let (ne1,ninfolst) = mk_array_free_exp e1 infolst in
            let (ne2,ninfolst) = mk_array_free_exp e2 ninfolst in
            if (List.length ninfolst)=0
            then
              ListNotIn (ne1,ne2,loc)
            else
              failwith "mk_array_free_formula: Invalid replacement"
      | ListAllN (e1,e2,loc) ->
            let (ne1,ninfolst) = mk_array_free_exp e1 infolst in
            let (ne2,ninfolst) = mk_array_free_exp e2 ninfolst in
            if (List.length ninfolst)=0
            then
              ListAllN (ne1,ne2,loc)
            else
              failwith "mk_array_free_formula: Invalid replacement"
      | ListPerm (e1,e2,loc)->
            let (ne1,ninfolst) = mk_array_free_exp e1 infolst in
            let (ne2,ninfolst) = mk_array_free_exp e2 ninfolst in
            if (List.length ninfolst)=0
            then
              ListPerm (ne1,ne2,loc)
            else
              failwith "mk_array_free_formula: Invalid replacement"
      | EqMax (e1,e2,e3,loc)->
            let (ne1,ninfolst) = mk_array_free_exp e1 infolst in
            let (ne2,ninfolst) = mk_array_free_exp e2 ninfolst in
            let (ne3,ninfolst) = mk_array_free_exp e3 ninfolst in
            if (List.length ninfolst)=0
            then
              EqMax (ne1,ne2,ne3,loc)
            else
              failwith "mk_array_free_formula: Invalid replacement"
      | EqMin (e1,e2,e3,loc)->
            let (ne1,ninfolst) = mk_array_free_exp e1 infolst in
            let (ne2,ninfolst) = mk_array_free_exp e2 ninfolst in
            let (ne3,ninfolst) = mk_array_free_exp e3 ninfolst in
            if (List.length ninfolst)=0
            then
              EqMin (ne1,ne2,ne3,loc)
            else
              failwith "mk_array_free_formula: Invalid replacement"
      | _ ->  p
  in
  let rec mk_array_free_formula_lst
        (* (p:p_formula) (infolstlst:(((array_transform_info list) * ((exp * exp) list)) list)):(((p_formula list) * b_formula) list)= *)
        (p:p_formula) (infolstlst:(((array_transform_info list) * ((exp * exp) list)) list)):((((exp * exp) list) * b_formula) list)=
    match infolstlst with
      | (alst,eelst)::rest ->
            (* let plst = List.map (fun (e1,e2) -> Eq (e1,e2,no_pos)) eelst in *)
            begin
              match eelst with
                | [] -> mk_array_free_formula_lst p rest
                | _ -> (eelst,(mk_array_free_formula p alst,None))::(mk_array_free_formula_lst p rest)
            end
      | [] -> []
  in
  mk_array_free_formula_lst p translate_infolstlst
;;

let rec translate_array_formula_LHS
      (f:formula) (infolst:array_transform_info list) (f_whole:formula):formula=
  match f with
    | BForm (b,fl)->
          let rec helper
                (* (lhslst:((p_formula list) * b_formula) list):formula=*)
                (lhslst:((((exp * exp) list) * b_formula) list)) : formula =
            match lhslst with
              | [] -> f
              | (eelst,bformula)::rest ->
                    let ante = mk_and_list (List.map (fun (i, ni) -> produce_new_index_predicate_wrapper (extract_index_predicate f_whole i) i ni) eelst) in
                    (* let ante = mk_and_list (List.map (fun p -> BForm ((p,None),None)) plst) in *)
                    let imply = mk_imply ante (BForm (bformula,None)) in
                    And (imply,helper rest,no_pos)
          in
          let lhslst = translate_array_formula_LHS_b_formula b infolst in
          helper lhslst
    | And (f1,f2,l)->
          And (translate_array_formula_LHS f1 infolst f_whole,translate_array_formula_LHS f2 infolst f_whole,l)
    | AndList lst->
          AndList (List.map (fun (t,f)->(t,translate_array_formula_LHS f infolst f_whole)) lst)
    | Or (f1,f2,fl,l)->
          Or (translate_array_formula_LHS f1 infolst f_whole,translate_array_formula_LHS f2 infolst f_whole,fl,l)
    | Not (f,fl,l)->
          Not (translate_array_formula_LHS f infolst f_whole,fl,l)
    | Forall (sv,f,fl,l)->
          Forall (sv,translate_array_formula_LHS f infolst f_whole,fl,l)
    | Exists (sv,f,fl,l)->
          Exists (sv,translate_array_formula_LHS f infolst f_whole,fl,l)
;;

let translate_array_formula_LHS
      (f:formula) (infolst:array_transform_info list):formula=
  translate_array_formula_LHS f infolst f
;;

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

let translate_out_array_in_imply
      (ante:formula) (conseq:formula) : (formula * formula) =
  let (ante,conseq) = standarize_array_imply ante conseq in
  let (info_lst,n_conseq) = get_array_transform_info_lst (And (conseq,ante,no_pos)) in
  let n_ante = translate_array_formula_LHS ante info_lst in
  let n_ante =
    match mk_array_equal_formula ante info_lst with
      | Some f -> And (f,n_ante,no_pos)
      | None -> n_ante
  in
  let (_,n_conseq) = get_array_transform_info_lst conseq in
  (n_ante,n_conseq)
;;
(*          *******************************         *)

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
      | VarPerm _
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

(* For update_array_1d *)
let rec translate_array_relation
      (f:formula):formula=
  let translate_array_relation_in_b_formula
        ((p,ba):b_formula):b_formula=
    let helper
          (p:p_formula):p_formula=
      match p with
        | RelForm (SpecVar (_,id,_),elst,loc) ->
              if id="update_array_1d"
              then
                begin
                  match (List.nth elst 1) with
                    | Var (SpecVar (t1,id1,p1) as array_sv,loc)->
                          let new_array_at = ArrayAt (SpecVar (Array (t1,1000),id1,p1),[List.nth elst 3],no_pos) in
                          Eq (new_array_at,List.nth elst 2,no_pos)
                    | _ -> failwith "translate_array_relation: Not Var"
                end
              else
                p
        | _ -> p
    in
    (helper p,ba)
  in
  match f with
    | BForm (b,fl)->
          BForm (translate_array_relation_in_b_formula b,fl)
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


let translate_out_array_in_one_formula
      (f:formula):formula=
  let f = standarize_one_formula f in
  let (info_lst,_) = get_array_transform_info_lst f in
  let nf = translate_array_formula_LHS f info_lst in
  let nf =
    match mk_array_equal_formula f info_lst with
      | Some f -> And (f,nf,no_pos)
      | None -> nf
  in
  nf
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
        | VarPerm _
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
  let pf = !print_pure in
  Debug.no_1 "translate_back_array_in_one_formula" pf pf (fun f -> translate_back_array_in_one_formula f) f
;;
(* END of translating back the array to a formula *)


(* Controlled by Globals.array_translate *)
let translate_out_array_in_imply
      (ante:formula)(conseq:formula):(formula*formula)=
  if !Globals.array_translate then translate_out_array_in_imply ante conseq
  else (ante,conseq)

let drop_array_formula
      (f:formula):formula=
  if !Globals.array_translate then drop_array_formula f
  else f

let translate_array_relation
      (f:formula):formula=
  if !Globals.array_translate then translate_array_relation f
  else f



let drop_array_formula
      (f:formula):formula=
  let pr = !print_pure in
  Debug.no_1 "drop_array_formula" pr pr (fun fo->drop_array_formula fo) f

let translate_out_array_in_imply
      (ante:formula)(conseq:formula):(formula*formula)=
  let p1 = !print_pure in
  let p2 (f1,f2) = "new ante: "^(p1 f1)^"\nnew conseq: "^(p1 f2) in
  Debug.no_2 "translate_out_array_in_imply" p1 p1 p2 (fun f1 f2-> translate_out_array_in_imply f1 f2) ante conseq

let translate_array_relation
      (f:formula):formula=
  let pf = !print_pure in
  Debug.no_1 "translate_array_relation" pf pf (fun f-> translate_array_relation f) f
;;

let translate_out_array_in_one_formula_full
      (f:formula):formula=
  let f = translate_array_relation f in
  let nf = translate_out_array_in_one_formula f in
  let dnf = drop_array_formula nf in
  dnf
;;

let translate_out_array_in_one_formula_full
      (f:formula):formula=
  if !Globals.array_translate then translate_out_array_in_one_formula_full f
  else f
;;

let translate_out_array_in_one_formula_full
      (f:formula):formula=
  let pf = !print_pure in
  Debug.no_1 "translate_out_array_in_one_formula_full" pf pf (fun f -> translate_out_array_in_one_formula_full f) f
;;
