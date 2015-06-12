#include "xdebug.cppo"
open VarGen
(* Created on 20th Dec 2012 by asankhs to handle Infinity *)

open Globals
open Gen
open Cprinter

module CP = Cpure
module MCP = Mcpure
module DD = Debug
open CP

type  pai_num = Bottom | Neg_inf | Pos_inf | Finite

(* Equisatisfiable Normalization *)
(* 
   v<=\inf      ==> true
   v>=\inf      ==> v=\inf
   v<=-\inf     ==> v=-\inf
   v>=-\inf     ==> true
   min(w,\inf)  ==> w
   min(w,-\inf) ==> -\inf
   max(w,\inf)  ==> \inf
   max(w,-\inf) ==> w
   v<inf        ==> not(v=inf)
   v>inf        ==> false
   v<-inf       ==> false
   v>-inf       ==> not(v=-inf)
   \inf!=c      ==> true
   \inf=c       ==> false
   \inf<=c      ==> false
   \inf>c       ==> true
*)

(*
Normalizes Min and Max Exp as per the rules
   min(w,\inf)  ==> w
   min(w,-\inf) ==> -\inf
   max(w,\inf)  ==> \inf
   max(w,-\inf) ==> w
*)
let rec normalize_exp (exp: CP.exp) : CP.exp =
  let () = DD.vv_trace("in normalize_exp: "^ (string_of_formula_exp exp)) in
  (*let exp = CP.norm_exp exp in*)
  match exp with
  | CP.Min(e1,e2,pos) -> 
    let e1_norm = normalize_exp e1 in
    let e2_norm = normalize_exp e2 in
    if CP.is_const_or_var e1_norm && CP.is_inf e2_norm then e1_norm
    else if CP.is_inf e1_norm && CP.is_const_or_var e2_norm then e2_norm
    else CP.Min(e1_norm,e2_norm,pos)
  | CP.Max(e1,e2,pos) -> 
    let e1_norm = normalize_exp e1 in
    let e2_norm = normalize_exp e2 in
    if CP.is_const_or_var e1_norm && CP.is_inf e2_norm then e2_norm
    else if CP.is_inf e1_norm && CP.is_const_or_var e2_norm then e1_norm
    else CP.Max(e1_norm,e2_norm,pos)
  | CP.Add(e1,e2,pos) -> 
    let rec helper e1 e2 = 
      let e1_norm = normalize_exp e1 in
      let e2_norm = normalize_exp e2 in
      if CP.is_inf e1_norm && CP.is_inf e2_norm then e1_norm else 
      if CP.is_const_exp e1_norm && CP.is_inf e2_norm
      then e2_norm
      else if CP.is_inf e1_norm && CP.is_const_exp e2_norm
      then e1_norm
      else match e1_norm with
        | CP.Add(e3,e4,pos) -> let e5  = CP.Add(e4,e2_norm,pos) in helper e3 e5
        | _ -> CP.Add(e1_norm,e2_norm,pos)
    in helper e1 e2
  | CP.NegInfConst _  -> if !Globals.allow_inf_qe_coq then exp else CP.mkNegInfConst no_pos
  | _ -> exp

let normalize_exp (exp: CP.exp) : CP.exp =
  Debug.no_1 "infinity.normalize_exp" string_of_formula_exp string_of_formula_exp normalize_exp exp 

(* normalize 
   \inf+v = 0 ==> v=-\inf
   \inf+v op \inf ==>  \inf op \inf, for op be =,>,<,>= etc
   \inf+v op w+\inf ==>  \inf op \inf, for op be =,>,<,>= etc *)
let check_var_add_inf (exp1: CP.exp) (exp2: CP.exp) : bool * CP.exp = 
  let aux exp1 exp2 = match exp1 with
    | CP.Add(e1,e2,pos) -> let flag = (CP.is_var e1 && CP.is_inf e2) || (CP.is_var e2 && CP.is_inf e1) in
      if flag  && CP.is_inf exp2 then true,exp2 else 
        (match exp2 with
         | CP.Add(e1,e2,pos) -> if flag && (CP.is_var e1 && CP.is_inf e2) then true,e2
           else if (CP.is_var e2 && CP.is_inf e1) then true,e1
           else false,exp2
         | _ -> false,exp1)
    | _ -> false,exp1
  in let f1,e1 = (aux exp1 exp2) in
  if f1 then f1,e1 else (aux exp2 exp1)

(* normalize \inf <= const + var ~~> \inf <= var and so on *)
let check_const_add_inf (exp: CP.exp) : bool * CP.exp = 
  match exp with
  | CP.Add(e1,e2,pos) -> if CP.is_const_or_tmp e1 then (true,e2)
    else if CP.is_const_or_tmp e2 then (true,e1) else false,exp
  | _ -> false,exp

(* similar to above but for -\inf: 0 <= const + var + \inf  ~~> 0 <= var + \inf and so on *)
let check_const_add_neg_inf (exp1: CP.exp) (exp2: CP.exp) : bool * CP.exp = 
  match exp2 with
  | CP.IConst(b,_) -> if b == 0 then (match exp1 with
      | CP.Add(e1,e2,pos) ->  (match e1 with 
          | CP.Add(e3,e4,pos) -> if CP.is_inf e2 && CP.is_const_or_tmp e3 then true,CP.Add(e4,e2,pos) 
            else if CP.is_inf e2 && CP.is_const_or_tmp e4 then true,CP.Add(e3,e2,pos)
            else if CP.is_inf e3 && CP.is_const_or_tmp e2 then true,CP.Add(e3,e4,pos) 
            else if CP.is_inf e3 && CP.is_const_or_tmp e4 then true,CP.Add(e3,e2,pos)
            else if CP.is_inf e4 && CP.is_const_or_tmp e3 then true,CP.Add(e4,e2,pos) 
            else if CP.is_inf e4 && CP.is_const_or_tmp e2 then true,CP.Add(e3,e4,pos)
            else false,exp1
          | _ -> (match e2 with 
              | CP.Add(e3,e4,pos) ->  if CP.is_inf e1 && CP.is_const_or_tmp e3 then true,CP.Add(e1,e4,pos) 
                else if CP.is_inf e1 && CP.is_const_or_tmp e4 then true,CP.Add(e1,e3,pos)
                else if CP.is_inf e3 && CP.is_const_or_tmp e1 then true,CP.Add(e3,e4,pos) 
                else if CP.is_inf e3 && CP.is_const_or_tmp e4 then true,CP.Add(e1,e3,pos)
                else if CP.is_inf e4 && CP.is_const_or_tmp e3 then true,CP.Add(e1,e4,pos) 
                else if CP.is_inf e4 && CP.is_const_or_tmp e1 then true,CP.Add(e3,e4,pos)
                else false,exp1
              | _ -> false,exp1))
      | _ -> false,exp1)
    else false,exp2
  | _ -> false,exp2

(*
 a+b<\inf   <--> a<\inf & b<\inf
 a+b<=\inf  <--> true
-\inf<a+b  <--> -\inf<a & -\inf<b
 -\inf<=a+b <--> true
 a+b=\inf   <--> (a=\inf | b=\inf)
 a+b=-\inf  <--> (a=-\inf | b=-\inf)
 \inf<=a+b  <--> a+b=\inf  <--> (a=\inf | b=\inf)
 -\inf>=a+b <--> a+b=-\inf <--> (a=-\inf | b=-\inf)
*)
let split_inf_add (exp1: CP.exp) (exp2: CP.exp) pos : bool *CP.exp * CP.exp = 
  match exp1,exp2 with
  | CP.Add(e1,e2,_),e -> if is_inf e then (true,e1,e2) else (false,exp1,exp2)
  | _ , _ -> false,exp1,exp2

let split_inf_add (exp1: CP.exp) (exp2: CP.exp) pos : bool *CP.exp * CP.exp = 
  let pr  = string_of_formula_exp in 
  DD.no_2 "split_inf_add"  pr pr (fun (a,b,c) -> string_of_bool a) 
    (fun e1 e2 -> split_inf_add e1 e2 pos) exp1 exp2

let split_neg_inf_add (exp1: CP.exp) (exp2: CP.exp) pos : bool *CP.exp * CP.exp = 
  match exp1,exp2 with
  | CP.IConst(0,_),CP.Add(e1,e2,_) -> (match e1,e2 with
      | CP.Add(e3,e4,pos), e
      | e,CP.Add(e3,e4,pos) -> 
        let (f,er1,er2) as rt = split_inf_add (CP.Add(e3,e4,pos)) e pos in
        if f then rt 
        else let (f,er1,er2) as rt = split_inf_add e3 (CP.Add(e,e4,pos)) pos in
          if f then rt else 
            let (f,er1,er2) as rt = split_inf_add (CP.Add(e,e4,pos)) e3 pos in
            if f then rt else false,exp1,exp2
      | _ -> false,exp1,exp2)
  | _ , _ -> false,exp1,exp2


(*
--eps converts v>w to 1+w <= v detect it and revert back to substitute \inf during normalization
*)
let check_leq (exp1: CP.exp) (exp2: CP.exp) pos : CP.p_formula = 
  match exp1,exp2 with
  | CP.Add(e1,e2,_),CP.Var(sv,_) -> 
    if is_one e1 && is_var e2 then Gt(exp2,e2,pos)
    else if is_var e1 && is_one e2 then Gt(exp2,e1,pos)
    else Lte(exp1,exp2,pos)
  | _ -> Lte(exp1,exp2,pos)
(* 
Returns true if both side of exp1 is \inf 
used to handle rules with infinity in both sides
   \inf+\inf=0   ==> false
     // \inf=-\inf  ==> false
   \inf+c+\inf=0 ==> ?false
     // \inf+c=-\inf  ==> ?false?
*)

let check_neg_inf2_inf (exp1: CP.exp) (exp2: CP.exp) : bool = 
  match exp1,exp2 with
  | CP.Var(sv1,_),CP.Var(sv2,_) -> if is_inf_sv sv1 && is_inf_sv sv2 then
      if (is_primed sv1 && not(is_primed sv2)) || (is_primed sv2 && not(is_primed sv1))
      then true else false
    else false 
  | _ -> (
      match exp1 with
      | CP.Add(e1,e2,pos) ->
        (* WN : why dos e1,e2 need to be both \inf? *)
        if CP.is_inf e1 && CP.is_inf e2
        then
          if CP.is_int exp2
          then
            (match exp2 with
             | CP.IConst(b,_) -> if b == 0 then true else false
             | _ -> false)
          else false
        else false
      | _ -> false)

(*
Return true if exp1 is \inf and exp2 is const
used to detect c = -\inf as c + \inf = 0 
*)
let check_neg_inf2_const (exp1: CP.exp) (exp2: CP.exp) : bool = 
  match exp1 with
  | CP.Add(e1,e2,pos) -> 
    if (CP.is_inf e1 && CP.is_const_exp e2) || (CP.is_inf e2 && CP.is_const_exp e1)
    then 
      if CP.is_int exp2
      then (match exp2 with
          | CP.IConst(b,_) -> if b == 0 then true else false
          | _ -> false)
      else false
    else false
  | _ -> false

(*
Return true if exp1 is \inf or exp2 is \inf
used to detect v = -\inf as v + \inf = 0 
*)

let check_neg_inf2 (exp1: CP.exp) (exp2: CP.exp) : bool = 
  match exp1 with
  | CP.Add(e1,e2,pos) -> 
    if CP.is_inf e1 || CP.is_inf e2 
    then
      if CP.is_int exp2
      then (match exp2 with
          | CP.IConst(b,_) -> if b == 0 then true else false
          | _ -> false)
      else false
    else false
  | _ -> false

(*
Same as check_neg_inf2 but with 3 exps used for EqMax and EqMin
*)
let check_neg_inf (exp1: CP.exp) (exp2: CP.exp) (exp3: CP.exp) 
  : bool * CP.exp * CP.exp = 
  match exp1 with
  | CP.Add(a1,a2,pos) -> 
    let oexp = 
      if CP.is_inf a1 then a2 
      else 
      if CP.is_inf a2 then a1 else exp1 
    in
    (match exp2 with
     | CP.Add(e1,e2,pos) -> 
       let flag = 
         if CP.is_inf e1 || CP.is_inf e2 
         then
           if CP.is_int exp3
           then (match exp3 with
               | CP.IConst(b,_) -> if b == 0 then true else false
               | _ -> false)
           else false
         else false
       in let exp = 
         if CP.is_inf e1 then e2 
         else 
         if CP.is_inf e2 then e1 else exp2
       in flag,oexp,exp
     | _ -> match exp3 with
       | CP.Add(e1,e2,pos) -> 
         let flag = 
           if CP.is_inf e1 || CP.is_inf e2 
           then
             if CP.is_int exp2
             then (match exp2 with
                 | CP.IConst(b,_) -> 
                   if b == 0 then true else false
                 | _ -> false)
             else false
           else false
         in let exp = 
           if CP.is_inf e1 then e2 
           else 
           if CP.is_inf e2 then e1 else exp3
         in flag,oexp,exp
       | _ -> false,exp2,exp3)
  | _ -> false,exp2,exp3

let contains_inf_or_inf_var (f:CP.formula) : bool = 
  let f_f f = None in
  let f_bf f = let bf,_ = f in
    match bf with
    | CP.XPure _
    | CP.LexVar _
    | CP.BConst _
    | CP.BVar _ -> Some(false)
    | _ -> None in
  let f_e f = 
    match f with
    | InfConst _ ->  Some(true) 
    | Var _ -> if is_inf f then Some(true) else Some(false)
    | Null _ | IConst _ | FConst _ | AConst _ | Tsconst _ -> Some(false)
    | _ -> None
  in fold_formula f (f_f,f_bf,f_e) (List.exists (fun c -> c))

let contains_inf (f:CP.formula) : bool = 
  let f_f f = None in
  let f_bf f = let bf,_ = f in
    match bf with
    | CP.XPure _
    | CP.LexVar _
    | CP.BConst _
    | CP.BVar _ -> Some(false)
    | _ -> None in
  let f_e f = 
    match f with
    | InfConst _ -> Some(true)
    | NegInfConst _ -> Some(true)
    | Null _ | Var _ | IConst _ | FConst _ | AConst _ | Tsconst _ -> Some(false)
    | _ -> None
  in fold_formula f (f_f,f_bf,f_e) (List.exists (fun c -> c))

let contains_inf (f:CP.formula) : bool = 
  let pr = string_of_pure_formula in
  DD.no_1 "contains_inf" pr string_of_bool contains_inf f


let simplify_b_formula (bf: CP.b_formula) : CP.b_formula * (CP.b_formula list) = 
  let rec helper p_f split_p_f_lst = 
    match p_f with
    | CP.Lt(e1,e2,pos) -> let f,e1_split,e2_split = split_inf_add e1 e2 pos in
      let e1_p_f = CP.Lt(e1_split,(mkInfConst pos),pos) in
      let e2_p_f = CP.Lt(e2_split,(mkInfConst pos),pos) in
      if f then CP.BConst(true,pos),(e1_p_f::e2_p_f::split_p_f_lst)
      else let f,e1_nsplit,e2_nsplit = split_neg_inf_add e1 e2 pos in 
        let e1_p_f = CP.Gt(CP.Add(e1_nsplit,(mkInfConst pos),pos),CP.IConst(0,pos),pos) in
        let e2_p_f = CP.Gt(CP.Add(e2_nsplit,(mkInfConst pos),pos),CP.IConst(0,pos),pos) in
        if f then CP.BConst(true,pos),(e1_p_f::e2_p_f::split_p_f_lst)
        else p_f,split_p_f_lst
    | CP.Lte(e1,e2,pos) -> let f,e1_split,e2_split = split_inf_add e1 e2 pos in
      if f then CP.BConst(true,pos),split_p_f_lst
      else let f,e1_nsplit,e2_nsplit = split_neg_inf_add e1 e2 pos in 
        if f then CP.BConst(true,pos),split_p_f_lst
        else p_f,split_p_f_lst
    | CP.Gt(e1,e2,pos) -> let f,e1_split,e2_split = split_inf_add e2 e1 pos in
      let e1_p_f = CP.Lt(e1_split,(mkInfConst pos),pos) in
      let e2_p_f = CP.Lt(e2_split,(mkInfConst pos),pos) in
      if f then CP.BConst(true,pos),(e1_p_f::e2_p_f::split_p_f_lst)
      else let f,e1_nsplit,e2_nsplit = split_neg_inf_add e2 e1 pos in 
        let e1_p_f = CP.Gt(CP.Add(e1_nsplit,(mkInfConst pos),pos),CP.IConst(0,pos),pos) in
        let e2_p_f = CP.Gt(CP.Add(e2_nsplit,(mkInfConst pos),pos),CP.IConst(0,pos),pos) in
        if f then CP.BConst(true,pos),(e1_p_f::e2_p_f::split_p_f_lst)
        else p_f,split_p_f_lst
    | CP.Gte(e1,e2,pos) -> let f,e1_split,e2_split = split_inf_add e2 e1 pos in
      if f then CP.BConst(true,pos),split_p_f_lst 
      else let f,e1_nsplit,e2_nsplit = split_neg_inf_add e2 e1 pos in 
        if f then CP.BConst(true,pos),split_p_f_lst
        else p_f,split_p_f_lst
    | _ -> p_f,split_p_f_lst
  in let p_f,bf_ann = bf in 
  let p_f,xs = helper p_f [] in
  let xs_bf = List.map (fun c -> (c,bf_ann)) xs in
  (p_f,bf_ann),xs_bf 
let simplify_b_formula (bf: CP.b_formula) : CP.b_formula * (CP.b_formula list) = 
  let pr = string_of_b_formula in 
  DD.no_1 "infinity.simplify_b_formula" pr (fun c -> pr (fst c)) simplify_b_formula bf
(*
Normalize b_formula containing \inf 
*)

let rec normalize_b_formula (bf: CP.b_formula) :CP.b_formula = 
  let () = DD.vv_trace("in normalize_b_formula: "^ (string_of_b_formula bf)) in
  (*let () = Gen.Profiling.push_time "INF-Normalize" in*)
  let rec helper p_f =
    (*let p_f_norm =*)
    (match p_f with
     | CP.Lt(e1,e2,pos) -> 
       let e1_norm = normalize_exp e1 in
       let e2_norm = normalize_exp e2 in
       if check_neg_inf2_inf e1_norm e2_norm then CP.BConst(false,pos)
       else if check_neg_inf2_inf e2_norm e1_norm then CP.BConst(true,pos)
       else if check_neg_inf2_const e2_norm e1_norm then CP.BConst(true,pos)
       else if CP.is_const_exp e1_norm && CP.is_inf e2_norm then CP.BConst(true,pos)
       (*else if CP.is_const_or_var e1_norm && CP.is_inf e2_norm then CP.Neq(e1_norm,e2_norm,pos)*)
       else if CP.is_inf e1_norm && CP.is_const_or_var e2_norm then CP.BConst(false,pos)
       else if check_neg_inf2 e1_norm e2_norm then CP.BConst(false,pos)
       (*else if check_neg_inf2 e2_norm e1_norm then CP.Neq(e1_norm,e2_norm,pos)*)
       else if fst(check_const_add_inf e1_norm) && CP.is_inf e2_norm then 
         let ec = snd (check_const_add_inf e1_norm) in helper (CP.Lt(ec,e2_norm,pos))
       else if fst(check_const_add_inf e2_norm) && CP.is_inf e1_norm then 
         let ec = snd (check_const_add_inf e2_norm) in helper (CP.Lt(e1_norm,ec,pos))
       else if fst(check_const_add_neg_inf e1_norm e2_norm) then
         let ec = snd(check_const_add_neg_inf e1_norm e2_norm) in helper (CP.Lt(ec,e2_norm,pos)) 
       else if fst(check_const_add_neg_inf e2_norm e1_norm) then
         let ec = snd(check_const_add_neg_inf e2_norm e1_norm) in helper (CP.Lt(e1_norm,ec,pos)) 
       else let f,e = (check_var_add_inf e1_norm e2_norm) in if f then helper (CP.Lt(e,e,pos)) 
         else CP.Lt(e1_norm,e2_norm,pos)
     | CP.Lte(e1,e2,pos) -> 
       let e1_norm = normalize_exp e1 in
       let e2_norm = normalize_exp e2 in
       if check_neg_inf2_inf e1_norm e2_norm then CP.BConst(false,pos)
       else if check_neg_inf2_inf e2_norm e1_norm then CP.BConst(true,pos)
       else if check_neg_inf2_const e1_norm e2_norm then CP.BConst(false,pos)
       else if CP.is_inf e1_norm && CP.is_const_exp e2_norm then CP.BConst(false,pos)
       else if CP.is_const_or_var e1_norm && CP.is_inf e2_norm then CP.BConst(true,pos)
       else if CP.is_inf e1_norm && CP.is_const_or_var e2_norm then CP.Eq(e1_norm,e2_norm,pos)
       else if check_neg_inf2 e1_norm e2_norm then CP.Eq(e1_norm,e2_norm,pos)
       else if check_neg_inf2 e2_norm e1_norm then CP.BConst(true,pos)
       else if fst(check_const_add_inf e1_norm) && CP.is_inf e2_norm then 
         let ec = snd (check_const_add_inf e1_norm) in helper (CP.Lte(ec,e2_norm,pos))
       else if fst(check_const_add_inf e2_norm) && CP.is_inf e1_norm then 
         let ec = snd (check_const_add_inf e2_norm) in helper (CP.Lte(e1_norm,ec,pos))
       else if fst(check_const_add_neg_inf e1_norm e2_norm) then
         let ec = snd(check_const_add_neg_inf e1_norm e2_norm) in helper (CP.Lte(ec,e2_norm,pos)) 
       else if fst(check_const_add_neg_inf e2_norm e1_norm) then
         let ec = snd(check_const_add_neg_inf e2_norm e1_norm) in helper (CP.Lte(e1_norm,ec,pos))
       else let f,e = (check_var_add_inf e1_norm e2_norm) in if f then helper (CP.Lte(e,e,pos)) 
         else check_leq e1_norm e2_norm pos (*CP.Lte(e1_norm,e2_norm,pos)*)
     | CP.Gt(e1,e2,pos) -> 
       let e1_norm = normalize_exp e1 in
       let e2_norm = normalize_exp e2 in
       if check_neg_inf2_inf e1_norm e2_norm then CP.BConst(true,pos)
       else if check_neg_inf2_inf e2_norm e1_norm then CP.BConst(false,pos)
       else if check_neg_inf2_const e1_norm e2_norm then CP.BConst(true,pos)
       else if CP.is_inf e1_norm && CP.is_const_exp e2_norm then CP.BConst(true,pos)
       else if CP.is_const_or_var e1_norm && CP.is_inf e2_norm then CP.BConst(false,pos)
       (*else if CP.is_inf e1_norm && CP.is_const_or_var e2_norm then CP.Neq(e1_norm,e2_norm,pos)
         else if check_neg_inf2 e1_norm e2_norm then CP.Neq(e1_norm,e2_norm,pos)*)
       else if check_neg_inf2 e2_norm e1_norm then CP.BConst(false,pos)
       else if fst(check_const_add_inf e1_norm) && CP.is_inf e2_norm then 
         let ec = snd (check_const_add_inf e1_norm) in helper (CP.Gt(ec,e2_norm,pos))
       else if fst(check_const_add_inf e2_norm) && CP.is_inf e1_norm then 
         let ec = snd (check_const_add_inf e2_norm) in helper (CP.Gt(e1_norm,ec,pos))
       else if fst(check_const_add_neg_inf e1_norm e2_norm) then
         let ec = snd(check_const_add_neg_inf e1_norm e2_norm) in helper (CP.Gt(ec,e2_norm,pos)) 
       else if fst(check_const_add_neg_inf e2_norm e1_norm) then
         let ec = snd(check_const_add_neg_inf e2_norm e1_norm) in helper (CP.Gt(e1_norm,ec,pos))
       else let f,e = (check_var_add_inf e1_norm e2_norm) in if f then helper (CP.Gt(e,e,pos)) 
         else CP.Gt(e1_norm,e2_norm,pos)
     | CP.Gte(e1,e2,pos) -> 
       let e1_norm = normalize_exp e1 in
       let e2_norm = normalize_exp e2 in
       if check_neg_inf2_inf e1_norm e2_norm then CP.BConst(true,pos)
       else if check_neg_inf2_inf e2_norm e1_norm then CP.BConst(false,pos)
       else if CP.is_inf e1_norm && CP.is_inf e2_norm then CP.BConst(true,pos) else
       if check_neg_inf2_const e2_norm e1_norm then CP.BConst(false,pos)
       else if CP.is_const_exp e1_norm && CP.is_inf e2_norm then CP.BConst(false,pos)
       else if CP.is_const_or_var e1_norm && CP.is_inf e2_norm then CP.Eq(e1_norm,e2_norm,pos)
       else if CP.is_inf e1_norm && CP.is_const_or_var e2_norm then CP.BConst(true,pos)
       else if check_neg_inf2 e1_norm e2_norm then CP.BConst(true,pos)
       else if check_neg_inf2 e2_norm e1_norm then CP.Eq(e1_norm,e2_norm,pos)
       else if fst(check_const_add_inf e1_norm) && CP.is_inf e2_norm then 
         let ec = snd (check_const_add_inf e1_norm) in helper (CP.Gte(ec,e2_norm,pos))
       else if fst(check_const_add_inf e2_norm) && CP.is_inf e1_norm then 
         let ec = snd (check_const_add_inf e2_norm) in helper (CP.Gte(e1_norm,ec,pos))
       else if fst(check_const_add_neg_inf e1_norm e2_norm) then
         let ec = snd(check_const_add_neg_inf e1_norm e2_norm) in helper (CP.Gte(ec,e2_norm,pos)) 
       else if fst(check_const_add_neg_inf e2_norm e1_norm) then
         let ec = snd(check_const_add_neg_inf e2_norm e1_norm) in helper (CP.Gte(e1_norm,ec,pos))
       else let f,e = (check_var_add_inf e1_norm e2_norm) in if f then helper (CP.Gte(e,e,pos)) 
         else CP.Gte(e1_norm,e2_norm,pos)
     | CP.Eq (e1,e2,pos) -> 
       let e1_norm = normalize_exp e1 in
       let e2_norm = normalize_exp e2 in
       if check_neg_inf2_inf e1_norm e2_norm || check_neg_inf2_inf e2_norm e1_norm 
       then CP.BConst(false,pos)
       else if CP.is_inf e1_norm && CP.is_inf e2_norm then CP.BConst(true,pos)
       else if CP.is_const_exp e1_norm && CP.is_inf e2_norm then CP.BConst(false,pos)
       else if CP.is_inf e1_norm && CP.is_const_exp e2_norm then CP.BConst(false,pos)
       else if check_neg_inf2_const e1_norm e2_norm || check_neg_inf2_const e2_norm e1_norm 
       then CP.BConst(false,pos)
       else if fst(check_const_add_inf e1_norm) && CP.is_inf e2_norm then 
         let ec = snd (check_const_add_inf e1_norm) in helper (CP.Eq(ec,e2_norm,pos))
       else if fst(check_const_add_inf e2_norm) && CP.is_inf e1_norm then 
         let ec = snd (check_const_add_inf e2_norm) in helper (CP.Eq(e1_norm,ec,pos))
       else if fst(check_const_add_neg_inf e1_norm e2_norm) then
         let ec = snd(check_const_add_neg_inf e1_norm e2_norm) in helper (CP.Eq(ec,e2_norm,pos)) 
       else if fst(check_const_add_neg_inf e2_norm e1_norm) then
         let ec = snd(check_const_add_neg_inf e2_norm e1_norm) in helper (CP.Eq(e1_norm,ec,pos))
       else let f,e = (check_var_add_inf e1_norm e2_norm) in if f then helper (CP.Eq(e,e,pos)) 
         else CP.Eq(e1_norm,e2_norm,pos)
     | CP.Neq (e1,e2,pos) -> 
       let e1_norm = normalize_exp e1 in
       let e2_norm = normalize_exp e2 in
       if check_neg_inf2_inf e1_norm e2_norm || check_neg_inf2_inf e2_norm e1_norm 
       then CP.BConst(true,pos)
       else if CP.is_inf e1_norm && CP.is_inf e2_norm then CP.BConst(false,pos)
       else if CP.is_const_exp e1_norm && CP.is_inf e2_norm then CP.BConst(true,pos)
       else if CP.is_inf e1_norm && CP.is_const_exp e2_norm then CP.BConst(true,pos)
       else if check_neg_inf2_const e1_norm e2_norm || check_neg_inf2_const e2_norm e1_norm
       then CP.BConst(true,pos)
       else if CP.is_inf e1_norm then CP.Lt(e2_norm,e1_norm,pos)
       else if CP.is_inf e2_norm then CP.Lt(e1_norm,e2_norm,pos)
       else if check_neg_inf2 e1_norm e2_norm then CP.Gt(e1_norm,e2_norm,pos) 
       else if check_neg_inf2 e2_norm e1_norm then CP.Gt(e2_norm,e1_norm,pos) 
       else let f,e = (check_var_add_inf e1_norm e2_norm) in if f then helper (CP.Neq(e,e,pos))
         else CP.Neq(e1_norm,e2_norm,pos)                            
     | CP.EqMax (e1,e2,e3,pos) -> 
       let flag,w1,w2 = check_neg_inf e1 e2 e3 in
       (*let () = if flag then print_string("True") else print_string("False") in
         let () = print_string("w1: "^(string_of_formula_exp w1)^"\n") in
         			let () = print_string("w2: "^(string_of_formula_exp w2)^"\n") in*)
       if flag then CP.Eq(w1,w2,pos)
       else
         let e1_norm = normalize_exp e1 in
         let e2_norm = normalize_exp e2 in
         let e3_norm = normalize_exp e3 in
         if check_neg_inf2 e2_norm e3_norm then Eq(e1_norm,e3_norm,pos)
         else if check_neg_inf2 e3_norm e2_norm then Eq(e1_norm,e2_norm,pos)
         else if CP.is_const_or_var e2_norm && CP.is_inf e3_norm then CP.Eq(e1_norm,e3_norm,pos)
         else if CP.is_inf e2_norm && CP.is_const_or_var e3_norm then CP.Eq(e1_norm,e2_norm,pos)
         else CP.EqMax(e1_norm,e2_norm,e3_norm,pos)
     | CP.EqMin (e1,e2,e3,pos) -> 
       let flag,w1,w2 = check_neg_inf e1 e2 e3 in
       if flag then CP.Eq(e1,(CP.mkIConst 0 pos),pos)
       else 
         let e1_norm = normalize_exp e1 in   
         let e2_norm = normalize_exp e2 in
         let e3_norm = normalize_exp e3 in
         if check_neg_inf2 e2_norm e3_norm then Eq(e1_norm,e2_norm,pos)
         else if check_neg_inf2 e3_norm e2_norm then Eq(e1_norm,e3_norm,pos)
         else if CP.is_const_or_var e2_norm && CP.is_inf e3_norm then CP.Eq(e1_norm,e2_norm,pos)
         else if CP.is_inf e2_norm && CP.is_const_or_var e3_norm then CP.Eq(e1_norm,e3_norm,pos)
         else CP.EqMin(e1_norm,e2_norm,e3_norm,pos)
     | _ -> p_f
    ) in  
  let (p_f,bf_ann) = bf in
  let () = DD.vv_trace("in normalized_b_formula: "^ (string_of_b_formula (p_f,bf_ann))) in
  (*let () = Gen.Profiling.pop_time "INF-Normalize" in*)
  ((helper p_f),bf_ann)

(* 
Main func normalization starts here
*)
let rec normalize_inf_formula (pf: CP.formula) : CP.formula = 
  let () = DD.vv_trace("in normalize_inf_formula: "^ (string_of_pure_formula pf)) in
  (*if not (contains_inf_or_inf_var pf) then pf else*)
  (match pf with 
   | CP.BForm (b,fl) -> 
     let b_norm = normalize_b_formula b in
     (*let bf =  CP.BForm(b_norm,fl) in *)
     let b,b_xs = simplify_b_formula b_norm in
     if List.length b_xs > 0 
     then let pf_lst = List.map (fun c -> CP.BForm(c,fl)) b_xs 
       in let pf = conj_of_list (CP.BForm(b,fl)::pf_lst) no_pos in normalize_inf_formula pf
     else CP.BForm(b,fl)
   (*let mkInfVar  = SpecVar (Int, zinf_str, Unprimed) in
     let mkNegInfVar =  SpecVar (Int, zinf_str, Primed) in
     let axiom = mkNeqVar mkInfVar mkNegInfVar no_pos in
     let b_norm  = mkAnd bf axiom no_pos in b_norm*)
   | CP.And (pf1,pf2,pos) -> 
     (*let () = Gen.Profiling.push_time "INF-Normalize_And" in*)
     (*let () = print_string("pf1: "^(string_of_pure_formula pf1)^"\n") in*)
     let pf1_norm = normalize_inf_formula pf1 in
     let pf2_norm = normalize_inf_formula pf2 in
     (*let () = Gen.Profiling.pop_time "INF-Normalize_And" in*)
     CP.And(pf1_norm,pf2_norm,pos) 
   | CP.AndList pflst -> 
     let pflst_norm = List.map 
         (fun (sl,pf) -> (sl,normalize_inf_formula pf)) pflst in CP.AndList(pflst_norm)
   | CP.Or (pf1,pf2,fl,pos) -> 
     let pf1_norm = normalize_inf_formula pf1 in
     let pf2_norm = normalize_inf_formula pf2 in
     CP.Or(pf1_norm,pf2_norm,fl,pos) 
   | CP.Not (nf,fl,pos) -> 
     let nf_norm = normalize_inf_formula nf in CP.Not(nf_norm,fl,pos)
   | CP.Forall (qid, qf,fl,pos) -> 
     let qf_norm = normalize_inf_formula qf in CP.Forall(qid,qf_norm,fl,pos)
   | CP.Exists (qid, qf,fl,pos) -> 
     let qf_norm = normalize_inf_formula qf in CP.Exists(qid,qf_norm,fl,pos))

(* convert \inf to Zinfinity and -\inf to ZinfinityPRMD
   and add ZinfintyPRMD < Zinfinity *)

let convert_inf_to_var (pf:CP.formula) : CP.formula =
  let f_f f = None in
  let f_bf_neg bf = let (f,l) = bf in 
    match f with
    | Eq(e1,e2,pos) (*| Neq(e1,e2,pos) | 
                      Lt(e1,e2,pos) | Gt(e1,e2,pos) |
                      Lte(e1,e2,pos) | Gte(e1,e2,pos)*)
      -> (*let e1,e2 = normalize_exp e1,normalize_exp e2 in *)
      if check_neg_inf2 e1 e2 
      then (match e1 with 
          | Add(a1,a2,pos) -> if is_inf a1 && is_inf a2 then Some(mkFalse_b pos)
            else if is_inf a1 
            then Some(Eq(CP.Var(CP.SpecVar(Int,constinfinity,Primed),pos),a2,pos),l)
            else Some(Eq(a1,CP.Var(CP.SpecVar(Int,constinfinity,Primed),pos),pos),l)
          | _ -> Some(Eq(e1,e2,pos),l))
      else if check_neg_inf2 e2 e1
      then (match e2 with 
          | Add(a1,a2,pos) -> if is_inf a1 && is_inf a2 then Some(mkFalse_b pos)
            else if is_inf a1 
            then Some(Eq(CP.Var(CP.SpecVar(Int,constinfinity,Primed),pos),a2,pos),l)
            else Some(Eq(a1,CP.Var(CP.SpecVar(Int,constinfinity,Primed),pos),pos),l)
          | _ -> Some(Eq(e1,e2,pos),l))
      else None
    | _ -> None in
  let f_bf bf = None in 
  let f_e_neg e = Some(normalize_exp e) in
  let f_e e =
    match e with
    | CP.InfConst (i,pos) -> Some (CP.Var(CP.SpecVar(Int,i,Unprimed),pos))
    | CP.NegInfConst (i,pos) -> Some (CP.Var(CP.SpecVar(Int,i,Primed),pos))
    | _ -> None
  in
  let pf = map_formula pf (f_f,f_bf_neg,f_e_neg) in
  map_formula pf (f_f,f_bf,f_e)

let convert_inf_to_var (pf:CP.formula) : CP.formula =
  Debug.no_1 "convert_inf_to_var" string_of_pure_formula string_of_pure_formula 
    convert_inf_to_var pf 

let convert_var_to_inf (pf:CP.formula) : CP.formula =
  let f_f f = None in
  let f_bf bf = None in
  let f_e e = 
    match e with
    | Var(sv,pos) -> if is_inf e 
      then if not(is_primed sv) then Some (mkInfConst pos) else 
        if (!Globals.allow_inf_qe_coq) then Some(NegInfConst(zinf_str,pos)) else Some(mkNegInfConst pos) 
      else None
    | _ -> None
  in
  map_formula pf (f_f,f_bf,f_e)

let rec contains_inf_eq_b_formula (bf: CP.b_formula) : bool = 
  let (p_f,bf_ann) = bf in
  match p_f with
  | CP.Frm _
  | CP.XPure _
  | CP.LexVar _
  | CP.ImmRel _
  | CP.BConst _
  | CP.BVar _ -> false
  | CP.Lt (e1,e2,pos) 
  | CP.Lte (e1,e2,pos)
  | CP.Gt (e1,e2,pos)
  | CP.Gte (e1,e2,pos) -> false
  | CP.Eq (e1,e2,pos) -> if CP.is_inf e1 || CP.is_inf e2 || check_neg_inf2 e1 e2 || check_neg_inf2 e2 e1 
    then  true else false
  | CP.Neq (e1,e2,pos) -> false
  | CP.SubAnn (e1,e2,pos) 
  | CP.ListIn (e1,e2,pos)
  | CP.ListNotIn (e1,e2,pos)
  | CP.ListAllN (e1,e2,pos)
  | CP.ListPerm (e1,e2,pos) -> false
  | CP.EqMax (e1,e2,e3,pos) 
  | CP.EqMin (e1,e2,e3,pos) -> false
  | CP.BagIn _
  | CP.BagNotIn _
  | CP.BagSub _
  | CP.BagMin _
  | CP.BagMax _
  (* | CP.VarPerm _ *)
  | CP.RelForm _ -> false

(*
Check if the formula contains any assignment to \inf
*)
let rec contains_inf_eq (pf:CP.formula) : bool  =
  match pf with
  | CP.BForm (b,fl) -> contains_inf_eq_b_formula b 
  | CP.And (pf1,pf2,pos) -> contains_inf_eq pf1 || contains_inf_eq pf2
  | CP.AndList pflst -> List.exists 
                          (fun (sl,pf) -> contains_inf_eq pf) pflst
  | CP.Or (pf1,pf2,fl,pos) -> contains_inf_eq pf1 || contains_inf_eq pf2
  | CP.Not (nf,fl,pos) -> contains_inf_eq nf
  | CP.Forall (qid, qf,fl,pos) 
  | CP.Exists (qid, qf,fl,pos) -> contains_inf_eq qf

let contains_inf_eq (pf:CP.formula) : bool  =
  DD.no_1 "contains_inf_eq" string_of_pure_formula string_of_bool contains_inf_eq pf 

module EM = Gen.EqMap(CP.SV)


(*
Find the substitutions with \inf 

   x=\inf & x=c \/ x+\inf=0 & x=c
   ==> [(x=\inf & x=c,[x->\inf,x->c]),
        (x+\inf=0 & x=c,[x->-\inf,x->c])
       ]
*)
let find_inf_subs (f:CP.formula) : (CP.formula * EM.emap) list =
  let ds = CP.split_disjunctions f in
  let find_inf_eq e =
    let f_f f = 
      (match f with
       | And _ | AndList _  | BForm _ -> None 
       | _ -> Some [])
    in
    let f_bf bf = 
      (match bf with
       | (Eq _),_ -> Some ([bf]) 
       | _,_ -> Some ([])
      )
    in
    let f_e e = Some ([]) in
    (* let f_arg = (fun _ _ -> ()),(fun _ _ -> ()),(fun _ _ -> ()) in *)
    (* let subs e = trans_formula e () (f_f,f_bf,f_e) f_arg List.concat in *)
    let find_eq e = fold_formula e (f_f,f_bf,f_e) List.concat in
    let pr = string_of_pure_formula in
    let prl l = pr_list string_of_b_formula l in
    let find_eq e = DD.no_1 "find_inf_subs" pr prl find_eq e in
    let eq_list = find_eq e in
    (*let eq_list_vars = List.filter (fun bf ->  let (p_f,bf_ann) = bf in
      					match p_f with
      					| Eq(e1,e2,pos) -> if is_var e1 && is_var e2 then true else false
      					| _ -> false
      			) eq_list in*)
    let eqset = EM.mkEmpty in
    let neg_inf = CP.SpecVar(Int,constinfinity,Primed) in
    let eqset = List.fold_left (fun eset exp -> 
        let (p_f,bf_ann) = exp in
        (match p_f with
         | Eq (e1,e2,pos) -> (match e1,e2 with
             | Var(sv1,_),Var(sv2,_) -> EM.add_equiv eset sv1 sv2
             | _,IConst(0,_) -> 
               (match e1 with 
                | Add(a1,a2,_) -> 
                  (match a1, a2 with 
                   | Var(sa1,_),Var(sa2,_) -> if is_inf a1 
                     then EM.add_equiv eset sa2 neg_inf
                     else if is_inf a2 then EM.add_equiv eset sa1 neg_inf
                     else eset
                   | _ -> eset)
                | _ -> eset)
             | IConst(0,_),_ -> 
               (match e2 with 
                | Add(a1,a2,_) -> 
                  (match a1, a2 with 
                   | Var(sa1,_),Var(sa2,_) -> if is_inf a1 
                     then EM.add_equiv eset sa2 neg_inf
                     else if is_inf a2 then EM.add_equiv eset sa1 neg_inf
                     else eset
                   | _ -> eset)
                | _ -> eset)
             | _ -> eset)
         | _ -> eset)
      ) eqset eq_list in eqset 
  in 
  List.map (fun e -> (e,find_inf_eq e)) ds

(*
Find the integers bounded with \inf 

   x<\inf & c<x \/ x>-\inf & c>x
   ==> [(x<\inf & c<x,[x->\inf,x->c]),
        (x>-\inf & c>x,[x->-\inf,x->c])
       ]
*)

let find_inf_bounded (f:CP.formula) : (CP.formula * EM.emap) list =
  let ds = CP.split_disjunctions f in
  let find_inf_comp e =
    let f_f f = 
      (match f with
       | And _ | AndList _  | BForm _ -> None 
       | _ -> Some [])
    in
    let f_bf bf = 
      (match bf with
       | (Lt _),_ -> Some ([bf]) 
       | _,_ -> Some ([])
      )
    in
    let f_e e = Some ([]) in
    (* let f_arg = (fun _ _ -> ()),(fun _ _ -> ()),(fun _ _ -> ()) in *)
    (* let subs e = trans_formula e () (f_f,f_bf,f_e) f_arg List.concat in *)
    let find_comp e = fold_formula e (f_f,f_bf,f_e) List.concat in
    let pr = string_of_pure_formula in
    let prl l = pr_list string_of_b_formula l in
    let find_comp e = DD.no_1 "find_inf_bounded" pr prl find_comp e in
    let eq_list = find_comp e in
    (*let eq_list_vars = List.filter (fun bf ->  let (p_f,bf_ann) = bf in
      					match p_f with
      					| Eq(e1,e2,pos) -> if is_var e1 && is_var e2 then true else false
      					| _ -> false
      			) eq_list in*)
    let eqset = EM.mkEmpty in
    let eqset = List.fold_left (fun eset exp -> 
        let (p_f,bf_ann) = exp in
        (match p_f with
         | Lt (e1,e2,pos) -> (match e1,e2 with
             | Var(sv1,_),Var(sv2,_) -> EM.add_equiv eset sv1 sv2
             (*| _,IConst(0,_) -> 
                 (match e1 with 
                    | Add(a1,a2,_) -> 
                        (match a1, a2 with 
                        | Var(sa1,_),Var(sa2,_) -> if is_inf a1 
                                       then EM.add_equiv eset sa2 neg_inf
                          else if is_inf a2 then EM.add_equiv eset sa1 neg_inf
                          else eset
                        | _ -> eset)
                    | _ -> eset)*)
             (*| IConst(0,_),_ -> 
                 (match e2 with 
                    | Add(a1,a2,_) -> 
                        (match a1, a2 with 
                        | Var(sa1,_),Var(sa2,_) -> if is_inf a1 
                                       then EM.add_equiv eset sa2 neg_inf
                          else if is_inf a2 then EM.add_equiv eset sa1 neg_inf
                          else eset
                        | _ -> eset)
                    | _ -> eset)*)
             | _ -> eset)
         | _ -> eset)
      ) eqset eq_list in eqset 
  in 
  List.map (fun e -> (e,find_inf_comp e)) ds

let find_neginf_bounded (f:CP.formula) : (CP.formula * EM.emap) list =
  let ds = CP.split_disjunctions f in
  let find_inf_comp e =
    let f_f f = 
      (match f with
       | And _ | AndList _  | BForm _ -> None 
       | _ -> Some [])
    in
    let f_bf bf = 
      (match bf with
       | (Lt _),_ -> Some ([bf]) 
       | (Gt _),_ -> Some ([bf]) 
       | _,_ -> Some ([])
      )
    in
    let f_e e = Some ([]) in
    (* let f_arg = (fun _ _ -> ()),(fun _ _ -> ()),(fun _ _ -> ()) in *)
    (* let subs e = trans_formula e () (f_f,f_bf,f_e) f_arg List.concat in *)
    let find_comp e = fold_formula e (f_f,f_bf,f_e) List.concat in
    let pr = string_of_pure_formula in
    let prl l = pr_list string_of_b_formula l in
    let find_comp e = DD.no_1 "find_neginf_bounded" pr prl find_comp e in
    let eq_list = find_comp e in
    (*let eq_list_vars = List.filter (fun bf ->  let (p_f,bf_ann) = bf in
      					match p_f with
      					| Eq(e1,e2,pos) -> if is_var e1 && is_var e2 then true else false
      					| _ -> false
      			) eq_list in*)
    let eqset = EM.mkEmpty in
    let neg_inf = CP.SpecVar(Int,constinfinity,Primed) in
    let eqset = List.fold_left (fun eset exp -> 
        let (p_f,bf_ann) = exp in
        (match p_f with
         | Lt (e1,e2,pos) -> (match e1,e2 with
             | IConst(0,_),_ -> 
               (match e2 with 
                | Add(a1,a2,_) -> 
                  (match a1, a2 with 
                   | Var(sa1,_),Var(sa2,_) -> if is_inf a1 
                     then EM.add_equiv eset sa2 neg_inf
                     else if is_inf a2 then EM.add_equiv eset sa1 neg_inf
                     else eset
                   | _ -> eset)
                | _ -> eset)
             | _ -> eset)
         | Gt (e1,e2,pos) -> (match e1,e2 with
             | Var(sv1,_),Var(sv2,_) -> EM.add_equiv eset sv1 sv2
             | _,IConst(0,_) -> 
               (match e1 with 
                | Add(a1,a2,_) -> 
                  (match a1, a2 with 
                   | Var(sa1,_),Var(sa2,_) -> if is_inf a1 
                     then EM.add_equiv eset sa2 neg_inf
                     else if is_inf a2 then EM.add_equiv eset sa1 neg_inf
                     else eset
                   | _ -> eset)
                | _ -> eset)
             | _ -> eset)
         | _ -> eset)
      ) eqset eq_list in eqset 
  in 
  List.map (fun e -> (e,find_inf_comp e)) ds

let rec sub_inf_list_exp (exp: CP.exp) (vars: CP.spec_var list) (is_neg: bool) : CP.exp =
  match exp with
  | CP.Null _
  | CP.IConst _
  | CP.AConst _ 
  | CP.InfConst _
  | CP.NegInfConst _
  | CP.Tsconst _
  | CP.Tup2 _
  | CP.Bptriple _
  | CP.FConst _ -> exp
  | CP.Var (sv,pos) -> 
    if BList.mem_eq eq_spec_var sv vars 
    then if is_neg then (*CP.Var(CP.SpecVar(Int,constinfinity,Primed),pos) *)
        (mkSubtract (IConst(0,pos)) (Var(SpecVar(Int,constinfinity,Unprimed),pos)) pos)
      else CP.Var(CP.SpecVar(Int,constinfinity,Unprimed),pos) 
    else exp
  | CP.Add (a1, a2, pos) -> 
    let a1_conv = sub_inf_list_exp a1 vars is_neg in
    let a2_conv = sub_inf_list_exp a2 vars is_neg in
    CP.Add(a1_conv,a2_conv,pos)
  | CP.Subtract (a1, a2, pos) -> 
    let a1_conv = sub_inf_list_exp a1 vars is_neg in
    let a2_conv = sub_inf_list_exp a2 vars is_neg in
    CP.Subtract(a1_conv,a2_conv,pos)
  | CP.Mult (a1, a2, pos) -> 
    let a1_conv = sub_inf_list_exp a1 vars is_neg in
    let a2_conv = sub_inf_list_exp a2 vars is_neg in
    CP.Mult(a1_conv,a2_conv,pos)
  | CP.Div (a1, a2, pos) -> 
    let a1_conv = sub_inf_list_exp a1 vars is_neg in
    let a2_conv = sub_inf_list_exp a2 vars is_neg in
    CP.Div(a1_conv,a2_conv,pos)
  | CP.Max (a1, a2, pos) -> 
    let a1_conv = sub_inf_list_exp a1 vars is_neg in
    let a2_conv = sub_inf_list_exp a2 vars is_neg in
    CP.Max(a1_conv,a2_conv,pos)
  | CP.Min (a1, a2, pos) -> 
    let a1_conv = sub_inf_list_exp a1 vars is_neg in
    let a2_conv = sub_inf_list_exp a2 vars is_neg in
    CP.Min(a1_conv,a2_conv,pos)
  | CP.TypeCast (ty, a1, pos) ->
    let a1_conv = sub_inf_list_exp a1 vars is_neg in
    CP.TypeCast (ty, a1_conv, pos)
  | CP.Bag _
  | CP.BagUnion _
  | CP.BagIntersect _
  | CP.BagDiff _
  | CP.List _
  | CP.ListAppend _
  | CP.ListCons _
  | CP.ListHead _
  | CP.ListTail _
  | CP.ListLength _
  | CP.ListReverse _
  | CP.Func _
  | CP.Template _
  | CP.ArrayAt _ -> exp
  | Level _ -> Error.report_no_pattern()

let rec sub_inf_list_b_formula (bf:CP.b_formula) (vl: CP.spec_var list) (is_neg: bool) (is_bound: bool)
  : CP.b_formula * CP.b_formula = 
  let tbf = mkTrue_p no_pos in
  let (p_f,bf_ann) = bf in
  let p_f_conv,tbf = if is_bound && is_neg
    then (match p_f with
        | Eq(e1,e2,pos) -> 
          if (is_var e1 && is_inf e2) || (is_var e2 && is_inf e1) 
             || (check_neg_inf2 e1 e2) || (check_neg_inf2 e2 e1)
          then p_f,tbf else
            (match e1,e2 with
             | Var(sv,pos),Add(a1,a2,_) -> (match a1,a2 with
                 | Var(sv1,_),IConst(_,_)
                 | IConst(_,_),Var(sv1,_) ->  
                   if BList.mem_eq eq_spec_var sv vl || BList.mem_eq eq_spec_var sv1 vl
                   then            
                     let e1_conv = sub_inf_list_exp e1 vl is_neg in
                     let e2_conv = sub_inf_list_exp e2 vl is_neg in
                     Gt(e1_conv,e1_conv,pos),p_f
                   else p_f,tbf
                 | _, _ -> p_f,tbf)         
             | Add(a1,a2,_),Var(sv,pos) -> (match a1,a2 with
                 | Var(sv1,_),IConst(_,_)
                 | IConst(_,_),Var(sv1,_) ->  
                   if BList.mem_eq eq_spec_var sv vl || BList.mem_eq eq_spec_var sv1 vl
                   then            
                     let e1_conv = sub_inf_list_exp e1 vl is_neg in
                     let e2_conv = sub_inf_list_exp e2 vl is_neg in
                     Gt(e1_conv,e2_conv,pos),p_f
                   else p_f,tbf
                 | _, _ -> p_f,tbf)
             | _,_ -> p_f,tbf)
        | _ -> p_f,tbf
      )
    else if is_bound
    then (match p_f with
        | Eq(e1,e2,pos) -> 
          if (is_var e1 && is_inf e2) || (is_var e2 && is_inf e1) 
             || (check_neg_inf2 e1 e2) || (check_neg_inf2 e2 e1)
          then p_f,tbf else
            (match e1,e2 with
             | Var(sv,pos),Add(a1,a2,_) -> (match a1,a2 with
                 | Var(sv1,_),IConst(_,_)
                 | IConst(_,_),Var(sv1,_) ->  
                   if BList.mem_eq eq_spec_var sv vl || BList.mem_eq eq_spec_var sv1 vl
                   then            
                     let e1_conv = sub_inf_list_exp e1 vl is_neg in
                     let e2_conv = sub_inf_list_exp e2 vl is_neg in
                     Lt(e1_conv,e2_conv,pos),p_f
                   else p_f,tbf
                 | _, _ -> p_f,tbf) 
             | Add(a1,a2,_),Var(sv,pos) -> (match a1,a2 with
                 | Var(sv1,_),IConst(_,_)
                 | IConst(_,_),Var(sv1,_) ->  
                   if BList.mem_eq eq_spec_var sv vl || BList.mem_eq eq_spec_var sv1 vl
                   then            
                     let e1_conv = sub_inf_list_exp e1 vl is_neg in
                     let e2_conv = sub_inf_list_exp e2 vl is_neg in
                     Lt(e1_conv,e2_conv,pos),p_f
                   else p_f,tbf
                 | _, _ -> p_f,tbf) 
             | _,_ -> p_f,tbf)
        | _ -> p_f,tbf
      )
    else
      (match p_f with
       | CP.Frm _
       | CP.XPure _
       | CP.LexVar _
       | CP.ImmRel _
       | CP.BConst _
       | CP.BVar _ -> p_f,tbf
       | CP.Lt (e1,e2,pos) -> 
         let e1_conv = sub_inf_list_exp e1 vl is_neg in
         let e2_conv = sub_inf_list_exp e2 vl is_neg in
         CP.Lt(e1_conv,e2_conv,pos),tbf
       | CP.Lte (e1,e2,pos) -> 
         let e1_conv = sub_inf_list_exp e1 vl is_neg in
         let e2_conv = sub_inf_list_exp e2 vl is_neg in
         CP.Lte(e1_conv,e2_conv,pos),tbf
       | CP.Gt (e1,e2,pos) -> 
         let e1_conv = sub_inf_list_exp e1 vl is_neg in
         let e2_conv = sub_inf_list_exp e2 vl is_neg in
         CP.Gt(e1_conv,e2_conv,pos),tbf
       | CP.Gte (e1,e2,pos) -> 
         let e1_conv = sub_inf_list_exp e1 vl is_neg in
         let e2_conv = sub_inf_list_exp e2 vl is_neg in
         CP.Gte(e1_conv,e2_conv,pos),tbf
       | CP.SubAnn (e1,e2,pos) -> p_f,tbf
       | CP.Eq (e1,e2,pos) -> 
         if (is_var e1 && is_inf e2) || (is_var e2 && is_inf e1) 
            || (check_neg_inf2 e1 e2) || (check_neg_inf2 e2 e1)
            ||(is_var e1 && is_var e2)
         then p_f,tbf else
           let e1_conv = sub_inf_list_exp e1 vl is_neg in
           let e2_conv = sub_inf_list_exp e2 vl is_neg in
           CP.Eq(e1_conv,e2_conv,pos),tbf
       | CP.Neq (e1,e2,pos) -> 
         let e1_conv = sub_inf_list_exp e1 vl is_neg in
         let e2_conv = sub_inf_list_exp e2 vl is_neg in
         CP.Neq(e1_conv,e2_conv,pos),tbf
       | CP.ListIn (e1,e2,pos)
       | CP.ListNotIn (e1,e2,pos)
       | CP.ListAllN (e1,e2,pos)
       | CP.ListPerm (e1,e2,pos) -> p_f,tbf
       | CP.EqMax (e1,e2,e3,pos) -> 
         let e1_conv = sub_inf_list_exp e1 vl is_neg in
         let e2_conv = sub_inf_list_exp e2 vl is_neg in
         let e3_conv = sub_inf_list_exp e3 vl is_neg in
         CP.EqMax(e1_conv,e2_conv,e3_conv,pos),tbf
       | CP.EqMin (e1,e2,e3,pos) -> 
         let e1_conv = sub_inf_list_exp e1 vl is_neg in
         let e2_conv = sub_inf_list_exp e2 vl is_neg in
         let e3_conv = sub_inf_list_exp e3 vl is_neg in
         CP.EqMin(e1_conv,e2_conv,e3_conv,pos),tbf
       | CP.BagIn _
       | CP.BagNotIn _
       | CP.BagSub _
       | CP.BagMin _
       | CP.BagMax _
       (* | CP.VarPerm _ *)
       | CP.RelForm _ -> p_f,tbf
      ) in (p_f_conv,bf_ann),(tbf,bf_ann)

(*
substitute all variables in vl with \inf in f
*)
let rec sub_inf_list (f:CP.formula) (vl: CP.spec_var list) (is_neg: bool) (is_bound: bool) : CP.formula = 
  if List.length vl == 0 then f else 
    let rec helper pf vl =
      match pf with
      | CP.BForm (b,fl) -> 
        let b_norm,tbf = sub_inf_list_b_formula b vl is_neg is_bound
        in (mkAnd (CP.BForm(b_norm,fl)) (CP.BForm(tbf,fl)) no_pos)
      | CP.And (pf1,pf2,pos) -> 
        let pf1_norm = helper pf1 vl in
        let pf2_norm = helper pf2 vl in
        CP.And(pf1_norm,pf2_norm,pos) 
      | CP.AndList pflst -> 
        let pflst_norm = List.map (fun (sl,pf) -> (sl,helper pf vl)) pflst 
        in CP.AndList(pflst_norm)
      | CP.Or (pf1,pf2,fl,pos) -> 
        let pf1_norm = helper pf1 vl in
        let pf2_norm = helper pf2 vl in
        CP.Or(pf1_norm,pf2_norm,fl,pos) 
      | CP.Not (nf,fl,pos) -> 
        let nf_norm = helper nf vl
        in CP.Not(nf_norm,fl,pos)
      | CP.Forall (qid, qf,fl,pos) -> 
        let qf_norm = helper qf vl
        in CP.Forall(qid,qf_norm,fl,pos)
      | CP.Exists (qid, qf,fl,pos) -> 
        let qf_norm = helper qf vl
        in CP.Exists(qid,qf_norm,fl,pos)
    in
    helper f vl

let sub_inf_list (f:CP.formula) (vl: CP.spec_var list) (is_neg: bool) (is_bound: bool) : CP.formula = 
  Debug.no_1 "sub_inf_list" string_of_pure_formula string_of_pure_formula (fun _ -> sub_inf_list f vl is_neg is_bound) f

(*
do the substitutions with \inf 
*)
let find_equiv_all_x  (e:EM.elem) (s:EM.emap) : EM.elist  =
  let pr = EM.string_of_elem in
  let pr2 = pr_list EM.string_of_elem in 
  Debug.no_1 "find_equiv_all" pr pr2 (fun _ -> EM.find_equiv_all e s) e

let substitute_inf (f: CP.formula) : CP.formula =
  let f = convert_inf_to_var f in
  let sublist = find_inf_subs f in
  let boundlist = snd (List.split(find_inf_bounded f)) in 
  let negboundlist = snd (List.split(find_neginf_bounded f)) in 
  let after_sub = List.map (fun (pf,kv) -> 
      (*let filter_infs = List.filter (fun (e,k) -> is_inf_sv k) kv in
        			let vlistlist = List.map (fun (e,k) -> EM.find_equiv_all e kv) filter_infs in
                         let vlist = List.flatten vlistlist in*)
      let svlist = (find_equiv_all_x (SpecVar(Int,constinfinity,Unprimed)) kv) in  	
      let new_pf = sub_inf_list pf svlist false false in
      let svneglist = (find_equiv_all_x (SpecVar(Int,constinfinity,Primed)) kv) in  
      let new_pf = sub_inf_list new_pf svneglist true false in
      (*arith_simplify 10*) new_pf) sublist in
  (* let () = print_string("bound = "^(string_of_pure_formula (join_disjunctions after_sub))^"\n") in*)
  let after_sub = List.map (fun (pf,kv) -> 
      let svlist = (find_equiv_all_x (SpecVar(Int,constinfinity,Unprimed)) kv) in  	
      let new_pf = sub_inf_list pf svlist false true in
      new_pf) (List.combine after_sub boundlist) in 
  (* let () = print_string("bound < "^(string_of_pure_formula (join_disjunctions after_sub))^"\n") in*)
  let after_sub = List.map (fun (pf,kv) -> 
      let svneglist = (find_equiv_all_x (SpecVar(Int,constinfinity,Primed)) kv) in  
      let new_pf = sub_inf_list pf svneglist true true in
      x_add arith_simplify 10 new_pf) (List.combine after_sub negboundlist) in 
  (* let () = print_string("bound > "^(string_of_pure_formula (join_disjunctions after_sub))^"\n") in*)
  join_disjunctions after_sub

let substitute_inf (f: CP.formula) : CP.formula =
  Gen.Profiling.do_1 "INF-Substitute inf" substitute_inf f

let normalize_inf_formula (f: CP.formula): CP.formula =
  let pr = string_of_pure_formula in
  DD.no_1 "normalize_inf_formula" pr pr normalize_inf_formula f

let rec normalize_inf_formula_sat (f: CP.formula): CP.formula = 
  (*let pf = MCP.pure_of_mix f in*)
  if not (contains_inf f) then f else 
    (*let f =  arith_simplify 101 f in*) 
    let pf_norm =  if contains_inf_eq f then 
        normalize_inf_formula (substitute_inf f) 
        (*let f = (*MCP.mix_of_pure*) (convert_inf_to_var pf_norm) in 
          let x_sv = CP.SpecVar(Int,"x",Unprimed) in
          let x_var =  CP.Var(x_sv,no_pos) in
          let inf_var =  CP.Var(CP.SpecVar(Int,CP.zinf_str,Unprimed),no_pos) in (* Same Name as in parser.ml *)
          let x_f = CP.BForm((CP.Lte(x_var,inf_var,no_pos),None),None) in
          let inf_constr = CP.Forall(x_sv,x_f,None,no_pos) in
          let f = CP.And(f,inf_constr,no_pos) in f*)
      else (*MCP.mix_of_pure*) (normalize_inf_formula f) in (convert_inf_to_var pf_norm)
(*let () = DD.vv_trace("Normalized: "^ (string_of_pure_formula pf_norm)) in*)

let normalize_inf_formula_sat (f: CP.formula) : CP.formula = 
  let pr = Cprinter.string_of_pure_formula in
  Debug.no_1 "normalize_inf_formula_sat" pr pr normalize_inf_formula_sat f

let normalize_inf_formula_sat (f: CP.formula) : CP.formula = 
  Gen.Profiling.do_1 "INF-norm-sat" (normalize_inf_formula_sat) f

let normalize_inf_formula (f: CP.formula): CP.formula = 
  Gen.Profiling.do_1 "INF-norm-f" normalize_inf_formula f 

let normalize_inf_formula_imply (ante: CP.formula) (conseq: CP.formula) : CP.formula * CP.formula = 
  if not (contains_inf ante) && not (contains_inf conseq) then ante,conseq else
    (*let ante_norm = if contains_inf_eq ante 
      		then (*(normalize_inf_formula*) (substitute_inf ante)
      		else  (*normalize_inf_formula*) ante in*)
    let ante_norm_lst = split_conjunctions ante in
    let ante_norm = join_conjunctions (List.map normalize_inf_formula ante_norm_lst) in
    let conseq_norm = (*if contains_inf_eq conseq
                        		then (normalize_inf_formula (substitute_inf conseq))
                        		else normalize_inf_formula*) conseq in
    let new_a = convert_inf_to_var ante_norm in
    let new_c = (*convert_inf_to_var*) conseq_norm in
    let atoc_sublist = find_inf_subs new_a in
    let ante,conseq = if List.length atoc_sublist == 1 
      then let _,subs_c = List.hd atoc_sublist in 
        let vlist = find_equiv_all_x (SpecVar(Int,constinfinity,Unprimed)) subs_c in
        let new_c = sub_inf_list new_c vlist false false in (* substitute +ve inf *)
        let negvlist =  find_equiv_all_x (SpecVar(Int,constinfinity,Primed)) subs_c in
        let new_c =  sub_inf_list new_c negvlist true false in (* substitute -ve inf *)
        let new_c =  x_add arith_simplify 11 new_c in
        let new_c_lst  = split_conjunctions new_c in
        let new_c = join_conjunctions (List.map normalize_inf_formula new_c_lst) in
        let new_c = convert_inf_to_var new_c in
        new_a,new_c
      else new_a,new_c
    in let ante_norm = (*check if need to normalize again*)(*if contains_inf_eq ante 
                                                             		then *)normalize_inf_formula (substitute_inf ante)
    (*else ante*) in 
    let conseq_norm = if contains_inf_eq conseq then normalize_inf_formula (substitute_inf conseq) 
      else conseq in 
    convert_inf_to_var ante_norm,convert_inf_to_var conseq_norm

let normalize_inf_formula_imply (ante: CP.formula) (conseq: CP.formula) : CP.formula * CP.formula = 
  let pr = Cprinter.string_of_pure_formula in
  Debug.no_2 "INF-norm-imply" pr pr (pr_pair pr pr)
    normalize_inf_formula_imply ante conseq

let normalize_inf_formula_imply (ante: CP.formula) (conseq: CP.formula) : CP.formula * CP.formula = 
  Gen.Profiling.do_1 "INF-norm-imply" (normalize_inf_formula_imply ante) conseq

let join_pai_num (x: pai_num) (y: pai_num) : pai_num =
  match x,y with
  | Bottom,a 
  | a,Bottom -> a
  | Pos_inf,Pos_inf -> Pos_inf
  | Neg_inf,Neg_inf -> Neg_inf
  | Pos_inf,Neg_inf
  | Neg_inf,Pos_inf
  | Finite,_ 
  | _,Finite -> Finite

let propagate_pai (bf: CP.b_formula) (ls:(spec_var * pai_num) list) : (spec_var * pai_num) list  =
  let rec helper p_f =
    (match p_f with
     | CP.Lt(e1,e2,pos) 
     | CP.Gt(e2,e1,pos) 
     | CP.Lte(e1,e2,pos) 
     | CP.Gte(e2,e1,pos) ->
       let v1 = get_var_opt e1 in
       let v2 = get_var_opt e2 in
       (match v1,v2 with
        | Some(s1),Some(s2) -> 
          if List.exists (fun (s,p) -> eq_spec_var s1 s) ls && 
             List.exists (fun (s,p) -> eq_spec_var s2 s) ls
          then let sl1,pn1 = List.find (fun (l,_) -> eq_spec_var l s1) ls in
            let sl2,pn2 = List.find (fun (l,_) -> eq_spec_var l s2) ls in
            let s,p = 
              if pn1 = Pos_inf then let pn2_new = join_pai_num pn2 Pos_inf in sl2,pn2_new
              else if pn2 = Neg_inf then let pn1_new = join_pai_num pn1 Neg_inf in sl1,pn1_new
              else sl1,pn1
            in let ls_remove_s = List.filter (fun (l,_) -> not(eq_spec_var l s)) ls in
            (s,p)::ls_remove_s
          else ls 
        | _ ,_ -> ls)
     | CP.Eq (e1,e2,pos) -> 
       let v1 = get_var_opt e1 in
       let v2 = get_var_opt e2 in
       (match v1,v2 with
        | Some(s1),Some(s2) -> 
          if List.exists (fun (s,p) -> eq_spec_var s1 s) ls && 
             List.exists (fun (s,p) -> eq_spec_var s2 s) ls
          then let sl1,pn1 = List.find (fun (l,_) -> eq_spec_var l s1) ls in
            let sl2,pn2 = List.find (fun (l,_) -> eq_spec_var l s2) ls in
            let pn  = join_pai_num pn1 pn2 in
            let ls = List.filter (fun (l,_) -> not(eq_spec_var l sl1)) ls in
            let ls = List.filter (fun (l,_) -> not(eq_spec_var l sl2)) ls in
            (sl1,pn)::(sl2,pn)::ls
          else ls 
        | _ ,_ -> ls)

     | CP.Neq (e1,e2,pos) -> 
       let v1 = get_var_opt e1 in
       let v2 = get_var_opt e2 in
       (match v1,v2 with
        | Some(s1),Some(s2) -> 
          if List.exists (fun (s,p) -> eq_spec_var s1 s) ls && 
             List.exists (fun (s,p) -> eq_spec_var s2 s) ls
          then let sl1,pn1 = List.find (fun (l,_) -> eq_spec_var l s1) ls in
            let sl2,pn2 = List.find (fun (l,_) -> eq_spec_var l s2) ls in
            let s,p = match pn1,pn2 with
              | Pos_inf,_ -> sl2,join_pai_num pn2 Neg_inf
              | _,Pos_inf -> sl1,join_pai_num pn1 Neg_inf
              | _,Neg_inf -> sl1,join_pai_num pn1 Pos_inf
              | Neg_inf,_ -> sl2,join_pai_num pn2 Pos_inf
              | _,_ -> sl1,pn1
            in let ls_remove_s = List.filter (fun (l,_) -> not(eq_spec_var l s)) ls in
            (s,p)::ls_remove_s
          else ls 
        | _ ,_ -> ls)
     | _ -> ls
    ) in  
  let (p_f,bf_ann) = bf in (helper p_f)

let initialize_pai (bf: CP.b_formula) (ls:(spec_var * pai_num) list) 
  : CP.b_formula * (spec_var * pai_num) list  =
  let aux (s1:spec_var) (s2:spec_var) pai_new ls =
    if is_inf_sv s2 && not(is_inf_sv s1) then 
      if List.exists (fun (s,p) -> eq_spec_var s1 s) ls then
        let s,p = List.find (fun (l,_) -> eq_spec_var l s1) ls in
        let p = join_pai_num p pai_new in
        let ls_remove_s = List.filter (fun (l,_) -> not(eq_spec_var l s)) ls in
        true,((s,p)::ls_remove_s)
      else false,ls
    else false,ls
  in 
  let rec helper p_f =
    (match p_f with
     | CP.Gt(e2,e1,pos) 
     | CP.Lt(e1,e2,pos) ->
       let v1 = get_var_opt e1 in
       let v2 = get_var_opt e2 in
       (match v1,v2 with
        | Some(s1),Some(s2) -> let f,ls_new = aux s1 s2 Neg_inf ls in
          if f then  (mkTrue_p no_pos),ls_new
          else p_f,ls
        | None,None -> (match e1,e2 with
            | IConst(0,_),Add(e1,e2,_) -> 
              let v1 = get_var_opt e1 in
              let v2 = get_var_opt e2 in
              (match v1,v2 with
               | Some(s1),Some(s2) -> 
                 let f,ls_new = aux s1 s2 Pos_inf ls in
                 if f then  (mkTrue_p no_pos),ls_new
                 else let f,ls_new = aux s2 s1 Pos_inf ls in
                   if f then  (mkTrue_p no_pos),ls_new
                   else p_f,ls
               | _,_ -> p_f,ls)
            | _,_ -> p_f,ls)
        | _ ,_ -> p_f,ls) 
     | _ -> p_f,ls
    ) in  
  let (p_f,bf_ann) = bf in 
  let p_f,ls = (helper p_f) in (p_f,bf_ann),ls

let rec initialize_pai_formula (f:CP.formula) (ls:(spec_var * pai_num) list) 
  : CP.formula * (spec_var * pai_num) list = 
  let rec helper pf ls =
    match pf with
    | CP.BForm (b,fl) -> 
      let b,ls = initialize_pai b ls
      in CP.BForm(b,fl),ls
    | CP.And (pf1,pf2,pos) -> 
      let pf1,ls1 = helper pf1 ls in
      let pf2,ls2 = helper pf2 ls1 in
      CP.And(pf1,pf2,pos),ls2 
    | CP.AndList pflst ->  CP.AndList(pflst),ls
    | CP.Or (pf1,pf2,fl,pos) -> 
      let pf1,ls1 = helper pf1 ls in
      let pf2,ls2 = helper pf2 ls1 in
      CP.Or(pf1,pf2,fl,pos),ls2 
    | CP.Not (nf,fl,pos) -> 
      let nf,ls = helper nf ls
      in CP.Not(nf,fl,pos),ls
    | CP.Forall (qid, qf,fl,pos) -> 
      let qf,ls = helper qf ls
      in CP.Forall(qid,qf,fl,pos),ls
    | CP.Exists (qid, qf,fl,pos) -> 
      let qf,ls = helper qf ls
      in CP.Exists(qid,qf,fl,pos),ls
  in
  helper f ls

let gen_pai_constr (v:spec_var * pai_num) : CP.formula =
  let sv,pn = v in match pn with
  | Bottom -> CP.mkTrue no_pos
  | Neg_inf -> BForm(((CP.mkLt (mkVar sv no_pos) (mkInfConst no_pos) no_pos),None),None)
  | Pos_inf -> BForm(((CP.mkGt (mkVar sv no_pos) (mkNegInfConst no_pos) no_pos),None),None)
  | Finite -> (mkAnd (BForm(((CP.mkLt (mkVar sv no_pos) (mkInfConst no_pos) no_pos),None),None))
                 (BForm(((CP.mkGt (mkVar sv no_pos) (mkNegInfConst no_pos) no_pos),None),None)) no_pos)

let rec gen_pai_num_constraints (ls:(spec_var*pai_num) list) :CP.formula =
  match ls with
  | [] -> CP.mkTrue no_pos
  | x::xs -> CP.mkAnd (gen_pai_constr x) (gen_pai_num_constraints xs) no_pos

(* assumes only conjunctions are in formula and all quantifiers are eliminated *)
let fixed_point_pai_num (f: CP.formula) : CP.formula =
  let var_list = CP.fv f in 
  let ls = List.map (fun c -> (c,Bottom)) var_list in
  let f,var_pai_lst = initialize_pai_formula f ls in
  let clause_lst = list_of_bformula f in 
  let rec calc_fix var_pai_lst = 
    let rec aux cl vpl = match cl with
      | c::cs -> (match c with
          | BForm (b,fl) -> aux cs (propagate_pai b vpl)
          | _ -> aux cs vpl)
      | [] -> vpl in  
    (*let lst = List.map (fun c -> match c with
      | BForm (b,fl) -> propagate_pai b var_pai_lst
      | _ -> var_pai_lst
      ) clause_lst in *)
    let lst = aux clause_lst var_pai_lst in
    if (List.for_all (fun (sv,pi) -> (List.mem (sv,pi) lst)) var_pai_lst) &&
       (List.for_all (fun v -> (List.mem v var_pai_lst)) lst) then lst else calc_fix lst in
  let fix_lst = calc_fix var_pai_lst in
  let pai_constrs = convert_inf_to_var (gen_pai_num_constraints fix_lst) in 
  let f = mkAnd f pai_constrs no_pos in f 

let fixed_point_pai_num  (f: CP.formula) : CP.formula =
  Debug.no_1 "fixed_point_pai_num" string_of_pure_formula string_of_pure_formula fixed_point_pai_num f

let rec gen_instantiations (svl: CP.spec_var list) (fl: CP.formula list) : CP.formula list = 
  let mk_inf_eq x =  BForm(((CP.mkEq (mkVar x no_pos) (mkInfConst no_pos) no_pos),None),None) in
  let mk_neg_inf_eq x =  BForm(((CP.mkEq (mkVar x no_pos) (mkNegInfConst no_pos) no_pos),None),None) in
  match svl with
  | [] -> fl
  | x::xs -> let fl_sub_x = (*List.filter (fun c -> not(List.mem x (CP.fv c)))*) fl  in
    let x_eq_inf = mk_inf_eq x in
    let x_eq_neg_inf = mk_neg_inf_eq x in
    let fl_up = x_eq_inf::[x_eq_neg_inf] in 
    let fl_up_inf = List.map (fun f -> mkAnd f x_eq_inf no_pos) fl_sub_x in
    let fl_up_neg_inf = List.map (fun f -> mkAnd f x_eq_neg_inf no_pos) fl_sub_x in
    gen_instantiations xs (fl@fl_up@fl_up_inf@fl_up_neg_inf)

let gen_instantiations (svl: CP.spec_var list) (fl: CP.formula list) : CP.formula list = 
  Debug.no_1 "gen_instants" (pr_list string_of_pure_formula) (pr_list string_of_pure_formula)
    (fun _ -> gen_instantiations svl fl) fl

let rec elim_forall (f: CP.formula) : CP.formula = 
  let helper qid qf = 
    let inner_f = elim_forall qf in 
    let ins_lst = gen_instantiations [qid] [] in
    let l = List.map (fun pf ->  x_add arith_simplify 199 (mkAnd pf inner_f no_pos)) ins_lst in
    conj_of_list l no_pos in
  match f with
  | CP.BForm (b,fl) -> f
  | CP.And (pf1,pf2,pos) -> 
    let pf1 = elim_forall pf1 in
    let pf2 = elim_forall pf2 in
    CP.And(pf1,pf2,pos) 
  | CP.AndList pflst -> f
  | CP.Or (pf1,pf2,fl,pos) -> 
    let pf1 = elim_forall pf1 in
    let pf2 = elim_forall pf2 in
    CP.Or(pf1,pf2,fl,pos) 
  | CP.Not (nf,fl,pos) -> 
    let nf = elim_forall nf
    in CP.Not(nf,fl,pos)
  | CP.Forall (qid, qf,fl,pos) -> 
    let insf = helper qid qf in 
    CP.And(f,insf,pos)
  | CP.Exists (qid, qf,fl,pos) -> 
    let qf = elim_forall qf
    in CP.Exists(qid,qf,fl,pos)

let elim_forall (f: CP.formula) : CP.formula = 
  Debug.no_1 "elim_forall_inf" string_of_pure_formula string_of_pure_formula elim_forall f

let get_inst_forall (f:CP.formula): CP.formula list = 
  let vars,f,_,_ = CP.split_forall_quantifiers f in
  let ins_lst = gen_instantiations vars [] in
  List.map (fun pf ->  x_add arith_simplify 198 (mkAnd pf f no_pos)) ins_lst 

let get_inst_forall (f:CP.formula): CP.formula list = 
  Debug.no_1 "elim_inf_forall" string_of_pure_formula (pr_list string_of_pure_formula)
    get_inst_forall f

let quantifier_elim (f: CP.formula): CP.formula list = 
  (*let f = elim_forall f in *)
  (*let _ = print_endline("f: "^(string_of_pure_formula f)) in*)
  (*let vars = List.filter (fun c -> not(is_inf_sv c)) (CP.fv f) in*)
  let vars,f = CP.split_ex_quantifiers f in
  let ins_lst = gen_instantiations vars [] in
  let ls = List.map (fun pf ->  x_add arith_simplify 200 (mkAnd pf f no_pos)) ins_lst 
  in f::ls

let quantifier_elim (f: CP.formula): CP.formula list = 
  Debug.no_1 "elim_inf_exists" string_of_pure_formula (pr_list string_of_pure_formula)
    quantifier_elim f

let rec elim_forall_exists (f: CP.formula) : CP.formula = 
  let helper qid qf = 
    let inner_f = elim_forall_exists qf in 
    let ins_lst = gen_instantiations [qid] [] in
    let l = List.map (fun pf ->  x_add arith_simplify 199 (mkAnd pf inner_f no_pos)) ins_lst in
    conj_of_list l no_pos in
  let helper_ex qid qf = 
    let inner_f = elim_forall_exists qf in 
    let ins_lst = gen_instantiations [qid] [] in
    let l = List.map (fun pf ->  x_add arith_simplify 200 (mkAnd pf inner_f no_pos)) ins_lst in
    disj_of_list l no_pos in
  match f with
  | CP.BForm (b,fl) -> f
  | CP.And (pf1,pf2,pos) -> 
    let pf1 = elim_forall pf1 in
    let pf2 = elim_forall pf2 in
    CP.And(pf1,pf2,pos) 
  | CP.AndList pflst -> f
  | CP.Or (pf1,pf2,fl,pos) -> 
    let pf1 = elim_forall pf1 in
    let pf2 = elim_forall pf2 in
    CP.Or(pf1,pf2,fl,pos) 
  | CP.Not (nf,fl,pos) -> 
    let nf = elim_forall nf
    in CP.Not(nf,fl,pos)
  | CP.Forall (qid, qf,fl,pos) -> 
    let insf = helper qid qf in 
    CP.And(f,insf,pos)
  | CP.Exists (qid, qf,fl,pos) -> 
    let insf = helper_ex qid qf in
    CP.Or(f,insf,None,pos)

let elim_forall_exists (f: CP.formula) : CP.formula = 
  Debug.no_1 "elim_forall_exists_inf" string_of_pure_formula string_of_pure_formula elim_forall_exists f
