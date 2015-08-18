open VarGen
open Camlp4.PreCast
open Cpure
open Globals
open Lexing
open Gen
module H = Hashtbl
module TI = Typeinfer

(******************************************************************************)

let loc = no_pos

(* let tlist = ref [];; *)

class ['a] type_stack_pr (epr:'a->string) (eq:'a->'a->bool)  =
  object (self)
    inherit ['a] stack_pr "type_stack_pr" epr eq as super
    method get_spec_var_ident var p =
      let same_sv sv =
        match sv,p with
        | SpecVar (_,id,Primed),Primed
        | SpecVar (_,id,Unprimed),Unprimed -> id=var
        | _ -> false
      in
      try
        super # find same_sv
      with
        Not_found->
        Cpure.SpecVar (UNK,var,p)
  end

let tlist = new type_stack_pr string_of_spec_var eq_spec_var

(******************************************************************************)

let expression = Gram.Entry.mk "expression"

(******************************************************************************)

(* let get_var var stab =                                    *)
(*   if is_substr "PRI" var                                  *)
(*   then                                                    *)
(*     let var = String.sub var 3 (String.length var - 3) in *)
(*     Typeinfer.get_spec_var_ident stab var Primed          *)
(*   else Typeinfer.get_spec_var_ident stab var Unprimed     *)

let get_var var tlist = 
  if is_substr "PRI" var 
  then 
    let var = String.sub var 3 (String.length var - 3) in
    tlist # get_spec_var_ident var Primed
    (* TI.get_spec_var_ident (tlist # get_stk) var Primed *)
  else tlist # get_spec_var_ident var Unprimed

let add_prefix var prefix = match var with
  | SpecVar (t,id,p) -> SpecVar (t,prefix ^ id,p)

let is_node var = match var with 
  | Var (SpecVar (_,id,_), _) -> (* is_substr "NOD" id || *) id=self
  | _ -> false

let get_node var = match var with 
  | Var (SpecVar (_,id,_), _) -> 
    if id=self then id else 
      String.sub id 3 (String.length id - 3)
  | _ -> report_error no_pos "Expected a pointer variable"

let is_rec_node var = match var with 
  (* | Var (SpecVar (_,id,_), _) -> is_substr "RECNOD" id *)
  | _ -> false

let get_rec_node var = match var with 
  | Var (SpecVar (_,id,_), _) -> String.sub id 6 (String.length id - 6)
  | _ -> report_error no_pos "Expected a recursive pointer variable"

let is_int c = '0' <= c && c <= '9'

let get_type_list_for_fixcalc_output (f:Cpure.formula) =
  let f = Trans_arr.translate_array_one_formula f in
  let rec helper_e e =
    match e with
    | Add (e1,e2,loc)
    | Subtract (e1,e2,loc)
    | Mult (e1,e2,loc)
    | Div (e1,e2,loc)->
      (helper_e e1) @ (helper_e e2)
    | Var (sv,_)->
      [sv]
    | _ -> []
  in
  let helper_b (p,ba) =
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
      (helper_e e1) @ (helper_e e2)
    | _ ->
      []
  in
  let rec helper f =
    match f with
    | BForm (b,fl)->
      helper_b b
    | And (f1,f2,_)
    | Or (f1,f2,_,_)->
      (helper f1)@(helper f2)
    | AndList lst->
      failwith "get_type_list_for_fixcalc_output: AndList To Be Implemented, can use [] as default"
    | Not (nf,_,_)
    | Forall (_,nf,_,_)
    | Exists (_,nf,_,_)->
      helper nf
  in
  helper f
;;

let initialize_tlist f =
  tlist # push_list (get_type_list_for_fixcalc_output f)
;;

(* TODO:WN : does this affect ptr arithmetic later ? *)
(* some of the convertion already handled by norm_pure_result *)
(* incr/ex5b2.ss output problem if is_node stuff removed *)
(* < !!! **fixcalc.ml#393:svls (from parse_fix):[p:node,res:Unknown] *)
(* < !!! **fixcalc.ml#1063:Result of fixcalc (parsed): :[ (not(res:boolean) | (p:node=null & res:boolean))] *)
(* --- *)
(* > !!! **fixcalc.ml#393:svls (from parse_fix):[NODp:Unknown,res:Unknown] *)
(* > !!! **fixcalc.ml#1063:Result of fixcalc (parsed): :[ (not(res:boolean) | (0>=NODp:Unknown & res:boolean))] *)
(* 66c66 *)
(* < !!! **pi.ml#781:>>POST:  (not(res:boolean) | (p:node=null & res:boolean)) *)
(* --- *)
(* > !!! **pi.ml#781:>>POST:  (not(res:boolean) | (0>=NODp:Unknown & res:boolean)) *)
(* 75c75,76 *)
(* <      (not(res:boolean) | (p:node=null & res:boolean))&{FLOW,(4,5)=__norm#E}[] *)
(* --- *)
(* >      (not(res:boolean) | (0>=NODp:Unknown & res:boolean))& *)
(* >      {FLOW,(4,5)=__norm#E}[] *)

let initialize_tlist_from_fpairlist fpairlst =
  tlist # push_list ( List.fold_left (fun r (f1,f2,_) -> r@(get_type_list_for_fixcalc_output f1)@(get_type_list_for_fixcalc_output f2)) []  fpairlst)
;;

(******************************************************************************)

EXTEND Gram
    GLOBAL: expression;
expression:
    [ "expression" NONA
        [ x = LIST1 or_formula -> x ]
    ];

or_formula:
    [ "or_formula" LEFTA
        [ x = SELF; "||"; y = SELF -> mkOr x y None loc
        | x = and_formula -> x ]
    ];

and_formula:
    [ "and_formula" LEFTA
        [ x = SELF; "&&"; y = SELF -> mkAnd x y loc
        | x = formula -> x ]
    ];

formula:
    [ "formula" LEFTA
        [ NATIVEINT; "="; exp        -> mkTrue loc
          | exp; "="; NATIVEINT        -> mkTrue loc
          | NATIVEINT; "<"; exp        -> mkTrue loc
          | exp; "<"; NATIVEINT        -> mkTrue loc
          | NATIVEINT; ">"; exp        -> mkTrue loc
          | exp; ">"; NATIVEINT        -> mkTrue loc
          | NATIVEINT; "<="; exp       -> mkTrue loc
          | exp; "<="; NATIVEINT       -> mkTrue loc
          | NATIVEINT; ">="; exp       -> mkTrue loc
          | exp; ">="; NATIVEINT       -> mkTrue loc
          | NATIVEINT; "!="; exp       -> mkTrue loc
          | exp; "!="; NATIVEINT       -> mkTrue loc
          | NATIVEINT; "="; NATIVEINT  -> mkTrue loc
          | NATIVEINT; "<"; NATIVEINT  -> mkTrue loc
          | NATIVEINT; ">"; NATIVEINT  -> mkTrue loc
          | NATIVEINT; "<="; NATIVEINT -> mkTrue loc
          | NATIVEINT; ">="; NATIVEINT -> mkTrue loc
          | NATIVEINT; "!="; NATIVEINT -> mkTrue loc
          | x = INT; "="; y = INT ->
                let tmp =
                  if int_of_string x = int_of_string y
                  then BConst (true,loc)
                  else BConst (false,loc)
                in BForm ((tmp, None), None)
          | x = exp; "<"; y = exp ->
                (* let () = Debug.binfo_hprint (add_str "test" Cprinter.string_of_formula_exp) x no_pos in *)
                (* let () = Debug.binfo_hprint (add_str "test" Cprinter.string_of_formula_exp) y no_pos in *)
                (* if is_bool_res_var y && is_zero x then *)
                (*   BForm ((BVar (get_var "res" tlist, loc), None), None) *)
                (* else if is_bool_res_var x && is_one y then *)
                (*   Not (BForm ((BVar (get_var "res" tlist, loc), None), None), None, loc)  *)
                (* else *)
                  let tmp = 
                    if !Globals.old_parse_fix then
                      if is_node y && is_zero x then 
                        Neq (Var(get_var (get_node y) tlist, loc), Null loc, loc)
                      else if is_node x && is_one y then 
                        Eq (Var(get_var (get_node x) tlist, loc), Null loc, loc)
                      else if is_self_var y then 
                        Neq (Var(get_var "self" tlist, loc), Null loc, loc)
                      else Lt (x, y, loc) 
                    else Lt (x, y, loc) 
                  in BForm ((tmp, None), None)
          | x = exp; ">"; y = exp ->
                (* let () = Debug.binfo_hprint (add_str "test" Cprinter.string_of_formula_exp) x no_pos in *)
                (* let () = Debug.binfo_hprint (add_str "test" Cprinter.string_of_formula_exp) y no_pos in *)
                (* if is_bool_res_var x && is_zero y then  *)
                (*   BForm ((BVar (get_var "res" tlist, loc), None), None)  *)
                (* else if is_bool_res_var y && is_one x then  *)
                (*   Not (BForm ((BVar (get_var "res" tlist, loc), None), None), None, loc)  *)
                (* else *)
                  let tmp = 
                    if !Globals.old_parse_fix then
                      if is_node x && is_zero y then 
                        Neq (Var(get_var (get_node x) tlist, loc), Null loc, loc)
                      else if is_node y && is_one x then 
                        Eq (Var(get_var (get_node y) tlist, loc), Null loc, loc)
                      else if is_self_var x then 
                        Neq (Var(get_var "self" tlist, loc), Null loc, loc)
                      else Gt (x, y, loc)
                    else Gt (x, y, loc)
                  in BForm ((tmp, None), None)
          | x = exp; "<="; y = exp ->
                (* let () = Debug.binfo_hprint (add_str "test" Cprinter.string_of_formula_exp) x no_pos in *)
                (* let () = Debug.binfo_hprint (add_str "test" Cprinter.string_of_formula_exp) y no_pos in *)
                (* if is_bool_res_var x && is_zero y then  *)
                (*   Not (BForm ((BVar (get_var "res" tlist, loc), None), None), None, loc)  *)
                (* else if is_bool_res_var y && is_one x then  *)
                (*   BForm ((BVar (get_var "res" tlist, loc), None), None)  *)
                (* else *)
                  let tmp = 
                    if !Globals.old_parse_fix then
                      if is_node x && is_zero y then 
                        Eq (Var(get_var (get_node x) tlist, loc), Null loc, loc)
                      else if is_node y && is_one x then 
                        Neq (Var(get_var (get_node y) tlist, loc), Null loc, loc)
                      else if is_self_var x then 
                        Eq (Var(get_var "self" tlist, loc), Null loc, loc)
                      else Lte (x, y, loc)
                    else Lte (x, y, loc)
                  in BForm ((tmp, None), None)
          | x = exp; ">="; y = exp ->
                (* let () = Debug.binfo_hprint (add_str "test" Cprinter.string_of_formula_exp) x no_pos in *)
                (* let () = Debug.binfo_hprint (add_str "test" Cprinter.string_of_formula_exp) y no_pos in *)
                (* if is_bool_res_var y && is_zero x then  *)
                (*   Not (BForm ((BVar (get_var "res" tlist, loc), None), None), None, loc)  *)
                (* else *)
                (*   if is_bool_res_var x && is_one y then  *)
                (*     BForm ((BVar (get_var "res" tlist, loc), None), None)  *)
                (*   else *)
                    let tmp = 
                    if !Globals.old_parse_fix then
                      if is_node y && is_zero x then 
                        Eq (Var(get_var (get_node y) tlist, loc), Null loc, loc)
                      else
                        if is_node x && is_one y then 
                          Neq (Var(get_var (get_node x) tlist, loc), Null loc, loc)
                        else
                          if is_self_var y then 
                            Eq (Var(get_var "self" tlist, loc), Null loc, loc)
                          else Gte (x, y, loc)
                    else Gte (x, y, loc)
                    in BForm ((tmp, None), None)
          | x = exp; "="; y = exp ->
                (* let () = Debug.binfo_hprint (add_str "test" Cprinter.string_of_formula_exp) x no_pos in *)
                (* let () = Debug.binfo_hprint (add_str "test" Cprinter.string_of_formula_exp) y no_pos in *)
                let tmp = 
                    if !Globals.old_parse_fix then
                      if is_node x && is_node y then 
                        Eq (Var(get_var (get_node x) tlist, loc), 
                        Var(get_var (get_node y) tlist, loc), loc)
                      else
                      if is_node x && is_rec_node y then 
                        Eq (Var(get_var (get_node x) tlist, loc), 
                            Var(add_prefix (get_var (get_rec_node y) tlist) "REC", loc), loc)
                      else
                      if is_node y && is_rec_node x then 
                        Eq (Var(get_var (get_node y) tlist, loc), 
                            Var(add_prefix (get_var (get_rec_node x) tlist) "REC", loc), loc)
                      else
                      if is_rec_node x && is_rec_node y then 
                        Eq (Var(add_prefix (get_var (get_rec_node x) tlist) "REC", loc), 
                            Var(add_prefix (get_var (get_rec_node y) tlist) "REC", loc), loc)
                      else Eq (x, y, loc)
                    else Eq (x, y, loc)
                in BForm ((tmp, None), None)
          | x = exp; "!="; y = exp ->
                let tmp = Neq (x, y, loc) in
                BForm ((tmp, None), None)
        ]
    ];

exp:
    [ "exp" LEFTA
        [ x = SELF; "+"; y = SELF -> Add (x, y, loc)
          | x = SELF; "-"; y = SELF -> Subtract (x, y, loc)
                (* | x = INT; y = SELF -> *)
                (*       let ni=IConst (int_of_string x, loc)  *)
                (*       in Mult (ni, y, loc) *) (* bugs in post/t/ack3.ss : res >= 1 && m >= 0 && res >= 1 + m + n 0 >= res && 0 = m && res = n + 1 1 = 0 *)
          | x = INT; "*"; y = SELF ->
                let ni=IConst (int_of_string x, loc) 
                in Mult (ni, y, loc)
          | x = specvar             -> Var (x, loc)
          | x = INT                 -> IConst (int_of_string x, loc) 
          | NATIVEINT               -> Var (SpecVar(Named "abc", "abc", Unprimed),loc)
        ]
    ];

specvar:
    [ "specvar" NONA
        [ x = LIDENT -> get_var x tlist
          | x = UIDENT ->
                if is_substr "REC" x
                then
                  add_prefix (get_var (String.sub x 3 (String.length x - 3)) tlist) "REC"
                else get_var x tlist
        ]
    ];

END

(******************************************************************************)

let parse_fix s = Gram.parse_string expression (Loc.mk "<string>") s

let parse_fix s =
  Debug.no_1 "parse_fix" pr_id (pr_list !Cpure.print_formula) parse_fix s


