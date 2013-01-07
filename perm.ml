open Gen
open Globals
open Ipure
open Cpure

(*type of permissions*)


type iperm = Ipure.exp option (*type of permission in iformula*)

type cperm = Cpure.spec_var option (*type of permission in cformula*)

type cperm_var = Cpure.spec_var (*permission variable in cformula*)

let print_sv = ref (fun (c:spec_var) -> "cpure printer has not been initialized")

let string_of_perm_type t =
  match t with
    | Frac -> "Frac"
    | Count -> "Count"
    | NoPerm -> "NoPerm"
    | Dperm  -> "Dperm"

(*To disable concurrency verification, for testing purposes*)
let disable_para () =
  allow_norm:= true;
  perm:= NoPerm;
  ann_vp:= false;
  allow_ls:= false;
  allow_locklevel:=false

(*To enable concurrency verification*)
let enable_para () =
  allow_norm:= false;
  perm:= (match !perm with
    | NoPerm -> Frac (*the default is fractional permission*)
    | _ -> !perm);
  ann_vp:= true;
  allow_ls:= true;
  (*
    need to enable filtering_flag, so that we could prove more programs.
    For example, if we want to prove: n>10 & f=1.0 |- n>=11.
    Because n is solved by an integer solver n>10 |- n>=11 valid.
    However, n is solved by an floating point solver, it is not valid.
    Therefore, we enable the flag, so that (f=1.0) is filtered out,
    therefore the remaining antecedent n>10 could be proven by
    an integer solver
  *)
  filtering_flag:=true; 
  allow_locklevel:=true

let allow_perm ():bool = 
  match !perm with
    | NoPerm -> false
    | _ -> true

let set_perm perm_str = 
  if perm_str = "fperm" then
    let _ = allow_norm := false in
    perm:=Frac
  else if perm_str = "cperm" then perm:=Count
  else if perm_str = "dperm" then perm:=Dperm 
  else perm:= NoPerm

(*Some constants*)
module PERM_const =
struct
  let full_perm_name = full_perm_var_name 
  let perm_name = ("perm_")
end;;

(*Generic for permissions*)
module type PERM =
  sig
    val full_perm_name : ident
    val cperm_typ :typ
    val empty_iperm : iperm
    (* val empty_perm : cperm *)
    val full_iperm : iperm
    (* val full_perm : cperm *)
    val fv_iperm : iperm -> (ident * primed) list
    val get_iperm : iperm -> Ipure.exp list
    val apply_one_iperm : ((ident * primed) * (ident*primed)) -> Ipure.exp -> Ipure.exp
    val full_perm_var : cperm_var
    val full_perm_constraint : Mcpure.mix_formula
    val string_of_cperm : cperm -> string
    val mkFullPerm_pure : cperm_var -> Cpure.formula
    (* val mkFullPerm_pure_from_ident : ident -> Cpure.formula *)
    val mkPermInv : cperm_var -> Cpure.formula
    val mkPermWrite : cperm_var -> Cpure.formula
    val float_out_iperm : iperm -> loc -> (iperm * ( ( (ident*primed) * Ipure.formula )list) )
    val float_out_mix_max_iperm : iperm -> loc -> (iperm * Ipure.formula option)
    val fv_cperm : cperm -> cperm_var list
    val get_cperm : cperm -> cperm_var list
    val subst_var_perm : (cperm_var * cperm_var) -> cperm -> cperm
    val fresh_cperm_var : cperm_var -> cperm_var
    val mkEq_cperm : cperm_var -> cperm_var -> loc -> Cpure.b_formula
   end;;

(*=======================================*)
(*====distinct fractional permissions====*)
(*=======================================*)
module DPERM : PERM=
struct
  include PERM_const
  let cperm_typ = Tree_sh
  let empty_iperm = None
  let full_iperm = Some (Ipure.Tsconst(Tree_shares.Ts.top,no_pos))
  let full_perm = Some (Cpure.SpecVar (cperm_typ, full_perm_name, Unprimed))
  let fv_iperm p= match p with
       | Some e -> (Ipure.afv e)
       | None -> []
  let get_iperm perm = match perm with
      | None -> []
      | Some f -> [f]
  let string_of_cperm (perm:cperm) : string = pr_opt !print_sv perm
  let apply_one_iperm = Ipure.e_apply_one
  let full_perm_var = (Cpure.SpecVar (cperm_typ, full_perm_name, Unprimed))
  let mkFullPerm_pure  (f:cperm_var) : Cpure.formula = Cpure.BForm ((Cpure.Eq ( Cpure.Var (f,no_pos), Cpure.Var (full_perm_var,no_pos) , no_pos) ,None), None)
  let mkFullPerm_pure_from_ident id : Cpure.formula =   mkFullPerm_pure (Cpure.SpecVar (cperm_typ, id, Unprimed))
  let mkPermInv (f:cperm_var) : Cpure.formula = Cpure.mkTrue no_pos 
    
  let mkPermWrite (f:cperm_var) : Cpure.formula = Cpure.BForm ((Cpure.Eq ( Cpure.Var (f,no_pos), Cpure.Tsconst(Tree_shares.Ts.top, no_pos),no_pos),None),None)
  let full_perm_constraint = Mcpure.OnePF (mkPermWrite full_perm_var)
  let float_out_iperm perm pos =  match perm with
      | None -> (None, [])
      | Some f -> match f with
            | Ipure.Var _ -> (Some f,[])
		    | _ ->
                let nn_perm = ((perm_name^(string_of_int pos.start_pos.Lexing.pos_lnum)^(fresh_trailer ())),Unprimed) in
			    let nv_perm = Ipure.Var (nn_perm,pos) in
                let npf_perm = Ipure.BForm ((Ipure.Eq (nv_perm,f,pos), None), None) in (*TO CHECK: slicing for permissions*)
                (Some nv_perm,[(nn_perm,npf_perm)])
  let float_out_mix_max_iperm perm pos = match perm with
      | None -> (None, None)
      | Some f ->  match f with
		    | Ipure.Var _ -> (Some f, None)
		    | _ ->
		        let new_name_perm = fresh_var_name "ptr" pos.start_pos.Lexing.pos_lnum in
		        let nv_perm = Ipure.Var((new_name_perm, Unprimed), pos) in
			    (Some nv_perm, Some (Ipure.float_out_pure_min_max (Ipure.BForm ((Ipure.Eq (nv_perm, f, pos), None), None))))
  let fv_cperm perm = match perm with
      | None -> []
      | Some f -> [f]

  let get_cperm perm = match perm with
      | None -> []
      | Some f -> [f]
  let subst_var_perm ((fr, t) as s) perm = map_opt (Cpure.subst_var s) perm
  let fresh_cperm_var = Cpure.fresh_spec_var
  let mkEq_cperm v1 v2 pos = Cpure.mkEq_b (Cpure.mkVar v1 pos) ( Cpure.mkVar v2 pos) pos
end;;

(*==============================*)
(*====fractional permissions====*)
(*==============================*)
module FPERM : PERM=
struct
  include PERM_const
  let cperm_typ = Float
  let empty_iperm = None
  (* let empty_perm = None *)
  let full_iperm = Some (Ipure.FConst (1.0, no_pos))
  (*LDK: a specvar to indicate FULL permission*)
  let full_perm = Some (Cpure.SpecVar (cperm_typ, full_perm_name, Unprimed))
  let fv_iperm p= match p with
       | Some e -> (Ipure.afv e)
       | None -> []
  let get_iperm perm =
    match perm with
      | None -> []
      | Some f -> [f]
  let string_of_cperm (perm:cperm) : string =
    pr_opt !print_sv perm
  let apply_one_iperm = Ipure.e_apply_one
  let full_perm_var = (Cpure.SpecVar (cperm_typ, full_perm_name, Unprimed))
  let mkFullPerm_pure  (f:cperm_var) : Cpure.formula = 
    Cpure.BForm (((Cpure.Eq (
        (Cpure.Var (f,no_pos)),
        (Cpure.Var (full_perm_var,no_pos)),
        no_pos
    )),None), None)
  let mkFullPerm_pure_from_ident id : Cpure.formula = 
    let var = (Cpure.SpecVar (cperm_typ, id, Unprimed)) in
    mkFullPerm_pure var
(*create fractional permission invariant 0<f<=1*)
  let mkPermInv (f:cperm_var) : Cpure.formula =
    let upper = 
      Cpure.BForm (((Cpure.Lte (
          (Cpure.Var (f,no_pos)),
          (Cpure.FConst (1.0,no_pos)),
          no_pos
      )), None),None) in
    let lower =  Cpure.BForm (((Cpure.Gt (
        (Cpure.Var (f,no_pos)),
        (Cpure.FConst (0.0,no_pos)),
        no_pos
    )), None),None) in
    let inv = 
      (Cpure.And (lower,upper,no_pos)) in
    inv
  let mkPermWrite (f:cperm_var) : Cpure.formula =
    Cpure.BForm (((Cpure.Eq (
        (Cpure.Var (f,no_pos)),
        (Cpure.FConst (1.0,no_pos)),
        no_pos
    )),None),None)
  (*LDK: a constraint to indicate FULL permission = 1.0*)
  let full_perm_constraint = 
    Mcpure.OnePF (mkPermWrite full_perm_var)
  let float_out_iperm perm pos = 
    match perm with
      | None -> (None, [])
      | Some f -> match f with
            | Ipure.Var _ -> (Some f,[])
		    | _ ->
                let nn_perm = ((perm_name^(string_of_int pos.start_pos.Lexing.pos_lnum)^(fresh_trailer ())),Unprimed) in
			    let nv_perm = Ipure.Var (nn_perm,pos) in
                let npf_perm = Ipure.BForm ((Ipure.Eq (nv_perm,f,pos), None), None) in (*TO CHECK: slicing for permissions*)
                (Some nv_perm,[(nn_perm,npf_perm)])
  let float_out_mix_max_iperm perm pos =
    match perm with
      | None -> (None, None)
      | Some f -> 
	      match f with
		    | Ipure.Null _
		    | Ipure.IConst _
		    | Ipure.Var _ -> (Some f, None)
		    | _ ->
		        let new_name_perm = fresh_var_name "ptr" pos.start_pos.Lexing.pos_lnum in
		        let nv_perm = Ipure.Var((new_name_perm, Unprimed), pos) in
			    (Some nv_perm, Some (Ipure.float_out_pure_min_max (Ipure.BForm ((Ipure.Eq (nv_perm, f, pos), None), None))))
  let fv_cperm perm =
    match perm with
      | None -> []
      | Some f -> [f]

  let get_cperm perm =
    match perm with
      | None -> []
      | Some f -> [f]
  let subst_var_perm ((fr, t) as s) perm =
    map_opt (Cpure.subst_var s) perm
  let fresh_cperm_var = Cpure.fresh_spec_var
  let mkEq_cperm v1 v2 pos =
    Cpure.mkEq_b (Cpure.mkVar v1 pos) ( Cpure.mkVar v2 pos) pos
end;;

(*==============================*)
(*=====counting permissions=====*)
(*==============================*)
module CPERM : PERM =
struct
  include PERM_const
  let cperm_typ = Int
  let empty_iperm = None
  (* let empty_perm = None *)
  let full_iperm = Some (Ipure.IConst (1, no_pos))
  (*LDK: a specvar to indicate FULL permission*)
  let full_perm = Some (Cpure.SpecVar (cperm_typ, full_perm_name, Unprimed))
  let fv_iperm p = match p with
       | Some e -> (Ipure.afv e)
       | None -> []
  let get_iperm perm =
    match perm with
      | None -> []
      | Some f -> [f]
  let string_of_cperm (perm:cperm) : string =
    pr_opt !print_sv perm
  let apply_one_iperm = Ipure.e_apply_one
  let full_perm_var = (Cpure.SpecVar (cperm_typ, full_perm_name, Unprimed))
  (*LDK: a constraint to indicate FULL permission = 0*)
  let mkFullPerm_pure  (f:cperm_var) : Cpure.formula = 
    Cpure.BForm (((Cpure.Eq (
        (Cpure.Var (f,no_pos)),
        (Cpure.Var (full_perm_var,no_pos)),
        no_pos
    )),None), None)
  let mkFullPerm_pure_from_ident id : Cpure.formula = 
    let var = (Cpure.SpecVar (cperm_typ, id, Unprimed)) in
    mkFullPerm_pure var
(*create counting permission invariant c >=-1*)
  let mkPermInv (f:Cpure.spec_var) : Cpure.formula =
    let p_f = Cpure.mkGte (Cpure.Var (f,no_pos)) (Cpure.IConst (-1,no_pos)) no_pos in
    let b_f = (p_f,None) in
    Cpure.BForm (b_f,None)
  let mkPermWrite (f:Cpure.spec_var) : Cpure.formula =
    Cpure.BForm (((Cpure.Eq (
        (Cpure.Var (f,no_pos)),
        (Cpure.IConst (0,no_pos)),
        no_pos
    )),None),None)
  let full_perm_constraint = 
    Mcpure.OnePF (mkPermWrite full_perm_var)

  let float_out_iperm perm pos = 
    match perm with
      | None -> (None, [])
      | Some f -> match f with
            | Ipure.Var _ -> (Some f,[])
		    | _ ->
                let nn_perm = ((perm_name^(string_of_int pos.start_pos.Lexing.pos_lnum)^(fresh_trailer ())),Unprimed) in
			    let nv_perm = Ipure.Var (nn_perm,pos) in
                let npf_perm = Ipure.BForm ((Ipure.Eq (nv_perm,f,pos), None), None) in (*TO CHECK: slicing for permissions*)
                (Some nv_perm,[(nn_perm,npf_perm)])
  let float_out_mix_max_iperm perm pos =
    match perm with
      | None -> (None, None)
      | Some f -> 
	      match f with
		    | Ipure.Null _
		    | Ipure.IConst _
		    | Ipure.Var _ -> (Some f, None)
		    | _ ->
		        let new_name_perm = fresh_var_name "ptr" pos.start_pos.Lexing.pos_lnum in
		        let nv_perm = Ipure.Var((new_name_perm, Unprimed), pos) in
			    (Some nv_perm, Some (Ipure.float_out_pure_min_max (Ipure.BForm ((Ipure.Eq (nv_perm, f, pos), None), None))))
  let fv_cperm perm =
    match perm with
      | None -> []
      | Some f -> [f]
  let get_cperm perm =
    match perm with
      | None -> []
      | Some f -> [f]
  let subst_var_perm ((fr, t) as s) perm = map_opt (Cpure.subst_var s) perm
  let fresh_cperm_var = Cpure.fresh_spec_var
  let mkEq_cperm v1 v2 pos = Cpure.mkEq_b (Cpure.mkVar v1 pos) ( Cpure.mkVar v2 pos) pos
end;;


(*==============================*)
(*===dispacher for permissions==*)
(*==============================*)
let cperm_typ () = 
  match !perm with
    | Count -> CPERM.cperm_typ
	| Dperm -> DPERM.cperm_typ
    | _ -> FPERM.cperm_typ

let empty_iperm () = 
  match !perm with
    | Count -> CPERM.empty_iperm
	| Dperm -> DPERM.empty_iperm
    | _ ->FPERM.empty_iperm

(* let empty_perm () =   match !perm with *)
(*     | Count -> CPERM.empty_perm *)
(*     | _ -> FPERM.empty_perm *)

let full_iperm () =   match !perm with
    | Count -> CPERM.full_iperm
	| Dperm -> DPERM.full_iperm
    | _ -> FPERM.full_iperm

(*LDK: a specvar to indicate FULL permission*)
let full_perm_name () =   match !perm with
    | Count -> CPERM.full_perm_name
	| Dperm -> DPERM.full_perm_name
    | _ -> FPERM.full_perm_name

(* let perm_name ()=   match !perm with *)
(*     | Count -> CPERM.perm_name *)
(*     | _ -> FPERM.perm_name *)

(* let full_perm ()=   match !perm with *)
(*     | Count -> CPERM.full_perm *)
(*     | _ -> FPERM.full_perm *)

let fv_iperm () =   match !perm with
    | Count -> CPERM.fv_iperm
	| Dperm -> DPERM.fv_iperm
    | _ -> FPERM.fv_iperm

let get_iperm p =  match !perm with
    | Count -> CPERM.get_iperm p
	| Dperm -> DPERM.get_iperm p
    | _ -> FPERM.get_iperm p

let apply_one_iperm () =   match !perm with
    | Count -> CPERM.apply_one_iperm
	| Dperm -> DPERM.apply_one_iperm
    | _ -> FPERM.apply_one_iperm

let full_perm_var () =  match !perm with
    | Count -> CPERM.full_perm_var
	| Dperm -> DPERM.full_perm_var
    | _ -> FPERM.full_perm_var

(*LDK: a constraint to indicate FULL permission = 1.0*)
let full_perm_constraint () =   match !perm with
    | Count -> CPERM.full_perm_constraint
	| Dperm -> DPERM.full_perm_constraint
    | _ -> FPERM.full_perm_constraint

let mkFullPerm_pure () =   match !perm with
    | Count -> CPERM.mkFullPerm_pure
	| Dperm -> DPERM.mkFullPerm_pure
    | _ -> FPERM.mkFullPerm_pure

(* let mkFullPerm_pure_from_ident =   match !perm with *)
(*     | Count -> CPERM.mkFullPerm_pure_from_ident *)
(*     | _ -> FPERM.mkFullPerm_pure_from_ident *)

(*create fractional permission invariant 0<f<=1*)
let mkPermInv () =   match !perm with
    | Count -> CPERM.mkPermInv
	| Dperm -> DPERM.mkPermInv
    | _ -> FPERM.mkPermInv

let mkPermWrite () =   match !perm with
    | Count -> CPERM.mkPermWrite
	| Dperm -> DPERM.mkPermWrite
    | _ -> FPERM.mkPermWrite

let float_out_iperm () =   match !perm with
    | Count -> CPERM.float_out_iperm
	| Dperm -> DPERM.float_out_iperm
    | _ -> FPERM.float_out_iperm

let float_out_mix_max_iperm () =   match !perm with
    | Count -> CPERM.float_out_mix_max_iperm
	| Dperm -> DPERM.float_out_mix_max_iperm
    | _ -> FPERM.float_out_mix_max_iperm

let fv_cperm p = match !perm with
    | Count -> CPERM.fv_cperm p
	| Dperm -> DPERM.fv_cperm p
    | _ -> FPERM.fv_cperm p

let get_cperm p = match !perm with
    | Count -> CPERM.get_cperm p
	| Dperm -> DPERM.get_cperm p
    | _ -> FPERM.get_cperm p

let subst_var_perm () =   match !perm with
    | Count -> CPERM.subst_var_perm
	| Dperm -> DPERM.subst_var_perm
    | _ -> FPERM.subst_var_perm

let fresh_cperm_var () =   match !perm with
    | Count -> CPERM.fresh_cperm_var
	| Dperm -> DPERM.fresh_cperm_var
    | _ -> FPERM.fresh_cperm_var

let mkEq_cperm () =   match !perm with
    | Count ->  CPERM.mkEq_cperm
	| Dperm -> DPERM.mkEq_cperm
    | _ -> FPERM.mkEq_cperm

let string_of_cperm () = match !perm with
  | Count ->  CPERM.string_of_cperm
  | Dperm -> DPERM.string_of_cperm
  | _ -> FPERM.string_of_cperm

  
  
let drop_tauto f = 
 let fv = full_perm_var () in
 let rec helper f = match f with 
  | BForm ((Eq (Tsconst (t,_), Var (v,_),_),_),_) 
  | BForm ((Eq (Var (v,_), Tsconst (t,_),_),_),_) -> if eq_spec_var v fv && Tree_shares.Ts.full t then mkTrue no_pos else f
  | BForm _ -> f
  | And (f1,f2,l) -> mkAnd (helper f1) (helper f2) l
  | AndList l -> AndList (map_l_snd helper l)
  | Or (f1,f2,l,p) -> mkOr (helper f1) (helper f2) l p 
  | Not (b,l,p) -> mkNot (helper b) l p 
  | Forall (s,f,l,p) -> Forall (s, helper f, l,p) 
  | Exists (v,f,l,p) -> Exists (v, helper f, l,p) in
 let pr =  !print_formula in
 Debug.no_1_loop "drop_tauto" pr pr helper f
