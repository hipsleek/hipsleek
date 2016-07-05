#include "xdebug.cppo"
open Gen
open VarGen
open Globals
open Ipure
open Cpure

(*type of permissions*)

type iperm = Ipure.exp option (*type of permission in iformula*)

(*which is Var for FPERM and CPERM
  and is Bptriple for BPERM*)
type cperm = Cpure.exp option (*type of permission in cformula*)

type cperm_var = Cpure.spec_var (*permission variable in cformula*)

let print_sv = ref (fun (c:spec_var) -> "cpure printer has not been initialized")
let print_exp = ref (fun (c:Cpure.exp) -> "cpure printer has not been initialized")

(* ================================= *)
(* UTILITIES for Permissions*)
let rev_trans_spec_var v = match v with Cpure.SpecVar (t,v,p)-> (v,p) 
(* ================================ *)

let string_of_perm_type t =
  match t with
  | Frac -> "Frac"
  | Count -> "Count"
  | NoPerm -> "NoPerm"
  | Dperm  -> "Dperm"
  | Bperm  -> "Bperm"

(*To disable concurrency verification, for testing purposes*)
let disable_para () =
  allow_norm:= true;
  perm:= NoPerm;
  (* ann_vp:= false; *)
  allow_ls:= false;
  allow_locklevel:=false

(*To enable concurrency verification*)
let enable_para () =
  Globals.old_norm_w_coerc := true;
  Globals.old_search_always := true;
  allow_norm:= false;
  allow_field_ann := false;
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
  (* Using variable permissions, a global variable is considered
     pass-by-ref.
     Reference: http://www.comp.nus.edu.sg/~leduykha/pubs/ldk-vperm-icfem2012-tr.pdf
  *)
  pass_global_by_value := false;
  (* 
     For testing.
     Clear this flag so that information about locksets are transferred
     until proving post-condition when new locks are created inside
     the scope of the procedure.
  *)
  (* Globals.elim_exists := false; *)
  allow_locklevel:=true

let allow_perm ():bool = 
  match !perm with
  | NoPerm -> false
  | _ -> true

let set_perm perm_str = 
  if perm_str = "fperm" then
    let () = allow_norm := false in
    perm:=Frac
  else if perm_str = "cperm" then perm:=Count
  else if perm_str = "dperm" then perm:=Dperm 
  else if perm_str = "bperm" then perm:=Bperm 
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
  val mkPermInv : Cpure.exp -> Cpure.formula
  val mkPermInv_var : cperm_var -> Cpure.formula
  val mkPermWrite : Cpure.exp -> Cpure.formula
  val mkPermWrite_var : cperm_var -> Cpure.formula
  val float_out_iperm : iperm -> loc -> (iperm * ( ( (ident*primed) * Ipure.formula )list) )
  val float_out_min_max_iperm : iperm -> loc -> (iperm * Ipure.formula option)
  val fv_cperm : cperm -> cperm_var list
  val get_cperm : cperm -> Cpure.exp list
  val get_cperm_var : cperm -> cperm_var list
  val subst_var_perm : (cperm_var * cperm_var) -> cperm -> cperm
  val fresh_cperm_var : cperm_var -> cperm_var
  val mkEq_cperm : cperm_var -> cperm_var -> loc -> Cpure.b_formula
  val rev_trans_perm : cperm -> iperm   (*revert from cperm to iperm*)
  val get_perm_var_lists : cperm -> cperm -> (cperm_var list) * (cperm_var list) (*get two equal-size lists of varperms*)
end;;

(*==============================*)
(*====Bounded permissions====*)
(*==============================*)
(*Because bperm requires a bound, there are no corresponding notions
  of DEFAULT empty permission (None) or full permission *)
module BPERM : PERM=
struct
  include PERM_const
  let cperm_typ = Bptyp (* Bounded permission typ*)
  let empty_iperm = None 
  let full_iperm =
    let exp_one = Ipure.IConst (0, no_pos) in
    Some (Ipure.Bptriple ((exp_one,exp_one,exp_one), no_pos)) (*undefined for bperm*)
  (*LDK: a specvar to indicate FULL permission*)
  (* let full_perm = Some (Cpure.SpecVar (cperm_typ, full_perm_name, Unprimed)) (\*undefined for bperm*\) *)
  let fv_iperm p = match p with
    | Some e -> (Ipure.afv e)
    | None -> []
  let get_iperm perm =
    match perm with
    | None -> failwith ("bounded permission cannot be empty in get_iperm")
    | Some f -> [f]
  let string_of_cperm (perm:cperm) : string =
    pr_opt !print_exp perm
  let apply_one_iperm = Ipure.e_apply_one
  let full_perm_var = (Cpure.SpecVar (cperm_typ, full_perm_name, Unprimed))
  let mkFullPerm_pure  (f:cperm_var) : Cpure.formula = (*TOCHECK*)
    Cpure.BForm (((Cpure.Eq (
        (Cpure.Var (f,no_pos)),
        (Cpure.Var (full_perm_var,no_pos)),
        no_pos
      )),None), None)
  let mkFullPerm_pure_from_ident id : Cpure.formula = (*TOCHECK*)
    let var = (Cpure.SpecVar (cperm_typ, id, Unprimed)) in
    mkFullPerm_pure var

  (*0<=c<=t+a & t>=0*)
  let mkPermInv (e:Cpure.exp) : Cpure.formula = (*TOCHECK*)
    (match e with
     | Cpure.Bptriple ((varc,vart,vara),e_pos) ->
       let c = Cpure.mkVar varc no_pos in
       let t = Cpure.mkVar vart no_pos in
       let a = Cpure.mkVar vara no_pos in
       let zero_exp = Cpure.IConst (0,no_pos) in
       let t_plus_a = mkAdd t a no_pos in
       let f1 = Cpure.mkGteExp c zero_exp no_pos in
       let f2 = Cpure.mkGteExp t_plus_a c no_pos in
       let f3 = Cpure.mkGteExp t zero_exp no_pos in
       let f12 = Cpure.mkAnd f1 f2 no_pos in
       let f123 = Cpure.mkAnd f12 f3 no_pos in
       f123
     | _ -> failwith ("[perm.ml] BPERM.mkPermInv : bounded permission is undefined (6)"))

  (*THIS METHOD SHOULD BE REMOVED in the end*)
  let mkPermInv_var (f:cperm_var) : Cpure.formula = (*TOCHECK*)
    Cpure.mkTrue no_pos

  let mkPermWrite_var (f:cperm_var) : Cpure.formula = (*TOCHECK*)
    Cpure.mkTrue no_pos

  (*c=t+a & c>0*)
  let mkPermWrite (e:Cpure.exp) : Cpure.formula = (*TOCHECK*)
    (match e with
     | Cpure.Bptriple ((varc,vart,vara),e_pos) ->
       let c = Cpure.mkVar varc no_pos in
       let t = Cpure.mkVar vart no_pos in
       let a = Cpure.mkVar vara no_pos in
       let zero_exp = Cpure.IConst (0,no_pos) in
       let t_plus_a = mkAdd t a no_pos in
       let f1 = Cpure.mkGtExp c zero_exp no_pos in (*c>0*)
       let f2 = Cpure.mkEqExp c t_plus_a no_pos in (*c=t+a*)
       let f12 = Cpure.mkAnd f1 f2 no_pos in
       f12
     | _ -> failwith ("[perm.ml] BPERM.mkPermWrite : bounded permission is undefined"))

  let full_perm_constraint = 
    Mcpure.OnePF (mkPermWrite_var full_perm_var)

  let float_out_iperm perm pos = 
    match perm with
    | None -> (None, [])
    | Some e ->
      match e with
      | Ipure.Bptriple ((ec,et,ea),e_pos) ->
        let float_one f = 
          match f with
          | Ipure.Var _ -> (f,[])
          | _ ->
            let nn_perm = (("bperm_"^(string_of_int pos.start_pos.Lexing.pos_lnum)^(fresh_trailer ())),Unprimed) in
            let nv_perm = Ipure.Var (nn_perm,pos) in
            let npf_perm = Ipure.BForm ((Ipure.Eq (nv_perm,f,pos), None), None) in (*TO CHECK: slicing for permissions*)
            (nv_perm,[(nn_perm,npf_perm)])
        in
        let ec_var,ec_ls = float_one ec in
        let et_var,et_ls = float_one et in
        let ea_var,ea_ls = float_one ea in
        (* let new_triple = Ipure.Bptriple ((ec_var,et_var,ea_var),e_pos) in *)
        let new_perm = Ipure.Bptriple ((ec_var,et_var,ea_var),e_pos) in
        (Some new_perm,ec_ls@et_ls@ea_ls)
      (* let nn_perm = ((perm_name^(string_of_int pos.start_pos.Lexing.pos_lnum)^(fresh_trailer ())),Unprimed) in *)
      (* let nv_perm = Ipure.Var (nn_perm,pos) in *)
      (* let npf_perm = Ipure.BForm ((Ipure.Eq (nv_perm,new_triple,pos), None), None) in (\*TO CHECK: slicing for permissions*\) *)
      (* let perm = [(nn_perm,npf_perm)] in *)
      (* (Some nv_perm,ec_ls@et_ls@ea_ls@perm) *)
      | _ -> failwith ("bounded permission is undefined")

  let float_out_min_max_iperm perm pos =
    match perm with
    | None -> (None, None)
    | Some f -> 
      match f with
      | Ipure.Bptriple ((ec,et,ea),e_pos) ->
        let float_one f =
          match f with
          | Ipure.Var _ -> (f, None)
          | _ ->
            let new_name_perm = fresh_var_name "bperm_" pos.start_pos.Lexing.pos_lnum in
            let nv_perm = Ipure.Var((new_name_perm, Unprimed), pos) in
            (nv_perm, Some (Ipure.float_out_pure_min_max (Ipure.BForm ((Ipure.Eq (nv_perm, f, pos), None), None))))
        in
        let ec_var,ec_f = float_one ec in
        let et_var,et_f = float_one et in
        let ea_var,ea_f = float_one ea in
        let new_triple = Ipure.Bptriple ((ec_var,et_var,ea_var),e_pos) in
        let p_f = List.fold_left (fun a b ->
            (match a with
             | None -> b
             | Some f1 ->
               (match b with
                | None -> Some f1
                | Some f2 -> Some (Ipure.mkAnd f1 f2 no_pos)))
          ) ec_f [et_f;ea_f] in
        (Some new_triple,p_f)
      | _ -> failwith ("float_out_min_max_iperm: expecting bperm triple")

  let fv_cperm perm : Cpure.spec_var list =
    match perm with
    | None -> []
    | Some f -> Cpure.afv f

  let get_cperm perm : Cpure.exp list =
    match perm with
    | None -> []
    | Some f -> [f]

  let get_cperm_var perm : cperm_var list =
    (match perm with
     | None -> []
     | Some f -> 
       (match f with
        | Cpure.Bptriple ((varc,vart,vara),_) -> [varc;vart;vara]
        | _ -> failwith ("get_cperm: expecting Bptriple")))

  let subst_var_perm ((fr, t) as s) perm =
    map_opt (Cpure.e_apply_one s) perm

  let fresh_cperm_var = Cpure.fresh_spec_var
  let mkEq_cperm v1 v2 pos =
    Cpure.mkEq_b (Cpure.mkVar v1 pos) ( Cpure.mkVar v2 pos) pos
  (*revert from cperm to iperm*)
  let rev_trans_perm perm =
    (match perm with
     | Some e ->
       (match e with
        | (Cpure.Bptriple ((c,t,a),p)) ->
          let nc = Ipure.Var (rev_trans_spec_var c, p) in
          let nt = Ipure.Var (rev_trans_spec_var t, p) in
          let na = Ipure.Var (rev_trans_spec_var a, p) in
          Some (Ipure.Bptriple ((nc,nt,na),p))
        | _ -> failwith ("rev_trans_perm: expecting Bptriple"))
     | None -> None)

  (*get two equal-size lists of varperms*)
  let get_perm_var_lists perm1 perm2 =
    (match perm1, perm2 with
     | Some _, Some _ ->
       let ls1 = get_cperm_var perm1 in
       let ls2 = get_cperm_var perm2 in
       (ls1,ls2)
     | Some _, None
     | None, Some _ ->
       report_error no_pos "[BPERM] get_perm_var_lists : unexpected for bperm"
     | None, None ->
       ([],[]))

end;; (*BPERM*)


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
  let string_of_cperm (perm:cperm) : string = pr_opt !print_exp perm
  let apply_one_iperm = Ipure.e_apply_one
  let full_perm_var = (Cpure.SpecVar (cperm_typ, full_perm_name, Unprimed))
  let mkFullPerm_pure  (f:cperm_var) : Cpure.formula = Cpure.BForm ((Cpure.Eq ( Cpure.Var (f,no_pos), Cpure.Var (full_perm_var,no_pos) , no_pos) ,None), None)
  let mkFullPerm_pure_from_ident id : Cpure.formula =   mkFullPerm_pure (Cpure.SpecVar (cperm_typ, id, Unprimed))
  let mkPermInv_var (f:cperm_var) : Cpure.formula = Cpure.mkTrue no_pos 
  let mkPermInv (e:Cpure.exp) : Cpure.formula = Cpure.mkTrue no_pos 

  let mkPermWrite_var (f:cperm_var) : Cpure.formula = Cpure.BForm ((Cpure.Eq ( Cpure.Var (f,no_pos), Cpure.Tsconst(Tree_shares.Ts.top, no_pos),no_pos),None),None)
  let mkPermWrite (e:Cpure.exp) : Cpure.formula =
    (match e with
     | Cpure.Var _ ->
       Cpure.BForm ((Cpure.Eq (e, Cpure.Tsconst(Tree_shares.Ts.top, no_pos),no_pos),None),None)
     | _ -> failwith ("[perm.ml] DPERM.mkPermWrite : expecting Var"))
  let full_perm_constraint = Mcpure.OnePF (mkPermWrite_var full_perm_var)
  let float_out_iperm perm pos =  match perm with
    | None -> (None, [])
    | Some f -> match f with
      | Ipure.Var _ -> (Some f,[])
      | _ ->
        let nn_perm = ((perm_name^(string_of_int pos.start_pos.Lexing.pos_lnum)^(fresh_trailer ())),Unprimed) in
        let nv_perm = Ipure.Var (nn_perm,pos) in
        let npf_perm = Ipure.BForm ((Ipure.Eq (nv_perm,f,pos), None), None) in (*TO CHECK: slicing for permissions*)
        (Some nv_perm,[(nn_perm,npf_perm)])
  let float_out_min_max_iperm perm pos = match perm with
    | None -> (None, None)
    | Some f ->  match f with
      | Ipure.Var _ -> (Some f, None)
      | _ ->
        let new_name_perm = fresh_var_name "ptr" pos.start_pos.Lexing.pos_lnum in
        let nv_perm = Ipure.Var((new_name_perm, Unprimed), pos) in
        (Some nv_perm, Some (Ipure.float_out_pure_min_max (Ipure.BForm ((Ipure.Eq (nv_perm, f, pos), None), None))))
  let fv_cperm perm = match perm with
    | None -> []
    | Some f -> Cpure.afv f

  let get_cperm perm = match perm with
    | None -> []
    | Some f -> [f]

  let get_cperm_var perm : cperm_var list =
    (match perm with
     | None -> []
     | Some f -> 
       (match f with
        | Cpure.Var (v,_) -> [v]
        | _ -> failwith ("get_cperm: expecting Var")))

  let subst_var_perm ((fr, t) as s) perm = map_opt (Cpure.e_apply_one s) perm
  let fresh_cperm_var = Cpure.fresh_spec_var
  let mkEq_cperm v1 v2 pos = Cpure.mkEq_b (Cpure.mkVar v1 pos) ( Cpure.mkVar v2 pos) pos
  let rev_trans_perm (c : cperm) : iperm =
    (match c with
     | Some f -> 
       (match f with
        | Cpure.Var (v,p) -> Some (Ipure.Var (rev_trans_spec_var v, p))
        | _ -> failwith ("rev_trans_perm: expecting Var"))
     | None -> None)

  (*get two equal-size lists of varperms*)
  let get_perm_var_lists perm1 perm2 =
    (match perm1, perm2 with
     | Some _, Some _ ->
       let ls1 = get_cperm_var perm1 in
       let ls2 = get_cperm_var perm2 in
       (ls1,ls2)
     | Some _, None
     | None, Some _ ->
       report_error no_pos "[DPERM] get_perm_var_lists : unexpected for Dperm"
     | None, None ->
       ([],[]))
end;; (*DPERM*)

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
    pr_opt !print_exp perm
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
  let mkPermInv (e:Cpure.exp) : Cpure.formula =
    (match e with
     | Cpure.Var _ ->
       let upper = 
         Cpure.BForm (((Cpure.Lte (e,(Cpure.FConst (1.0,no_pos)),no_pos)), None),None) in
       let lower =  Cpure.BForm (((Cpure.Gt (e,(Cpure.FConst (0.0,no_pos)),no_pos)), None),None) in
       let inv = 
         (Cpure.And (lower,upper,no_pos)) in
       inv
     | _ -> failwith ("[perm.ml] FPERM.mkPermInv : expecting Var"))

  let mkPermInv_var (f:cperm_var) : Cpure.formula =
    let f_var = Cpure.Var (f,no_pos) in
    mkPermInv f_var

  let mkPermWrite (e:Cpure.exp) : Cpure.formula =
    (match e with
     | Cpure.Var _ ->
       Cpure.BForm (((Cpure.Eq (e,(Cpure.FConst (1.0,no_pos)),no_pos)),None),None)
     | _ -> failwith ("[perm.ml] FPERM.mkPermWrite : expecting Var"))

  let mkPermWrite_var (f:cperm_var) : Cpure.formula =
    Cpure.BForm (((Cpure.Eq (
        (Cpure.Var (f,no_pos)),
        (Cpure.FConst (1.0,no_pos)),
        no_pos
      )),None),None)
  (*LDK: a constraint to indicate FULL permission = 1.0*)
  let full_perm_constraint = 
    Mcpure.OnePF (mkPermWrite_var full_perm_var)
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
  let float_out_min_max_iperm perm pos =
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
    | Some f -> Cpure.afv f

  let get_cperm perm =
    match perm with
    | None -> []
    | Some f -> [f]

  let get_cperm_var perm : cperm_var list =
    (match perm with
     | None -> []
     | Some f -> 
       (match f with
        | Cpure.Var (v,_) -> [v]
        | _ -> failwith ("get_cperm: expecting Var")))

  let subst_var_perm ((fr, t) as s) perm =
    map_opt (Cpure.e_apply_one s) perm
  let fresh_cperm_var = Cpure.fresh_spec_var
  let mkEq_cperm v1 v2 pos =
    Cpure.mkEq_b (Cpure.mkVar v1 pos) ( Cpure.mkVar v2 pos) pos
  let rev_trans_perm (c : cperm) : iperm =
    (match c with
     | Some f -> 
       (match f with
        | Cpure.Var (v,p) -> Some (Ipure.Var (rev_trans_spec_var v, p))
        | _ -> failwith ("rev_trans_perm: expecting Var"))
     | None -> None)

  (*get two equal-size lists of varperms*)
  let get_perm_var_lists perm1 perm2 =
    (match perm1, perm2 with
     | Some _, Some _ ->
       let ls1 = get_cperm_var perm1 in
       let ls2 = get_cperm_var perm2 in
       (ls1,ls2)
     | Some f1, None ->
       let f1 = Cpure.get_var f1 in
       ([f1],[full_perm_var])
     | None, Some f2 ->
       let f2 = Cpure.get_var f2 in
       ([full_perm_var],[f2])
     | None, None ->
       ([],[]))

end;; (*FPERM*)

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
    pr_opt !print_exp perm
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
  let mkPermInv (e:Cpure.exp) : Cpure.formula =
    (match e with
     | Cpure.Var _ ->
       let p_f = Cpure.mkGte e (Cpure.IConst (-1,no_pos)) no_pos in
       let b_f = (p_f,None) in
       Cpure.BForm (b_f,None)
     | _ -> failwith ("[perm.ml] FPERM.mkPermInv : expecting Var"))

  let mkPermInv_var (f:Cpure.spec_var) : Cpure.formula =
    let f_var = Cpure.Var (f,no_pos) in
    mkPermInv f_var

  let mkPermWrite (e:Cpure.exp) : Cpure.formula =
    (match e with
     | Cpure.Var _ ->
       Cpure.BForm (((Cpure.Eq (e,(Cpure.IConst (0,no_pos)),no_pos)),None),None)
     | _ -> failwith ("[perm.ml] CPERM.mkPermWrite : expecting Var"))

  let mkPermWrite_var (f:Cpure.spec_var) : Cpure.formula =
    Cpure.BForm (((Cpure.Eq (
        (Cpure.Var (f,no_pos)),
        (Cpure.IConst (0,no_pos)),
        no_pos
      )),None),None)

  let full_perm_constraint = 
    Mcpure.OnePF (mkPermWrite_var full_perm_var)

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
  let float_out_min_max_iperm perm pos =
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
    | Some f -> Cpure.afv f
  let get_cperm perm =
    match perm with
    | None -> []
    | Some f -> [f]
  let get_cperm_var perm : cperm_var list =
    (match perm with
     | None -> []
     | Some f -> 
       (match f with
        | Cpure.Var (v,_) -> [v]
        | _ -> failwith ("get_cperm: expecting Var")))
  let subst_var_perm ((fr, t) as s) perm = map_opt (Cpure.e_apply_one s) perm
  let fresh_cperm_var = Cpure.fresh_spec_var
  let mkEq_cperm v1 v2 pos = Cpure.mkEq_b (Cpure.mkVar v1 pos) ( Cpure.mkVar v2 pos) pos
  let rev_trans_perm (c : cperm) : iperm =
    (match c with
     | Some f -> 
       (match f with
        | Cpure.Var (v,p) -> Some (Ipure.Var (rev_trans_spec_var v, p))
        | _ -> failwith ("rev_trans_perm: expecting Var"))
     | None -> None)

  (*get two equal-size lists of varperms*)
  let get_perm_var_lists perm1 perm2 =
    (match perm1, perm2 with
     | Some _, Some _ ->
       let ls1 = get_cperm_var perm1 in
       let ls2 = get_cperm_var perm2 in
       (ls1,ls2)
     | Some f1, None ->
       let f1 = Cpure.get_var f1 in
       ([f1],[full_perm_var])
     | None, Some f2 ->
       let f2 = Cpure.get_var f2 in
       ([full_perm_var],[f2])
     | None, None ->
       ([],[]))

end;; (*CPERM*)


(*==============================*)
(*===dispacher for permissions==*)
(*==============================*)

(*get two equal-size lists of varperms*)
let get_perm_var_lists cperm1 cperm2 = 
  match !perm with
  | Count -> CPERM.get_perm_var_lists cperm1 cperm2
  | Dperm -> DPERM.get_perm_var_lists cperm1 cperm2
  | Bperm -> BPERM.get_perm_var_lists cperm1 cperm2
  | Frac -> FPERM.get_perm_var_lists cperm1 cperm2
  | NoPerm -> FPERM.get_perm_var_lists cperm1 cperm2

let rev_trans_perm cperm = 
  match !perm with
  | Count -> CPERM.rev_trans_perm cperm
  | Dperm -> DPERM.rev_trans_perm cperm
  | Bperm -> BPERM.rev_trans_perm cperm
  | Frac -> FPERM.rev_trans_perm cperm
  | NoPerm -> None

let cperm_typ () = 
  match !perm with
  | Count -> CPERM.cperm_typ
  | Dperm -> DPERM.cperm_typ
  | Bperm -> BPERM.cperm_typ
  | Frac -> FPERM.cperm_typ
  | NoPerm -> FPERM.cperm_typ

let empty_iperm () = 
  match !perm with
  | Count -> CPERM.empty_iperm
  | Dperm -> DPERM.empty_iperm
  | Bperm -> BPERM.empty_iperm
  | Frac ->FPERM.empty_iperm
  | NoPerm ->FPERM.empty_iperm

(* let empty_perm () =   match !perm with *)
(*     | Count -> CPERM.empty_perm *)
(*     | _ -> FPERM.empty_perm *)

let full_iperm () =   match !perm with
  | Count -> CPERM.full_iperm
  | Dperm -> DPERM.full_iperm
  | Bperm -> BPERM.full_iperm
  | Frac -> FPERM.full_iperm
  | NoPerm -> FPERM.full_iperm

(*LDK: a specvar to indicate FULL permission*)
let full_perm_name () =   match !perm with
  | Count -> CPERM.full_perm_name
  | Dperm -> DPERM.full_perm_name
  | Bperm -> BPERM.full_perm_name
  | Frac -> FPERM.full_perm_name
  | NoPerm -> FPERM.full_perm_name

(* let perm_name ()=   match !perm with *)
(*     | Count -> CPERM.perm_name *)
(*     | _ -> FPERM.perm_name *)

(* let full_perm ()=   match !perm with *)
(*     | Count -> CPERM.full_perm *)
(*     | _ -> FPERM.full_perm *)

let fv_iperm () =   match !perm with
  | Count -> CPERM.fv_iperm
  | Dperm -> DPERM.fv_iperm
  | Bperm -> BPERM.fv_iperm
  | Frac -> FPERM.fv_iperm
  | NoPerm -> FPERM.fv_iperm

let get_iperm p =  match !perm with
  | Count -> CPERM.get_iperm p
  | Dperm -> DPERM.get_iperm p
  | Bperm -> BPERM.get_iperm p
  | Frac -> FPERM.get_iperm p
  | NoPerm -> FPERM.get_iperm p

let apply_one_iperm () =   match !perm with
  | Count -> CPERM.apply_one_iperm
  | Dperm -> DPERM.apply_one_iperm
  | Bperm -> BPERM.apply_one_iperm
  | Frac -> FPERM.apply_one_iperm
  | NoPerm -> FPERM.apply_one_iperm

let full_perm_var () =  match !perm with
  | Count -> CPERM.full_perm_var
  | Dperm -> DPERM.full_perm_var
  | Bperm -> BPERM.full_perm_var
  | Frac -> FPERM.full_perm_var
  | NoPerm -> FPERM.full_perm_var

(*LDK: a constraint to indicate FULL permission = 1.0*)
let full_perm_constraint () =   match !perm with
  | Count -> CPERM.full_perm_constraint
  | Dperm -> DPERM.full_perm_constraint
  | Bperm -> BPERM.full_perm_constraint
  | Frac -> FPERM.full_perm_constraint
  | NoPerm -> FPERM.full_perm_constraint

let mkFullPerm_pure () =   match !perm with
  | Count -> CPERM.mkFullPerm_pure
  | Dperm -> DPERM.mkFullPerm_pure
  | Bperm -> BPERM.mkFullPerm_pure
  | Frac -> FPERM.mkFullPerm_pure
  | NoPerm -> FPERM.mkFullPerm_pure

(* let mkFullPerm_pure_from_ident =   match !perm with *)
(*     | Count -> CPERM.mkFullPerm_pure_from_ident *)
(*     | _ -> FPERM.mkFullPerm_pure_from_ident *)

(*create fractional permission invariant 0<f<=1*)
let mkPermInv () =   match !perm with
  | Count -> CPERM.mkPermInv
  | Dperm -> DPERM.mkPermInv
  | Bperm -> BPERM.mkPermInv
  | Frac -> FPERM.mkPermInv
  | NoPerm -> FPERM.mkPermInv

let mkPermInv_var () =   match !perm with
  | Count -> CPERM.mkPermInv_var
  | Dperm -> DPERM.mkPermInv_var
  | Bperm -> BPERM.mkPermInv_var
  | Frac -> FPERM.mkPermInv_var
  | NoPerm -> FPERM.mkPermInv_var

let mkPermWrite () =   match !perm with
  | Count -> CPERM.mkPermWrite
  | Dperm -> DPERM.mkPermWrite
  | Bperm -> BPERM.mkPermWrite
  | Frac -> FPERM.mkPermWrite
  | NoPerm -> FPERM.mkPermWrite

let mkPermWrite_var () =   match !perm with
  | Count -> CPERM.mkPermWrite_var
  | Dperm -> DPERM.mkPermWrite_var
  | Bperm -> BPERM.mkPermWrite_var
  | Frac -> FPERM.mkPermWrite_var
  | NoPerm -> FPERM.mkPermWrite_var

let float_out_iperm () =   match !perm with
  | Count -> CPERM.float_out_iperm
  | Dperm -> DPERM.float_out_iperm
  | Bperm -> BPERM.float_out_iperm
  | Frac -> FPERM.float_out_iperm
  | NoPerm -> FPERM.float_out_iperm

let float_out_min_max_iperm () =   match !perm with
  | Count -> CPERM.float_out_min_max_iperm
  | Dperm -> DPERM.float_out_min_max_iperm
  | Bperm -> BPERM.float_out_min_max_iperm
  | Frac -> FPERM.float_out_min_max_iperm
  | NoPerm -> FPERM.float_out_min_max_iperm

let fv_cperm p = match !perm with
  | Count -> CPERM.fv_cperm p
  | Dperm -> DPERM.fv_cperm p
  | Bperm -> BPERM.fv_cperm p
  | Frac -> FPERM.fv_cperm p
  | NoPerm -> FPERM.fv_cperm p

let get_cperm p = match !perm with
  | Count -> CPERM.get_cperm p
  | Dperm -> DPERM.get_cperm p
  | Bperm -> BPERM.get_cperm p
  | Frac -> FPERM.get_cperm p
  | NoPerm -> FPERM.get_cperm p

let get_cperm_var p = match !perm with
  | Count -> CPERM.get_cperm_var p
  | Dperm -> DPERM.get_cperm_var p
  | Bperm -> BPERM.get_cperm_var p
  | Frac -> FPERM.get_cperm_var p
  | NoPerm -> FPERM.get_cperm_var p

let subst_var_perm () =   match !perm with
  | Count -> CPERM.subst_var_perm
  | Dperm -> DPERM.subst_var_perm
  | Bperm -> DPERM.subst_var_perm
  | Frac -> FPERM.subst_var_perm
  | NoPerm -> FPERM.subst_var_perm

let fresh_cperm_var () =   match !perm with
  | Count -> CPERM.fresh_cperm_var
  | Dperm -> DPERM.fresh_cperm_var
  | Bperm -> BPERM.fresh_cperm_var
  | Frac -> FPERM.fresh_cperm_var
  | NoPerm -> FPERM.fresh_cperm_var

let mkEq_cperm () =   match !perm with
  | Count ->  CPERM.mkEq_cperm
  | Dperm -> DPERM.mkEq_cperm
  | Bperm -> BPERM.mkEq_cperm
  | Frac -> FPERM.mkEq_cperm
  | NoPerm -> FPERM.mkEq_cperm

let string_of_cperm () = match !perm with
  | Count ->  CPERM.string_of_cperm
  | Dperm -> DPERM.string_of_cperm
  | Bperm -> BPERM.string_of_cperm
  | Frac -> FPERM.string_of_cperm
  | NoPerm -> FPERM.string_of_cperm



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
  Debug.no_1 "drop_tauto" pr pr helper f
