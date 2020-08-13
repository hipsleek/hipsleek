#include "xdebug.cppo"
open VarGen
(*
  Call Fixpoint Calculator for numerical domains
*)

open Globals
open Gen
open Cformula
module DD = Debug
module Pr = Cprinter
module CP = Cpure
module MCP = Mcpure
module TP = Tpdispatcher

let fix_num = new counter 0

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

let is_self = CP.is_self_var

let is_null = CP.is_null

let rec string_of_elems elems string_of sep = match elems with
  | [] -> ""
  | h::[] -> string_of h
  | h::t -> (string_of h) ^ sep ^ (string_of_elems t string_of sep)

(******************************************************************************)
let gen_fixcalc_file str_fc=
  let file_name = (List.hd !Globals.source_files) in
  let out_chn =
    let reg = Str.regexp "\(\.ss\)\|\(.slk\)" in
    let file_name1 = "logs/gen_" ^ (Str.global_replace reg ".fc" file_name) in
    (* let () = print_endline (file_name1 ^ ".fc") in *)
    let () = print_endline_quiet ("\n generating fixcalc file : " ^ file_name1) in
    (try Unix.mkdir "logs" 0o750 with _ -> ());
    (*open_out*) open_out_gen [Open_wronly; Open_append; Open_creat] 0o600 (file_name1)
  in
  let () = output_string out_chn str_fc in
  let () = close_out out_chn in
  ()


(******************************************************************************)

let fixcalc_of_spec_var x = match x with
  (* | CP.SpecVar (Named _, id, Unprimed) -> if String.compare id self =0 then id else "NOD" ^ id *)
  (* | CP.SpecVar (Named _, id, Primed) -> "NODPRI" ^ id *)
  (* TODO: Handle mixture of non-numerical and numerical variables *)
  (* Still have problem with the order of parameters of relation *)
  (*  | CP.SpecVar (Named _, id, Unprimed)*)
  (*  | CP.SpecVar (Named _, id, Primed) -> *)
  (*    report_error no_pos "Relation contains non-numerical variables"*)
  | CP.SpecVar (_, id, Unprimed) -> id
  | CP.SpecVar (_, id, Primed) -> "PRI" ^ id

let fixcalc_of_spec_var x =
  DD.no_1 "fixcalc_of_spec_var" !CP.print_sv (fun c->c) fixcalc_of_spec_var x

let rec fixcalc_of_exp_list e op number = match number with
  | 0 -> ""
  | 1 -> fixcalc_of_exp e
  | n -> fixcalc_of_exp e ^ op ^ (fixcalc_of_exp_list e op (n-1))

and fixcalc_of_exp e = match e with
  | CP.Null _ -> "null"
  | CP.Var (x, _) -> fixcalc_of_spec_var x
  | CP.IConst (i, _) -> string_of_int i
  | CP.FConst (f, _) -> string_of_float f
  | CP.Add (e1, e2, _) -> fixcalc_of_exp e1 ^ op_add ^ fixcalc_of_exp e2
  | CP.Subtract (e1, e2, _) ->
    fixcalc_of_exp e1 ^ op_sub ^ "(" ^ fixcalc_of_exp e2 ^ ")"
  | CP.Mult (e1, e2, _) ->
    begin
      match e1, e2 with
      | (CP.IConst (i,_), CP.IConst (j,_)) -> string_of_int (i*j)
      | (CP.IConst (i,_),_) ->
            if i >= 0 then
              fixcalc_of_exp_list e2 op_add i
            else
              "0 " ^ op_sub ^ (fixcalc_of_exp_list e2 op_sub (-i))
      | (_,CP.IConst (i,_)) ->
            if i >= 0 then
              fixcalc_of_exp_list e1 op_add i
            else
              "0 " ^ op_sub ^ (fixcalc_of_exp_list e1 op_sub (-i))
      | _ -> illegal_format ("Fixcalc.fixcalc_of_exp: Not supported expression")
    end
  | CP.InfConst _ -> "inf"
  | _ ->
        let () = x_binfo_hp (add_str "fixcalc_of_exp error :" (fun _ -> "" )) e no_pos in
        illegal_format ("Fixcalc.fixcalc_of_exp: Not supported expression")

let fixcalc_of_exp f=
  DD.no_1 "fixcalc_of_exp" !CP.print_exp (fun s->s) (fun f-> fixcalc_of_exp f) f
;;

let fixcalc_of_exp f=
  DD.no_1 "fixcalc_of_exp" !CP.print_exp (fun s->s) (fun f-> fixcalc_of_exp f) f
;;

let fixcalc_of_bool b =
  match b with
  | true -> "1=1"
  | false -> "1=0"

let rec fixcalc_of_b_formula b =
  let (pf, _) = b in
  match pf with
  | CP.BConst (b,_) -> fixcalc_of_bool b
  | CP.BVar (x, _) -> fixcalc_of_spec_var x
  | CP.Lt (e1, e2, _) -> fixcalc_of_exp e1 ^ op_lt ^ fixcalc_of_exp e2
  | CP.Lte (e1, e2, _) -> fixcalc_of_exp e1 ^ op_lte ^ fixcalc_of_exp e2
  | CP.Gt (e1, e2, _) -> fixcalc_of_exp e1 ^ op_gt ^ fixcalc_of_exp e2
  | CP.Gte (e1, e2, _) -> fixcalc_of_exp e1 ^ op_gte ^ fixcalc_of_exp e2
  | CP.Eq (e1, e2, _) ->
    if is_null e2 then fixcalc_of_exp e1 ^ op_lte ^ "0"
    else
    if is_null e1 then fixcalc_of_exp e2 ^ op_lte ^ "0"
    else fixcalc_of_exp e1 ^ op_eq ^ fixcalc_of_exp e2
  | CP.Neq (e1, e2, _) ->
    if is_null e1 then
      let s = fixcalc_of_exp e2 in s ^ op_gt ^ "0"
    else
    if is_null e2 then
      let s = fixcalc_of_exp e1 in s ^ op_gt ^ "0"
    else
      let s = fixcalc_of_exp e1 in
      let t = fixcalc_of_exp e2 in
      "((" ^ s ^ op_lt ^ t ^ ")" ^ op_or ^ "(" ^ s ^ op_gt ^ t ^ "))"
  | CP.EqMax (e1, e2, e3, _) ->
    let e1str = fixcalc_of_exp e1 in
    let e2str = fixcalc_of_exp e2 in
    let e3str = fixcalc_of_exp e3 in
    "((" ^ e2str ^ " >= " ^ e3str ^ " && " ^ e1str ^ " = " ^ e2str ^ ") || ("
    ^ e3str ^ " > " ^ e2str ^ " && " ^ e1str ^ " = " ^ e3str ^ "))"
  | CP.EqMin (e1, e2, e3, _) ->
    let e1str = fixcalc_of_exp e1 in
    let e2str = fixcalc_of_exp e2 in
    let e3str = fixcalc_of_exp e3 in
    "((" ^ e2str ^ " <= " ^ e3str ^ " && " ^ e1str ^ " = " ^ e2str ^ ") || ("
    ^ e3str ^ " < " ^ e2str ^ " && " ^ e1str ^ " = " ^ e3str ^ "))"
  | CP.RelForm (id,args,_) ->
        let () = x_tinfo_hp (add_str "fixcalc_of_b_formula RelForm: " Cprinter.string_of_b_formula) b no_pos in
        if List.exists
          (fun x -> match x with | CP.IConst _ -> true | _ -> false) args
        then "0=0"
        else
          (fixcalc_of_spec_var id) ^ "(" ^
              (string_of_elems args fixcalc_of_exp ",") ^ ")"
  | _ ->
    let () = x_binfo_hp (add_str "fixcalc trans error :" Cprinter.string_of_b_formula) b no_pos in
    illegal_format ("Fixcalc.fixcalc_of_b_formula: Do not support bag, list")

let fixcalc_of_b_formula f=
  DD.no_1 "fixcalc_of_b_formula" !CP.print_b_formula (fun s->s) (fun f-> fixcalc_of_b_formula f) f
;;

let rec fixcalc_of_pure_formula f = match f with
  | CP.BForm ((CP.BVar (x,_),_),_) -> fixcalc_of_spec_var x ^ op_gt ^ "0"
  | CP.BForm (b,_) -> fixcalc_of_b_formula b
  | CP.And (p1, p2, _) ->
    "" ^ fixcalc_of_pure_formula p1 ^ op_and ^ fixcalc_of_pure_formula p2 ^ "" (* baga/infer/btree.slk *)
  | CP.AndList b ->
    (match b with
     | [] -> fixcalc_of_pure_formula (CP.mkFalse no_pos)
     | (_,x)::t -> fixcalc_of_pure_formula
                     (List.fold_left (fun a (_,c) -> CP.mkAnd a c no_pos) x t)
    )
  | CP.Or (p1, p2,_ , _) ->
    "(" ^ fixcalc_of_pure_formula p1 ^ op_or ^ fixcalc_of_pure_formula p2 ^ ")"
  | CP.Not (p,_ , _) ->
    begin
      match p with
      | CP.BForm ((CP.BVar (x,_),_),_) -> fixcalc_of_spec_var x ^ op_lte ^ "0"
      | CP.BForm ((CP.Eq (e1,e2,loc),ba),fl) ->
            let new_f = CP.BForm ((CP.Neq (e1,e2,loc),ba),fl) in
            fixcalc_of_pure_formula new_f
      | CP.BForm ((CP.Neq (e1,e2,loc),ba),fl) ->
            let new_f = CP.BForm ((CP.Eq (e1,e2,loc),ba),fl) in
            fixcalc_of_pure_formula new_f
      | _ -> illegal_format ("Fixcalc.fixcalc_of_pure_formula: Not supported Not-formula ::"^(!CP.print_formula f))
    end
  | CP.Forall (sv, p,_ , _) ->
    " (forall (" ^ fixcalc_of_spec_var sv ^ ":" ^
    fixcalc_of_pure_formula p ^ ")) "
  | CP.Exists (sv, p,_ , _) ->
    " (exists (" ^ fixcalc_of_spec_var sv ^ ":" ^
    fixcalc_of_pure_formula p ^ ")) "
;;

let fixcalc_of_pure_formula f=
  (* let f = Omega.simplify f in *)
  DD.no_1 "fixcalc_of_pure_formula(really called)" !CP.print_formula (fun s->s) (fun f-> fixcalc_of_pure_formula f) f
;;

let fixcalc_of_pure_formula f=
  let f = x_add_1 Trans_arr.translate_array_one_formula f in
  fixcalc_of_pure_formula f
;;

let fixcalc_of_pure_formula f=
  DD.no_1 "fixcalc_of_pure_formula" !CP.print_formula (fun s->s) (fun f-> fixcalc_of_pure_formula f) f
;;

let rec fixcalc_of_h_formula f = match f with
  | Star {h_formula_star_h1 = h1; h_formula_star_h2 = h2} ->
    "(" ^ fixcalc_of_h_formula h1 ^ op_and ^ fixcalc_of_h_formula h2 ^ ")"
  | StarMinus {h_formula_starminus_h1 = h1; h_formula_starminus_h2 = h2} ->
    "(" ^ fixcalc_of_h_formula h1 ^ op_and ^ fixcalc_of_h_formula h2 ^ ")"
  | Conj {h_formula_conj_h1 = h1; h_formula_conj_h2 = h2}
  | ConjStar {h_formula_conjstar_h1 = h1; h_formula_conjstar_h2 = h2}
  | ConjConj {h_formula_conjconj_h1 = h1; h_formula_conjconj_h2 = h2} ->
    "(" ^ fixcalc_of_h_formula h1 ^ op_or ^ fixcalc_of_h_formula h2 ^ ")"
  | ThreadNode {h_formula_thread_node = sv; h_formula_thread_name = c;} ->
    (*TOCHECK: currently ignore delayed and resource*)
    if CP.is_self_spec_var sv then self ^ op_gt ^ "0"
    else c ^ "(" ^ (fixcalc_of_spec_var sv) ^ "," ^
         (string_of_elems [] fixcalc_of_spec_var ",") ^ ")"
  | DataNode {h_formula_data_node = sv; h_formula_data_name = c;
              h_formula_data_arguments = svs} ->
    (* if CP.is_self_spec_var sv then self ^ op_gt ^ "0" *)
    (* else c ^ "(" ^ (fixcalc_of_spec_var sv) ^ "," ^  *)
    (*                (string_of_elems svs fixcalc_of_spec_var ",") ^ ")" *)
    (fixcalc_of_spec_var sv)  ^ op_gt ^ "0"
  | ViewNode {h_formula_view_node = sv; h_formula_view_name = c;
              h_formula_view_arguments = svs} ->
    if CP.is_self_spec_var sv then self ^ op_gt ^ "0"
    else if (List.length svs = 0) then c ^ "(" ^ (fixcalc_of_spec_var sv) ^ ")"
    else
      let str =
        try
          let (svl1,pf) = Excore.map_num_invs # find c in
          let svl2 = sv::svs in
          let svl2 = if (List.length svl1 < List.length svl2) then
              List.rev (List.tl (List.rev svl2)) (* svl2 has idx variable, remove it *)
            else svl2 in
          let new_pf = CP.subst (List.combine svl1 svl2) pf in
          fixcalc_of_pure_formula new_pf
        with _ ->
          c ^ "(" ^ (fixcalc_of_spec_var sv) ^ "," ^
          (string_of_elems svs fixcalc_of_spec_var ",") ^ ")"
      in str
  (* fixcalc_of_pure_formula new_pf *)
  (* else if (List.length svs = 0) then c ^ "(" ^ (fixcalc_of_spec_var sv) ^ ")" *)
  (* else c ^ "(" ^ (fixcalc_of_spec_var sv) ^ "," ^ *)
  (*                (string_of_elems svs fixcalc_of_spec_var ",") ^ ")" *)
  | HTrue -> "HTrue"
  | HFalse -> "HFalse"
  | HEmp -> "0=0"
  | HRel _ -> "HTrue"
  | Hole _ | FrmHole _ | HVar _ ->
    illegal_format ("Fixcalc.fixcalc_of_h_formula: Not supported Hole-formula")
  | Phase _ -> Error.report_no_pattern ()

let fixcalc_of_mix_formula f = match f with
  | MCP.MemoF _ -> "1=1"
  | MCP.OnePF pf -> fixcalc_of_pure_formula pf

let rec fixcalc_of_formula e = match e with
  | Or _ ->
    illegal_format ("Fixcalc.fixcalc_of_formula: Not supported Or-formula")
  | Base {formula_base_heap = h; formula_base_pure = p} ->
    "(" ^ fixcalc_of_h_formula h ^ op_and ^ fixcalc_of_mix_formula p ^ ")"
  | Exists {formula_exists_qvars = svs; formula_exists_heap = h;
            formula_exists_pure = p} ->
    " exists (" ^ (string_of_elems svs fixcalc_of_spec_var ",") ^ ": " ^
    fixcalc_of_h_formula h ^ op_and ^ fixcalc_of_mix_formula p ^ ")"

let fixcalc_of_formula e =
  Debug.no_1 "fixcalc_of_formula" Cprinter.string_of_formula pr_id fixcalc_of_formula e

(******************************************************************************)

let subst_inv_lower_view_x view_invs f0=
  (*****************************************)
  let rec subst_h (hf: h_formula)=
    match hf with
    | Star s -> begin
        let nh1, ps1 = subst_h s.h_formula_star_h1 in
        let nh2, ps2 = subst_h s.h_formula_star_h2 in
        match nh1,nh2 with
        | HEmp,HEmp -> HEmp,ps1@ps2
        | HEmp,_ -> nh2,ps1@ps2
        | _ , HEmp -> nh1,ps1@ps2
        | _ ->
          (Star {s with h_formula_star_h1 = nh1;
                        h_formula_star_h2 = nh2
                }, ps1@ps2)
      end
    | ViewNode vn -> begin
        try
          let (_,(form_args, inv)) = List.find (fun (s1,_) -> String.compare s1 vn.h_formula_view_name = 0) view_invs in
          let sst = List.combine form_args (vn.h_formula_view_node::vn.h_formula_view_arguments) in
          (HEmp, [ (CP.subst sst (MCP.pure_of_mix inv))])
        with _ -> hf,[]
      end
    | _ -> hf,[]
  in
  let rec subst_helper f=
    match f with
    | Base fb ->
      let nh,ps = subst_h fb.formula_base_heap in
      let p = CP.conj_of_list ((MCP.pure_of_mix fb.formula_base_pure)::ps) (pos_of_formula f) in
      Base {fb with formula_base_pure = MCP.mix_of_pure p;
                    formula_base_heap = nh;}
    | Exists _ ->
      let quans,bare = split_quantifiers f in
      let nf = subst_helper  bare in
      (add_quantifiers quans nf)
    | Or orf ->
      let nf1= (subst_helper orf.formula_or_f1) in
      let nf2 = (subst_helper orf.formula_or_f2) in
      (Or {orf with formula_or_f1 = nf1;
                    formula_or_f2 = nf2;
          })
  in
  (*****************************************)
  if view_invs = [] then f0 else subst_helper f0

let subst_inv_lower_view view_invs f=
  let pr1= Cprinter.string_of_formula in
  let pr2 = pr_pair pr_id (pr_pair !CP.print_svl Cprinter.string_of_mix_formula) in
  Debug.no_2 "subst_inv_lower_view" (pr_list_ln pr2) pr1 pr1
    (fun _ _ -> subst_inv_lower_view_x view_invs f)
    view_invs f
(******************************************************************************)

(* let fixcalc_exe = "/home/thaitm/hg-repository/infer-rec/sleekex/bin/fixcalc " *)
(* let fixcalc_exe = "fixcalc " *)

let local_oc = "./fixcalc"
let global_oc = try FileUtil.which "fixcalc" with Not_found -> ""

let fixcalc_exe = if !Globals.is_solver_local then (ref "./fixcalc ") else (ref "fixcalc ")

let fixcalc_exe =
  if (Sys.file_exists local_oc) then ref (local_oc^" ")
  else if (Sys.file_exists global_oc)  then ref (global_oc^" ")
  else
    begin
      print_endline "ERROR : fixcalc cannot be found!!"; ref ("fixcalc ":string)
    end

let fixcalc_options = " -v:-1"
(* to suppress some printing *)

let syscall cmd =
  let () = Debug.ninfo_hprint (add_str  "cmd" pr_id) cmd no_pos in
  let ic, oc = Unix.open_process cmd in
  let buf = Buffer.create 16 in
  (try
     while true do
       Buffer.add_channel buf ic 1
     done
   with End_of_file -> ());
  let todo_unk = Unix.close_process (ic, oc) in
  (Buffer.contents buf)

(* TODO(WN): this already performs some feature of norm_pure_result *)
(* mainly for pointers; need to remove this redundancy for performance *)
(* need to handle SELF and REC variables (top-down fixcalc) *)
let parse_fix_svl svl res =
  let fixpoints = x_add_1 Parse_fix.parse_fix res in
  let svl1 = List.fold_left (fun acc pf ->
      acc@(CP.fv pf)
  ) [] fixpoints in
  let svl1 = CP.remove_dups_svl svl1 in
  let svl2 = List.map (fun sv1 ->
      match sv1 with CP.SpecVar(t1, id1, pr1) ->
          let svl = (List.filter (fun sv -> CP.eq_spec_var_rec sv sv1) svl) in
          match svl with
            | [] -> sv1
            | hd::tl -> CP.SpecVar(CP.type_of_spec_var hd, id1, pr1)
  ) svl1 in
  let sst = List.combine svl1 svl2 in
  let pr = Cprinter.string_of_typed_spec_var_list in
  let () = x_binfo_hp (add_str "svls (orig)" pr) svl no_pos in
  let () = x_binfo_hp (add_str "svl1 (from parse_fix)" pr) svl1 no_pos in
  let () = x_binfo_hp (add_str "svl2 (from parse_fix)" pr) svl2 no_pos in
   let fixpoints = List.map (fun fp -> CP.subst sst fp) fixpoints in
  fixpoints

let parse_fix_svl svl res =
  let pr = Cprinter.string_of_spec_var_list in
  let pr2 = (pr_list !CP.print_formula) in
  Debug.no_2 "parse_fix_svl" pr pr_id pr2 parse_fix_svl svl res

let parse_fix_rel_defs rel_defs res =
  let svl = List.fold_left (fun acc (pf1, pf2, _) ->
      acc@(CP.fv pf1)@(CP.fv pf2)
  ) [] rel_defs in
  let svl = CP.remove_dups_svl svl in
  let fs = parse_fix_svl svl res in
  List.map Omega.trans_bool fs

(******************************************************************************)

(* Deprecated *)
(*
  (* let compute_inv name vars fml pf = *)
  (* if not !Globals.do_infer_inv then pf *)
  (* else *)
  (* let output_of_sleek = "fixcalc"^(fix_num # str_get_next)^".inp" in *)
  (* let oc = open_out output_of_sleek in *)
  (* let input_fixcalc =  *)
  (* name ^ ":=" ^ "{" ^ "[" ^ self ^ "," ^  *)
  (* (string_of_elems vars fixcalc_of_spec_var ",") ^ "]" ^ " -> [] -> []: " ^ *)
  (* (string_of_elems fml (fun (c,_)-> fixcalc_of_formula c) op_or) ^ *)
  (* "\n};\n\nFix1:=bottomupgen([" ^ name ^ "]);\n\n" *)
  (* in  *)
  (* Printf.fprintf oc "%s" input_fixcalc; *)
  (* flush oc; *)
  (* close_out oc; *)
  (* let res = syscall (!fixcalc_exe ^ output_of_sleek ^ fixcalc_options) in *)
  (* let new_pf = List.hd (x_add_1 Parse_fix.parse_fix res) in *)
  (*   (\*let () = Pr.fmt_string("\nInv: "^(Pr.string_of_pure_formula new_pf)) in*\) *)
  (* let check_imply = Omega.imply new_pf pf "1" 100.0 in *)
  (* if check_imply then ( *)
  (* Pr.fmt_string "INV:  "; *)
  (* Pr.pr_angle name  *)
  (* (fun x -> Pr.fmt_string (Pr.string_of_typed_spec_var x)) vars; *)
  (* Pr.fmt_string ("\nOLD: " ^ (Pr.string_of_pure_formula pf) ^ *)
  (* "\nNEW: " ^ (Pr.string_of_pure_formula new_pf) ^ "\n\n");			 *)
  (* new_pf) *)
  (* else pf *)
*)

(******************************************************************************)

let rec remove_paren s n = if n=0 then "" else match s.[0] with
    | '(' -> remove_paren (String.sub s 1 (n-1)) (n-1)
    | ')' -> remove_paren (String.sub s 1 (n-1)) (n-1)
    | _ -> (String.sub s 0 1) ^ (remove_paren (String.sub s 1 (n-1)) (n-1))

(******************************************************************************)

let widen (f1 : CP.formula) (f2 : CP.formula) : CP.formula =
  let () = DD.ninfo_hprint (add_str "f1" Cprinter.string_of_pure_formula) f1 no_pos in
  let () = DD.ninfo_hprint (add_str "f2" Cprinter.string_of_pure_formula) f2 no_pos in
  let svl1 = CP.fv f1 in
  let svl2 = CP.fv f2 in
  let () = DD.ninfo_hprint (add_str "svl1" Cprinter.string_of_spec_var_list) svl1 no_pos in
  let () = DD.ninfo_hprint (add_str "svl2" Cprinter.string_of_spec_var_list) svl2 no_pos in

  (* Prepare the input for the fixpoint calculation *)
  let input_fixcalc =
    try
      "F1:={[" ^ (string_of_elems svl1 fixcalc_of_spec_var ",") ^ "]: " ^
      (string_of_elems [f1] fixcalc_of_pure_formula op_or) ^ "};\n" ^
      "F2:={[" ^ (string_of_elems svl2 fixcalc_of_spec_var ",") ^ "]: " ^
      (string_of_elems [f2] fixcalc_of_pure_formula op_or) ^ "};\n" ^
      "F2W:=widen(F1,F2,SimHeur);\nF2W;"
    with _ -> report_error no_pos "Error in widening with fixcalc"
  in
  DD.binfo_pprint ("input = " ^ input_fixcalc) no_pos;

  let _ =
    if !Globals.gen_fixcalc then gen_fixcalc_file input_fixcalc else ()
  in

  (* Call the fixpoint calculation *)
  let output_of_sleek = "fixcalc.inp" in
  let oc = open_out output_of_sleek in
  Printf.fprintf oc "%s" input_fixcalc;
  flush oc;
  close_out oc;
  let res = syscall (!fixcalc_exe ^ output_of_sleek ^ fixcalc_options) in

  (* Remove parentheses *)
  let res = remove_paren res (String.length res) in
  (* x_binfo_zp (lazy (("res = " ^ res ^ "\n"))) no_pos; *)

  (* Parse result *)
  let inv = List.hd (x_add_1 Parse_fix.parse_fix res) in
  let () = x_binfo_hp (add_str "result" Cprinter.string_of_pure_formula) inv no_pos in
  inv

let widen (f1 : CP.formula) (f2 : CP.formula) : CP.formula =
  let pr = !CP.print_formula in
  Debug.no_2 "widen" pr pr pr widen f1 f2
(******************************************************************************)

let compute_pure_inv (fmls:CP.formula list) (name:ident) (para_names:CP.spec_var list): CP.formula =
  let vars = para_names in
  let fmls = List.map (fun p ->
      let exists_vars = CP.diff_svl (CP.fv_wo_rel p) para_names in
      CP.mkExists exists_vars p None no_pos) fmls in

  (* Prepare the input for the fixpoint calculation *)
  let input_fixcalc =
    try
      name ^ ":={[" ^ (string_of_elems vars fixcalc_of_spec_var ",") ^
      "] -> [] -> []: " ^ (string_of_elems fmls fixcalc_of_pure_formula op_or) ^
      "\n};\nbottomupgen([" ^ name ^ "], [1], SimHeur);"
    with _ -> report_error no_pos "compute_pure_inv: Error in translating the input for fixcalc"
  in
  DD.ninfo_zprint (lazy (("Input of fixcalc: " ^ input_fixcalc))) no_pos;

  let _ =
    if !Globals.gen_fixcalc then gen_fixcalc_file input_fixcalc else ()
  in

  (* Call the fixpoint calculation *)
  let output_of_sleek = "logs/fixcalc"^(* (fix_num # str_get_next)^ *)".inp" in
  let () = x_tinfo_pp ("fixcalc file name: " ^ output_of_sleek) no_pos in
  let oc = open_out output_of_sleek in
  Printf.fprintf oc "%s" input_fixcalc;
  flush oc;
  close_out oc;
  let res = syscall (!fixcalc_exe ^" "^ output_of_sleek ^ fixcalc_options) in

  (* Remove parentheses *)
  let res = remove_paren res (String.length res) in
  DD.ninfo_zprint (lazy (("res = " ^ res ^ "\n"))) no_pos;

  (* Parse result *)
  let inv = List.hd (x_add_1 Parse_fix.parse_fix res) in
  inv

(******************************************************************************)
let slk2fix_body lower_invs fml0 vname dataname para_names=
  (*rename to avoid clashing, capture rev_subst also*)
  (* let self_sv = CP.SpecVar (Named dataname, self, Unprimed) in *)
  let vars =  para_names in
  let fr_vars = CP.fresh_spec_vars (vars) in
  let sst = List.combine vars fr_vars in
  let rev_sst = List.combine fr_vars vars in
  let fs = List.map (fun (f,_) -> x_add Cformula.subst sst (x_add subst_inv_lower_view lower_invs f)) fml0 in
  let input_fixcalc =
    try
      vname ^ ":={[" ^ (self) ^ (if (List.length fr_vars > 0) then "," else "") ^ (string_of_elems fr_vars fixcalc_of_spec_var ",") ^
      "] -> [] -> []: " ^
      (string_of_elems fs (fun c-> fixcalc_of_formula c) op_or) ^
      "\n};\n"
    with _ -> report_error no_pos "slk2fix_body: Error in translating the input for fixcalc"
  in
  DD.ninfo_zprint (lazy (("Input of fixcalc: " ^ input_fixcalc))) no_pos;
  (input_fixcalc, fr_vars, rev_sst)

let slk2fix_body_wo_fresh_vars lower_invs fml0 vname para_names=
  let vars =  para_names in
  let fs = List.map (fun (f,_) -> (x_add subst_inv_lower_view lower_invs f)) fml0 in
  let input_fixcalc =
    try
      vname ^ ":={[" ^ (self) ^ (if (List.length vars > 0) then "," else "") ^ (string_of_elems vars fixcalc_of_spec_var ",") ^
      "] -> [] -> []: " ^
      (string_of_elems fs (fun c-> fixcalc_of_formula c) op_or) ^
      "\n};\n"
    with _ -> report_error no_pos "slk2fix_body_wo_fresh_vars: Error in translating the input for fixcalc"
  in
  DD.ninfo_zprint (lazy (("Input of fixcalc: " ^ input_fixcalc))) no_pos;
  (input_fixcalc)

let slk2fix_header disj_num vnames=
  let () = DD.ninfo_hprint (add_str "vnames" (pr_list pr_id)) vnames no_pos in
  let ls_vnames = String.concat "," vnames in
  let ls_disj_nums=  String.concat "," (List.map (fun _ -> string_of_int disj_num) vnames) in
  let () = DD.ninfo_hprint (add_str "ls_vnames" pr_id) ls_vnames no_pos in
  "bottomupgen([" ^ ls_vnames ^ "], [" ^ ls_disj_nums ^ "], SimHeur);"

let compute_invs_fixcalc input_fixcalc=
  let rec get_lines s curp res=
    try
      let n = String.index_from s curp '\n' in
      let str = String.sub s curp (n-curp) in
      if String.length str > 0 then  get_lines s (n+1) res@[str] else res
    with _ ->
      (res)
  in
  let output_of_sleek =  (* Globals.fresh_any_name *) "logs/fixcalc"^(* (fix_num # str_get_next)^ *)".inp" in
  let () = DD.ninfo_pprint ("fixcalc file name: " ^ output_of_sleek) no_pos in
  let oc = open_out output_of_sleek in
  Printf.fprintf oc "%s" input_fixcalc;
  flush oc;
  close_out oc;
  let res = syscall (!fixcalc_exe ^" "^ output_of_sleek ^ fixcalc_options) in

  (* Remove parentheses *)
  let res = remove_paren res (String.length res) in

  (* Parse result *)
  let () = DD.ninfo_hprint (add_str "res= " pr_id) res no_pos in
  (* let () = print_endline ("res ="^ res) in *)
  let lines = get_lines res 0 [] in
  let () = DD.ninfo_hprint (add_str "lines" (pr_list_ln pr_id)) lines no_pos in
  let invs = List.fold_left (fun r line -> r@(x_add_1 Parse_fix.parse_fix line)) [] lines in
  let () = DD.ninfo_hprint (add_str "res(parsed)= " (pr_list !CP.print_formula)) invs no_pos in
  invs


let compute_invs_fixcalc input_fixcalc =
  let pr = (pr_list Cprinter.string_of_pure_formula) in
  Debug.no_1 "compute_invs_fixcalc" pr_id pr compute_invs_fixcalc input_fixcalc

let lookup_inv invs pos fr_vars rev_sst=
  let rec helper rest_invs=
    match rest_invs with
    | inv::tail ->
      let svl = CP.fv inv in
      if CP.intersect_svl svl fr_vars != [] then
        CP.subst rev_sst inv
      else helper tail
    | [] -> (* report_error no_pos "something wrong with fixcalc" *)
      raise Not_found
  in
  try
    helper invs
  with _ ->
    List.nth invs pos

(* TODO: TO MERGE WITH ABOVE *)
let compute_heap_pure_inv fml (name:ident) data_name (para_names:CP.spec_var list) transed_views: CP.formula =
  let format_str_file s =
    let src = Str.regexp "^" in
    let target = ">> " in
    ("\n"^Str.global_replace src target s) in
  (* let vars = para_names in *)
  (* Prepare the input for the fixpoint calculation *)
  let lower_invs = Cast.extract_view_x_invs transed_views in
  let input_fixcalc, fr_vars, rev_sst =
    (* try *)
    (*     name ^ ":={[" ^ self ^ "," ^ (string_of_elems vars fixcalc_of_spec_var ",") ^  *)
    (*     "] -> [] -> []: " ^  *)
    (*     (string_of_elems fml (fun (c,_)-> fixcalc_of_formula (x_add subst_inv_lower_view lower_invs c)) op_or) ^ *)
    (*     "\n};\nbottomupgen([" ^ name ^ "], [1], SimHeur);" *)
    (*   with _ -> report_error no_pos "Error in translating the input for fixcalc" *)
    let fixc_body,fr_vars, rev_sst = slk2fix_body lower_invs fml name data_name para_names in
    let fixc_header = slk2fix_header 1 [name] in
    (fixc_body ^ fixc_header, fr_vars, rev_sst)
  in
  x_tinfo_zp (lazy (("Input of fixcalc: " ^ (format_str_file input_fixcalc)))) no_pos;

  let _ =
    if !Globals.gen_fixcalc then gen_fixcalc_file input_fixcalc else ()
  in

  (* (\* Call the fixpoint calculation *\) *)
  (* let output_of_sleek =  Globals.fresh_any_name "fixcalc.inp" in *)
  (* let oc = open_out output_of_sleek in *)
  (* Printf.fprintf oc "%s" input_fixcalc; *)
  (* flush oc; *)
  (* close_out oc; *)
  (* let res = syscall (!fixcalc_exe ^ output_of_sleek ^ fixcalc_options) in *)

  (* (\* Remove parentheses *\) *)
  (* let res = remove_paren res (String.length res) in *)
  (* DD.ninfo_zprint (lazy (("res = " ^ res ^ "\n"))) no_pos; *)

  (* (\* Parse result *\) *)
  (* let () = DD.ninfo_hprint (add_str "res(parsed)= " pr_id) res no_pos in *)
  (* let inv = List.hd (Parse_fix.parse_fix res) in *)
  (* let () = DD.info_hprint (add_str "res(parsed)= " !CP.print_formula) inv no_pos in *)
  (* inv *)
  let invs = (x_add_1 compute_invs_fixcalc input_fixcalc) in
  lookup_inv invs 0 fr_vars rev_sst

let compute_heap_pure_inv fml (name:ident) data_name (para_names:CP.spec_var list) lower_invs: CP.formula =
  let pr1 = !CP.print_formula in
  let pr2 (f, _) = Cprinter.string_of_formula f in
  Debug.no_3 "compute_heap_pure_inv" (pr_list_ln pr2) pr_id !CP.print_svl pr1
    (fun _ _ _ ->  compute_heap_pure_inv fml name data_name para_names lower_invs)
    fml name para_names

(******************************************************************************)

let compute_inv_x name vars fml data_name lower_views pf =
  if List.exists CP.is_bag_typ vars then Fixbag.compute_inv name vars fml pf 1
  else
  if not !Globals.do_infer_inv then pf
  else let new_pf = x_add compute_heap_pure_inv fml name data_name vars lower_views in
    let check_imply = TP.imply_raw new_pf pf in
    if check_imply then
      let () = DD.ninfo_hprint (add_str ("new 1 inv("^name^")") !CP.print_formula) new_pf no_pos in
      let () = print_endline_quiet "" in
      new_pf
    else pf

let compute_inv name vars fml data_name lower_views pf =
  let pr1 (f,_) = Cprinter.prtt_string_of_formula f in
  let pr2 = !CP.print_formula in
  Debug.no_4 " compute_inv" pr_id !CP.print_svl (pr_list_ln pr1) pr2 pr2
    (fun _ _ _ _ -> compute_inv_x name vars fml data_name lower_views pf)
    name vars fml pf

(*compute invs of views in one loop*)
let compute_inv_mutrec mutrec_vnames views =
  (**************************************************)
  let str_cmp s1 s2 = String.compare s1 s2 = 0 in
  let rec lookup_map vmaps vname0=
    match vmaps with
    | [] -> raise Not_found
    | (vname,b,c):: rest -> if str_cmp vname vname0 then
        (vname,b,c) else
        lookup_map rest vname0
  in
  let update_view invs pos vmaps view all_rev_sst=
    try
      let (vname, fr_vars, rev_sst) = lookup_map vmaps view.Cast.view_name in
      let new_pf = lookup_inv invs pos fr_vars rev_sst in
      (* let pf =  MCP.pure_of_mix view.Cast.view_user_inv in *)
      let check_imply = true (* TP.imply_raw new_pf pf *) in
      if check_imply then
        let _ = DD.ninfo_hprint (add_str ("new 2 inv(" ^ vname^")") !CP.print_formula) new_pf no_pos in
        (* let _ = print_endline "" in *)
        (* let idx = CP.mk_typed_spec_var Int "idx" in *)
        (* let new_pf_svl = CP.fv new_pf in *)
        (* let new_pf = if List.mem idx new_pf_svl then CP.wrap_exists_svl new_pf [idx] else new_pf in *)
        let () = DD.ninfo_hprint (add_str "new_pf" !CP.print_formula) new_pf no_pos in
        let memo_pf_P = MCP.memoise_add_pure_P (MCP.mkMTrue no_pos) new_pf in
        (* let memo_pf_N = MCP.memoise_add_pure_N (MCP.mkMTrue pos) inv in *)
        (* let xpure_flag = Tpdispatcher.check_diff memo_pf_N memo_pf_P in *)
        begin
          x_tinfo_hp (add_str "memo_pf_P" Cprinter.string_of_mix_formula) memo_pf_P no_pos;
          view.Cast.view_fixcalc <- Some memo_pf_P;
          (* view.Cast.view_x_formula <- memo_pf_P; *)
          view.Cast.view_baga_x_over_inv <- Some [([], new_pf)];
          view
        end
      else view
    with _ -> view
  in
  (**************************************************)
  if (not !Globals.do_infer_inv) && (not !Globals.gen_baga_inv) then
    views
  else
    (*get all views of the loop*)
    (*subst inv of their depent (lower) views
      (remember to remove members of the loop)
    *)
    let mutrec_views, rest = List.partition (fun v ->
        Gen.BList.mem_eq str_cmp v.Cast.view_name  mutrec_vnames
      ) views in
    let lower_invs = Cast.extract_view_x_invs rest in
    (*gen cf of each view*)
    let fixc_bodys, vnames, vmaps = List.fold_left (fun (r1,r2,r3) view ->
        let fixc_body, fr_vars, rev_sst = slk2fix_body lower_invs
            view.Cast.view_un_struc_formula view.Cast.view_name view.Cast.view_data_name view.Cast.view_vars in
        (r1 ^ "\n" ^ fixc_body, r2@[view.Cast.view_name], r3@[(view.Cast.view_name,fr_vars, rev_sst)])
      ) ("",[],[]) mutrec_views in
    let fixc_header = slk2fix_header 3 vnames in
    let input_fixcalc  =  fixc_bodys ^ fixc_header in
    let () = DD.ninfo_hprint (add_str "Input of fixcalc " pr_id) input_fixcalc no_pos in
    let _ =
      if !Globals.gen_fixcalc then gen_fixcalc_file input_fixcalc else ()
    in
    (* Call the fixpoint calculation *)
    let invs = (x_add_1 compute_invs_fixcalc input_fixcalc) in
    let () = x_tinfo_hp (add_str "invs" (pr_list Cprinter.string_of_pure_formula)) invs no_pos in
    (*get result and revert back*)
    (*set invs + flags*)
    let all_rev_sst = List.fold_left (fun r (_,_,sst) -> r@sst) [] vmaps in
    let r,_ = List.fold_left (fun (res,pos) view ->
        let nview = update_view invs pos vmaps view all_rev_sst in
        (res@[nview], pos+1)
      ) ([], 0) views in
    r

let compute_inv_mutrec mutrec_views views =
  let pr1 = pr_list pr_id in
  let pr2 v = (pr_pair pr_id (pr_option Cprinter.string_of_mix_formula)) (v.Cast.view_name,v.Cast.view_fixcalc) in
  Debug.no_eff_2 "compute_inv_mutrec" [false;true] pr1 (pr_list pr2)  (pr_list pr2)
    (fun _ _ -> compute_inv_mutrec mutrec_views views)
    mutrec_views views

(******************************************************************************)

(******************************************************************************)

let compute_pure_inv_x (fmls:CP.formula list) (name:ident) (para_names:CP.spec_var list): CP.formula =
  let vars = para_names in
  let fmls = List.map (fun p ->
      let exists_vars = CP.diff_svl (CP.fv_wo_rel p) para_names in
      CP.mkExists exists_vars p None no_pos) fmls in

  (* Prepare the input for the fixpoint calculation *)
  let input_fixcalc =
    try
      name ^ ":={[" ^ (string_of_elems vars fixcalc_of_spec_var ",") ^
      "] -> [] -> []: " ^ (string_of_elems fmls fixcalc_of_pure_formula op_or) ^
      "\n};\nbottomupgen([" ^ name ^ "], [1], SimHeur);"
    with _ -> report_error no_pos "compute_pure_inv_x: Error in translating the input for fixcalc"
  in
  DD.ninfo_zprint (lazy (("Input of fixcalc: " ^ input_fixcalc))) no_pos;

  let _ =
    if !Globals.gen_fixcalc then gen_fixcalc_file input_fixcalc else ()
  in

  (* Call the fixpoint calculation *)
  let output_of_sleek = (* Globals.fresh_any_name *) "logs/fixcalc"^(* (fix_num # str_get_next)^ *)".inp" in
  let () = DD.ninfo_pprint ("fixcalc file name: " ^ output_of_sleek) no_pos in
  let oc = open_out output_of_sleek in
  Printf.fprintf oc "%s" input_fixcalc;
  flush oc;
  close_out oc;
  let res = syscall (!fixcalc_exe ^" "^ output_of_sleek ^ fixcalc_options) in

  (* Remove parentheses *)
  let res = remove_paren res (String.length res) in
  DD.ninfo_zprint (lazy (("res = " ^ res ^ "\n"))) no_pos;

  (* Parse result *)
  let inv = List.hd (x_add_1 Parse_fix.parse_fix res) in
  inv

let compute_pure_inv (fmls:CP.formula list) (name:ident) (para_names:CP.spec_var list): CP.formula =
  let pr1 = !CP.print_formula in
  Debug.no_3 "compute_pure_inv" (pr_list_ln pr1) pr_id !CP.print_svl pr1
    (fun _ _ _ ->  compute_pure_inv_x fmls name para_names)
    fmls name para_names

(******************************************************************************)

let rec is_rec pf = match pf with
  | CP.BForm (bf,_) -> CP.is_RelForm pf
  | CP.And (f1,f2,_) -> is_rec f1 || is_rec f2
  | CP.AndList b -> exists_l_snd is_rec b
  | CP.Or (f1,f2,_,_) -> is_rec f1 || is_rec f2
  | CP.Not (f,_,_) -> is_rec f
  | CP.Forall (_,f,_,_) -> is_rec f
  | CP.Exists (_,f,_,_) -> is_rec f

let rec is_not_rec pf = match pf with
  | CP.BForm (bf,_) -> not(CP.is_RelForm pf)
  | CP.And (f1,f2,_) -> is_not_rec f1 && is_not_rec f2
  | CP.AndList b -> all_l_snd is_not_rec b
  | CP.Or (f1,f2,_,_) -> is_not_rec f1 && is_not_rec f2
  | CP.Not (f,_,_) -> is_not_rec f
  | CP.Forall (_,f,_,_) -> is_not_rec f
  | CP.Exists (_,f,_,_) -> is_not_rec f

let substitute_args_x a_rel = match a_rel with
  | CP.BForm ((CP.RelForm (SpecVar (_,id,_) as name,args,o1),o2),o3) ->
    let new_args, subs =
      let prog = !Cast.global_prog in
      (*   match !Cast.global_prog with *)
      (*   | Some p -> p *)
      (*   | None -> failwith (x_loc^"substitute_args: Initialize global_prog first!") *)
      (* in *)
      let typed_args =
        try
          List.combine (x_add_1 Cast.look_up_rel_args_type_from_prog prog id) args
        with _ ->  (* args *)
            failwith "substitute_args: failure with look_up_rel_args_type"
      in
      List.split
        (List.map (fun (t,e) ->
             match e with
             | CP.Var _ -> (e, [])
             | _ ->
               (try
                  (* TODO: Must refine the renaming method. It is really awkward now... *)
                  let fvs = CP.afv e in
                  let arb =
                    if List.length fvs > 0 then
                      begin
                        match (List.hd (CP.afv e)) with
                        | SpecVar (_,new_name,_) ->
                          new_name
                      end
                    else
                      "c"
                  in
                  let arb = CP.mk_typed_spec_var t arb in
                  let var = CP.fresh_spec_var_prefix "fc" arb in
                  let var = CP.mkVar var no_pos in
                  (var, [CP.mkEqExp var e no_pos])
                with _ -> (e,[]))
           ) typed_args)
    in
    (CP.BForm ((CP.RelForm (name,new_args,o1),o2),o3), List.concat subs)
  | _ -> report_error no_pos "substitute_args_x Expected a relation"

let substitute_args rcase =
  (* TODOIMM this throws an exception for imm ex8e1f.ss. To fix *)
  try
    let rels = CP.get_RelForm rcase in
    let rcase_wo_rel = x_add_1 TP.simplify_raw (CP.drop_rel_formula rcase) in
    let rels, subs =
      List.split (List.map (fun rel -> substitute_args_x rel) rels) in
    let res = [rcase_wo_rel]@rels@(List.concat subs) in
    CP.conj_of_list res no_pos
  with Invalid_argument _ -> rcase

let substitute_args rcase =
  let pr = !CP.print_formula in
  Debug.no_1 "substitute_args" pr pr substitute_args rcase

(* TODO: Need to handle computed relation in the future *)
let rec get_other_branches or_fml args = match or_fml with
  | Or fml ->
    (get_other_branches fml.formula_or_f1 args) @
    (get_other_branches fml.formula_or_f2 args)
  | _ ->
    (* TODO CHECK: a *)
    let _,p,_,_,_,a = split_components or_fml in
    let conjs = CP.list_of_conjs (MCP.pure_of_mix p) in
    List.filter (fun pure -> CP.subset args (CP.fv pure)) conjs

let process_base_rec pfs rel specs =
  match x_add_1 CP.get_rel_id rel with
  | None -> report_error no_pos "process_base_rec: Expected a relation"
  | Some ivs ->
    let (rcases, bcases) = List.partition is_rec pfs in

    (* TODO *)
    let or_post = get_or_post specs (CP.get_rel_id_list rel) in
    let bcases =
      begin
        match or_post with
        | [] -> bcases
        | [or_fml] ->
          let other_branches = get_other_branches or_fml (CP.get_rel_args rel) in
          let other_branches = List.map (fun p -> CP.mkNot_s p) other_branches in
          let pure_other_branches = CP.conj_of_list other_branches no_pos in
          List.filter (fun b -> TP.is_sat_raw (MCP.mix_of_pure
                                                 (CP.mkAnd b pure_other_branches no_pos))) bcases
        | _ -> bcases
      end
    in
    (* let () = x_binfo_pp ("bcases:"^((pr_list !CP.print_formula) bcases)) no_pos in *)
    (* let () = x_binfo_pp ("rcases:"^((pr_list !CP.print_formula) rcases)) no_pos in *)
    let no_of_disjs =
      List.map (fun b ->
          let disjs = CP.list_of_disjs b in
          (* TODO *)
          let cond = List.exists (fun d ->
              let conjs = CP.list_of_conjs d in
              List.exists (fun c -> CP.is_eq_const c) conjs
            ) disjs
          in
          if cond then 1 else List.length disjs
        ) bcases in
    let no_of_disjs = List.fold_left (fun a b -> max a b) 1 no_of_disjs in

    (* Normalize each relation *)
    let rcases = List.map (fun x -> substitute_args x) rcases in
    let () = x_tinfo_pp ("rcases:"^((pr_list !CP.print_formula) rcases)) no_pos in
    bcases @ rcases, no_of_disjs

let compute_def (rel_fml, pf, no) ante_vars =
  let (name,vars) = match rel_fml with
    | CP.BForm ((CP.RelForm (name,args,_),_),_) ->
      (* let _ = print_endline ("### args:"^((pr_list !CP.print_exp) args)) in *)
      (CP.name_of_spec_var name, (List.concat (List.map CP.afv args)))
    | _ -> report_error no_pos
             ("Wrong format: " ^ (!CP.print_formula rel_fml) ^ "\n")
  in
  (* let _ = print_endline ("compute_def vars: "^(Cprinter.string_of_typed_spec_var_list vars)) in *)
  let pre_vars, post_vars =
    List.partition (fun v -> List.mem v ante_vars) vars in
  let (pre_vars,post_vars,pf) = Trans_arr.expand_array_sv_wrapper rel_fml pf pre_vars post_vars in
  (* let pre_vars = Trans_arr.expand_array_variable pf pre_vars in *)
  (* let post_vars = Trans_arr.expand_array_variable pf post_vars in *)
  (* let pf = Trans_arr.expand_relation pf in *)
  begin
    print_endline_quiet "\n*************************************";
    print_endline_quiet "****** Before putting into fixcalc*******";
    print_endline_quiet ("pre_vars: "^(string_of_spec_var_list pre_vars));
    print_endline_quiet ("post_vars: "^(string_of_spec_var_list post_vars));
    print_endline_quiet "*************************************";
    print_endline_quiet ("formula: "^(!CP.print_formula pf));
    print_endline_quiet "*************************************";
  end;
  try
    let (pf2,subs) = x_add_1 CP.extract_mult pf in
    let pf = x_add_1 CP.drop_nonlinear_formula pf in
    let rhs = x_add_1 fixcalc_of_pure_formula pf in
    let input_fixcalc =
      name ^ ":={["
      ^ (string_of_elems pre_vars fixcalc_of_spec_var ",") ^ "] -> ["
      ^ (string_of_elems post_vars fixcalc_of_spec_var ",") ^ "] -> []: "
      ^ rhs ^ "\n};"
    in input_fixcalc
  with e ->
    let () = y_binfo_pp ("Toan : need to remove * in pf for fixcalc") in
    report_error ~exc:(Some e) no_pos (x_loc^"compute_def:Error in translating the input for fixcalc")
;;

let compute_def (rel_fml, pf, no) ante_vars =
  let pr1 = function
    | (rel_f,pf,_) -> ("rel_fml: "^(!CP.print_formula rel_f)^"\npf: "^(!CP.print_formula pf))
  in
  Debug.no_2 "compute_def" pr1 (pr_list !CP.print_sv) (fun x -> x) (fun one two -> compute_def one two) (rel_fml, pf, no) ante_vars
;;

let string_of_rel_defs =
  let pr0 = !CP.print_formula in
  let pr1 = pr_list (pr_triple pr0 pr0 string_of_int) in
  pr1

let compute_cmd rel_defs bottom_up =
  let nos = List.map (fun (_,_,a) -> a) rel_defs in
  (* let nos = string_of_elems nos string_of_int "," in *)
  let nos = string_of_elems nos (fun _ ->
      string_of_int !Globals.fixcalc_disj) "," in
  (* let () = x_binfo_hp (add_str "rel_defs" string_of_rel_defs) rel_defs no_pos in *)
  (* let () = x_binfo_hp (add_str "No of disjs" (fun x -> x)) nos no_pos in *)
  let rels = List.map (fun (a,_,_) ->
      CP.name_of_spec_var (CP.name_of_rel_form a)) rel_defs in
  let names = string_of_elems rels (fun x -> x) "," in
  if bottom_up then
    (* let () = x_binfo_pp "bottom up" no_pos in *)
    "\nbottomupgen([" ^ names ^ "], [" ^ nos ^ "], SimHeur);"
  else
    let () = x_binfo_pp "top down" no_pos in
    "\nTD:=topdown(" ^ names ^ ", " ^ nos ^ ", SimHeur);\nTD;"

let compute_cmd rel_defs bottom_up =
  Debug.no_2 "compute_cmd" pr_none pr_none pr_none compute_cmd rel_defs bottom_up

let compute_gfp_cmd rel_defs =
  let nos = List.map (fun (_,_,a) -> a) rel_defs in
  let nos = string_of_elems nos (fun _ ->
      string_of_int !Globals.fixcalc_disj) "," in
  let rels = List.map (fun (a,_,_) ->
      CP.name_of_spec_var (CP.name_of_rel_form a)) rel_defs in
  let names = string_of_elems rels (fun x -> x) "," in
    "\ngfp([" ^ names ^ "], [" ^ nos ^ "], SimHeur);"

let compute_fixpoint_aux rel_defs ante_vars bottom_up =
  (* Prepare the input for the fixpoint calculation *)

  let () = Parse_fix.initialize_tlist_from_fpairlist rel_defs in
  let def = List.fold_left (fun x y -> x ^ (compute_def y ante_vars)) "" rel_defs in
  (* let _ = print_endline ("### compute_fixpoint_aux def:"^def) in *)

  let cmd = compute_cmd rel_defs bottom_up in
  let input_fixcalc =  def ^ cmd  in
  DD.ninfo_pprint ">>>>>> compute_fixpoint <<<<<<" no_pos;
  (* let pr_f = Cprinter.string_of_pure_formula in *)
  (* let pr = pr_triple pr_f pr_f string_of_int in *)
  (* let remove_dups = Gen.BList.remove_dups_eq CP.eq_spec_var in *)
  (* let vs = remove_dups (List.concat (List.map (fun (f1,f2,_) -> (CP.fv f1)@(CP.fv f2)) rel_defs)) in *)
  (* x_binfo_hp (add_str "vs" Cprinter.string_of_spec_var_list) vs no_pos; *)
  (* x_binfo_hp (add_str "rel_def" (pr_list pr)) rel_defs no_pos; *)
  x_binfo_hp (add_str "Input of fixcalc: " pr_id) input_fixcalc no_pos;
  (* DD.info_hprint (add_str "def" pr_id) def no_pos; *)
  (* DD.info_hprint (add_str "cmd" pr_id) cmd no_pos; *)
  (* DD.info_zprint (lazy (("fixpoint input = " ^ input_fixcalc))) no_pos; *)
  (* Call the fixpoint calculation *)
  DD.ninfo_zprint (lazy (("Input of fixcalc: " ^ input_fixcalc))) no_pos;

  let _ =
    if !Globals.gen_fixcalc then gen_fixcalc_file input_fixcalc else ()
  in

  let output_of_sleek = if bottom_up then ("logs/fixcalc"^(* (fix_num #str_get_next)^ *)".inf") else "fixcalc.td" in
  let () = x_tinfo_pp ("fixcalc file name: " ^ output_of_sleek) no_pos in
  let oc = open_out output_of_sleek in
  Printf.fprintf oc "%s" input_fixcalc;
  flush oc;
  close_out oc;
  let res = syscall (!fixcalc_exe ^" "^ output_of_sleek ^ fixcalc_options) in

  (* Remove parentheses *)
  let res = remove_paren res (String.length res) in
  x_dinfo_zp (lazy (("res = " ^ res ^ "\n"))) no_pos;

  (* Parse result *)
  (* x_binfo_pp ("Result of fixcalc: " ^ res) no_pos; *)
(* let parse_fix_with_type_from_rel_defs rel_defs res = *)
  let fixpoints = x_add_1 parse_fix_rel_defs rel_defs res in
  let fixpoints = List.map TP.norm_pure_result fixpoints in
  x_binfo_hp (add_str "Result of fixcalc (parsed): "
                     (pr_list !CP.print_formula)) fixpoints no_pos;

  (* Pre-result *)
  let rels = List.map (fun (a,_,_) -> a) rel_defs in
  let res =
    try List.combine rels fixpoints
    with _ -> report_error no_pos "Error in compute_fixpoint_aux"
  in

  (* Substitute the parameters of each relation to the original ones *)
  (*  DD.ninfo_pprint ("res(b4): " ^ *)
  (*    (pr_list (pr_pair !CP.print_formula !CP.print_formula) res)) no_pos;*)
  (*  let res =*)
  (*    List.map (fun (a_rel,fixpoint) -> *)
  (*      match a_rel with*)
  (*      | CP.BForm ((CP.RelForm (name,args,o1),o2),o3) ->*)
  (*        let subst_arg = *)
  (*          try List.assoc name subs*)
  (*          with _ -> []*)
  (*        in*)
  (*        let subst_arg = List.map (fun (x,y) -> (y,x)) subst_arg in*)
  (*        if subst_arg = [] then (a_rel, fixpoint)*)
  (*        else (CP.subst subst_arg a_rel, CP.subst subst_arg fixpoint)*)
  (*      | _ -> report_error no_pos "compute_fixpoint_aux: Expected a relation"*)
  (*    ) res in*)
  (*  DD.ninfo_pprint ("res(af): " ^ *)
  (*    (pr_list (pr_pair !CP.print_formula !CP.print_formula) res)) no_pos;*)
  res

let compute_fixpoint_aux rel_defs ante_vars bottom_up =
  let pr0 = !CP.print_formula in
  let pr1 = pr_list (pr_triple pr0 pr0 string_of_int) in
  let pr2 = !CP.print_svl in
  let pr_res = pr_list (pr_pair pr0 pr0) in
  if (!Globals.allow_qe_fix)
  then List.map (fun ((a,_) as f) -> a,(Coqinf.qe_fixpoint f)) (List.map (fun (a,b,_) -> a,b) rel_defs)
  else
    DD.no_2 "compute_fixpoint_aux" pr1 pr2 pr_res
      (fun _ _ -> compute_fixpoint_aux rel_defs ante_vars bottom_up)
      rel_defs ante_vars

let compute_fixpoint_aux rel_defs ante_vars bottom_up =
  Debug.no_2 "compute_fixpoint_aux" pr_none pr_none pr_none (compute_fixpoint_aux rel_defs) ante_vars bottom_up

let extract_inv_helper_x (rel, pfs) ante_vars specs =
  (* Remove bag constraints *)
  let () = x_tinfo_hp (add_str "pfs(b4):" (pr_list !CP.print_formula)) pfs no_pos in
  let pfs = List.map (fun p ->
      let bag_vars = List.filter CP.is_bag_typ (CP.fv p) in
      if bag_vars == [] then p else
        let p = x_add_1 TP.simplify_raw p in
        CP.remove_cnts bag_vars p
    ) pfs
  in
  let () = x_tinfo_hp (add_str "pfs(af):" (pr_list !CP.print_formula)) pfs no_pos in

  (* Some other processes *)
  let pfs,no = process_base_rec pfs rel specs in
  Debug.tinfo_hprint (add_str "pfs(before existential):" (pr_list !CP.print_formula)) pfs no_pos;
  (* Make existence *)
  let pfs = List.concat (List.map (fun p ->
      let exists_vars = CP.diff_svl (CP.fv_wo_rel p) (CP.fv rel) in
      let res = CP.mkExists exists_vars p None no_pos in
      if CP.isConstTrue (x_add_1 TP.simplify_raw res) then [CP.mkTrue no_pos]
      else [res]) pfs)
  in

  let () = x_tinfo_hp (add_str "pfs(after existential):" (pr_list !CP.print_formula)) pfs no_pos in

  (* Disjunctive defintion for each relation *)
  let def = List.fold_left
      (fun p1 p2 -> CP.mkOr p1 p2 None no_pos) (CP.mkFalse no_pos) pfs in
  [(rel, def, no)]


let extract_inv_helper (rel, pfs) ante_vars specs =
  let pr1 = !CP.print_formula in
  let pr2 = pr_list_ln pr1 in
  let pr3 = Cprinter.string_of_struc_formula in
  Debug.no_3 "extract_inv_helper" (pr_pair pr1 pr2) !CP.print_svl pr3 (pr_list_ln (pr_triple pr1 pr1 string_of_int))
    (fun _ _ _ -> extract_inv_helper_x (rel, pfs) ante_vars specs)
    (rel, pfs) ante_vars specs

let arrange_para input_pairs ante_vars =
  let pairs, subs = List.split
      (List.map (fun (r,pfs) ->
           match r with
           | CP.BForm ((CP.RelForm (name,args,o1),o2),o3) ->
             let pre_args, post_args =
               List.partition
                 (fun e -> Gen.BList.subset_eq CP.eq_spec_var (CP.afv e) ante_vars)
                 args
             in
             let new_args = pre_args @ post_args in
             if new_args = args then ((r,pfs),[])
             else
               let subst_arg = List.combine (List.map CP.exp_to_spec_var args)
                   (List.map CP.exp_to_spec_var new_args)
               in
               ((CP.BForm ((CP.RelForm (name,new_args,o1),o2),o3),
                 List.map (fun x -> CP.subst subst_arg x) pfs),[(name,subst_arg)])
           | _ -> report_error no_pos "arrange_para: Expected a relation"
         ) input_pairs)
  in
  pairs, List.concat subs

(* let reorder old_args new_args args = *)
(*       let pairs = List.combine old_args args in *)
(*       let args = List.map (fun a -> List.assoc a pairs) new_args in *)
(*       args *)

(* let reorder_rev old_args new_args args = *)
(*   reorder new_args old_args args *)

(* let re_order_new args inp_bool_args = *)
(*        let dec_args = List.combine args inp_bool_args in *)
(*        let pre_args, post_args = List.partition (fun (_,b) -> b) dec_args in *)
(*        let pre_args = List.map fst pre_args in *)
(*        let post_args = List.map fst post_args in *)
(*        (pre_args@post_args) *)


let arrange_para_of_rel rhs_rel lhs_rel_name inp_bool_args bottom_up =
  match rhs_rel with
  | CP.BForm ((CP.RelForm (name,args,o1),o2),o3) ->
    if name = lhs_rel_name then
      let args = CP.re_order_new args inp_bool_args in
      (* let pairs = List.combine old_args args in *)
      (* let args = List.map (fun a -> List.assoc a pairs) new_args in *)
      CP.BForm ((CP.RelForm (name,args,o1),o2),o3)
    else
    if bottom_up then rhs_rel
    else report_error no_pos "Not support topdown fixpoint for mutual recursion"
  | _ -> report_error no_pos "arrange_para_of_rel: Expected a relation"

let arrange_para_of_pure fml lhs_rel_name subst bottom_up =
  let conjs = CP.list_of_conjs fml in
  let rel_conjs, others = List.partition CP.is_RelForm conjs in
  let new_rel_conjs = List.map (fun x -> arrange_para_of_rel x lhs_rel_name subst bottom_up) rel_conjs in
  CP.conj_of_list (others @ new_rel_conjs) no_pos

(* type: CP.formula -> CP.spec_var -> 'a list * 'a list -> bool -> CP.formula *)
let arrange_para_of_pure fml lhs_rel_name subst bottom_up =
  let pr_pf = !CP.print_formula in
  Debug.no_3 "arrange_para_of_pure" pr_pf !CP.print_sv (pr_list string_of_bool) pr_pf
    (fun _ _ _ -> arrange_para_of_pure fml lhs_rel_name subst bottom_up) fml lhs_rel_name subst

let no_change bool_lst =
  let rec aux_false lst = match lst with
    | [] -> true
    | f::l -> if f then false
      else aux_false l in
  let rec aux_true lst = match lst with
    | [] -> true
    | f::l -> if f then aux_true l
      else aux_false l in
  aux_true bool_lst

let no_change bool_lst =
  Debug.no_1 "no_change" (pr_list string_of_bool) string_of_bool no_change bool_lst

let build_inp_bool_args ante_vars args =
  List.map (fun e -> Gen.BList.subset_eq CP.eq_spec_var (CP.afv e) ante_vars) args

(* (==fixcalc.ml#1254==) *)
(* re_order_para@2@1 *)
(* re_order_para inp1 :[ PPP(mmmm_1371,n1_1372,n,k,m)] *)
(* re_order_para inp2 :[[ PPP(mmmm_1371,n1_1460,n_1446,k,m) & 0<=n1_1460 & 0<=m & n_1446<=k &  *)
(*  n=n_1446-1 & n1_1372=n1_1460+1 & 0<=mmmm_1371, n1_1372=0 & k=n & mmmm_1371=m & 0<=m]] *)
(* re_order_para inp3 :[n,k,m,s] *)
(* re_order_para@2 EXIT:([ PPP(n,k,m,mmmm_1371,n1_1372)],[[ 0<=n1_1460 & 0<=m & n_1446<=k & n=n_1446-1 & n1_1372=n1_1460+1 &  *)
(*  0<=mmmm_1371 & PPP(mmmm_1371,n1_1460,n_1446,k,m), n1_1372=0 & k=n & mmmm_1371=m & 0<=m]]) *)
(* WN : Obsolete as cannot handle mutual rec *)
(* type: CP.formula list -> *)
(*   CP.formula list list -> *)
(*   CP.spec_var list -> CP.formula list * CP.formula list list *)
(* let rec re_order_para rels pfs ante_vars = match rels with *)
(*   | [] -> ([],pfs) *)
(*   | r::rs -> *)
(*     let res_rs,res_pfs = re_order_para rs pfs ante_vars in *)
(*     (match r with *)
(*      | CP.BForm ((CP.RelForm (name,args,o1),o2),o3) -> *)
(*        let inp_bool_args = build_inp_bool_args ante_vars args in *)
(*        let new_args = x_add CP.re_order_new args inp_bool_args in *)
(*        (\* let pre_args, post_args = List.partition  *\) *)
(*        (\*     (fun e -> Gen.BList.subset_eq CP.eq_spec_var (CP.afv e) ante_vars) args  *\) *)
(*        (\* in *\) *)
(*        if x_add_1 no_change inp_bool_args (\* new_args = args *\) then (r::res_rs,res_pfs) *)
(*        else *)
(*          let subst_arg = inp_bool_args (\* args, new_args *\) in *)
(*          let new_pfs = List.map (fun pf_lst -> *)
(*              List.map (fun pf -> x_add arrange_para_of_pure pf name subst_arg true) pf_lst) res_pfs *)
(*          in ([CP.BForm ((CP.RelForm (name,new_args,o1),o2),o3)]@res_rs, new_pfs) *)
(*      | _ -> report_error no_pos "re_order_para: Expected a relation") *)

let find_rel lst name =
  let (_,r,_) = List.find (fun (a,_,_) -> CP.eq_spec_var a name) lst in
  r

let subs_rel lst_bool_args f =
  match f with
  | CP.BForm ((CP.RelForm (name,args,o1),o2),o3) ->
    begin
    try
      let r = find_rel lst_bool_args name in
      begin
        match r with
        | None -> f
        | Some b_args ->
          let args = CP.re_order_new args b_args in
          CP.BForm ((CP.RelForm (name,args,o1),o2),o3)
      end
    with _ ->
      let () = x_binfo_pp ("Cannot find relation "^(!CP.print_sv name)) no_pos in
      f
    end
  | _ -> f

let save_data = ref None
let save_reorder f = save_data := Some f
let get_reorder () =
  match !save_data with
  | None -> []
  | Some f -> f

let process_body_pure lst_bool_args fml =
  let conjs = CP.list_of_conjs fml in
  let new_conjs = List.map (subs_rel lst_bool_args) conjs in
  CP.conj_of_list (new_conjs) no_pos

(* type: CP.formula list -> *)
(*   CP.formula list list -> *)
(*   CP.spec_var list -> CP.formula list * CP.formula list list *)
let re_order_para rels pfs ante_vars =
  let to_bool_args r = match r with
    | CP.BForm ((CP.RelForm (name,args,o1),o2),o3) ->
      let b_arg = build_inp_bool_args ante_vars args in
      let nc = no_change b_arg in
      if nc then (name,None,r)
      else
        let new_args = x_add CP.re_order_new args b_arg in
        (name,Some b_arg,CP.BForm ((CP.RelForm (name,new_args,o1),o2),o3))
    | _ -> report_error no_pos "re_order_para: rels should have only relations"
  in let lst_bool_args = List.map to_bool_args rels in
  let () = save_reorder lst_bool_args in
  let pfs = List.map (List.map (process_body_pure lst_bool_args)) pfs in
  (List.map (fun (_,_,r)->r) lst_bool_args, pfs)

let re_order_para rels pfs ante_vars =
  let pr_pf = !CP.print_formula in
  let pr1 = pr_list pr_pf in
  let pr2 = pr_list pr1 in
  let pr3 = !CP.print_svl in
  Debug.no_3 "re_order_para" pr1 pr2 pr3 (pr_pair pr1 pr2) re_order_para rels pfs ante_vars

let arrange_para_new input_pairs ante_vars =
  let rels,pfs = List.split input_pairs in
  let () = x_tinfo_hp (add_str "rels(b4):" (pr_list !CP.print_formula)) rels no_pos in
  let () = x_tinfo_hp (add_str "pfs(b4):" (pr_list (pr_list !CP.print_formula))) pfs no_pos in
  let rels,pfs = x_add re_order_para rels pfs ante_vars in
  let () = x_tinfo_hp (add_str "rels(af):" (pr_list !CP.print_formula)) rels no_pos in
  let () = x_tinfo_hp (add_str "pfs(af):" (pr_list (pr_list !CP.print_formula))) pfs no_pos in
  try List.combine rels pfs
  with _ -> report_error no_pos "Error in re_order_para"

(* type: (CP.formula * CP.formula list) list -> *)
(*   CP.spec_var list -> (CP.formula * CP.formula list) list *)
let arrange_para_new input_pairs ante_vars =
  let pr_pf = !CP.print_formula in
  let pr1 = pr_list (pr_pair pr_pf (pr_list pr_pf)) in
  Debug.no_2 "arrange_para_new" pr1 !CP.print_svl pr1 arrange_para_new input_pairs ante_vars

(*  let pairs, subs = List.split *)
(*    (List.map (fun (r,pfs) ->*)
(*      match r with*)
(*      | CP.BForm ((CP.RelForm (name,args,o1),o2),o3) ->*)
(*        let pre_args, post_args = *)
(*          List.partition *)
(*            (fun e -> Gen.BList.subset_eq CP.eq_spec_var (CP.afv e) ante_vars) *)
(*          args*)
(*        in*)
(*        let new_args = pre_args @ post_args in*)
(*        if new_args = args then ((r,pfs),[])*)
(*        else*)
(*          let subst_arg = List.combine (List.map CP.exp_to_spec_var args) *)
(*                                       (List.map CP.exp_to_spec_var new_args) *)
(*          in*)
(*          ((CP.BForm ((CP.RelForm (name,new_args,o1),o2),o3), *)
(*            List.map (fun x -> CP.subst subst_arg x) pfs),[(name,subst_arg)])*)
(*      | _ -> report_error no_pos "arrange_para: Expected a relation"*)
(*    ) input_pairs)*)
(*  in *)
(*  pairs, List.concat subs*)

let arrange_para_td input_pairs ante_vars =
  let pairs = List.map (fun (r,pfs) ->
      match r with
      | CP.BForm ((CP.RelForm (name,args,o1),o2),o3) ->
        let inp_bool_args = build_inp_bool_args ante_vars args in
        let new_args = x_add CP.re_order_new args inp_bool_args in
        (* let pre_args, post_args =  *)
        (*   List.partition  *)
        (*     (fun e -> Gen.BList.subset_eq CP.eq_spec_var (CP.afv e) ante_vars)  *)
        (*     args *)
        (* in *)
        (* let new_args = pre_args @ post_args in *)
        if x_add_1 no_change inp_bool_args (* ew_args = args *) then (r,pfs)
        else
          let subst_arg = inp_bool_args (* args, new_args *) in
          CP.BForm ((CP.RelForm (name,new_args,o1),o2),o3),
          List.map (fun x -> x_add arrange_para_of_pure x name subst_arg false) pfs
      | _ -> report_error no_pos "arrange_para_td: Expected a relation"
    ) input_pairs
  in
  pairs

let rec unify_rels rel a_rel = match rel, a_rel with
  | (f1,CP.BForm ((CP.RelForm (name1,args1,p1),p2),p3)),
    (f2,CP.BForm ((CP.RelForm (name2,args2,_ ),_ ),_ )) ->
    let subst_arg = List.combine (List.map CP.exp_to_spec_var args2)
        (List.map CP.exp_to_spec_var args1) in
    let f2 = CP.subst subst_arg f2 in
    f2
  | _ -> report_error no_pos ("unify_rels: Expected a relation, " ^
                              (pr_pair !CP.print_formula !CP.print_formula) (snd rel, snd a_rel))

(*(n=0 & m=0) | (n=0 & m>0) ==> (n=0 & m>=0) *)
let fixc_reduce_disj_one_rel_x (rel_p, oblgs0)=
  (****************INTERNAL********************)
  let red_measure = 1 in
  let rec partition_comm_diff_x lst_ps1 lst_ps2 (comm, diff1, diff2)=
    match lst_ps1 with
    | [] -> (comm, diff1, diff2@lst_ps2)
    | p1::rest1 -> let n_comm, rest2 = List.partition (fun p2 -> CP.equalFormula p1 p2) lst_ps2 in
      if n_comm = [] then partition_comm_diff_x rest1 lst_ps2 (comm, diff1@[p1], diff2) else
        partition_comm_diff_x rest1 rest2 (comm@[p1], diff1, diff2)
  in
  let partition_comm_diff lst_ps1 lst_ps2 (comm, diff1, diff2)=
    let pr1 = pr_list !CP.print_formula in
    let pr2 = pr_triple pr1 pr1 pr1 in
    Debug.no_3 "partition_comm_diff" pr1 pr1 pr2 pr2
      (fun _ _ _ -> partition_comm_diff_x lst_ps1 lst_ps2 (comm, diff1, diff2))
      lst_ps1 lst_ps2 (comm, diff1, diff2)
  in
  let collect_comm lst_p lst_ps=
    let lst_comm, lst_rest = List.fold_left (fun (r_comm, r_rest) lst_p1 ->
        let comm,diff1,diff2 = partition_comm_diff lst_p lst_p1 ([],[],[]) in
        (*do reduce for one*)
        if comm = [] || (List.length diff1 != red_measure) || (List.length diff2 != red_measure) then
          (r_comm, r_rest@[lst_p1])
        else (r_comm@[comm,diff1,diff2], r_rest)
      ) ([],[]) lst_ps in
    if lst_comm = [] then ([], lst_p::lst_ps) else
      (lst_comm, lst_rest)
  in
  let find_max_common lst_ps=
    let rec collect_comm_lst lst_p rest_lst_ps done_lst_ps res=
      match rest_lst_ps with
      | [] ->
        let r1 = collect_comm lst_p done_lst_ps in
        (res@[r1])
      | lst_p1::rest_lsp1 -> let r1 = collect_comm lst_p (rest_lst_ps@done_lst_ps) in
        collect_comm_lst lst_p1 rest_lsp1 (done_lst_ps@[lst_p]) (res@[r1])
    in
    match lst_ps with
    | [] -> ([], lst_ps)
    | lst_p::rest -> let lst_comm = collect_comm_lst lst_p rest [] [] in
      (*get max_comm*)
      let sorted_comm = List.sort (fun (_,rest1) (_,rest2) -> List.length rest1 - List.length rest2) lst_comm in
      List.hd sorted_comm
  in
  let do_reduce_x (comm_ps, diff_ps1, diff_ps2)=
    let p1 = CP.conj_of_list diff_ps1 no_pos in
    let p2 = CP.conj_of_list diff_ps2 no_pos in
    let p = CP.mkOr p1 p2 None (CP.pos_of_formula p1) in
    let p1 = TP.pairwisecheck_raw p in
    let () = Debug.ninfo_hprint (add_str "p"  !CP.print_formula) p no_pos in
    let () = Debug.ninfo_hprint (add_str "p1"  !CP.print_formula) p1 no_pos in
    if CP.is_disjunct p1 then
      [(comm_ps@diff_ps1);(comm_ps@diff_ps2)]
    else [(p1::comm_ps)]
  in
  let do_reduce (comm_ps, diff_ps1, diff_ps2)=
    let pr1 = pr_list_ln !CP.print_formula in
    let pr2 =  pr_list_ln pr1 in
    let pr3 = pr_triple pr1 pr1 pr1 in
    Debug.no_1 "do_reduce" pr3 pr2
      (fun _ -> do_reduce_x (comm_ps, diff_ps1, diff_ps2))
      (comm_ps, diff_ps1, diff_ps2)
  in
  let rec reduce_one_disj oblgs=
    let lst_ps = List.map (CP.list_of_conjs) oblgs in
    let (lst_com_ps, rest_lst_ps) = find_max_common lst_ps in
    let lst_reduced_ps = List.fold_left (fun r comp -> r@(do_reduce comp)) [] lst_com_ps in
    let reduced_ps = List.map (fun ps -> CP.conj_of_list ps no_pos) lst_reduced_ps in
    let reduced_ps1 = Gen.BList.remove_dups_eq CP.equalFormula reduced_ps in
    let rest_ps= List.map (fun ps -> CP.conj_of_list ps no_pos) rest_lst_ps in
    (reduced_ps1@rest_ps)
  in
  (*****************END*INTERNAL****************)
  let ini_oblgs, rec_oblgs = List.partition (fun p ->
      (CP.get_list_rel_args p) = []
    ) oblgs0 in
  let ini_oblgs1 = reduce_one_disj ini_oblgs in
  (rel_p, rec_oblgs@ini_oblgs1)

let fixc_reduce_disj_one_rel pairs=
  let pr1 = !CP.print_formula in
  let pr2 = pr_pair pr1 (pr_list_ln pr1) in
  Debug.no_1 "fixc_reduce_disj_one_rel" pr2 pr2
    (fun _ -> fixc_reduce_disj_one_rel_x pairs) pairs

let fixc_preprocess_x pairs0 =
  let rec helper pairs res=
    match pairs with
    | [] -> res
    | r::rs ->
      let rel = snd r in
      let name = CP.name_of_rel_form rel in
      let same_rels, diff_rels =
        List.partition (fun r0 ->
            CP.eq_spec_var (CP.name_of_rel_form (snd r0)) name) rs in
      let unified_rels =
        if same_rels == [] then [(snd r, [fst r])]
        else
          let res = List.map (fun r0 ->
              if CP.equalFormula rel (snd r0) then (fst r0)
              else unify_rels r r0) same_rels in
          let unified_oblgs = (snd r, (fst r) :: res) in
          (*reduce number of disj*)
          let red_pairs = fixc_reduce_disj_one_rel unified_oblgs in
          [red_pairs]
      in
      helper diff_rels (res@unified_rels)
  in
  helper pairs0 []

let gfp_preprocess_x pairs0 =
  let rec helper pairs res=
    match pairs with
    | [] -> res
    | r::rs ->
      let rel = fst r in
      let name = CP.name_of_rel_form rel in
      let same_rels, diff_rels =
        List.partition (fun r0 ->
            CP.eq_spec_var (CP.name_of_rel_form (fst r0)) name) rs in
      let unified_rels =
        if same_rels == [] then [(fst r, [snd r])]
        else
          let res = List.map (fun r0 ->
              if CP.equalFormula rel (fst r0) then (snd r0)
              else unify_rels r r0) same_rels in
          let unified_oblgs = (fst r, (snd r) :: res) in
          (*reduce number of disj*)
          let red_pairs = fixc_reduce_disj_one_rel unified_oblgs in
          [red_pairs]
      in
      helper diff_rels (res@unified_rels)
  in
  helper pairs0 []

let fixc_preprocess pairs0 =
  let pr1 = !CP.print_formula in
  let pr2 = pr_list_ln (pr_pair pr1 pr1) in
  let pr3 = pr_list_ln (pr_pair pr1 (pr_list_ln pr1)) in
  Debug.no_1 "fixc_preprocess" pr2 pr3
    (fun _ -> fixc_preprocess_x pairs0) pairs0

let gfp_preprocess pairs0 =
  let pr1 = !CP.print_formula in
  let pr2 = pr_list_ln (pr_pair pr1 pr1) in
  let pr3 = pr_list_ln (pr_pair pr1 (pr_list_ln pr1)) in
  Debug.no_1 "gfp_preprocess" pr2 pr3
    (fun _ -> gfp_preprocess_x pairs0) pairs0

(*let rec unify_rels_ass rel a_rel = match rel, a_rel with*)
(*  | (CP.BForm ((CP.RelForm (name1,args1,p1),p2),p3),f1), *)
(*    (CP.BForm ((CP.RelForm (name2,args2,_ ),_ ),_ ),f2) ->*)
(*    let subst_arg = List.combine (List.map CP.exp_to_spec_var args2) *)
(*                                 (List.map CP.exp_to_spec_var args1) in*)
(*    let f2 = CP.subst subst_arg f2 in*)
(*    f2*)
(*  | _ -> report_error no_pos ("unify_rels_ass: Expected a relation, " ^ *)
(*        (pr_pair !CP.print_formula !CP.print_formula) (fst rel, fst a_rel))*)

(*let rec preprocess_rel_ass pairs = match pairs with*)
(*  | [] -> []*)
(*  | r::rs -> *)
(*    let rel = fst r in*)
(*    let name = CP.name_of_rel_form rel in*)
(*    let same_rels, diff_rels = *)
(*      List.partition (fun r0 -> *)
(*        CP.eq_spec_var (CP.name_of_rel_form (fst r0)) name) rs in*)
(*    let unified_rels = *)
(*      if same_rels == [] then [(fst r, [snd r])]*)
(*      else *)
(*        let res = List.map (fun r0 -> *)
(*                    if CP.equalFormula rel (fst r0) then (snd r0)*)
(*                    else unify_rels_ass r r0) same_rels in*)
(*        [(fst r, (snd r) :: res)]*)
(*    in*)
(*    unified_rels @ (preprocess_rel_ass diff_rels)*)

let compute_fixpoint_xx input_pairs_num ante_vars specs bottom_up =
  (* TODO: Handle non-recursive ones separately *)
  let () = x_tinfo_pp ("input_pairs_num: " ^ (pr_list
                                            (pr_pair !CP.print_formula !CP.print_formula) input_pairs_num)) no_pos in

  let pairs = fixc_preprocess input_pairs_num in

  let () = x_tinfo_hp (add_str "input_pairs(b4): " (pr_list
                                                  (pr_pair !CP.print_formula (pr_list !CP.print_formula)) )) pairs no_pos in

  (*  let pairs, subs = if bottom_up then arrange_para_new pairs ante_vars,[] *)
  (*    else arrange_para_td pairs ante_vars,[]*)
  (*  in*)

  let pairs = if bottom_up then arrange_para_new pairs ante_vars
    else arrange_para_td pairs ante_vars
  in

  let () = x_tinfo_hp (add_str "input_pairs(af): "  (pr_list
                                                   (pr_pair !CP.print_formula (pr_list !CP.print_formula)) )) pairs no_pos in
  let rel_defs = List.concat
      (List.map (fun pair -> extract_inv_helper pair ante_vars specs) pairs) in

  let () = x_tinfo_hp (add_str "rel_defs "  (pr_list
                                           (pr_triple !CP.print_formula !CP.print_formula string_of_int)) ) rel_defs no_pos in

  let true_const,rel_defs = List.partition (fun (_,pf,_) -> CP.isConstTrue pf) rel_defs in
  let non_rec_defs, rec_rel_defs = List.partition (fun (_,pf,_) -> is_not_rec pf) rel_defs in

  let () = x_tinfo_hp (add_str "rec_rel_defs "  (pr_list
                                               (pr_triple !CP.print_formula !CP.print_formula string_of_int)) ) rec_rel_defs no_pos in
  (* x_tinfo_hp (add_str "rec_rel_defs "  (pr_list *)
  x_tinfo_hp (add_str "non_rec_defs "  (pr_list
                                           (pr_triple !CP.print_formula !CP.print_formula string_of_int)) ) non_rec_defs no_pos;


  let true_const = List.map (fun (rel_fml,pf,_) -> (rel_fml,pf)) true_const in
  let non_rec_defs = List.map (fun (rel_fml,pf,_) -> (rel_fml,pf)) non_rec_defs in
  if rec_rel_defs=[]
  then
    let () = x_tinfo_pp ("compute_fixpoint_xx:then branch") no_pos in
    true_const @ non_rec_defs
  else
    true_const @ (* non_rec_defs @ *) (x_add compute_fixpoint_aux rel_defs ante_vars bottom_up)

let compute_fixpoint_xx input_pairs ante_vars specs bottom_up =
  let pr0 = !CP.print_formula in
  let pr1 = pr_list_ln (pr_pair pr0 pr0) in
  let pr2 = !CP.print_svl in
  let pr_res = pr_list (pr_pair pr0 pr0) in
  Debug.no_2 "compute_fixpoint_xx" pr1 pr2 pr_res
    (fun _ _ -> compute_fixpoint_xx input_pairs ante_vars specs bottom_up)
    input_pairs ante_vars

let compute_fixpoint_x input_pairs ante_vars specs bottom_up =
  let () = x_tinfo_pp ("input_pairs: " ^ (pr_list
                                        (pr_pair !CP.print_formula !CP.print_formula) input_pairs)) no_pos in
  let () = x_tinfo_hp (add_str "specs: " (Cprinter.string_of_struc_formula)) specs no_pos in
  let is_bag_cnt rel = List.exists CP.is_bag_typ (CP.fv rel) in
  let input_pairs_bag, input_pairs_num =
    List.partition (fun (p,r) -> is_bag_cnt r) input_pairs
  in
  let bag_res = if input_pairs_bag = [] || not(bottom_up) then []
    else Fixbag.compute_fixpoint 1 input_pairs_bag ante_vars true
  in
  let num_res = if input_pairs_num = [] then []
    else x_add compute_fixpoint_xx input_pairs_num ante_vars specs bottom_up
  in bag_res @ num_res

let compute_fixpoint_x2 input_pairs ante_vars specs bottom_up =
  let pr = !CP.print_formula in
  if !Globals.split_fixcalc then
    let () = x_binfo_hp (add_str "input_pairs" (pr_list (pr_pair pr pr))) input_pairs no_pos in
    let constrs = List.fold_left (fun acc (pf,_) ->
        let () = DD.tinfo_hprint (add_str "pf" pr) pf no_pos in
        let p_aset = CP.pure_ptr_equations pf in
        let () = DD.tinfo_hprint (add_str "p_aset" (pr_list (pr_pair !CP.print_sv !CP.print_sv))) p_aset no_pos in
        let pf = CP.wrap_exists_svl pf (Gen.BList.difference_eq CP.eq_spec_var (CP.fv pf) ante_vars) in
        let pf = x_add_1 Omega.simplify pf in
        let pfs = CP.split_conjunctions pf in
        let () = DD.tinfo_hprint (add_str "pf" pr) pf no_pos in
        acc@pfs
      ) [] input_pairs in
    let constrs = Gen.BList.remove_dups_eq CP.equalFormula constrs in
    let () = DD.tinfo_hprint (add_str "constrs" (pr_list pr)) constrs no_pos in
    let res = List.fold_left (fun acc constr ->
        let input_pairs1, input_pairs2 = List.partition (fun (pf,_) -> TP.imply_raw pf constr) input_pairs  in
        let () = DD.tinfo_hprint (add_str "constr" pr) constr no_pos in
        let () = DD.tinfo_hprint (add_str "input_pairs1" (pr_list (pr_pair pr pr))) input_pairs1 no_pos in
        let () = DD.tinfo_hprint (add_str "input_pairs2" (pr_list (pr_pair pr pr))) input_pairs2 no_pos in
        let res1 = compute_fixpoint_x input_pairs1 ante_vars specs bottom_up in
        let () = DD.tinfo_hprint (add_str "res1" (pr_list (pr_pair pr pr))) res1 no_pos in
        let res1 = List.map (fun (pf1,pf2) -> (pf1,CP.mkAnd pf2 constr no_pos)) res1 in
        let () = DD.tinfo_hprint (add_str "res1" (pr_list (pr_pair pr pr))) res1 no_pos in
        let res2 = compute_fixpoint_x input_pairs2 ante_vars specs bottom_up in
        let () = DD.tinfo_hprint (add_str "res2" (pr_list (pr_pair pr pr))) res2 no_pos in
        let res2 = List.map (fun (pf1,pf2) -> (pf1,CP.mkAnd pf2 (CP.mkNot constr None no_pos) no_pos)) res2 in
        let () = DD.tinfo_hprint (add_str "res2" (pr_list (pr_pair pr pr))) res2 no_pos in
        let rec helper acc (pf1,pf2) =
          match acc with
          | [] -> [(pf1,pf2)]
          | (pf3,pf4)::tl ->
            if (CP.equalFormula pf1 pf3)
            then
              let pf5 = x_add_1 Omega.simplify (CP.mkOr pf2 pf4 None no_pos) in
              let () = DD.tinfo_hprint (add_str "pf2" pr) pf2 no_pos in
              let () = DD.tinfo_hprint (add_str "pf4" pr) pf4 no_pos in
              let () = DD.tinfo_hprint (add_str "pf5" pr) pf5 no_pos in
              (pf1,pf5)::tl
            else (pf3,pf4)::(helper tl (pf1,pf2))
        in
        let acc = List.fold_left (fun acc pf ->
            helper acc pf
          ) acc (res1@res2) in
        let () = DD.tinfo_hprint (add_str "acc" (pr_list (pr_pair pr pr))) acc no_pos in
        acc
      ) [] constrs in
    let () = DD.tinfo_hprint (add_str "res" (pr_list (pr_pair pr pr))) res no_pos in
    res
  else
    (* compute_fixpoint_x input_pairs ante_vars specs bottom_up *)
    let n_base = List.fold_left (fun acc (pf1,pf2) ->
        let new_acc = match pf2 with
          | CP.BForm((CP.RelForm (sv,_,_), _), _) ->
            let svl = CP.fv pf1 in
            if Gen.BList.mem_eq CP.eq_spec_var sv svl then acc else acc+1
          | _ -> acc
        in new_acc
      ) 1 input_pairs in
    let () = x_tinfo_hp (add_str "n_base" string_of_int) n_base no_pos in
    (* Wrapper.wrap_num_disj compute_fixpoint_x n_base input_pairs ante_vars specs bottom_up *)
    compute_fixpoint_x input_pairs ante_vars specs bottom_up

(* WN:tofix Wrapper to translate back array *)
(*
 let compute_fixpoint_x2 input_pairs ante_vars specs bottom_up =
  let resultlst = compute_fixpoint_x2 input_pairs ante_vars specs bottom_up in
  List.map (fun (a,b) ->
      (Trans_arr.translate_back_array_in_one_formula a,Trans_arr.add_unchanged_info_to_formula_f (Trans_arr.translate_back_array_in_one_formula b))) resultlst
*)

let compute_fixpoint_x2 input_pairs ante_vars specs bottom_up =
  let pr0 = !CP.print_formula in
  let pr1 = pr_list_ln (pr_pair pr0 pr0) in
  let pr2 = !CP.print_svl in
  let pr_res = add_str "before normalizing the result" (pr_list (pr_pair pr0 pr0)) in
  DD.no_3 "compute_fixpoint_x2" pr_id pr1 pr2 pr_res
    (fun _ _ _ -> compute_fixpoint_x2 input_pairs ante_vars specs true)
    "after input normalization" input_pairs ante_vars

(* Wrapper to
1. translate back array
2. trasnform imm formula to imm-free formula and back
3. disable fixcalc inner imm-free to imm transformation (eg. calling simpilfy, etc) *)
let compute_fixpoint_x2 input_pairs ante_vars specs bottom_up =
  let fixpt (input_pairs,specs) = x_add compute_fixpoint_x2 input_pairs ante_vars specs bottom_up in
  let fst_pre = (List.map (fold_pair1f (x_add_1 Immutable.map_imm_to_int_pure_formula))) in
  let snd_pre = Immutable.map_imm_to_int_struc_formula in
  let pre = fold_pair2f fst_pre snd_pre in
  let post ls = Wrapper.wrap_with_int_to_imm (List.map (fold_pair1f Immutable.map_int_to_imm_pure_formula)) ls in
  (* let fixpt =  Wrapper.wrap_wo_int_to_imm fixpt in *)
  let fixpt (input_pairs,specs) = Wrapper.wrap_pre_post_process pre post fixpt (input_pairs,specs) in
  let reslst =  Wrapper.wrap_wo_int_to_imm fixpt (input_pairs,specs) in
  List.map (fun (a,b) -> (Trans_arr.translate_back_array_in_one_formula a,Trans_arr.translate_back_array_in_one_formula b)) reslst
;;

let compute_fixpoint (i:int) input_pairs ante_vars specs =
  let pr0 = !CP.print_formula in
  let pr1 = pr_list_ln (pr_pair pr0 pr0) in
  let pr2 = !CP.print_svl in
  let pr_res = pr_list (pr_pair pr0 pr0) in
  DD.no_2_num i "compute_fixpoint_2" pr1 pr2 pr_res
    (fun _ _ -> compute_fixpoint_x2 input_pairs ante_vars specs true)
    input_pairs ante_vars

let compute_fixpoint_x input_pairs ante_vars specs bottom_up =
  let pr0 = !CP.print_formula in
  let pr1 = pr_list_ln (pr_pair pr0 pr0) in
  let pr2 = !CP.print_svl in
  let pr_res = add_str "before normalizing the result" (pr_list (pr_pair pr0 pr0)) in
  DD.no_3 "compute_fixpoint_x" pr_id pr1 pr2 pr_res
    (fun _ _ _ -> compute_fixpoint_x input_pairs ante_vars specs bottom_up)
    "after input normalization" input_pairs ante_vars


(*call the wrappers for:
1. transform imm formula to imm-free formula and back
2. disable fixcalc inner imm-free to imm transformation (eg. calling simplify, etc)  *)
let compute_fixpoint_x input_pairs ante_vars specs bottom_up =
  let fixpt (input_pairs,specs) = (* Wrapper.wrap_wo_int_to_imm *) (x_add compute_fixpoint_x input_pairs ante_vars specs) bottom_up in
  let fst_pre = (List.map (fold_pair1f (x_add_1 Immutable.map_imm_to_int_pure_formula))) in
  let snd_pre = Immutable.map_imm_to_int_struc_formula in
  let pre = fold_pair2f fst_pre snd_pre in
  let post ls = Wrapper.wrap_with_int_to_imm (List.map (fold_pair1f Immutable.map_int_to_imm_pure_formula)) ls in
  (* let fixpt =  Wrapper.wrap_wo_int_to_imm fixpt in *)
  let fixpt (input_pairs,specs) = Wrapper.wrap_pre_post_process pre post fixpt (input_pairs,specs) in
  Wrapper.wrap_wo_int_to_imm fixpt (input_pairs,specs)

let compute_fixpoint_td (i:int) input_pairs ante_vars specs =
  let pr0 = !CP.print_formula in
  let pr1 = pr_list_ln (pr_pair pr0 pr0) in
  let pr2 = !CP.print_svl in
  let pr_res = pr_list (pr_pair pr0 pr0) in
  DD.no_2_num i "compute_fixpoint_td" pr1 pr2 pr_res
    (fun _ _ -> compute_fixpoint_x input_pairs ante_vars specs false)
    input_pairs ante_vars

let substitute_args_gfp rcase =
  (* TODOIMM this throws an exception for imm ex8e1f.ss. To fix *)
  try
    let rels = CP.get_RelForm rcase in
    let rcase_wo_rel = x_add_1 TP.simplify_raw rcase in
    let rels, subs =
      List.split (List.map (fun rel -> substitute_args_x rel) rels) in
    let res = [rcase_wo_rel]@rels@(List.concat subs) in
    CP.conj_of_list res no_pos
  with Invalid_argument _ -> rcase

let process_base_rec_gfp pfs rel specs =
  match x_add_1 CP.get_rel_id rel with
  | None -> report_error no_pos "process_base_rec: Expected a relation"
  | Some ivs ->
    let (rcases, bcases) = List.partition is_rec pfs in
    let or_post = get_or_post specs (CP.get_rel_id_list rel) in
    let bcases =
      begin
        match or_post with
        | [] -> bcases
        | [or_fml] ->
          let other_branches = get_other_branches or_fml (CP.get_rel_args rel) in
          let other_branches = List.map (fun p -> CP.mkNot_s p) other_branches in
          let pure_other_branches = CP.conj_of_list other_branches no_pos in
          List.filter (fun b -> TP.is_sat_raw (MCP.mix_of_pure
                                                 (CP.mkAnd b pure_other_branches no_pos))) bcases
        | _ -> bcases
      end
    in
    (* let () = x_binfo_pp ("bcases:"^((pr_list !CP.print_formula) bcases)) no_pos in *)
    let () = x_binfo_pp ("rcases:"^((pr_list !CP.print_formula) rcases)) no_pos in
    let no_of_disjs =
      List.map (fun b ->
          let disjs = CP.list_of_disjs b in
          (* TODO *)
          let cond = List.exists (fun d ->
              let conjs = CP.list_of_conjs d in
              List.exists (fun c -> CP.is_eq_const c) conjs
            ) disjs
          in
          if cond then 1 else List.length disjs
        ) bcases in
    let no_of_disjs = List.fold_left (fun a b -> max a b) 1 no_of_disjs in
    (* Normalize each relation *)
(*    let rcases = List.map (fun x -> substitute_args_gfp x) rcases in *)
    let () = x_tinfo_pp ("rcases:"^((pr_list !CP.print_formula) rcases)) no_pos in
    bcases @ rcases, no_of_disjs

let extract_inv_helper_gfp (rel, pfs) ante_vars specs =
  let () = x_binfo_hp (add_str "pfs(b4):" (pr_list !CP.print_formula)) pfs no_pos in
  let pfs = List.map (fun p ->
      let bag_vars = List.filter CP.is_bag_typ (CP.fv p) in
      if bag_vars == [] then p else
        let p = x_add_1 TP.simplify_raw p in
        CP.remove_cnts bag_vars p
    ) pfs
  in
  let () = x_binfo_hp (add_str "pfs(af):" (pr_list !CP.print_formula)) pfs no_pos in
  let pfs,no = process_base_rec_gfp pfs rel specs in
  Debug.binfo_hprint (add_str "pfs(before existential):" (pr_list !CP.print_formula)) pfs no_pos;
  (* Make existence *)
  let pfs = List.concat (List.map (fun p ->
      let exists_vars = CP.diff_svl (CP.fv_wo_rel p) (CP.fv rel) in
      let res = CP.mkExists_gfp exists_vars p None no_pos in
    (*  if CP.isConstTrue (x_add_1 TP.simplify_raw res) then [CP.mkTrue no_pos]
      else*) [res]) pfs)
  in
  let () = x_binfo_hp (add_str "pfs(after existential):" (pr_list !CP.print_formula)) pfs no_pos in
  (* Disjunctive defintion for each relation *)
  let def = List.fold_left
      (fun p1 p2 -> CP.mkAnd p1 p2 no_pos) (CP.mkTrue no_pos) pfs in
  [(rel, def, no)]

let rec fixcalc_of_gfp_formula f = match f with
  | CP.BForm ((CP.BVar (x,_),_),_) -> fixcalc_of_spec_var x ^ op_gt ^ "0"
  | CP.BForm (b,_) -> fixcalc_of_b_formula b
  | CP.And (p1, p2, _) ->
    "" ^ fixcalc_of_gfp_formula p1 ^ op_and ^ fixcalc_of_gfp_formula p2 ^ "" (* baga/infer/btree.slk *)
  | CP.AndList b ->
    (match b with
     | [] -> fixcalc_of_gfp_formula (CP.mkFalse no_pos)
     | (_,x)::t -> fixcalc_of_gfp_formula
                     (List.fold_left (fun a (_,c) -> CP.mkAnd a c no_pos) x t)
    )
  | CP.Or (p1, p2,_ , _) ->
    "(" ^ fixcalc_of_gfp_formula p1 ^ op_or ^ fixcalc_of_gfp_formula p2 ^ ")"
  | CP.Not (p,_ , _) ->
    "!" ^ "(" ^ fixcalc_of_gfp_formula p ^ ")"
  | CP.Forall (sv, p,_ , _) ->
    " (forall (" ^ fixcalc_of_spec_var sv ^ ":" ^
    fixcalc_of_gfp_formula p ^ ")) "
  | CP.Exists (sv, p,_ , _) ->
    " (exists (" ^ fixcalc_of_spec_var sv ^ ":" ^
    fixcalc_of_gfp_formula p ^ ")) "
;;

let compute_def_gfp (rel_fml, pf, no) ante_vars =
  let (name,vars) = match rel_fml with
    | CP.BForm ((CP.RelForm (name,args,_),_),_) ->
      (* let _ = print_endline ("### args:"^((pr_list !CP.print_exp) args)) in *)
      (CP.name_of_spec_var name, (List.concat (List.map CP.afv args)))
    | _ -> report_error no_pos
             ("Wrong format: " ^ (!CP.print_formula rel_fml) ^ "\n")
  in
  let _ = print_endline ("compute_def vars: "^(Cprinter.string_of_typed_spec_var_list vars)) in
  let pre_vars, post_vars =
    List.partition (fun v -> List.mem v ante_vars) vars in
  let (pre_vars,post_vars,pf) = Trans_arr.expand_array_sv_wrapper rel_fml pf pre_vars post_vars in
  (* let pre_vars = Trans_arr.expand_array_variable pf pre_vars in *)
  (* let post_vars = Trans_arr.expand_array_variable pf post_vars in *)
  (* let pf = Trans_arr.expand_relation pf in *)
  begin
    print_endline_quiet "\n*************************************";
    print_endline_quiet "****** Before putting into fixcalc*******";
    print_endline_quiet ("pre_vars: "^(string_of_spec_var_list pre_vars));
    print_endline_quiet ("post_vars: "^(string_of_spec_var_list post_vars));
    print_endline_quiet "*************************************";
    print_endline_quiet ("formula: "^(!CP.print_formula pf));
    print_endline_quiet "*************************************";
  end;
  try
    let rhs = x_add_1 fixcalc_of_gfp_formula pf in
    let input_fixcalc =
      name ^ ":={["
      ^ (string_of_elems pre_vars fixcalc_of_spec_var ",") ^ "] -> ["
      ^ (string_of_elems post_vars fixcalc_of_spec_var ",") ^ "] -> []: "
      ^ rhs ^ "\n};"
    in input_fixcalc
  with e ->
    report_error ~exc:(Some e) no_pos (x_loc^"compute_def:Error in translating the input for fixcalc")
;;

let compute_gfp_aux rel_defs ante_vars=
  let () = Parse_fix.initialize_tlist_from_fpairlist rel_defs in
  let def = List.fold_left (fun x y -> x ^ (compute_def_gfp y ante_vars)) "" rel_defs in
  let cmd = compute_gfp_cmd rel_defs in
  let input_fixcalc =  def ^ cmd  in
  DD.ninfo_pprint ">>>>>> compute_fixpoint <<<<<<" no_pos;
  x_binfo_hp (add_str "Input of fixcalc: " pr_id) input_fixcalc no_pos;
  DD.ninfo_zprint (lazy (("Input of fixcalc: " ^ input_fixcalc))) no_pos;
  let _ =
    if !Globals.gen_fixcalc then gen_fixcalc_file input_fixcalc else ()
  in
  let output_of_sleek = "fixcalc.gfp" in
  let () = x_tinfo_pp ("fixcalc file name: " ^ output_of_sleek) no_pos in
  let oc = open_out output_of_sleek in
  Printf.fprintf oc "%s" input_fixcalc;
  flush oc;
  close_out oc;
  let res = syscall (!fixcalc_exe ^" "^ output_of_sleek ^ fixcalc_options) in
  let res = remove_paren res (String.length res) in
  x_dinfo_zp (lazy (("res = " ^ res ^ "\n"))) no_pos;
  let fixpoints = x_add_1 parse_fix_rel_defs rel_defs res in
  let fixpoints = List.map TP.norm_pure_result fixpoints in
  x_binfo_hp (add_str "Result of fixcalc (parsed): "
                     (pr_list !CP.print_formula)) fixpoints no_pos;
  let rels = List.map (fun (a,_,_) -> a) rel_defs in
  let res =
    try List.combine rels fixpoints
    with _ -> report_error no_pos "Error in compute_fixpoint_aux"
  in
  res

let compute_gfp_xx input_pairs_num ante_vars specs=
  let () = x_binfo_pp ("input_pairs_num: " ^ (pr_list
                                                (pr_pair !CP.print_formula !CP.print_formula) input_pairs_num)) no_pos in
  let pairs = gfp_preprocess input_pairs_num in
  let () = x_binfo_hp (add_str "input_pairs(b4): " (pr_list
                                                  (pr_pair !CP.print_formula (pr_list !CP.print_formula)) )) pairs no_pos in
  let pairs =  arrange_para_td pairs ante_vars in
  let () = x_binfo_hp (add_str "input_pairs(af): "  (pr_list
                                                       (pr_pair !CP.print_formula (pr_list !CP.print_formula)) )) pairs no_pos in
  let rel_defs = List.concat
      (List.map (fun pair -> extract_inv_helper_gfp pair ante_vars specs) pairs) in
  let () = x_binfo_hp (add_str "rel_defs "  (pr_list
                                               (pr_triple !CP.print_formula !CP.print_formula string_of_int)) ) rel_defs no_pos in
  let true_const,rel_defs = List.partition (fun (_,pf,_) -> CP.isConstTrue pf) rel_defs in
  let non_rec_defs, rec_rel_defs = List.partition (fun (_,pf,_) -> is_not_rec pf) rel_defs in
  let () = x_binfo_hp (add_str "rec_rel_defs "  (pr_list
                                                   (pr_triple !CP.print_formula !CP.print_formula string_of_int)) ) rec_rel_defs no_pos in
  x_binfo_hp (add_str "non_rec_defs "  (pr_list
                                           (pr_triple !CP.print_formula !CP.print_formula string_of_int)) ) non_rec_defs no_pos;
  let true_const = List.map (fun (rel_fml,pf,_) -> (rel_fml,pf)) true_const in
  let non_rec_defs = List.map (fun (rel_fml,pf,_) -> (rel_fml,pf)) non_rec_defs in
  if rec_rel_defs==[] then
    let () = x_binfo_pp ("compute_fixpoint_xx:then branch") no_pos in
    true_const @ non_rec_defs
  else
    true_const @ (x_add compute_gfp_aux rel_defs ante_vars)

let compute_gfp (i:int) input_pairs ante_vars specs =
  let pr0 = !CP.print_formula in
  let pr1 = pr_list_ln (pr_pair pr0 pr0) in
  let pr2 = !CP.print_svl in
  let pr_res = pr_list (pr_pair pr0 pr0) in
  DD.no_2_num i "compute_gfp" pr1 pr2 pr_res
    (fun _ _ -> compute_gfp_xx input_pairs ante_vars specs)
    input_pairs ante_vars


