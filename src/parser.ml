open VarGen
module DD=Debug (* which Debug is this? *)
open Camlp4
open Globals
(* open Exc.ETABLE_NFLOW *)
open Exc.GTable
open Iast
open Token
open Sleekcommons
open Gen.Basic
open HipUtil
(* open Label_only *)

open Perm

module F = Iformula
module P = Ipure
module VP = IvpermUtils
module E1 = Error
module I = Iast
module Ts = Tree_shares.Ts
module LO = Label_only.LOne
(* module LO = Label_only.Lab_List *)
module Lbl = Label_only

module LO2 = Label_only.Lab2_List

module SHGram = Camlp4.Struct.Grammar.Static.Make(Lexer.Make(Token))

(* some variables and functions decide which parser will be used *)
let parser_name = (* ref "unknown" *) ref "default"

let set_parser name =
  parser_name := name

let pred_root_id = ref ""

(* type definitions *)

type type_decl =
  | Data of data_decl
  | Enum of enum_decl
  | View of view_decl
  | Hopred of hopred_decl
  | Barrier of barrier_decl

type decl =
  | Type of type_decl
  | Func of func_decl
  | Rel of rel_decl (* An Hoa *)
  | Hp of hp_decl
  | Axm of axiom_decl (* An Hoa *)
  | Global_var of exp_var_decl
  | Logical_var of exp_var_decl (* Globally logical vars *)
  | Proc of proc_decl
  (* | Coercion of coercion_decl *)
  | Coercion_list of coercion_decl_list
  | Include of string
  | Template of templ_decl
  | Ut of ut_decl
  | Ui of ui_decl


type member =
  | Field of (typed_ident * loc)
  | Inv of F.formula
  | Method of proc_decl

type spec_qualifier =
  | Static
  | Dynamic

type ann =
  | AnnMode of mode
  | AnnType of typ
  | AnnMater

type file_offset =
  {
    line_num: int;
    line_start: int;
    byte_num: int;
  }

let sv_of_id t =
  if String.contains t '\'' then (* Remove the primed in the identifier *)
    (Str.global_replace (Str.regexp "[']") "" t, Primed)
  else (t, Unprimed)

let convert_lem_kind (l: lemma_kind_t) =
    match l with
      | TLEM           -> LEM
      | TLEM_PROP      -> LEM_PROP
      | TLEM_SPLIT      -> LEM_SPLIT
      | TLEM_TEST      -> LEM_TEST
      | TLEM_TEST_NEW  -> LEM_TEST_NEW
      | TLEM_UNSAFE    -> LEM_UNSAFE
      | TLEM_SAFE      -> LEM_SAFE
      | TLEM_INFER     -> LEM_INFER
      | TLEM_INFER_PRED   -> LEM_INFER_PRED

let default_rel_id = "rel_id__"
(* let tmp_rel_decl = ref (None : rel_decl option) *)

(* let set_tmp_rel_decl (rd:rel_decl)= *)
(*   match !tmp_rel_decl with *)
(*     | None -> tmp_rel_decl := (Some rd) *)
(*     | Some _ -> report_error no_pos "cparser.set_tmp_rel_decl: something wrong" *)

(* let get_tmp_rel_decl ():rel_decl = *)
(*   match !tmp_rel_decl with *)
(*     | Some rd -> let () = tmp_rel_decl := None in rd *)
(*     | None -> report_error no_pos "cparser.set_tmp_rel_decl: something wrong" *)

let macros = ref (Hashtbl.create 19)

(* An Hoa : Counting of holes "#" *)
let hash_count = ref 0

(* An Hoa : Generic data type for the abbreviated syntax x.f::<a> *)
let generic_pointer_type_name = "_GENERIC_POINTER_"
let func_names = new Gen.stack (* list of names of ranking functions *)
let rel_names = new Gen.stack (* list of names of relations declared *)
let templ_names = new Gen.stack (* List of declared templates' names *)
let ut_names = new Gen.stack (* List of declared unknown temporal' names *)
let ui_names = new Gen.stack (* List of declared unknown imm rel *)
let view_names = new Gen.stack (* list of names of views declared *)
let hp_names = new Gen.stack (* list of names of heap preds declared *)
(* let g_rel_defs = new Gen.stack (\* list of relations decl in views *\) *)

let  conv_ivars_icmd il_w_itype =
  let inf_o = new Globals.inf_obj_sub (* Globals.clone_sub_infer_const_obj () *) (* Globals.infer_const_obj # clone *) in
  let (i_consts,ivl,extn_lst) = List.fold_left
      (fun (lst_l,lst_r,lst_e) e ->
        match e with
        | FstAns l ->
          (begin match l with
          | INF_EXTN lst -> (lst_l,lst_r,lst::lst_e)
          | _ -> (l::lst_l,lst_r,lst_e)
          end)
        | SndAns r -> (lst_l,r::lst_r,lst_e)) ([],[],[]) il_w_itype in
  let (i_consts,ivl) = (List.rev i_consts,List.rev ivl) in
  let infer_extn_lst = merge_infer_extn_lsts (List.rev extn_lst) in
  let i_consts = if is_empty infer_extn_lst then i_consts else i_consts @ [INF_EXTN infer_extn_lst] in
  let () = inf_o # set_list i_consts in
  (inf_o,i_consts,ivl)

(****** global vars used by CIL parser *****)
let is_cparser_mode = ref false

let cparser_base_loc = ref {line_num = 1;
                           line_start = 1;
                           byte_num = 1;}

(* ------ end of global vars for CIL ----- *)

let get_pos x =
  try
    let sp = Parsing.symbol_start_pos () in
    let ep = Parsing. symbol_end_pos () in
    let mp = Parsing.rhs_start_pos x in
    if (!is_cparser_mode) then (
      let new_sp = {sp with Lexing.pos_lnum = sp.Lexing.pos_lnum + !cparser_base_loc.line_num -1;
                            Lexing.pos_bol = sp.Lexing.pos_bol + !cparser_base_loc.byte_num -1;
                            Lexing.pos_cnum = sp.Lexing.pos_cnum + !cparser_base_loc.byte_num -1;} in
      let new_ep = {ep with Lexing.pos_lnum = ep.Lexing.pos_lnum + !cparser_base_loc.line_num -1;
                            Lexing.pos_bol = ep.Lexing.pos_bol + !cparser_base_loc.byte_num -1;
                            Lexing.pos_cnum = ep.Lexing.pos_cnum + !cparser_base_loc.byte_num -1;} in
      let new_mp = {mp with Lexing.pos_lnum = mp.Lexing.pos_lnum + !cparser_base_loc.line_num -1;
                            Lexing.pos_bol = mp.Lexing.pos_bol + !cparser_base_loc.byte_num -1;
                            Lexing.pos_cnum = mp.Lexing.pos_cnum + !cparser_base_loc.byte_num -1;} in
      { start_pos = new_sp;
        end_pos = new_ep;
        mid_pos = new_mp; }
    )
    else (
      { start_pos = sp;
        end_pos = ep;
        mid_pos = mp; }
    )
  with _ ->
    { start_pos = Lexing.dummy_pos;
      end_pos = Lexing.dummy_pos;
      mid_pos = Lexing.dummy_pos; }

(* compute the position by adding the location return by camlp4 with starting_offset *)
let get_pos_camlp4 l x =
  let sp = Camlp4.PreCast.Loc.start_pos l in
  let ep = Camlp4.PreCast.Loc.stop_pos l in
  let mp = Camlp4.PreCast.Loc.start_pos (Camlp4.PreCast.Loc.shift x l) in
  if (!is_cparser_mode) then (
    let new_sp = {sp with Lexing.pos_lnum = sp.Lexing.pos_lnum + !cparser_base_loc.line_num - 1;
                          Lexing.pos_bol = sp.Lexing.pos_bol + !cparser_base_loc.byte_num - 1;
                          Lexing.pos_cnum = sp.Lexing.pos_cnum + !cparser_base_loc.byte_num - 1;} in
    let new_ep = {ep with Lexing.pos_lnum = ep.Lexing.pos_lnum + !cparser_base_loc.line_num - 1;
                          Lexing.pos_bol = ep.Lexing.pos_bol + !cparser_base_loc.byte_num - 1;
                          Lexing.pos_cnum = ep.Lexing.pos_cnum + !cparser_base_loc.byte_num - 1;} in
    let new_mp = {mp with Lexing.pos_lnum = mp.Lexing.pos_lnum + !cparser_base_loc.line_num - 1;
                          Lexing.pos_bol = mp.Lexing.pos_bol + !cparser_base_loc.byte_num - 1;
                          Lexing.pos_cnum = mp.Lexing.pos_cnum + !cparser_base_loc.byte_num - 1;} in
    { start_pos = new_sp;
      end_pos = new_ep;
      mid_pos = new_mp; }
  )
  else (
    { start_pos = sp;
      end_pos = ep;
      mid_pos = mp; }
  )

let get_mater_vars l = List.fold_left (fun a (((_,v),_),al)-> if (List.exists (fun c-> c=AnnMater) al) then v::a else a) [] l

let rec get_mode (anns : ann list) : mode = match anns with
	| ann :: rest -> begin
		match ann with
		  | AnnMode m -> m
		  | _ -> get_mode rest
	  end
	| [] -> ModeOut (* default to ModeOut if there is no annotation. *)

let rec get_modes (anns : ann list list) : mode list =
	match anns with
	  | alist :: rest ->
		  let m_rest = get_modes rest in
		  let m = get_mode alist in
			m :: m_rest
	| [] -> []

let rec split_specs specs = match specs with
	| sp :: rest -> begin
		let hipfuncspec, dspecs = split_specs rest in
		  match sp with
			| (Static, pre, post) -> ((pre, post) :: hipfuncspec, dspecs)
			| (Dynamic, pre, post) -> (hipfuncspec, (pre, post) :: dspecs)
	  end
	| [] -> ([], [])

let rec split_members mbrs = match mbrs with
	| mbr :: rest -> begin
		let fields, invs, meths = split_members rest in
		  match mbr with
			| Field f -> (f :: fields, invs, meths)
			| Inv i -> (fields, i :: invs, meths)
			| Method m ->
				(fields, invs, m :: meths)
	  end
	| [] -> ([], [], [])

let rec remove_spec_qualifier (_, pre, post) = (pre, post)


let label_struc_list (lgrp:(Lbl.spec_label_def*F.struc_formula) list list) : (Lbl.spec_label_def*F.struc_formula) list =
  List.concat lgrp

let label_struc_groups (lgrp:(Lbl.spec_label_def*F.struc_formula) list list) : F.struc_formula =
  let lst = (label_struc_list lgrp) in
  match lst with
    | [(_,e)] -> e
    | _ ->  F.EList lst

  (* F.EList (label_struc_list lgrp) *)

let label_struc_list_auto (lgrp:(Lbl.spec_label_def*F.struc_formula) list list)  =
  let n = List.length lgrp in
  let fl = List.concat lgrp in
  let all_unlab = List.for_all (fun (l,_) -> LO2.is_unlabelled l) fl in
  if n<=1 || not(all_unlab) then fl
  else
    (* automatically insert numeric label if spec is completely unlabelled *)
    let _,lgr = List.fold_left (fun (a1,a2) c ->
            let ngrp = List.map (fun ((_,s),d)-> ((Some a1,[]),d)) c in
            ((a1+1), a2@ngrp) ) (1,[]) lgrp
    in lgr

(* auto insertion of numeric if unlabelled *)
let label_struc_groups_auto (lgrp:(Lbl.spec_label_def*F.struc_formula) list list) : F.struc_formula =
  let lst = (label_struc_list_auto lgrp) in
  match lst with
    | [(_,e)] -> e
    | _ ->  F.EList lst


let un_option s d = match s with
  | Some v -> v
  | None -> d

let error_on_dups f l p = if (Gen.BList.check_dups_eq f l) then report_error p ("list contains duplicates") else l

let label_formula f ofl = (match f with
          | P.BForm (b,_) -> P.BForm (b,ofl)
          | P.And _ -> f
          | P.AndList b -> f
          | P.Or  (b1,b2,_,l)  -> P.Or(b1,b2,ofl,l)
          | P.Not (b1,_,l)     -> P.Not(b1,ofl,l)
          | P.Forall (q,b1,_,l)-> P.Forall(q,b1,ofl,l)
          | P.Exists (q,b1,_,l)-> P.Exists(q,b1,ofl,l))

let bf_to_var p = match p with
  | P.Var (v,_) -> v
  | _ -> report_error (get_pos 1) ("expected var, found : "^(Iprinter.string_of_formula_exp p)^"\n")

  (*intermediate representation for pure formulae*)
type pure_double =
  | Pure_f of P.formula
  | Pure_c of P.exp
  | Pure_t of(P.exp * (P.ann option)) (* for data ann: var * ann, where var represents a data field *)

let mk_purec_absent e = Pure_t(e,Some F.mk_absent_ann)

let string_of_pure_double p =
  match p with
  | Pure_f f -> "Pure_f: " ^ (Iprinter.string_of_pure_formula f)
  | Pure_c c -> "Pure_c: " ^ (Iprinter.string_of_formula_exp c)
  | Pure_t t -> "Pure_t: " ^ (Iprinter.string_of_formula_exp (fst t))

let get_pure_exp p pos : P.exp =
  match p with
  | Pure_c c -> c
  | Pure_t t -> (fst t)
  | Pure_f f -> report_error pos "pure expression unexpected here"

let apply_pure_form1 fct form = match form with
  | Pure_f f -> Pure_f (fct f)
  | _ -> report_error (get_pos 1) "with 1 expected pure_form, found cexp"

let apply_cexp_form1 fct form = match form with
  | Pure_c f
  | Pure_t (f, _) -> Pure_c (fct f)
  | _ -> report_error (get_pos 1) "with 1 expected cexp, found pure_form"

let apply_pure_form2 fct form1 form2 = match (form1,form2) with
  | Pure_f f1 ,Pure_f f2 -> Pure_f (fct f1 f2)
  | Pure_f f1 , Pure_c f2
  | Pure_f f1 , Pure_t (f2, _)-> (match f2 with
                             | P.Var (v,_) -> Pure_f(fct f1 (P.BForm (((P.mkBVar v (get_pos 1)), None), None)))
                             | _ -> report_error (get_pos 1) "with 2 expected pure_form, found cexp in var" )
  | Pure_c f1, Pure_f f2
  | Pure_t (f1, _), Pure_f f2 -> (match f1 with
                             | P.Var (v,_) -> Pure_f(fct (P.BForm (((P.mkBVar v (get_pos 1)), None), None )) f2)
                             | _ -> report_error (get_pos 1) "with 2 expected pure_form in f1, found cexp")
  | Pure_c f1, Pure_c f2 -> (
      let bool_var1 = (
        match f1 with
        | P.Var (v,_) -> P.BForm (((P.mkBVar v (get_pos 1)), None), None )
        | P.Ann_Exp (P.Var (v, _), Bool, _) -> P.BForm (((P.mkBVar v (get_pos 1)), None), None)
        | _ -> report_error (get_pos 1) "with 2 expected pure_form in f1, found cexp") in
      let bool_var2 = (
        match f2 with
        | P.Var (v,_) -> P.BForm (((P.mkBVar v (get_pos 1)), None), None )
        | P.Ann_Exp (P.Var (v, _), Bool, _) -> P.BForm (((P.mkBVar v (get_pos 1)), None), None)
        | _ -> report_error (get_pos 1) "with 2 expected pure_form in f2, found cexp") in
      Pure_f(fct bool_var1 bool_var2)
    )
  | _ -> report_error (get_pos 1) "with 2 expected cexp, found pure_form"

let apply_cexp_form2 fct form1 form2 = match (form1,form2) with
  | Pure_c f1, Pure_c f2
  | Pure_c f1, Pure_t (f2, _)
  | Pure_t (f1,_), Pure_c f2
  | Pure_t (f1,_), Pure_t (f2, _)
      -> Pure_c (fct f1 f2)
  | _ -> report_error (get_pos 1) "with 2 expected cexp, found pure_form"

let apply_cexp_form2 fct form1 form2 =
  DD.no_2 "Parser.apply_cexp_form2: " string_of_pure_double string_of_pure_double
          (fun _ -> "") (apply_cexp_form2 fct) form1 form2

let cexp_list_to_pure fct ls1 = Pure_f (P.BForm (((fct ls1), None), None))

let cexp_to_pure1 fct f =
  match f with
  | Pure_t (f, _)
  | Pure_c f -> Pure_f (P.BForm (((fct f), None), None))
  | _ -> report_error (get_pos 1) "with 1 convert expected cexp, found pure_form"

let cexp_to_pure_slicing fct f sl = match f with
  | Pure_c f
  | Pure_t (f, _) -> Pure_f (P.BForm (((fct f), sl), None))
  | _ -> report_error (get_pos 1) "with 1 convert expected cexp, found pure_form"

let cexp_to_pure2 fct f01 f02 =
  match (f01,f02) with
  | Pure_c f1, Pure_c f2 -> (
      match f1 with
      | P.List(explist,pos) ->
          let tmp = List.map (fun c -> P.BForm (((fct c f2), None), None)) explist in
          let len =  List.length tmp in
          let res =
            if (len > 1) then List.fold_left (fun c1 c2 -> P.mkAnd c1 c2 (get_pos 2)) (List.hd tmp) (List.tl tmp)
            else  P.BForm (((fct f1 f2), None), None) in
          Pure_f(res)
      | _ -> (
          match f2 with
          | P.List(explist,pos) ->
              let tmp = List.map (fun c -> P.BForm (((fct f1 c), None), None)) explist in
              let len = List.length tmp in
              let res =
                if ( len > 1 ) then List.fold_left (fun c1 c2 -> P.mkAnd c1 c2 (get_pos 2)) (List.hd tmp) (List.tl tmp)
                else P.BForm (((fct f1 f2), None), None) in
              Pure_f(res)
          | _ -> (
              let typ1 = P.typ_of_exp f1 in
              let typ2 = P.typ_of_exp f2 in
              let rec arr_typ_check typ1 typ2 = (
                match typ1 with
                | Array (t1,_) -> begin
                    match t1 with
                      | Array _ -> arr_typ_check t1 typ2
                      | _ ->
                            if t1== UNK || t1 == typ2 then true
                            else (
                                match typ2 with
                                  | Array (t2,_) -> begin
                                      match t2 with
                                        | Array _ -> arr_typ_check typ1 t2
                                        | _ -> if t2== UNK || t1==t2 then true else false
                                    end
                                  | _ -> false
                    )
                  end
                | _ -> (
                    match typ2 with
                    | Array (t,_) -> begin
                        match t with
                          | Array _ -> arr_typ_check typ1 t
                          | _ -> if t== UNK || t==typ1 then true else false
                      end
                    | _ -> false
                  )
              ) in
              if (typ1 = typ2) || (typ1 == UNK) || (typ2 == UNK) || (arr_typ_check typ1 typ2) then
                Pure_f (P.BForm(((fct f1 f2), None), None))
              else
                report_error (get_pos 1) "with 2 convert expected the same cexp types, found different types"
            )
        )
    )
  | Pure_f f1 , Pure_c f2 -> (
      match f1  with
      | P.BForm((pf,il),oe) -> (
          match pf with
          | P.Lt (a1, a2, _)
          | P.Lte (a1, a2, _)
          | P.Gt (a1, a2, _)
          | P.Gte (a1, a2, _)
          | P.Eq (a1, a2, _)
          | P.Neq (a1, a2, _) ->
              let tmp = P.BForm(((fct a2 f2), None),None) in
              Pure_f (P.mkAnd f1 tmp (get_pos 2))
          | _ -> report_error (get_pos 1) "error should be an equality exp"
        )
      | _ -> begin
          if P.is_esv f2 && P.is_bexp f1 then
            begin
              let f = f1 in
              let e1 = f2 in
              let e2 = P.BExpr f in
              let pf = fct e1 e2 in
              let f0 = P.BForm(((fct e1 e2), None), None) in
              let nf =  P.transform_bexp_p f0 None None pf in
              Pure_f nf
            end
          else
            report_error (get_pos 1) "error should be a binary exp"
        end
    )
  | Pure_c e1, Pure_f f -> begin
      if P.is_esv e1 && P.is_bexp f then
        begin
          let e2 = P.BExpr f in
          let pf = fct e1 e2 in
          let f0 = P.BForm(((fct e1 e2), None), None) in
          (* let nf =  P.transform_bexp f0 None None e1 f in *)
          let nf =  P.transform_bexp_p f0 None None pf in
          Pure_f nf
        end
      else
        report_error (get_pos 1) "with 2 convert bexpr  1"
    end
  | Pure_f f1, Pure_f f2 -> begin
      if  P.is_bexp f1 && P.is_bexp f2 then
        begin
          let e1 = P.BExpr f1 in
          let e2 = P.BExpr f2 in
          let pf = fct e1 e2 in
          let f0 = P.BForm(((fct e1 e2), None), None) in
          (* let nf =  P.transform_bexp f0 None None e1 f in *)
          let nf =  P.transform_bexp_p f0 None None pf in
          Pure_f nf
        end
      else
        report_error (get_pos 1) "with 2 convert bexpr 2"
    end
  | _ -> report_error (get_pos 1) "with 2 convert expected cexp, found pure_form"

(* Use the Stream.npeek to look ahead the TOKENS *)
let peek_try =
 SHGram.Entry.of_parser "peek_try"
    (fun strm ->
       match Stream.npeek 2 strm with
         | [_;IN_T,_]  -> ()
         | [_;NOTIN,_] -> ()
	 | [GT,_; CBRACE,_] -> raise Stream.Failure (*vp*)
         | [SEMICOLON,_; CBRACE,_] -> raise Stream.Failure
         | [OPAREN,_; EXISTS,_ ] -> raise Stream.Failure
         | [GT,_;STAR,_] -> raise Stream.Failure
         | [GT,_;STARMINUS,_] -> raise Stream.Failure
         | [GT,_;INV,_] -> raise Stream.Failure
         | [GT,_;INV_EXACT,_] -> raise Stream.Failure
         | [GT,_;INV_SAT,_] -> raise Stream.Failure
         | [GT,_;AND,_] -> raise Stream.Failure
         | [GT,_;ANDSTAR,_] -> raise Stream.Failure
         | [GT,_;UNIONSTAR,_] -> raise Stream.Failure
         | [GT,_;ANDAND,_] -> raise Stream.Failure
         | [GT,_;OR,_] -> raise Stream.Failure
         | [GT,_;ORWORD,_] -> raise Stream.Failure
         | [GT,_;DOT,_] -> raise Stream.Failure
         | [GT,_;DERIVE,_] -> raise Stream.Failure
         | [GT,_;EQV,_] -> raise Stream.Failure
	     | [GT,_;CONSTR,_] -> raise Stream.Failure
         | [GT,_;LEFTARROW,_] -> raise Stream.Failure
         | [GT,_;RIGHTARROW,_] -> raise Stream.Failure
         | [GT,_;EQUIV,_] -> raise Stream.Failure
         | [GT,_;CPAREN,_] -> raise Stream.Failure
         | [GT,_;SEMICOLON,_]-> raise Stream.Failure
         | [GT,_;ENSURES,_]-> raise Stream.Failure
         | [GT,_;ENSURES_EXACT,_]-> raise Stream.Failure
         | [GT,_;ENSURES_INEXACT,_]-> raise Stream.Failure
         | [GT,_;IMM,_] -> raise Stream.Failure
         | [GT,_;ACCS,_] -> raise Stream.Failure
         | [GT,_;AT,_] -> raise Stream.Failure
         | [GT,_;MUT,_] -> raise Stream.Failure
		 | [GT,_;MAT,_] -> raise Stream.Failure
         | [GT,_;DERV,_] -> raise Stream.Failure
         | [GT,_;SPLIT1Ann,_] -> raise Stream.Failure
         | [GT,_;SPLIT2Ann,_] -> raise Stream.Failure
         | [GT,_;LEND,_] -> raise Stream.Failure
         | [GT,_;CASE,_] -> raise Stream.Failure
         | [GT,_;VARIANCE,_] -> raise Stream.Failure
         | [GT,_;_] -> ()
         | [SEMICOLON,_;_] -> ()
         | _ -> raise Stream.Failure  )

 let peek_try_st =
 SHGram.Entry.of_parser "peek_try_st"
     (fun strm ->
       match Stream.npeek 2 strm with
          | [_; OP_DEC,_] -> ()
          | _ -> raise Stream.Failure)

 let peek_try_st_in =
 SHGram.Entry.of_parser "peek_try_st_in"
     (fun strm ->
       match Stream.npeek 2 strm with
          | [_; OP_INC,_] -> ()
          | _ -> raise Stream.Failure)

 let peek_try_st_qi =
 SHGram.Entry.of_parser "peek_try_st_qi"
     (fun strm ->
       match Stream.npeek 2 strm with
          | [_; DOT,_] -> ()
          | _ -> raise Stream.Failure)

 let peek_invocation =
 SHGram.Entry.of_parser "peek_invocation"
     (fun strm ->
       match Stream.npeek 5 strm with
          | [_; OPAREN,_;_;_;_] -> ()
          | [_; OSQUARE,_; _; CSQUARE, _ ; OPAREN,_] -> ()
          | _ -> raise Stream.Failure)

 let peek_member_name =
 SHGram.Entry.of_parser "peek_member_name"
     (fun strm ->
       match Stream.npeek 2 strm with
          | [IDENTIFIER n,_;DOT,_] -> raise Stream.Failure
          | _ -> ())

 let peek_exp_st =
 SHGram.Entry.of_parser "peek_exp_st"
     (fun strm ->
       match Stream.npeek 1 strm with
          | [DPRINT,_] -> raise Stream.Failure
          | _ -> ())

 let peek_try_declarest =
 SHGram.Entry.of_parser "peek_try_declarest"
     (fun strm ->
       match Stream.npeek 2 strm with
          | [_;EQ,_] -> raise Stream.Failure
          | [CONST,_;_] -> ()
          | [INT,_;IDENTIFIER n,_] -> ()
          | [FLOAT,_;IDENTIFIER n,_] -> ()
          | [BOOL,_;IDENTIFIER n,_] -> ()
          | [IDENTIFIER n,_;IDENTIFIER id,_] -> ()
          | [INT,_;OSQUARE,_] -> ()
          (* | [INFINT_TYPE,_;OSQUARE,_] -> () *)
          | [FLOAT,_;OSQUARE,_] -> ()
          | [BOOL,_;OSQUARE,_] -> ()
          (* For pointer*)
          | [INT,_;STAR,_] -> ()
          | [VOID,_;STAR,_] -> ()
          | [FLOAT,_;STAR,_] -> ()
          | [BOOL,_;STAR,_] -> ()
          | [IDENTIFIER n,_;STAR,_] -> ()
          |  _ -> raise Stream.Failure)

let peek_print =
SHGram.Entry.of_parser "peek_print"
	(fun strm ->
		match Stream.npeek 3 strm with
		| [i,_;j,_;k,_]-> print_string((Token.to_string i)^" "^(Token.to_string j)^" "^(Token.to_string k)^"\n");()
		| _ -> raise Stream.Failure)

(*This is quite similar to peek_and_pure*)
 let peek_and =
   SHGram.Entry.of_parser "peek_and"
       (fun strm ->
           match Stream.npeek 3 strm with
             | [AND,_;FLOW i,_;_] -> raise Stream.Failure
             | [AND,_;OSQUARE,_;STRING _,_] -> raise Stream.Failure
             | _ -> ())

 let peek_pure =
   SHGram.Entry.of_parser "peek_pure"
       (fun strm ->
           match Stream.npeek 3 strm with
             | [FORALL,_;OPAREN,_;_] -> ()
             | [EXISTS,_;OPAREN,_;_] -> ()
             | [UNION,_;OPAREN,_;_] -> ()
             | [IDENTIFIER id,_;OPAREN,_;_] -> ()
             | [_;COLONCOLON,_;_] -> raise Stream.Failure
             | [_;OPAREN,_;_] -> raise Stream.Failure
             | [_;PRIME,_;COLONCOLON,_] -> raise Stream.Failure
             | [OPAREN,_;_;COLONCOLON,_] -> raise Stream.Failure
             | _ -> ())

 let peek_pure_out =
   SHGram.Entry.of_parser "peek_pure_out"
       (fun strm ->
           match Stream.npeek 3 strm with
             | [FORALL,_;OPAREN,_;_] -> ()
             | [EXISTS,_;OPAREN,_;_] -> ()
             | [UNION,_;OPAREN,_;_] -> ()
	     (* | [XPURE,_;OPAREN,_;_] -> () *)
             | [IDENTIFIER id,_;OPAREN,_;_] ->  if hp_names # mem id then raise Stream.Failure else ()
             | [_;COLONCOLON,_;_] -> raise Stream.Failure
             | [_;PRIME,_;COLONCOLON,_] -> raise Stream.Failure
             | [OPAREN,_;_;COLONCOLON,_] -> raise Stream.Failure
             | [OSQUARE,_;_;COLONCOLON,_] -> raise Stream.Failure
             | [OSQUARE,_;DOUBLEQUOTE,_;_]-> raise Stream.Failure
             (* | [i,_;j,_;k,_]-> print_string("start here: i:" ^ (Token.to_string i)^" j:"^(Token.to_string j)^" k:"^(Token.to_string k)^" end here \n");() *)
             | _ -> ())

 let peek_typecast =
   SHGram.Entry.of_parser "peek_typecast"
       (fun strm ->
           match Stream.npeek 3 strm with
             | [OPAREN,_;VOID,_;CPAREN, _] -> ()
             | [OPAREN,_;INT,_;CPAREN, _] -> ()
             | [OPAREN,_;FLOAT,_;CPAREN, _] -> ()
             | [OPAREN,_;INFINT_TYPE,_;CPAREN, _] -> ()
             | [OPAREN,_;BOOL,_;CPAREN, _] -> ()
             | [OPAREN,_;BAG,_;CPAREN, _] -> ()
             | [OPAREN,_;IDENTIFIER id,_;CPAREN, _] -> ()
             | [OPAREN,_;REL,_; _] -> ()
             | [OPAREN,_;_;OSQUARE,_] -> ()                   (* array type cast *)
             | [OPAREN,_;_;STAR,_] -> ()                      (* pointer type cast *)
             | _ -> raise Stream.Failure)

let peek_dc =
   SHGram.Entry.of_parser "peek_dc"
       (fun strm ->
           match Stream.npeek 2 strm with
             | [OPAREN,_;EXISTS,_] -> ()
             | _ -> raise Stream.Failure)

(*This seems similar to peek_and*)
 let peek_and_pure =
   SHGram.Entry.of_parser "peek_and_pure"
       (fun strm ->
           match Stream.npeek 3 strm with
             | [AND,_;FLOW i,_;_] -> raise Stream.Failure
             | [AND,_;OSQUARE,_;STRING _,_] -> raise Stream.Failure
             | _ -> ())

 let peek_view_decl =
   SHGram.Entry.of_parser "peek_heap_args"
       (fun strm ->
           match Stream.npeek 3 strm with
             | [PRED,_;IDENTIFIER n,_;LT,_] ->  ()
             | [IDENTIFIER n,_;LT,_;_] ->  ()
             (* | [IDENTIFIER n,_;OBRACE,_] ->  () (\*This is for prim_view_decl*\) *)
             | _ -> raise Stream.Failure)

 let peek_heap_args =
   SHGram.Entry.of_parser "peek_heap_args"
       (fun strm ->
           match Stream.npeek 2 strm with
             | [IDENTIFIER n,_;EQ,_] ->  ()
             | _ -> raise Stream.Failure)

let peek_hash_thread =
   SHGram.Entry.of_parser "peek_hash_thread"
       (fun strm ->
           match Stream.npeek 3 strm with
             | [_;_;COMMA,_] ->  raise Stream.Failure
             | [_;_;GT,_] ->  raise Stream.Failure
             | _ -> ())

 let peek_extended =
   SHGram.Entry.of_parser "peek_extended"
       (fun strm ->
           match Stream.npeek 3 strm with
             | [OSQUARE,_;_;ORWORD,_] -> ()
             | _ -> raise Stream.Failure)

 let peek_div_op =
   SHGram.Entry.of_parser "peek_div_op"
       (fun strm ->
           match Stream.npeek 3 strm with
             (* | [_;_;DIV,_] -> let () = print_endline "peek_div_op1" in () *)
             | [_;DIV,_;_] -> (* let () = print_endline "peek_div_op2" in *)()
             | ls -> (* let () = print_endline "peek_div_op3" in *) raise Stream.Failure)

 let peek_cexp_list =
   SHGram.Entry.of_parser "peek_cexp_list"
       (fun strm ->
           match Stream.npeek 6 strm with
             | [_;COMMA,_;_;GTE,_;_;_] -> ()
             | [_;COMMA,_;_;AND,_;_;_] -> ()
             | [_;COMMA,_;_;COMMA,_;_;SEMICOLON,_] -> ()
             | _ -> raise Stream.Failure)

 let peek_heap =
   SHGram.Entry.of_parser "peek_heap"
       (fun strm ->
           match Stream.npeek 3 strm with
             |[_;COLONCOLON,_;_] -> ()
             |[_;PRIME,_;COLONCOLON,_] -> ()
             |[EMPTY,_;_;_] -> ()
             |[_;EMPTY,_;_] -> ()
             |[_;_;EMPTY,_] -> ()
             |[HTRUE,_;_;_] -> ()
             |[_;HTRUE,_;_] -> ()
             |[_;_;HTRUE,_] -> ()
             | _ -> raise Stream.Failure)

let peek_star =
   SHGram.Entry.of_parser "peek_star"
       (fun strm ->
           match Stream.npeek 3 strm with
             | [AND,_;IDENTIFIER id,_; COLONCOLON,_] -> raise Stream.Failure
             | [STAR,_;OPAREN,_;_] -> raise Stream.Failure
             | [STAR,_;PFULL,_;_] -> raise Stream.Failure
             | [STAR,_;PLEND,_;_] -> raise Stream.Failure
             | [STAR,_;PVALUE,_;_] -> raise Stream.Failure
             | [STAR,_;PFRAC,_;_] -> raise Stream.Failure
             | [STAR,_;PZERO,_;_] -> raise Stream.Failure
             | _ -> ())

let peek_heap_and =
   SHGram.Entry.of_parser "peek_heap_and"
       (fun strm ->
           match Stream.npeek 4 strm with
             |[AND,_;OPAREN ,_; IDENTIFIER id,_; COLONCOLON,_] -> ()
             |[AND,_;IDENTIFIER id,_; COLONCOLON,_; _,_] -> ()
             |[AND,_;SELFT t,_; COLONCOLON,_; _,_] -> ()
             |[AND,_;THIS t,_; COLONCOLON,_; _,_] -> ()
             |[AND,_;RES t,_; COLONCOLON,_; _,_] -> ()
             | _ -> raise Stream.Failure)

let peek_heap_andstar =
   SHGram.Entry.of_parser "peek_heap_andstar"
       (fun strm ->
           match Stream.npeek 4 strm with
             |[ANDSTAR,_;OPAREN ,_; IDENTIFIER id,_; COLONCOLON,_] -> ()
             |[ANDSTAR,_;IDENTIFIER id,_; COLONCOLON,_; _,_] -> ()
             |[ANDSTAR,_;SELFT t,_; COLONCOLON,_; _,_] -> ()
             |[ANDSTAR,_;THIS t,_; COLONCOLON,_; _,_] -> ()
             |[ANDSTAR,_;RES t,_; COLONCOLON,_; _,_] -> ()
             | _ -> raise Stream.Failure)

let peek_heap_unionstar =
   SHGram.Entry.of_parser "peek_heap_unionstar"
       (fun strm ->
           match Stream.npeek 4 strm with
             |[UNIONSTAR,_;OPAREN ,_; IDENTIFIER id,_; COLONCOLON,_] -> ()
             |[UNIONSTAR,_;IDENTIFIER id,_; COLONCOLON,_; _,_] -> ()
             |[UNIONSTAR,_;SELFT t,_; COLONCOLON,_; _,_] -> ()
             |[UNIONSTAR,_;THIS t,_; COLONCOLON,_; _,_] -> ()
             |[UNIONSTAR,_;RES t,_; COLONCOLON,_; _,_] -> ()
             | _ -> raise Stream.Failure)

let peek_heap_starminus =
   SHGram.Entry.of_parser "peek_heap_starminus"
       (fun strm ->
           match Stream.npeek 4 strm with
             |[STARMINUS,_;OPAREN ,_; IDENTIFIER id,_; COLONCOLON,_] -> ()
             |[STARMINUS,_;IDENTIFIER id,_; COLONCOLON,_; _,_] -> ()
             |[STARMINUS,_;SELFT t,_; COLONCOLON,_; _,_] -> ()
             |[STARMINUS,_;THIS t,_; COLONCOLON,_; _,_] -> ()
             |[STARMINUS,_;RES t,_; COLONCOLON,_; _,_] -> ()
             | _ -> raise Stream.Failure)

let peek_array_type =
   SHGram.Entry.of_parser "peek_array_type"
       (fun strm ->
           match Stream.npeek 2 strm with
             |[_;OSQUARE,_] -> (* An Hoa*) (* let () = print_endline "Array found!" in *) ()
             (* |[_;OSQUARE,_;COMMA,_] -> (\* An Hoa*\) (\* let () = print_endline "Array found!" in *\) () *)
             | _ -> raise Stream.Failure)

let peek_pointer_type =
   SHGram.Entry.of_parser "peek_pointer_type"
       (fun strm ->
           match Stream.npeek 2 strm with
             |[_;STAR,_] -> (* let () = print_endline "Pointer found!" in *) ()
             | _ -> raise Stream.Failure)

let peek_obrace_par =
  SHGram.Entry.of_parser "peek_obrace_par"
    (fun strm ->
      match Stream.npeek 2 strm with
      | [OBRACE,_;CASE,_] -> raise Stream.Failure
      | _ -> ())

let peek_relassume =
  SHGram.Entry.of_parser "peek_relassume"
    (fun strm ->
      match Stream.npeek 1 strm with
      | [IDENTIFIER "RA",_] -> raise Stream.Failure
      | _ -> ())

let get_heap_id_info (cid: ident * primed) (heap_id : (ident * int * int * Camlp4.PreCast.Loc.t)) =
  let (base_heap_id, ref_level, deref_level, l) = heap_id in
  let s = ref base_heap_id in
  for i = 1 to ref_level do
    s := !s ^ "_star";
  done;
  if (deref_level == 0) then
    (cid, !s, 0)
  else if ((deref_level > 0) && (!is_cparser_mode)) then
    (* dereference case, used to parse specs in C programs *)
    (cid, !s, deref_level)
  else
    report_error (get_pos_camlp4 l 1) "unexpected heap_id"

(* Determine whether an ineq e1!=e2 *)
(* is a linking constraints         *)
let is_ineq_linking_constraint e1 e2 =
  match e1, e2 with
  | Pure_c c1, Pure_c c2 ->
    (List.length (Gen.BList.remove_dups_eq P.eq_var
      ((P.afv c1) @ (P.afv c2)))) > 1
  | _ -> false

(* let rec set_slicing_utils_pure_double f il =        *)
(*   let pr_pure_double = function                     *)
(* 	| Pure_f pf -> Iprinter.string_of_pure_formula pf *)
(* 	| Pure_c pc -> Iprinter.string_of_formula_exp pc  *)
(*   in                                                *)
(*   DD.no_2 "set_slicing_utils_pure_double"           *)
(* 	pr_pure_double                                    *)
(* 	string_of_bool                                    *)
(* 	pr_pure_double                                    *)
(* 	set_slicing_utils_pure_double_x f il              *)

let set_slicing_utils_pure_double f il =
  (*
	il = true  -> Pure_f pf is a linking constraint
	il = false -> Pure_f pf is not a linking constraint,
	              but we need to find its linking variables
                or linking expressions in !F.linking_exp_list,
	              if any. Those linking variables/expressions
	              were added into the list at Pure_c cases.
  *)
  (* if !Globals.do_slicing then *)
	if not !Globals.dis_slc_ann then
	match f with
  | Pure_f pf ->
    let ls = P.find_lexp_formula pf !Ipure.linking_exp_list in
    if (ls == [] && not il) then f
    else Pure_f (P.set_il_formula pf (Some (il, Globals.fresh_int(), ls)))
	  (* if il then Pure_f (set_il_formula pf (Some (il, Globals.fresh_int(), []))) *)
	  (* else                                                                       *)
		(* let ls = P.find_lexp_formula pf !Ipure.linking_exp_list in                 *)
		(* if (ls == []) then f                                                       *)
		(* else Pure_f (set_il_formula pf (Some (il, Globals.fresh_int(), ls)))       *)
  | Pure_c pc -> let () = Hashtbl.add !Ipure.linking_exp_list pc 0 in f
    | Pure_t (pc, ann0) -> let () = Hashtbl.add !Ipure.linking_exp_list pc 0 in
                          (* let () = Hashtbl.add !Ipure.linking_exp_list ann0 0 in *)
                          f
  else f

let pred_get_root_pos root_id args=
  let rec look_up rest_args n=
    match rest_args with
      | [] -> 0
      | (_,id,_)::rest -> if String.compare id root_id = 0 then n else
          look_up rest (n+1)
  in
  if String.compare root_id "" = 0 then 0 else look_up args 0

let pred_get_args_partition args_ann=
  let rec helper rem_args_ann parts=
    match rem_args_ann with
      | [] -> parts
      | (i,dep_i)::rest ->
            let part,rest1 = List.partition (fun (i1,dep_i1) -> i=dep_i1 || i1 =dep_i) rest in
            if part = [] then
              helper rest parts
            else
              let new_part = i::(List.map (fun (i,_) -> i) part) in
              helper rest1 (parts@[new_part])
  in
  (*ann the order*)
  let _, tripl_args_ann, args = List.fold_left (fun (n, r1,r2) (t,(id,i), p) ->
      (n+1, r1@[(n, i)], r2@[(t,id,p)])
  ) (0,[],[]) args_ann in
  let parts = helper tripl_args_ann [] in
  (args, parts)

let rec get_heap_ann annl : P.ann =
  match annl with
    | (Some a) :: r -> a
    | None :: r -> get_heap_ann r
    | [] ->  P.NoAnn (* P.ConstAnn Mutable *)

and get_heap_ann_opt annl : P.ann option =
  match annl with
    | a :: r -> a
    | [] ->  None

and get_heap_ann_list annl : P.ann list  =
  match annl with
    | (Some a) :: r -> a :: get_heap_ann_list r
    |  None :: r ->  P.NoAnn (* P.ConstAnn Mutable  *):: get_heap_ann_list r
    | [] -> []

let stmt_list_to_block t pos =
  match t with
  | Empty _ -> Block {
      exp_block_body = Empty pos;
      exp_block_jump_label = NoJumpLabel;
      exp_block_local_vars = [];
      exp_block_pos = pos; }
  | _ -> Block {
      exp_block_body = t;
      exp_block_jump_label = NoJumpLabel;
      exp_block_local_vars = [];
      exp_block_pos = pos; }

(* let arg_option = SHGram.Entry.mk "arg_option" *)
let hip_with_option = SHGram.Entry.mk "hip_with_option"
let sprog = SHGram.Entry.mk "sprog"
let hprog = SHGram.Entry.mk "hprog"
let hproc = SHGram.Entry.mk "hproc"
let sprog_int = SHGram.Entry.mk "sprog_int"
let opt_spec_list_file = SHGram.Entry.mk "opt_spec_list_file"
let opt_spec_list = SHGram.Entry.mk "opt_spec_list"
let statement = SHGram.Entry.mk "statement"
let cp_file = SHGram.Entry.mk "cp_file"

EXTEND SHGram
  GLOBAL:  hip_with_option sprog hprog hproc sprog_int opt_spec_list_file opt_spec_list statement cp_file;
  sprog:[[ t = command_list; `EOF -> t ]];
  sprog_int:[[ t = command; `EOF -> t ]];
  hprog:[[ t = hprogn; `EOF ->  t ]];
  hproc:[[ t = proc_decl; `EOF -> t]];
  cp_file:[[ t = cp_list; `EOF ->  t ]];

(* ZH: For Option *)
arg_option: [[t = LIST0 non_empty_arg_list-> List.flatten t]];

(* arg_list : [[ t = non_empty_arg_list -> t]]; *)

non_empty_arg_list: [[ `ARGOPTION t -> let _ = print_endline "!!!!!non_empty_arg_list!" in [t]]];

hip_with_option: [[ opt =arg_option; h = hprog-> (opt,h)]];

macro: [[`PMACRO; n=id; `EQEQ ; tc=tree_const -> if !Globals.perm=(Globals.Dperm) then Hashtbl.add !macros n tc else  report_error (get_pos 1) ("distinct share reasoning not enabled")]];

command_list: [[ t = LIST0 non_empty_command_dot -> t ]];

command: [[ t=OPT non_empty_command_dot-> un_option t EmptyCmd]];

non_empty_command_dot: [[t=non_empty_command; `DOT -> t]];

(* For R{..} and I{..} *)
expect_infer_term: [[f = meta_constr -> f]];

expect_infer_relassume:
  [[ il2 = OPT cond_path; l=meta_constr; `CONSTR;r=meta_constr ->
      (un_option il2 [], l, None,  r)
   | il2 = OPT cond_path; l=meta_constr; `REL_GUARD; guard = meta_constr; `CONSTR;r=meta_constr ->
      (un_option il2 [], l, Some guard,  r)
  ]];

expect_infer:
  [[
    `EXPECT_INFER; ty=validate_result; peek_relassume; t=id; `OBRACE; f = OPT expect_infer_term; `CBRACE ->
       (match t with
          | "R" -> ExpectInfer (ty, V_Residue f)
          | "I" | "IE" | "IU" -> ExpectInfer (ty, V_Infer (t,f))
          | "RE" -> failwith "parser"
          | _ -> raise Stream.Failure)
  | `EXPECT_INFER; ty=validate_result; t=id; `OBRACE; f = OPT expect_infer_relassume; `CBRACE ->
       (match t with
          | "RA" -> ExpectInfer (ty, V_RelAssume f)
          | _ -> failwith "not possible")
  ]];

non_empty_command:
    [[  t=data_decl           -> DataDef t
        | c=class_decl -> DataDef c
      | `PRED;t= view_decl     -> PredDef t
      | `PRED_EXT;t= view_decl_ext     -> PredDef t
      | `PRED_PRIM;t=prim_view_decl     -> PredDef t
      | t=barrier_decl        -> BarrierCheck t
      | t = func_decl         -> FuncDef t
      | t = rel_decl          -> RelDef t
      | t = hp_decl          -> HpDef t
      | l = coerc_decl_aux -> LemmaDef l
      | t= axiom_decl -> AxiomDef t (* [4/10/2011] An Hoa : axiom declarations *)
      | t=let_decl            -> t
      | t= checknorm_cmd         -> CheckNorm t
      | t= checkeq_cmd         -> EqCheck t
      | t= checkentail_cmd     -> EntailCheck t
      | t= checksat_cmd     -> SatCheck t
      | t= checknondet_cmd     -> NonDetCheck t
      | t= validate_cmd     -> Validate t
      | t= relassume_cmd     -> RelAssume t
      | t=reldefn_cmd     -> RelDefn t
      | t=shapeinfer_cmd     -> ShapeInfer t
      | t=shapedivide_cmd     -> ShapeDivide t
      | t=shapeconquer_cmd     -> ShapeConquer t
      | t=shapelfp_cmd     -> ShapeLFP t
      | t=shaperec_cmd     -> ShapeRec t
      | t=shapepost_obl_cmd     -> ShapePostObl t
      | t=shapeinfer_proper_cmd     -> ShapeInferProp t
      | t=shapesplit_base_cmd     -> ShapeSplitBase t
      | t=shapeElim_cmd     -> ShapeElim t
      | t=shapeReuseSubs_cmd     -> ShapeReuseSubs t
      | t=shapeReuse_cmd     -> ShapeReuse t
      | t=predUnfold_cmd     ->
        let check_qualifier q =
          begin
           match q with
           | Some id ->
             if id="disj" then () else failwith ("found "^id^" qbut expecting disj")
           | None -> ()
          end in
        let q = fst t in
        let () = check_qualifier q in
        PredUnfold t
      | t=shapeExtract_cmd     -> ShapeExtract t
      | t=decl_dang_cmd        -> ShapeDeclDang t
      | t= decl_unknown_cmd        -> ShapeDeclUnknown t
      | t=shape_sconseq_cmd     -> ShapeSConseq t
      | t=shape_sante_cmd     -> ShapeSAnte t
      | t = shape_add_dangling_cmd -> ShapeAddDangling t
      | t = shape_unfold_cmd -> ShapeUnfold t
      | t = shape_param_dangling_cmd -> ShapeParamDangling t
      | t = shape_simplify_cmd -> ShapeSimplify t
      | t = shape_merge_cmd -> ShapeMerge t
      | t = shape_trans_to_view_cmd -> ShapeTransToView t
      | t = shape_derive_pre_cmd -> ShapeDerivePre t
      | t = shape_derive_post_cmd -> ShapeDerivePost t
      | t = shape_derive_view_cmd -> ShapeDeriveView t
      | t = shape_extn_view_cmd -> ShapeExtnView t
      | t = data_mark_rec_cmd -> DataMarkRec t
      | t = shape_normalize_cmd -> ShapeNormalize t
      | t = pred_elim_head_cmd -> PredElimHead t
      | t = pred_elim_tail_cmd -> PredElimTail t
      | t = pred_unify_disj_cmd -> PredUnifyDisj t
      | t=pred_split_cmd     -> PredSplit t
      | t=pred_norm_seg_cmd     -> PredNormSeg t
      | t=pred_norm_disj_cmd     -> PredNormDisj t
      | t = rel_infer_cmd -> RelInfer t
      | t=simplify_cmd        -> Simplify t
      | t=hull_cmd        -> Slk_Hull t
      | t=pairwise_cmd        -> Slk_PairWise t
      | t= infer_cmd           -> InferCmd t
      | t= captureresidue_cmd  -> CaptureResidue t
      | t=print_cmd           -> PrintCmd t
      | t=cmp_cmd           ->  CmpCmd t
      | t=time_cmd            -> t
      | t = ui_decl         -> UiDef t
      (* TermInf: Command for Termination Inference *)
      | t = templ_decl -> TemplDef t
      | t = templ_solve_cmd -> TemplSolv t
      | t = ut_decl -> UtDef t
      | t = term_infer_cmd -> TermInfer
      | t = term_assume_cmd -> TermAssume t
      | t = expect_infer -> t
      | t=macro	-> EmptyCmd]];

pure_inv: [[`INV; pf=pure_constr -> pf]];

opt_pure_inv: [[t=OPT pure_inv -> t ]];

data_decl:
    [[ dh=data_header ; db = data_body ; dinv = opt_pure_inv
        -> {data_name = dh;
            data_pos = get_pos_camlp4 _loc 1;
            data_fields = db;
            data_parent_name="Object"; (* Object; *)
            data_invs = [];
            data_pure_inv = dinv;
            data_is_template = false;
            data_methods = [];} ]];

template_data_decl:
    [[ dh=template_data_header ; db = data_body
        -> {data_name = dh;
            data_pos = get_pos_camlp4 _loc 1;
            data_fields = db;
            data_parent_name="Object"; (* Object; *)
            data_invs = [];
            data_pure_inv = None;
            data_is_template = true;
            data_methods = [];} ]];

with_typed_var: [[`OSQUARE; typ; `CSQUARE -> ()]];

data_header:
    [[ `DATA; `IDENTIFIER t; OPT with_typed_var -> t ]];

template_data_header:
    [[ `TEMPL; `DATA; `IDENTIFIER t; OPT with_typed_var -> t ]];

data_body:
      [[`OBRACE; fl=field_list2;`SEMICOLON; `CBRACE -> fl
      | `OBRACE; fl=field_list2; `CBRACE   ->  fl
      | `OBRACE; `CBRACE                   -> []] ];

(* field_list:[[ fl = LIST1 one_field SEP `SEMICOLON -> error_on_dups (fun n1 n2-> (snd (fst n1))==(snd (fst n2))) fl (get_pos_camlp4 _loc 1) *)
(*            ]];  *)

(* field_ann: [[ *)
(*      `REC -> Iast.REC *)
(*   |  `VAL -> Iast.VAL *)
(* ]]; *)

field_ann: [[
    `HASH;`IDENTIFIER id -> id
  (* | `AT;`IDENTIFIER id -> id *)
]];

field_anns: [[
     anns = LIST0 field_ann -> anns
]];

field_list2:[[
     t = typ; `IDENTIFIER n -> [((t,n),get_pos_camlp4 _loc 1,false, (gen_field_ann t) (* F_NO_ANN *))]
  | t = typ; `IDENTIFIER n ; ann=field_anns -> [((t,n),get_pos_camlp4 _loc 1,false, ann)]
  |  t = typ; `OSQUARE; t2=typ; `CSQUARE; `IDENTIFIER n -> [((t,n), get_pos_camlp4 _loc 1,false, (gen_field_ann t)(* F_NO_ANN *))]
  |  t=typ; `IDENTIFIER n; peek_try; `SEMICOLON; fl = SELF ->(
	 if List.mem n (List.map get_field_name fl) then
	   report_error (get_pos_camlp4 _loc 4) (n ^ " is duplicated")
	 else
	   ((t, n), get_pos_camlp4 _loc 3, false, (gen_field_ann t) (* F_NO_ANN *)) :: fl )
  |  t=typ; `IDENTIFIER n; ann=field_anns ; peek_try; `SEMICOLON; fl = SELF ->(
	 if List.mem n (List.map get_field_name fl) then
	   report_error (get_pos_camlp4 _loc 4) (n ^ " is duplicated")
	 else
           let ann = if ann=[] then (gen_field_ann t) else ann in
	   ((t, n), get_pos_camlp4 _loc 3, false,ann) :: fl )
  | t1= typ; `OSQUARE; t2=typ; `CSQUARE; `IDENTIFIER n; peek_try; `SEMICOLON; fl = SELF ->
	(if List.mem n (List.map get_field_name fl) then
	  report_error (get_pos_camlp4 _loc 4) (n ^ " is duplicated")
	else
	  ((t1, n), get_pos_camlp4 _loc 3, false, (gen_field_ann t1)(*F_NO_ANN*)) :: fl )
]
    (* An Hoa [22/08/2011] Inline fields extension*)
  | "inline fields" [
	`INLINE; t = typ; `IDENTIFIER n -> [((t,n),get_pos_camlp4 _loc 1,true, (gen_field_ann t) (*F_NO_ANN*))]
      | `INLINE; t = typ; `OSQUARE; t2=typ; `CSQUARE; `IDENTIFIER n -> [((t,n), get_pos_camlp4 _loc 1,true, [] (*F_NO_ANN*))]
      | `INLINE; t=typ; `IDENTIFIER n; peek_try; `SEMICOLON; fl = SELF ->(
	    if List.mem n (List.map get_field_name fl) then
	      report_error (get_pos_camlp4 _loc 4) (n ^ " is duplicated")
	    else
	      ((t, n), get_pos_camlp4 _loc 3, true, (gen_field_ann t) (*F_NO_ANN*)) :: fl )
      | `INLINE; t1= typ; `OSQUARE; t2=typ; `CSQUARE; `IDENTIFIER n; peek_try; `SEMICOLON; fl = SELF ->
	    (if List.mem n (List.map get_field_name fl) then
	      report_error (get_pos_camlp4 _loc 4) (n ^ " is duplicated")
	    else
	      ((t1, n), get_pos_camlp4 _loc 3, true, (gen_field_ann t1) (*F_NO_ANN*)) :: fl )]];

(* one_field:   *)
(*   [[ t=typ; `IDENTIFIER n -> ((t, n), get_pos_camlp4 _loc 1) *)
(*    | t=typ; `OSQUARE; t2=typ; `CSQUARE; `IDENTIFIER n -> ((t,n), get_pos_camlp4 _loc 1)  *)
(*    ]];  *)

 (********** Views **********)

barrier_decl:
	[[ `BARRIER; `IDENTIFIER n; `OSQUARE; thc=integer_literal; `CSQUARE; `LT; shv=LIST1 typed_id_list SEP `COMMA;`GT;`EQEQ; bc=barrier_constr ->
		{barrier_thc = thc; barrier_name = n; barrier_shared_vars = shv; barrier_tr_list =bc;}]];



barrier_constr: [[`OSQUARE; t=LIST1 b_trans SEP `COMMA ; `CSQUARE-> t]];

b_trans : [[`OPAREN; fs= integer_literal; `COMMA; ts= integer_literal; `COMMA ;`OSQUARE;t=LIST1 spec_list SEP `COMMA;`CSQUARE; `CPAREN -> (fs,ts,t)]];

derv_view:
[[
   `IDENTIFIER vn;`LT;sl= id_list_opt; `GT -> (vn,sl)
]];

prop_extn:
[[
  `IDENTIFIER vn;`OSQUARE;props= id_list_opt;`CSQUARE;`LT;sl= id_list_opt;`GT -> (vn,props,sl)
]];

view_decl:
  [[ vh= view_header; `EQEQ; vb=view_body; oi= opt_inv; obi = opt_baga_inv; obui = opt_baga_under_inv; li= opt_inv_lock; mpb = opt_mem_perm_set
          (* let f = (fst vb) in *)
          ->  let (oi, oboi) = oi in
              { vh with view_formula = (fst vb);
              view_invariant = oi;
              view_baga_inv = obi;
              view_baga_over_inv = oboi;
              view_baga_under_inv = obui;
              view_mem = mpb;
              view_is_prim = false;
              view_is_hrel = None;
              view_kind = View_NORM; (* TODO : *)
              view_inv_lock = li;
              try_case_inference = (snd vb) }
    |  vh = view_header; `EQEQ; `EXTENDS; orig_v = derv_view; `WITH ; extn = prop_extn ->
      let vd = { vh with view_derv = true;
               view_derv_info = [(orig_v,extn)];
               view_kind = View_DERV;
           } in
      if !Globals.old_pred_extn then vd
      else
        (* let (id,_) = orig_v in *)
        { vd with
              view_derv_from = Some (REGEX_LIST [(fst(orig_v),true)]); (* views for extension *)
              view_derv_extns = [extn]; (* features of expension *)
            }
    |  vh = view_header; `EQEQ; `EXTENDS; orig_v = selective_id_star_list_bracket; `WITH ; extn = prop_extn ->
           { vh with view_derv = true;
               (* view_derv_info = [(orig_v,extn)]; *)
               view_kind = View_DERV;
               view_derv_from = Some orig_v; (* views for extension *)
               view_derv_extns = [extn]; (* features of expension *)
           }
 ]];

prim_view_decl:
  [[ vh= view_header; oi= opt_inv; obi = opt_baga_inv; obui = opt_baga_under_inv; li= opt_inv_lock
      -> let (oi, oboi) = oi in
          { vh with
          (* view_formula = None; *)
          view_invariant = oi;
          view_baga_inv = obi;
          view_baga_over_inv = oboi;
          view_baga_under_inv = obui;
          view_kind = View_PRIM;
          view_is_prim = true;
          view_is_hrel = None;
          view_inv_lock = li} ]];

view_decl_ext:
  [[ vh= view_header_ext; `EQEQ; vb= view_body; oi= opt_inv; obi = opt_baga_inv; obui = opt_baga_under_inv; li= opt_inv_lock
      -> let (oi, oboi) = oi in
          { vh with view_formula = (fst vb);
          view_invariant = oi;
          view_baga_inv = obi;
          view_baga_over_inv = oboi;
          view_baga_under_inv = obui;
          view_kind = View_EXTN;
          view_inv_lock = li;
          try_case_inference = (snd vb) } ]];

(* view_decl_spec:                                                                                                                                              *)
(*   [[ vh= view_header_ext; `EQEQ; `SPEC; va=view_header_ext;`WITH; vb=view_body; oi= opt_inv; obi = opt_baga_inv; obui = opt_baga_under_inv; li= opt_inv_lock *)
(*       ->                                                                                                                                                     *)
(*       let compare_list_string cmp ls1 ls2=                                                                                                                   *)
(*         let rec helper ls01 ls02=                                                                                                                            *)
(*           match ls01,ls02 with                                                                                                                               *)
(*             | [],[] -> true                                                                                                                                  *)
(*             | s1::rest1,s2::rest2 -> if cmp s1 s2 then helper rest1 rest2 else false                                                                         *)
(*             | _ -> false                                                                                                                                     *)
(*         in                                                                                                                                                   *)
(*         helper ls1 ls2                                                                                                                                       *)
(*       in                                                                                                                                                     *)
(*       let cmp_id id1 id2=                                                                                                                                    *)
(*         if String.compare id1 id2 =0 then true else false                                                                                                    *)
(*       in                                                                                                                                                     *)
(*       let cmp_typed_id (t1,id1) (t2,id2)=                                                                                                                    *)
(*         if t1=t2 && String.compare id1 id2 =0 then true else false                                                                                           *)
(*       in                                                                                                                                                     *)
(*       if not (compare_list_string cmp_id vh.view_vars va.view_vars &&                                                                                        *)
(*                   compare_list_string cmp_typed_id vh.view_prop_extns va.view_prop_extns) then                                                               *)
(*         report_error no_pos ("parser.view_decl_spec: not compatiable in view_spec " ^ vh.view_name)                                                          *)
(*       else                                                                                                                                                   *)
(*         let (oi, oboi) = oi in                                                                                                                               *)
(*         { vh with view_formula = (fst vb);                                                                                                                   *)
(*             view_invariant = oi;                                                                                                                             *)
(*             view_baga_inv = obi;                                                                                                                             *)
(*             view_baga_over_inv = oboi;                                                                                                                       *)
(*             view_baga_under_inv = obui;                                                                                                                      *)
(*             view_kind = View_SPEC;                                                                                                                      *)
(*             view_parent_name = Some va.view_name;                                                                                                            *)
(*             view_inv_lock = li;                                                                                                                              *)
(*             try_case_inference = (snd vb) } ]];                                                                                                              *)


opt_inv_lock: [[t=OPT inv_lock -> t]];

inv_lock:
    [[`INVLOCK; dc=disjunctive_constr -> (F.subst_stub_flow n_flow dc)]];

opt_baga_inv: [[t=OPT baga_invs -> t]];

opt_baga_under_inv: [[t=OPT baga_under_invs -> t]];

baga_invs:
    [[`INV_EXACT; bil = LIST0 baga_inv SEP `OR -> bil]];

baga_under_invs:
    [[`INV_SAT; bil = LIST0 baga_inv SEP `OR -> bil]];

opt_inv: [[t=OPT inv -> un_option t ((P.mkTrue no_pos), None
    (* Some [([], P.mkTrue no_pos)] *))]];

opt_mem_perm_set: [[t=OPT mem_perm_set -> t ]];

mem_perm_set: [[ `MEM; e = cexp; `LEFTARROW; `OPAREN;  mpl = LIST0 mem_perm_layout SEP `SEMICOLON; `CPAREN
				-> let fal,g = List.split mpl in
				   let fv,al = List.split fal in
					{	F.mem_formula_exp = e;
					F.mem_formula_exact = false;
					F.mem_formula_field_values = fv;
					F.mem_formula_field_layout = al;
					F.mem_formula_guards = g}
		| `MEME; e = cexp; `LEFTARROW; `OPAREN; mpl = LIST0 mem_perm_layout SEP `SEMICOLON; `CPAREN
				-> let fal,g = List.split mpl in
				   let fv,al = List.split fal in
					{	F.mem_formula_exp = e;
					F.mem_formula_exact = true;
					F.mem_formula_field_values = fv;
					F.mem_formula_field_layout = al;
					F.mem_formula_guards = g} ]];

mem_perm_layout:[[
`IDENTIFIER dn; `LT; annl = ann_list; `GT; guard = OPT pure_guard ->
let fv,annl = List.split annl in
let perml = get_heap_ann_list annl in ((dn,fv),(dn,perml)),(un_option guard (P.mkTrue no_pos)) ]];

pure_guard: [[ `AND; e = pure_constr -> e
]];

ann_list:[[b = LIST0 cexp_ann SEP `COMMA -> b]];

cexp_ann: [[ `INT_LITER (i,_) ; ah = ann_heap ->  (P.IConst(i,no_pos),ah)
           | e = OPT cid ; ah = ann_heap ->
           let evar = (un_option e ("Anon_"^(fresh_trailer()),Unprimed) ) in (P.Var(evar,no_pos),ah)
          ]];

opt_derv: [[t=OPT derv -> un_option t false ]];

opt_split: [[t=OPT split -> un_option t SPLIT0 ]];

derv : [[ `DERV -> true ]];

split : [[ `SPLIT1Ann -> SPLIT1
  | `SPLIT2Ann -> SPLIT2 ]];

inv:
  [[`INV; pc=pure_constr; ob=opt_branches ->
      let f = P.mkAnd pc ob (get_pos_camlp4 _loc 1) in
      (f, Some [([], f)])
   |`INV; h=ho_fct_header ->
         let f = P.mkTrue no_pos in
         (f, Some [([], f)])
   |`INV; bil = LIST0 baga_inv SEP `OR ->
        let pf =  List.fold_left (fun pf0 (idl,pf2) ->
         let idl = List.filter (fun (_,p) -> p==None) idl in
         let idl = List.map fst idl in
         let pf1 = List.fold_left (fun pf0 id ->
             let sv = (id,Unprimed) in
             P.mkAnd pf0 (P.mkNeqExp (P.Var (sv,no_pos)) (P.Null no_pos) no_pos) no_pos
           ) (P.mkTrue no_pos) idl in
         P.mkOr pf0 (P.mkAnd pf1 pf2 no_pos) None no_pos
       ) (P.mkFalse no_pos) bil in
        (pf, Some bil)]];

baga_formula:
    [[pc=pure_constr; ob=opt_branches -> (P.mkAnd pc ob (get_pos_camlp4 _loc 1))
      | h=ho_fct_header -> (P.mkTrue no_pos)]];

baga_inv:
    [[`BG; `OPAREN; `OSQUARE; il = LIST0 cid_or_pair SEP `COMMA; `CSQUARE; `COMMA; p=baga_formula; `CPAREN ->
        let il = List.map (fun ((name,p),s)->
          let () = if p==Primed then print_endline_quiet "WARNING: primed variable disallowed" in
          (name,s)
          (* match s with *)
          (* | Some(n2,p) ->  *)
          (*   let () = if p==Primed then print_endline_quiet "WARNING: primed variable disallowed" in *)
          (*   (name,Some(n2)) *)
          (* | None -> (name,None) *)
        ) il in
        (il,p)]];

opt_infer_post: [[t=OPT infer_post -> un_option t true ]];

infer_post :
  [[
   `PRE -> false
   | `POST  -> true
   ]];

opt_infer_xpost: [[t=OPT infer_xpost -> un_option t None ]];

infer_xpost :
  [[
   `XPRE -> Some false
   | `XPOST  -> Some true
  ]];

opt_transpec: [[t=OPT transpec -> un_option t None ]];

transpec:
  [[ `OBRACE; `IDENTIFIER old_view_name; `LEFTARROW; `IDENTIFIER new_view_name; `CBRACE ->
(*    if not(view_names # mem old_view_name) then *)
(*      report_error (get_pos_camlp4 _loc 1) ("Predicate " ^ old_view_name ^ " is not initialized.")*)
(*    else if not(view_names # mem new_view_name) then *)
(*      report_error (get_pos_camlp4 _loc 1) ("Predicate " ^ new_view_name ^ " is not initialized.")*)
(*    else *)
      Some (old_view_name, new_view_name)
  ]];


ann_label:
  [[
     `SAT  -> Lbl.LA_Sat
   | `IMM  -> Lbl.LA_Imply
   ]];

ann_heap:
  [[
    `MUT -> Some (P.ConstAnn(Mutable))
   | `IMM  -> Some (P.ConstAnn(Imm))
   | `LEND -> Some (P.ConstAnn(Lend))
   | `ACCS -> Some (P.ConstAnn(Accs))
   | `AT; t=cid  -> Some (P.PolyAnn(t, get_pos_camlp4 _loc 1))
   | `DERV -> None
   ]];

ann_heap_list: [[ b=LIST0 ann_heap -> b ]];

opt_branches:[[t=OPT branches -> un_option t (P.mkTrue no_pos)]];

branches : [[`AND; `OSQUARE; b= LIST1 one_branch SEP `SEMICOLON ; `CSQUARE -> P.mkAndList_opt b ]];

(* one_branch_single : [[ `STRING (_,id); `COLON; pc=pure_constr -> (LO.singleton id,pc)]]; *)

one_string: [[`STRING (_,id)-> id]];

one_string_w_ann: [[  id = one_string; ann_lbl = OPT ann_label -> (id, un_option ann_lbl (Lbl.LA_Both) )]];

string_w_ann_list: [[`COMMA; lbl_lst = LIST0 one_string_w_ann SEP `COMMA -> lbl_lst]];

opt_string_w_ann_list: [[lbl_lst = OPT string_w_ann_list -> un_option lbl_lst [] ]];

(* one_branch : [[ lbl = LIST1 one_string SEP `COMMA ; `COLON; pc=pure_constr -> (LO.norm lbl,pc)]]; *)
one_branch : [[ lbl = one_string; lblA = opt_string_w_ann_list ; `COLON; pc=pure_constr -> (LO.convert lbl lblA,pc)]];

opt_branch:[[t=OPT branch -> un_option t LO.unlabelled]];

branch: [[ `STRING (_,id);`COLON ->
    if !Globals.remove_label_flag then  LO.unlabelled
    else LO.singleton id ]];

view_header:
  [[ `IDENTIFIER vn; opt1 = OPT opt_brace_vars; `LT; l= opt_ann_cid_list; `GT ->
      let () = view_names # push vn in
      let mvs = get_mater_vars l in
      let cids, anns = List.split l in
      let modes = get_modes anns in
      let pos = get_pos_camlp4 _loc 1 in
      Iast.mk_view_header vn opt1 cids mvs modes pos
]];

id_type_list_opt: [[ t = LIST0 cid_typ SEP `COMMA -> t ]];

(* form_list_opt: [[ t = LIST0 disjunctive_constr SEP `COMMA -> t ]]; *)

rflow_form_list_opt: [[ t = LIST0 rflow_form SEP `COMMA -> t ]];

rflow_kind:
  [[ `MINUS -> INFLOW
   | `PLUS -> OUTFLOW
  ]];

rflow_form:
  [[ k = OPT rflow_kind; dc = disjunctive_constr (* core_constr *) ->
     { F.rflow_kind = un_option k NEUTRAL;
       F.rflow_base = F.subst_stub_flow n_flow dc; }
      (* match cc with                                                                                  *)
      (* | F.Base f -> {                                                                                *)
      (*   F.rflow_kind = un_option k NEUTRAL;                                                          *)
      (*   F.rflow_base = cc; }                                                                         *)
      (* | _ -> report_error (get_pos_camlp4 _loc 2) ("Non-Base formula is disalowed in resource flow") *)
  ]];

formula_ann: [[ `SPLITANN -> HO_SPLIT ]];

ho_id: [[ `PERCENT; `IDENTIFIER id -> id ]];

id_ann:
  [[ hid = ho_id; t = OPT formula_ann -> (NEUTRAL, hid, (un_option t HO_NONE))
   | `PLUS; hid = ho_id; t = OPT formula_ann -> (OUTFLOW, hid, (un_option t HO_NONE))
   | `MINUS; hid = ho_id; t = OPT formula_ann -> (INFLOW,  hid, (un_option t HO_NONE))
  ]];

id_ann_list_opt :[[b = LIST0 id_ann SEP `COMMA -> b]];

opt_brace_vars : [[ `OBRACE; sl = id_ann_list_opt; `CBRACE -> sl ]];

rflow_form_list : [[ `OBRACE; sl = rflow_form_list_opt; `CBRACE ->
    List.map (fun ff -> {ff with F.rflow_base = F.subst_stub_flow n_flow ff.F.rflow_base}) sl ]];

view_header_ext:
    [[ `IDENTIFIER vn;`OSQUARE;sl= id_type_list_opt (*id_list*) ;`CSQUARE; `LT; l= opt_ann_cid_list; `GT ->
      let cids, anns = List.split l in
      let cids_t, br_labels = List.split cids in
	  let has_labels = List.exists (fun c-> not (LO.is_unlabelled c)) br_labels in
      (* DD.info_hprint (add_str "parser-view_header(cids_t)" (pr_list (pr_pair string_of_typ pr_id))) cids_t no_pos; *)
      let _, cids = List.split cids_t in
      (* if List.exists (fun x -> match snd x with | Primed -> true | Unprimed -> false) cids then *)
      (*   report_error (get_pos_camlp4 _loc 1) ("variables in view header are not allowed to be primed") *)
      (* else *)
      let modes = get_modes anns in
      let () = view_names # push vn in
        { view_name = vn;
          view_pos = get_pos_camlp4 _loc 1;
          view_data_name = "";
          view_imm_map = [];
          view_type_of_self = None;
          (* view_actual_root = None; *)
          view_vars = (* List.map fst *) cids;
          view_ho_vars = [];
          (* view_frac_var = empty_iperm; *)
          view_labels = br_labels,has_labels;
          view_parent_name = None;
          view_derv = false;
          view_derv_from = None;
          view_derv_extns = [];
          view_modes = modes;
          view_typed_vars = cids_t;
          view_pt_by_self  = [];
          view_formula = F.mkETrue top_flow (get_pos_camlp4 _loc 1);
          view_inv_lock = None;
          view_is_prim = false;
          view_is_hrel = None;
          view_kind = View_EXTN;
          view_prop_extns = sl;
          view_derv_info = [];
          view_invariant = P.mkTrue (get_pos_camlp4 _loc 1);
          view_baga_inv = None;
          view_baga_over_inv = None;
          view_baga_under_inv = None;
          view_mem = None;
		  view_materialized_vars = get_mater_vars l;
          try_case_inference = false;
			}]];

(** An Hoa : Modify the rules to capture the extensional identifiers **)
cid:
  [[
     (* `IDENTIFIER t; `PRIME	 	-> (* print_string ("primed id:"^t^"\n"); *) (t, Primed) *)
   `IDENTIFIER t	-> if String.contains t '\'' then (* Remove the primed in the identifier *)
		 (Str.global_replace (Str.regexp "[']") "" t,Primed)
	   else (t,Unprimed)
    | `RES _                 	->  (res_name, Unprimed)
    | `SELFT _               	->  (self, Unprimed)
    | `NULL                     ->  (null_name, Unprimed)
    | `THIS _         		->  (this, Unprimed)]];


cid_or_pair:
  [[
    `OPAREN; e1=cexp_w ; `COMMA;  e2= cexp_w; `CPAREN ->
    let pe1 = get_pure_exp e1 no_pos in
    let pe2 = get_pure_exp e2 no_pos in
    (("_",Unprimed),(Some(pe1,pe2)))
  | i = cid -> (i,None)
  ]];


(** An Hoa : Access extension. For example: in "x.node.value", ".node.value" is the idext **)
(* idext:
	[[ `DOT; `IDENTIFIER t 				-> "." ^ t
	| `DOT; `IDENTIFIER t; u=idext 		-> "." ^ t ^ u]]; *)

view_body:
  [[ t = formulas -> ((F.subst_stub_flow_struc top_flow (fst t)),(snd t))
   | `FINALIZE; t = split_combine -> (F.mkEFalseF (),false)
  ]];


(********** Constraints **********)

opt_heap_arg_list: [[t=LIST1 cexp SEP `COMMA -> t]];

opt_heap_arg_list2:[[t=LIST1 heap_arg2 SEP `COMMA -> error_on_dups (fun n1 n2-> (fst n1)==(fst n2)) t (get_pos_camlp4 _loc 1)]];

opt_heap_data_arg_list: [[t=LIST1 cexp_data_p SEP `COMMA -> t]];

opt_heap_data_arg_list2:[[t=LIST1 heap_arg2_data SEP `COMMA -> error_on_dups (fun n1 n2-> (fst n1) == (fst n2)) t (get_pos_camlp4 _loc 1)]];

heap_arg2: [[ peek_heap_args; `IDENTIFIER id ; `EQ;  e=cexp -> (id,e)]];

heap_arg2_data: [[ peek_heap_args; `IDENTIFIER id ; `EQ;  e = cexp_data_p -> (id,e)]];

opt_cid_list: [[t=LIST0 cid SEP `COMMA -> error_on_dups (fun n1 n2-> (fst n1)==(fst n2)) t (get_pos_camlp4 _loc 1)]];

cid_list: [[t=LIST1 cid SEP `COMMA -> error_on_dups (fun n1 n2-> (fst n1)==(fst n2)) t (get_pos_camlp4 _loc 1)]];

(* annotated cid list *)
opt_ann_cid_list: [[t=LIST0 ann_cid SEP `COMMA -> t]];

c_typ:
 [[ `COLON; t= typ -> t
 ]];

cid_typ:
  [[ `IDENTIFIER id ; t=OPT c_typ ->
      let ut = un_option t UNK in
      let _ =
        (* WN : code below uses side-effects and may also result in relational name clashes *)
        if is_RelT ut then
          (* let () = print_endline ("ll 1: " ^ id) in *)
          let () = rel_names # push id in
          (* let rd = get_tmp_rel_decl () in *)
         (*  let rd = {rd with rel_name = id} in *)
        (* (\*push rd in the list*\) *)
        (*   let () = g_rel_defs # push rd in *)
          ()
        else (* let () = print_endline ("ll: " ^ id)  in *) ()
      in
        (ut,id)
   ]];

ann_cid:[[ ob= opt_branch; c = cid_typ; al=opt_ann_list ->((c, ob), al)]];


opt_ann_list: [[t=LIST0 ann -> t]];

p_vp_ann:
  [[ `PZERO -> VP_Zero
   | `PFULL -> VP_Full
   | `PVALUE -> VP_Value
   | `PLEND -> VP_Lend
   | `PFRAC;`OPAREN; `INT_LITER(i1,_); `DIV;  `INT_LITER(i2,_)
         (* `FRAC _LIT (f,s) *);`CPAREN-> VP_Frac (Frac.make i1 i2)
   (* | `AT; `FRAC_LIT (f, _) -> VP_Frac f *)
   (* | `PREF -> VP_Ref *)
  ]];

ann:
  [[ `AT; `IDENTIFIER id -> begin
      if id = "out" then AnnMode ModeOut
      else report_error (get_pos_camlp4 _loc 2) ("unrecognized mode: " ^ id) end
   | `AT ; `IN_T       -> AnnMode ModeIn
   | `MAT -> AnnMater  ]];

sq_clist: [[`OSQUARE; l= opt_cid_list; `CSQUARE -> l ]];

formulas:
  [[ ec= extended_l     ->(ec,false)
	 | dc=disjunctive_constr  -> ((F.formula_to_struc_formula dc),true)]];

extended_l:
  [[ peek_extended; `OSQUARE; h=extended_constr_grp ; `ORWORD; t=LIST1 extended_constr_grp SEP `ORWORD; `CSQUARE ->
     label_struc_groups (h::t)
   | h=extended_constr_grp -> label_struc_groups [h]]];

extended_l2:
  [[ peek_extended; `OSQUARE; h=extended_constr_grp2 ; `ORWORD; t=LIST1 extended_constr_grp2 SEP `ORWORD; `CSQUARE ->
     label_struc_groups (h::t)
   | h=extended_constr_grp2 -> label_struc_groups [h]]];

extended_constr_grp:
   [[ c=extended_constr -> [(Lbl.empty_spec_label_def,c)]
    | `IDENTIFIER id; `COLON; `OSQUARE; t = LIST0 extended_constr SEP `ORWORD; `CSQUARE -> List.map (fun c-> (LO2.singleton id,c)) t]];

extended_constr_grp2:
   [[ c=extended_constr2 -> [(Lbl.empty_spec_label_def,c)]
    | `IDENTIFIER id; `COLON; `OSQUARE; t = LIST0 extended_constr2 SEP `ORWORD; `CSQUARE -> List.map (fun c-> (LO2.singleton id,c)) t]];

(* then_extended : [[ `THEN; il = extended_l -> il ]]; *)

then_extended : [[ il = extended_l -> il ]];

extended_constr:
	[[ `CASE; `OBRACE; il= impl_list; `CBRACE ->
      F.ECase {
          F.formula_case_branches = il;
          F.formula_case_pos = (get_pos_camlp4 _loc 3) }
	| sl=sq_clist; oc=disjunctive_constr; rc= OPT then_extended -> F.mkEBase sl [] [] oc rc (get_pos_camlp4 _loc 2)]];

extended_constr2:
	[[ sl=sq_clist; oc=disjunctive_constr; rc= OPT then_extended -> F.mkEBase sl [] [] oc rc (get_pos_camlp4 _loc 2)]];

impl_list:[[t=LIST1 impl -> t]];

impl: [[ pc=pure_constr; `LEFTARROW; ec=extended_l; `SEMICOLON ->
			if(List.length (Ipure.look_for_anonymous_pure_formula pc))>0 then report_error (get_pos_camlp4 _loc 1) ("anonymous variables in case guard are disalowed")
		  else (pc,ec)]];

(* seem _loc 2 is empty *)
disjunctive_constr:
  [ "disj_or" LEFTA
    [ dc=SELF; `ORWORD; oc=SELF -> F.mkOr dc oc (get_pos_camlp4 _loc 1)]
  | [ dc=SELF; `ANDWORD; oc=SELF -> dc]
  | [peek_dc; `OPAREN;  dc=SELF; `CPAREN -> dc]
  | "disj_base"
    [ cc=core_constr_and -> cc
    | `EXISTS; ocl= cid_list; `COLON; cc= core_constr_and ->
	  (match cc with
      | F.Base ({
          F.formula_base_heap = h;
          F.formula_base_pure = p;
          F.formula_base_vperm = vp;
          F.formula_base_flow = fl;
          F.formula_base_and = a; }) ->
        F.mkExists ocl h p vp fl a (get_pos_camlp4 _loc 1)
      | _ -> report_error (get_pos_camlp4 _loc 4) ("only Base is expected here."))
    ]
  ];

core_constr_and : [[
    f1 = core_constr; `ANDWORD; ls=core_constr_conjunctions ->
      let main = F.add_formula_and ls f1 in
      main
  | f1 = core_constr -> f1
]];

core_constr_conjunctions: [ "core_constr_and" LEFTA
                   [ f1 = SELF; `ANDWORD; f2 = SELF -> f1@f2]
                   | [f1 = and_core_constr -> [f1]]
                  ];

and_core_constr:
  [
    [ dl = pure_constr; `CONSTR; f = core_constr  ->
      let h,p,_,fl,_ = F.split_components f in
      let pos = (get_pos_camlp4 _loc 2) in
      F.mkOneFormula h p dl None pos
    ]
  ];

core_constr:
  [
    [ pc= pure_constr; fc= opt_flow_constraints; fb=opt_branches ->
      let pos = (get_pos_camlp4 _loc 1) in
      F.formula_of_pure_with_flow_htrue (P.mkAnd pc fb pos) fc [] pos
    | vp= vperm_constr; pc= opt_pure_constr; fc= opt_flow_constraints; fb=opt_branches ->
      let pos = (get_pos_camlp4 _loc 1) in
      F.formula_of_vperm_pure_with_flow_emp (*
emp|htrue?*) (P.mkAnd pc fb pos) vp fc [] pos
    | hc= opt_heap_constr; vp= opt_vperm_constr; pc= opt_pure_constr; fc= opt_flow_constraints; fb= opt_branches ->
      let pos = (get_pos_camlp4 _loc 1) in
      F.mkBase hc (P.mkAnd pc fb pos) vp fc [] pos
    ]
  ];

opt_vperm_constr: [[ vp = OPT star_vperm_constr -> un_option vp VP.empty_vperm_sets ]];

star_vperm_constr: [[ `STAR; vp = vperm_constr -> vp ]];

vperm_constr:
  [[ vp = SELF; `STAR; vc = single_vperm_constr ->
      VP.merge_vperm_sets [vp; vc]
   | vc = single_vperm_constr -> vc
  ]];

single_vperm_constr:
  [[ ann = p_vp_ann ; `OSQUARE; ls = id_list; `CSQUARE ->
      let ls = List.map sv_of_id ls in
      VP.create_vperm_sets ann ls
  ]];

opt_flow_constraints: [[t=OPT flow_constraints -> un_option t stub_flow]];

flow_constraints: [[ `AND; `FLOW _; `IDENTIFIER id -> id]];

opt_formula_label: [[t=OPT formula_label -> un_option t None]];

opt_label: [[t= OPT label->un_option t ""]];

label : [[  `STRING (_,id);  `COLON -> id ]];

(* label_w_ann : [[  `STRING (_,id); ann_lbl = OPT ann_label; `COLON -> (id, un_option ann_lbl (Lbl.LA_Both)) ]]; *)

(* opt_pure_label :[[t=Opure_label -> un_option t (fresh_branch_point_id "")]]; *)

pure_label : [[ `DOUBLEQUOTE; `IDENTIFIER id; `DOUBLEQUOTE; `COLON -> fresh_branch_point_id id]];

formula_label: [[ `AT; `STRING (_,id) ->(fresh_branch_point_id id)]];

opt_heap_constr: [[ t = heap_constr -> t]];

(* heap_constr: *)
(*   [[    hrd=SELF; `STAR; hrw=SELF -> F.mkStar hrd hrw (get_pos_camlp4 _loc 2)]  *)
(* (\*      |[ shc = simple_heap_constr -> shc]  *\) *)
(*      |[ c=cid; `COLONCOLON; `IDENTIFIER id; simple2; hal=opt_heap_arg_list; `GT; ofl = opt_formula_label ->   *)
(*                     F.mkHeapNode c id false false false false hal ofl (get_pos_camlp4 _loc 2)  *)
(*   ]];  *)

heap_constr:
  [[ `OPAREN; hrd=heap_rd; `CPAREN; `SEMICOLON; hrw=heap_rw -> F.mkPhase hrd hrw (get_pos_camlp4 _loc 2)
   | `OPAREN; hrd=heap_rd; `CPAREN                          -> F.mkPhase hrd F.HEmp (get_pos_camlp4 _loc 2)
   | hrw = heap_rw                                          -> F.mkPhase F.HEmp hrw (get_pos_camlp4 _loc 2)]];

heap_rd:
  [[ shi= simple_heap_constr_imm; `STAR; hrd=SELF -> F.mkStar shi hrd (get_pos_camlp4 _loc 2)
   | shi=simple_heap_constr_imm; `AND; hrd=SELF  -> F.mkConj shi hrd (get_pos_camlp4 _loc 2)
   | shi=simple_heap_constr_imm                  -> shi]];


heap_rw:
  [[ hrd=heap_wr; `STAR; `OPAREN; hc=heap_constr; `CPAREN -> F.mkStar hrd hc (get_pos_camlp4 _loc 2)
   | hrd=heap_wr; peek_heap_starminus; `STARMINUS; `OPAREN; hc=heap_constr; `CPAREN -> F.mkStarMinus hc hrd (get_pos_camlp4 _loc 2)
   | shc=heap_wr; peek_heap_and; `AND; `OPAREN; wr = heap_constr; `CPAREN -> F.mkConjConj shc wr (get_pos_camlp4 _loc 2)
   | shc=heap_wr; peek_heap_andstar; `ANDSTAR; `OPAREN; wr = heap_constr; `CPAREN -> F.mkConjStar shc wr (get_pos_camlp4 _loc 2)
   | shc=heap_wr; peek_heap_unionstar; `UNIONSTAR; `OPAREN; wr = heap_constr; `CPAREN -> F.mkConj shc wr (get_pos_camlp4 _loc 2)
   | shc=heap_wr; peek_heap_starminus; `STARMINUS; wr = simple_heap_constr -> F.mkStarMinus wr shc (get_pos_camlp4 _loc 2)
   | shc=heap_wr; peek_heap_and; `AND; wr = simple_heap_constr -> F.mkConjConj shc wr (get_pos_camlp4 _loc 2)
   | shc=heap_wr; peek_heap_andstar; `ANDSTAR; wr = simple_heap_constr -> F.mkConjStar shc wr (get_pos_camlp4 _loc 2)
   | shc=heap_wr; peek_heap_unionstar; `UNIONSTAR; wr = simple_heap_constr -> F.mkConj shc wr (get_pos_camlp4 _loc 2)
   | hwr=heap_wr                                          -> F.mkPhase F.HEmp hwr (get_pos_camlp4 _loc 2)]];

heap_wr:
  [[
     shc=SELF; peek_star; `STAR; hw= simple_heap_constr    -> F.mkStar shc hw (get_pos_camlp4 _loc 2)
   | shc=simple_heap_constr        -> shc
   (* | shi=simple_heap_constr_imm; `STAR;  hw=SELF -> F.mkStar shi hw (get_pos_camlp4 _loc 2) *)
   (* | shi=simple_heap_constr_imm; `STAR; `OPAREN; hc=heap_constr; `CPAREN  -> F.mkStar shi hc (get_pos_camlp4 _loc 2) *)
  ]];

(* simple2:  [[ t= opt_type_var_list -> ()]]; *)

heap_id:
  [[
     `IDENTIFIER id -> (id, 0, 0, _loc)
   (* definitions below is for cparser *)
   | `VOID; `STAR -> ("void", 1, 0, _loc)
   | `INT; `STAR -> ("int", 1, 0, _loc)
   | `FLOAT; `STAR -> ("float", 1, 0, _loc)
   | `BOOL; `STAR -> ("bool", 1, 0, _loc)
   | `IDENTIFIER id; `STAR -> (id, 1, 0, _loc)
   | `VOID; `CARET -> ("void", 0, 1, _loc)
   | `INT; `CARET -> ("int", 0, 1, _loc)
   | `FLOAT; `CARET -> ("float", 0, 1, _loc)
   | `BOOL; `CARET -> ("bool", 0, 1, _loc)
   | `IDENTIFIER id; `CARET -> (id, 0, 1, _loc)
   | hid = heap_id; `STAR ->
       let (h, s, c, l) = hid in
       if (c > 0) then
         report_error (get_pos_camlp4 _loc 1) "invalid heap_id string"
       else
         (h, s+1, c, l)
   | hid = heap_id; `CARET ->
       let (h, s, c, l) = hid in
       (h, s, c+1, l)
  ]];

(*LDK: frac for fractional permission*)
(* TODO:HO *)
simple_heap_constr_imm:
  [[ peek_heap; c=cid; `COLONCOLON; hid = heap_id; opt1 = OPT rflow_form_list; frac = opt_perm; `LT; hl= opt_data_h_args; `GT; annl = ann_heap_list; dr= opt_derv; split= opt_split; ofl= opt_formula_label ->
       let imm_opt = get_heap_ann annl in
       let frac = if (Perm.allow_perm ()) then frac else empty_iperm () in
       let (c, hid, deref) = get_heap_id_info c hid in
       let ho_args = un_option opt1 [] in
       match hl with
       | ([],[]) -> F.mkHeapNode c hid ho_args deref dr split imm_opt false false false frac [] [] ofl (get_pos_camlp4 _loc 2)
       | ([],t) ->
           let t11, t12 = List.split t in
           let t21, t22 = List.split t12 in
           let t3 = List.combine t11 t21 in
           F.mkHeapNode2 c hid ho_args deref dr split imm_opt false false false frac t3 t22 ofl  (get_pos_camlp4 _loc 2)
       | (t,_)  ->
           let t1, t2 = List.split t in
           F.mkHeapNode c hid ho_args deref dr split imm_opt false false false frac t1 t2 ofl (get_pos_camlp4 _loc 2)
  ]];

(* the next three rules:
    separate the parsing args of heap/data node for backtracking
*)
thread_args:
   [[peek_hash_thread;(* `TOPAREN *)`LT; `HASH ; dl = opt_delayed_constr; rsr = disjunctive_constr; (* `TCPAREN *) `HASH; `GT -> (dl,rsr) ]];

non_thread_args1:
  [[
    `LT; hl= opt_general_h_args; `GT -> hl
  ]];

non_thread_args2:
  [[
    `LT; hl= opt_data_h_args; `GT -> hl
  ]];

(*LDK: add frac for fractional permission*)
simple_heap_constr:
    [[ peek_heap; c=cid; `COLONCOLON;  hid = heap_id; opt1 = OPT rflow_form_list ; (* simple2 ; *) frac= opt_perm;
 (*  peek_hash_thread;(* `TOPAREN *)`LT; `HASH ; dl = opt_delayed_constr; rsr = disjunctive_constr; (* `TCPAREN *) `HASH; `GT ; *)
    a=thread_args;
 ofl = opt_formula_label ->
     (*For threads as resource*)
     let (dl,rsr) = a in
     let (c, hid, deref) = get_heap_id_info c hid in
     F.mkThreadNode c hid (F.subst_stub_flow n_flow rsr) dl frac ofl (get_pos_camlp4 _loc 2)
   | peek_heap; c=cid; `COLONCOLON; hid = heap_id; opt1 = OPT rflow_form_list (* simple2 *); frac= opt_perm; (*`LT; hl= opt_general_h_args; `GT;*)
     hl = non_thread_args1;
     annl = ann_heap_list; dr=opt_derv; split= opt_split; ofl= opt_formula_label -> (
       (*ignore permission if applicable*)
       let frac = if (Perm.allow_perm ())then frac else empty_iperm () in
       let imm_opt = get_heap_ann annl in
       let (c, hid, deref) = get_heap_id_info c hid in
       let ho_args = un_option opt1 [] in
       match hl with
       (* WN : HeapNode2 is for d<field=v*> *)
       (*  p<> can be either node or predicate *)
       | ([],[]) -> F.mkHeapNode c hid ho_args deref dr split imm_opt false false false frac [] [] ofl (get_pos_camlp4 _loc 2)
       | ([],t) -> F.mkHeapNode2 c hid ho_args deref dr split imm_opt false false false frac t [] ofl (get_pos_camlp4 _loc 2)
       | (t,_)  -> F.mkHeapNode c hid ho_args deref dr split imm_opt false false false frac t [] ofl (get_pos_camlp4 _loc 2)
     )
   | peek_heap; c=cid; `COLONCOLON; hid = heap_id; opt1 = OPT rflow_form_list (* simple2 *); frac= opt_perm;
     (* `LT; hl= opt_data_h_args; `GT;*)
     hl = non_thread_args2;
     annl = ann_heap_list; dr=opt_derv; split= opt_split; ofl= opt_formula_label -> (
        (*ignore permission if applicable*)
        let frac = if (Perm.allow_perm ())then frac else empty_iperm () in
        let imm_opt = get_heap_ann annl in
        let (c, hid, deref) = get_heap_id_info c hid in
        let ho_args = un_option opt1 [] in
        match hl with
        | ([],[]) -> F.mkHeapNode c hid ho_args deref dr split imm_opt false false false frac [] [] ofl (get_pos_camlp4 _loc 2)
        | ([], t) ->
            let t11, t12 = List.split t in
            let t21, t22 = List.split t12 in
            let t3 = List.combine t11 t21 in
            F.mkHeapNode2 c hid ho_args deref dr split imm_opt false false false frac t3 t22 ofl (get_pos_camlp4 _loc 2)
        | (t, _)  ->
            let t1, t2 = List.split t in
            F.mkHeapNode c hid ho_args deref dr split imm_opt false false false frac t1 t2 ofl (get_pos_camlp4 _loc 2)
     )
   | peek_heap; c=cid; `COLONCOLON; hid = heap_id; opt1 = OPT rflow_form_list (* simple2 *); frac= opt_perm;
     (* `LT; hal=opt_general_h_args; `GT; *)
     hal = non_thread_args1;
     dr=opt_derv; split= opt_split; ofl = opt_formula_label -> (
       let (c, hid, deref) = get_heap_id_info c hid in
       let ho_args = un_option opt1 [] in
       match hal with
       | ([],[]) -> F.mkHeapNode c hid ho_args deref dr split (P.ConstAnn(Mutable)) false false false frac [] [] ofl (get_pos_camlp4 _loc 2)
       | ([],t) -> F.mkHeapNode2 c hid ho_args deref dr split (P.ConstAnn(Mutable)) false false false frac t [] ofl (get_pos_camlp4 _loc 2)
       | (t,_)  -> F.mkHeapNode c hid ho_args deref dr split (P.ConstAnn(Mutable)) false false false frac t [] ofl (get_pos_camlp4 _loc 2)
     )
   | t = ho_fct_header -> (
       let frac = (
         if (Perm.allow_perm ()) then
           full_iperm ()
         else
           empty_iperm ()
       ) in
       F.mkHeapNode ("",Primed) "" [] 0 false (*dr*) SPLIT0 (P.ConstAnn(Mutable)) false false false frac [] [] None  (get_pos_camlp4 _loc 1)
     )
     (* An Hoa : Abbreviated syntax. We translate into an empty type "" which will be filled up later. *)
   | peek_heap; c=cid; `COLONCOLON;  opt1 = OPT rflow_form_list (* simple2*) ; frac= opt_perm;
         (* `LT; hl= opt_general_h_args; `GT;*)
         hl = non_thread_args1;
         annl = ann_heap_list; dr=opt_derv; split= opt_split; ofl= opt_formula_label -> (
       let frac = if (Perm.allow_perm ()) then frac else empty_iperm () in
       let imm_opt = get_heap_ann annl in
       let ho_args = un_option opt1 [] in
       match hl with
       | ([],t) -> F.mkHeapNode2 c generic_pointer_type_name ho_args 0 dr split imm_opt false false false frac t [] ofl (get_pos_camlp4 _loc 2)
       | (t,_)  -> F.mkHeapNode c generic_pointer_type_name ho_args 0 dr split imm_opt false false false frac t [] ofl (get_pos_camlp4 _loc 2)
     )
   | peek_heap; c=cid; `COLONCOLON; opt1 = OPT rflow_form_list  (*simple2*); frac= opt_perm; (* `LT; hal=opt_general_h_args; `GT; *)
         hal = non_thread_args1;
         dr=opt_derv; split= opt_split; ofl = opt_formula_label -> (
       let ho_args = un_option opt1 [] in
       match hal with
       | ([],[])  -> F.mkHeapNode c generic_pointer_type_name ho_args 0 dr split (P.ConstAnn(Mutable)) false false false frac [] [] ofl (get_pos_camlp4 _loc 2)
       | ([],t) -> F.mkHeapNode2 c generic_pointer_type_name ho_args  0 dr split (P.ConstAnn(Mutable)) false false false frac t [] ofl (get_pos_camlp4 _loc 2)
       | (t,_)  -> F.mkHeapNode c generic_pointer_type_name ho_args  0 dr split (P.ConstAnn(Mutable)) false false false frac t [] ofl (get_pos_camlp4 _loc 2)
     )
     (* High-order variables, e.g. %P*)
   | `PERCENT; `IDENTIFIER id -> F.HVar (id,[])
   | `IDENTIFIER id; `OPAREN; cl = opt_cexp_list; `CPAREN ->
     let pos = get_pos_camlp4 _loc 2 in
     if hp_names # mem id then
       if !Globals.hrel_as_view_flag then
         (* report_error (get_pos 1) "hrel_as_view : to be implemented (1)" *)
         F.mk_hrel id cl pos
       else
         F.mk_hrel id cl pos
           (* F.HRel(id, cl, (get_pos_camlp4 _loc 2)) *)
         (*P.BForm ((P.RelForm (id, cl, get_pos_camlp4 _loc 1), None), None))*)
     else report_error (get_pos 1) ("should be a heap pred, not pure a relation here")
   | `HTRUE -> F.HTrue
   | `EMPTY -> F.HEmp
  ]];

(* (* HO Resource variables' annotation *)  *)
(* rflow_ann: [[ `IN_RFLOW | `OUT_RFLOW ]]; *)

(*LDK: parse optional fractional permission, default = 1.0*)
opt_perm: [[t = OPT perm -> t ]];

perm: [[
    `OPAREN; t = perm_aux; `CPAREN -> t
]];

(*LDK: for fractionl permission, we expect cexp*)
perm_aux: [[
    peek_div_op;
    (* peek_print; *)
    t1 = integer_literal ; `DIV ; t2 = integer_literal ->
     (* let () = x_binfo_hp pr_id "hello campl4" no_pos in *)
       Ipure.Div (Ipure.IConst(t1,get_pos_camlp4 _loc 2),
       Ipure.IConst(t2,get_pos_camlp4 _loc 4),get_pos_camlp4 _loc 3)
  | (* peek_print; *)
    t = LIST1 cexp SEP `COMMA ->
          begin
          match !Globals.perm with
            | Bperm -> (*Bounded permissions have 3 parameters*)
                if ((List.length t) ==3) then
                  let pc = List.hd t in
                  let pt = List.hd (List.tl t) in
                  let pa = List.hd (List.tl (List.tl t)) in
                  Ipure.Bptriple ((pc,pt,pa),get_pos_camlp4 _loc 1)
                else
                  let () = print_endline_quiet ("Warning: bounded permission has incorrect number of arguments") in
                  let e = Ipure.IConst (1,get_pos_camlp4 _loc 1) in
                  Ipure.Bptriple ((e,e,e),get_pos_camlp4 _loc 1)
            | _ -> List.hd t (*other permission systems have one parameter*)
          end
       ]];

opt_general_h_args: [[t = OPT general_h_args -> un_option t ([],[])]];

opt_data_h_args: [[t = OPT data_h_args -> un_option t ([],[])]];

(*general_h_args:
  [
  [ i = cexp ; t=opt_heap_arg_list -> (i::t,[])]
  |[ `IDENTIFIER id ; `EQ; i=cexp ; t=opt_heap_arg_list2 -> ([],(id,i)::t)]
  ];*)

general_h_args:
  [[ t= opt_heap_arg_list2 -> ([],t)
  | t= opt_heap_arg_list -> (t,[])]];

data_h_args:
  [[ t= opt_heap_data_arg_list2 -> ([],t)
  | t= opt_heap_data_arg_list -> (t,[])]];

opt_delayed_constr:[[t = OPT delayed_constr -> un_option t (P.mkTrue no_pos) ]];

delayed_constr:[[t = pure_constr; `CONSTR -> t ]];

opt_pure_constr:[[t=OPT and_pure_constr -> un_option t (P.mkTrue no_pos)]];

and_pure_constr: [[ peek_and_pure; `AND; t= pure_constr ->t]];

(* pure_constr_w_brace:                            *)
(*   [[ `OBRACE; c = pure_constr; `CBRACE -> c ]]; *)

(* pure_constr_t: [[ `OSQUARE; t= pure_constr; `CSQUARE ->t  *)
(*                   | t= pure_constr ->t *)
(* ]]; *)

(* (formula option , expr option )   *)

pure_constr:
  [[ peek_pure_out; t= cexp_w ->
       match t with
       | Pure_f f -> f
       | Pure_c (P.Var (v,_)) ->  P.BForm ((P.mkBVar v (get_pos_camlp4 _loc 1), None), None)
       | Pure_c (P.Ann_Exp (P.Var (v,_), Bool, _)) ->  P.BForm ((P.mkBVar v (get_pos_camlp4 _loc 1), None), None)
       | _ -> report_error (get_pos_camlp4 _loc 1) "expected pure_constr, found cexp"
  ]];

(* termu_id:                                                                       *)
(*   [[ `AT; `IDENTIFIER fn -> (fn, 0, P.mkTrue no_pos)                            *)
(*    | `AT; elem = termu_elem -> let (i, c) = elem in ("", i, c)                  *)
(*    | `AT; `IDENTIFIER fn; elem = termu_elem -> let (i, c) = elem in (fn, i, c)  *)
(*   ]];                                                                           *)

(* termu_elem:                                                                     *)
(*   [[ `OBRACE; `INT_LITER (i,_); `CBRACE -> (i, P.mkTrue no_pos)                 *)
(*    | `OBRACE; c = pure_constr; `CBRACE -> (0, c)                                *)
(*    | `OBRACE; `INT_LITER (i,_); `COMMA; c = pure_constr; `CBRACE -> (i, c)      *)
(*   ]];                                                                           *)

(* termu_args:                                                                     *)
(*   [[ `OPAREN; t=LIST0 cexp SEP `COMMA; `CPAREN -> t ]];                         *)

ann_term:
    [[  `TERM -> P.Term
      | `LOOP -> P.Loop
      | `MAYLOOP -> P.MayLoop
      (* | `TERMU; tid = OPT termu_id; targs = termu_args ->                 *)
      (*     let pos = get_pos_camlp4 _loc 1 in                              *)
      (*     let (fn, id, c) = un_option tid ("", 0, P.mkTrue no_pos) in     *)
      (*     P.TermU ({ P.tu_id = id; P.tu_sid = ""; P.tu_fname = fn;        *)
      (*                P.tu_args = targs; P.tu_cond = c; P.tu_pos = pos; }) *)
      (* | `TERMR; tid = OPT termu_id; targs = termu_args ->                 *)
      (*     let pos = get_pos_camlp4 _loc 1 in                              *)
      (*     let (fn, id, c) = un_option tid ("", 0, P.mkTrue no_pos) in     *)
      (*     P.TermR ({ P.tu_id = id; P.tu_sid = ""; P.tu_fname = fn;        *)
      (*                P.tu_args = targs; P.tu_cond = c; P.tu_pos = pos; }) *)
    ]];

cexp :
    [[t = cexp_data_p -> match t with
      | f, _ ->  f ]
    ];

cexp_data_p:
    [[t = cexp_w -> match t with
      | Pure_c f -> (f, None)
      | Pure_t (f, ann_opt ) -> (f, ann_opt)
      (* | _ -> report_error (get_pos_camlp4 _loc 1) "3 expected cexp, found pure_constr" *)
      | Pure_f f -> (BExpr f, None)
    ]
    ];

(*opt_slicing_label: [[ t = OPT slicing_label -> un_option t false ]];*)

slicing_label: [[ `DOLLAR -> true ]];

(*Unified specification for locks and waitlevel [ p1 # p2 ] *)
(*This is just syntactic sugar for p1 & p2 *)
exl_pure : [[  pc1=cexp_w; `HASH; pc2=cexp_w -> apply_pure_form2 (fun c1 c2-> P.mkAnd c1 c2 (get_pos_camlp4 _loc 2)) pc1 pc2 ]];

cexp_w:
  [ "pure_lbl"
    [ ofl= pure_label ; spc=SELF -> apply_pure_form1 (fun c-> label_formula c ofl) spc]
  | "slicing_label"
    [ sl=slicing_label; f=SELF -> set_slicing_utils_pure_double f sl ]
  | "AndList"
	[`ANDLIST;`OPAREN;t= LIST1 one_branch SEP `SEMICOLON ;`CPAREN ->
            Pure_f(P.mkAndList_opt t)(*to be used only for sleek testing*)]
  | "pure_or" RIGHTA
    [ pc1=SELF; `OR; pc2=SELF ->apply_pure_form2 (fun c1 c2-> P.mkOr c1 c2 None (get_pos_camlp4 _loc 2)) pc1 pc2]
  | "pure_and" RIGHTA
    [ pc1=SELF; peek_and; `AND; pc2=SELF -> apply_pure_form2 (fun c1 c2-> P.mkAnd c1 c2 (get_pos_camlp4 _loc 2)) pc1 pc2]
  | "pure_exclusive" RIGHTA
    [ `OSQUARE; t=exl_pure; `CSQUARE -> t]
  |"bconstrp" RIGHTA
    [ lc=SELF; `NEQ; cl=SELF ->
        let f = cexp_to_pure2 (fun c1 c2 -> P.mkNeq c1 c2 (get_pos_camlp4 _loc 2)) lc cl in
        set_slicing_utils_pure_double f (if !opt_ineq (* && (is_ineq_linking_constraint lc cl) *) then true else false)
    | lc=SELF; `EQ;   cl=SELF  -> begin
          (* let () = print_endline "xxxx" in *)
          (* let () = DD.info_hprint (add_str "lc" string_of_pure_double) lc no_pos in *)
          (* let () = DD.info_hprint (add_str "cl" string_of_pure_double) cl no_pos in *)
          let f = cexp_to_pure2 (fun c1 c2 -> P.mkEq c1 c2 (get_pos_camlp4 _loc 2)) lc cl in
          set_slicing_utils_pure_double f false
    end
    ]
  | "bconstr"
    [ lc=SELF; `LTE; cl=SELF ->
        let f = cexp_to_pure2 (fun c1 c2-> P.mkLte c1 c2 (get_pos_camlp4 _loc 2)) lc cl in
        set_slicing_utils_pure_double f false
    | lc=SELF; `LT; cl=SELF ->
        let f = cexp_to_pure2 (fun c1 c2-> P.mkLt c1 c2 (get_pos_camlp4 _loc 2)) lc cl in
        set_slicing_utils_pure_double f false
    | lc=SELF; `SUBANN; cl=SELF ->
        let f = cexp_to_pure2 (fun c1 c2-> P.mkSubAnn c1 c2 (get_pos_camlp4 _loc 2)) lc cl in
        set_slicing_utils_pure_double f false
    | lc=SELF; peek_try; `GT; cl=SELF ->
        let f = cexp_to_pure2 (fun c1 c2-> P.mkGt c1 c2 (get_pos_camlp4 _loc 2)) lc cl in
        set_slicing_utils_pure_double f false
    | lc=SELF; `GTE; cl=SELF ->
        let f = cexp_to_pure2 (fun c1 c2-> P.mkGte c1 c2 (get_pos_camlp4 _loc 2)) lc cl in
        set_slicing_utils_pure_double f false
    | lc=SELF; `IN_T;   cl=SELF ->
        let cid, pos = match lc with
          | Pure_c (P.Var (t, l)) -> (t, l)
          | Pure_c (P.Null l) -> ((null_name, Unprimed), l)
          | _ -> report_error (get_pos_camlp4 _loc 1) "expected cid" in
        let f = cexp_to_pure1 (fun c2 -> P.BagIn (cid,c2,pos)) cl in
        set_slicing_utils_pure_double f false
    | lc=SELF(*cid*); `NOTIN;  cl=SELF ->
        let cid, pos = match lc with
          | Pure_c (P.Var (t, l)) -> (t, l)
          | Pure_c (P.Null l) -> ((null_name,Unprimed), l)
          | _ -> report_error (get_pos_camlp4 _loc 1) "expected cid" in
        let f = cexp_to_pure1 (fun c2 -> P.BagNotIn(cid,c2,pos)) cl in
        set_slicing_utils_pure_double f false
    | lc=SELF; `SUBSET; cl=SELF ->
        let f = cexp_to_pure2 (fun c1 c2-> P.BagSub (c1, c2, (get_pos_camlp4 _loc 2))) lc cl in
        set_slicing_utils_pure_double f false
    | `BAGMAX; `OPAREN; c1=cid; `COMMA; c2=cid; `CPAREN ->
        let f = Pure_f (P.BForm ((P.BagMax (c1, c2, (get_pos_camlp4 _loc 2)), None), None)) in
        set_slicing_utils_pure_double f false
    | `BAGMIN; `OPAREN; c1=cid; `COMMA; c2=cid; `CPAREN ->
        let f = Pure_f (P.BForm ((P.BagMin (c1, c2, (get_pos_camlp4 _loc 2)), None), None))  in
        set_slicing_utils_pure_double f false
    | lc=SELF; `INLIST; cl=SELF ->
        let f = cexp_to_pure2 (fun c1 c2-> P.ListIn (c1, c2, (get_pos_camlp4 _loc 2))) lc cl in
        set_slicing_utils_pure_double f false
    | lc=SELF; `NOTINLIST; cl=SELF ->
        let f = cexp_to_pure2 (fun c1 c2-> P.ListNotIn (c1, c2, (get_pos_camlp4 _loc 2))) lc cl in
        set_slicing_utils_pure_double f false
    (* | ct=p_vp_ann ; `OSQUARE; ls= id_list; `CSQUARE ->                                       *)
    (*     let func t =                                                                         *)
    (*       if  String.contains t '\'' then                                                    *)
    (*         (* Remove the primed in the identifier *)                                        *)
    (*         (Str.global_replace (Str.regexp "[']") "" t,Primed)                              *)
    (*       else (t,Unprimed)                                                                  *)
    (*     in                                                                                   *)
    (*     let ls = List.map func ls in                                                         *)
    (*     let f = cexp_list_to_pure (fun ls -> P.VarPerm(ct,ls,(get_pos_camlp4 _loc 1))) ls in *)
    (*     set_slicing_utils_pure_double f false                                                *)
    | `ALLN; `OPAREN; lc=SELF; `COMMA; cl=SELF; `CPAREN ->
        let f = cexp_to_pure2 (fun c1 c2-> P.ListAllN (c1, c2, (get_pos_camlp4 _loc 2))) lc cl  in
        set_slicing_utils_pure_double f false
    | `PERM; `OPAREN; lc=SELF; `COMMA; cl=SELF; `CPAREN ->
        let f = cexp_to_pure2 (fun c1 c2-> P.ListPerm (c1, c2, (get_pos_camlp4 _loc 2))) lc cl in
        set_slicing_utils_pure_double f false
    | t_ann=ann_term; ls1=opt_measures_seq_sqr; ls2=opt_measures_seq ->
        let f = cexp_list_to_pure (fun ls1 -> P.LexVar(t_ann,ls1,ls2,(get_pos_camlp4 _loc 1))) ls1 in
        set_slicing_utils_pure_double f false
    ]
  | "pure_paren"
    [ peek_pure; `OPAREN; dc=SELF; `CPAREN -> dc ]
  | "type_casting"
    [ peek_typecast; `OPAREN; t = typ; `CPAREN; c = SELF ->
        apply_cexp_form1 (fun c -> P.mkTypeCast t c (get_pos_camlp4 _loc 1)) c
    ]
  (* constraint expressions *)
  | "gen"
    [ `OBRACE; c= opt_cexp_list; `CBRACE -> Pure_c (P.Bag (c, get_pos_camlp4 _loc 1))
    | `UNION; `OPAREN; c=opt_cexp_list; `CPAREN -> Pure_c (P.BagUnion (c, get_pos_camlp4 _loc 1))
    | `INTERSECT; `OPAREN; c=opt_cexp_list; `CPAREN -> Pure_c (P.BagIntersect (c, get_pos_camlp4 _loc 1))
    | `DIFF; `OPAREN; c1=SELF; `COMMA; c2=SELF; `CPAREN -> apply_cexp_form2 (fun c1 c2-> P.BagDiff (c1, c2, get_pos_camlp4 _loc 1) ) c1 c2
    | `OLIST; c1 = opt_cexp_list; `CLIST -> Pure_c (P.List (c1, get_pos_camlp4 _loc 1))
    |  c1=SELF; `COLONCOLONCOLON; c2=SELF -> apply_cexp_form2 (fun c1 c2-> P.ListCons (c1, c2, get_pos_camlp4 _loc 2)) c1 c2
    | `TAIL; `OPAREN; c1=SELF; `CPAREN -> apply_cexp_form1 (fun c1-> P.ListTail (c1, get_pos_camlp4 _loc 1)) c1
    | `APPEND; `OPAREN; c1= opt_cexp_list; `CPAREN -> Pure_c (P.ListAppend (c1, get_pos_camlp4 _loc 1))
    | `HEAD; `OPAREN; c=SELF; `CPAREN -> apply_cexp_form1 (fun c -> P.ListHead (c, get_pos_camlp4 _loc 1)) c
    | `LENGTH; `OPAREN; c=SELF; `CPAREN -> apply_cexp_form1 (fun c -> P.ListLength (c, get_pos_camlp4 _loc 1)) c
    | `REVERSE; `OPAREN; c1=SELF; `CPAREN -> apply_cexp_form1 (fun c1-> P.ListReverse (c1, get_pos_camlp4 _loc 1)) c1
    ]
  | "addit"
    [ c1=SELF ; `PLUS; c2=SELF -> apply_cexp_form2 (fun c1 c2-> P.mkAdd c1 c2 (get_pos_camlp4 _loc 2)) c1 c2
    | c1=SELF ; `MINUS; c2=SELF -> apply_cexp_form2 (fun c1 c2-> P.mkSubtract c1 c2 (get_pos_camlp4 _loc 2)) c1 c2
    ]
  | "mul"
    [ t1=SELF ; `STAR; t2=SELF ->
        apply_cexp_form2 (fun c1 c2-> P.mkMult c1 c2 (get_pos_camlp4 _loc 2)) t1 t2
    | t1=SELF ; `DIV ; t2=SELF -> apply_cexp_form2 (fun c1 c2-> P.mkDiv c1 c2 (get_pos_camlp4 _loc 2)) t1 t2
    ]
  | [`MINUS; c=SELF -> apply_cexp_form1 (fun c-> P.mkSubtract (P.IConst (0, get_pos_camlp4 _loc 1)) c (get_pos_camlp4 _loc 1)) c]
  | "ann_exp"
    [e=SELF ; `COLON; ty=typ -> apply_cexp_form1 (fun c-> P.mkAnnExp c ty (get_pos_camlp4 _loc 1)) e]
  | "una"
    [ `NULL -> Pure_c (P.Null (get_pos_camlp4 _loc 1))
    | `HASH ->
        (* let () = hash_count := !hash_count + 1 in  *)
        (* Pure_c (P.Var (("#" ^ (string_of_int !hash_count),Unprimed),(get_pos_camlp4 _loc 1))) *)
        mk_purec_absent (P.Var (("Anon"^fresh_trailer(),Unprimed),(get_pos_camlp4 _loc 1)))
    | `IDENTIFIER id1;`OPAREN; `IDENTIFIER id; `OPAREN; cl = id_list; `CPAREN ; `CPAREN ->
      if hp_names # mem id then
        if !Globals.hrel_as_view_flag then
          (* report_error (get_pos 1) "hrel_as_view : to be implemented (2)" *)
          Pure_f(P.BForm ((P.mkXPure id cl (get_pos_camlp4 _loc 1), None), None))
        else
          Pure_f(P.BForm ((P.mkXPure id cl (get_pos_camlp4 _loc 1), None), None))
      else
        begin
          if not(rel_names # mem id) then print_endline_quiet ("WARNING1 : parsing problem "^id^" is neither a ranking function nor a relation nor a heap predicate (not in rel_names)")
          else  print_endline_quiet ("WARNING2 : parsing problem "^id^" is neither a ranking function nor a relation nor a heap predicate (in rel_names)") ;
          Pure_f(P.BForm ((P.mkXPure id cl (get_pos_camlp4 _loc 1), None), None))
        end
    | `IDENTIFIER id; `OPAREN; cl = opt_cexp_list; `CPAREN ->
      (* AnHoa: relation constraint, for instance, given the relation
       * s(a,b,c) == c = a + b.
       * After this definition, we can have the relation constraint like
       * s(x,1,x+1), s(x,y,x+y), ...
       * in our formula.
       *)
        if func_names # mem id then Pure_c (P.Func (id, cl, get_pos_camlp4 _loc 1))
        else if templ_names # mem id then
          Pure_c (P.mkTemplate id cl (get_pos_camlp4 _loc 1))
        else if hp_names # mem id then (* Pure_f(P.BForm ((P.RelForm (id, cl, get_pos_camlp4 _loc 1), None), None)) *)
          report_error (get_pos 1) ("should be a pure relation, and not a heap pred here")
        else if ui_names # mem_eq (fun (id1, _) (id2, _) ->  id1 = id2 ) (id, true) then
          begin
            let _, is_pre = ui_names # find (fun (name,  _) -> name = id) in
            let pos = get_pos_camlp4 _loc 1 in
            let rel = P.RelForm (id, cl, pos) in
            Pure_f (P.BForm ((P.ImmRel (rel, P.mkUimmAnn is_pre  (BConst (true, pos)), pos), None), None))
          end
        else begin
          try
            let _, fname, is_pre = ut_names # find (fun (name, _, _) -> name = id) in
            let pos = get_pos_camlp4 _loc 1 in
            (* let cond = un_option c (P.mkTrue pos) in *)
            (* let nid = un_option nid 0 in *)
            let ann = P.mkUtAnn 0 id is_pre fname (P.mkTrue pos) cl pos in
            Pure_f (P.BForm ((P.LexVar (ann, [], [], pos), None), None))
          with Not_found ->
            if not (rel_names # mem id ) then
              if not !Globals.web_compile_flag then
                print_endline_quiet ("WARNING : parsing problem "^id^" is neither a ranking function nor a relation nor a heap predicate");
            Pure_f(P.BForm ((P.RelForm (id, cl, get_pos_camlp4 _loc 1), None), None))
        end
    | peek_cexp_list; ocl = opt_comma_list ->
        Pure_c(P.List(ocl, get_pos_camlp4 _loc 1))
    | t = cid ->
        let id,p = t in
        if String.contains id '.' then
          let strs = Gen.split_by "." id in
          let lock = List.hd strs in
          let mu = List.hd (List.tl strs) in
          if mu=Globals.level_name then
            Pure_c (P.Level ((lock,p), get_pos_camlp4 _loc 1))
          else
            Pure_c (P.Var (t, get_pos_camlp4 _loc 1))
        else
          Pure_c (P.Var (t, get_pos_camlp4 _loc 1))
    | t = cid; ann0 = LIST1 ann_heap -> Pure_t ((P.Var (t, get_pos_camlp4 _loc 1)), (get_heap_ann_opt ann0 ))
    | `IMM -> Pure_c (P.AConst(Imm, get_pos_camlp4 _loc 1))
    | `MUT -> Pure_c (P.AConst(Mutable, get_pos_camlp4 _loc 1))
    | `LEND -> Pure_c (P.AConst(Lend, get_pos_camlp4 _loc 1))
    | `ACCS -> Pure_c (P.AConst(Accs, get_pos_camlp4 _loc 1))
    | `AT;t=tree_const -> if !Globals.perm=Dperm then Pure_c (P.Tsconst(t,get_pos_camlp4 _loc 1)) else report_error (get_pos 1) ("distinct share reasoning not enabled")
    | `ATAT;t=id  ->
        let t = try Hashtbl.find !macros t with _ -> (print_string ("warning, undefined macro "^t); Ts.top) in
        Pure_c (P.Tsconst(t,get_pos_camlp4 _loc 1))
    | `INT_LITER (i,_) ; ann0 = LIST1 ann_heap ->
        Pure_t((P.IConst (i, get_pos_camlp4 _loc 1)) ,(get_heap_ann_opt ann0 ))
    | `INFINITY ->
        Pure_c (P.InfConst(constinfinity,get_pos_camlp4 _loc 1))
    | `NEGINFINITY ->
        Pure_c (P.NegInfConst(constinfinity,get_pos_camlp4 _loc 1))
    | `FLOAT_LIT (f,_) ; ann0 = LIST1 ann_heap ->
        Pure_t((P.FConst (f, get_pos_camlp4 _loc 1)), (get_heap_ann_opt ann0 ))
    | `INT_LITER (i,_) -> Pure_c (P.IConst (i, get_pos_camlp4 _loc 1))
    | `FLOAT_LIT (f,_) -> Pure_c (P.FConst (f, get_pos_camlp4 _loc 1))
    | `TUP2; `OPAREN; c1=SELF; `COMMA; c2=SELF; `CPAREN ->
          apply_cexp_form2 (fun c1 c2-> (P.Tup2 ((c1,c2), get_pos_camlp4 _loc 1))) c1 c2
    | `OPAREN; t=SELF; `CPAREN -> t
    | i=cid; `OSQUARE; c = LIST1 cexp SEP `COMMA; `CSQUARE ->
        Pure_c (P.ArrayAt (i, c, get_pos_camlp4 _loc 1))
    | `MAX; `OPAREN; c1=SELF; `COMMA; c2=SELF; `CPAREN ->
        apply_cexp_form2 (fun c1 c2-> P.mkMax c1 c2 (get_pos_camlp4 _loc 1)) c1 c2
    | `MIN; `OPAREN; c1=SELF; `COMMA; c2=SELF; `CPAREN ->
        apply_cexp_form2 (fun c1 c2-> P.mkMin c1 c2 (get_pos_camlp4 _loc 1)) c1 c2
    ]
  | "pure_base"
    [ `TRUE -> Pure_f (P.mkTrue (get_pos_camlp4 _loc 1))
    | `FALSE -> Pure_f (P.mkFalse (get_pos_camlp4 _loc 1))
    | `EXISTS; `OPAREN; ocl=opt_cid_list; `COLON; pc = SELF; `CPAREN ->
        apply_pure_form1 (fun c-> List.fold_left (fun f v ->P.mkExists [v] f None (get_pos_camlp4 _loc 1)) c ocl) pc
    | `FORALL; `OPAREN; ocl=opt_cid_list; `COLON; pc=SELF; `CPAREN ->
        apply_pure_form1 (fun c-> List.fold_left (fun f v-> P.mkForall [v] f None (get_pos_camlp4 _loc 1)) c ocl) pc
    | t=cid -> Pure_f (P.BForm ((P.mkBVar t (get_pos_camlp4 _loc 1), None), None ))
    | `NOT; `OPAREN; c=pure_constr; `CPAREN -> Pure_f (P.mkNot c None (get_pos_camlp4 _loc 1))
    | `NOT; t=cid -> Pure_f (P.mkNot (P.BForm ((P.mkBVar t (get_pos_camlp4 _loc 2), None), None )) None (get_pos_camlp4 _loc 1))
    ]
  ];


tree_const:[[
	 `OPAREN;`COMMA;`CPAREN->Ts.bot
	| `HASH -> Ts.top
	|`OPAREN;l=tree_const; `COMMA;`CPAREN-> Ts.mkNode l Ts.bot
	|`OPAREN;`COMMA; r=tree_const; `CPAREN-> Ts.mkNode Ts.bot r
	|`OPAREN;l=tree_const;`COMMA; r=tree_const; `CPAREN-> Ts.mkNode l r
]];

(* [[ *)
(*     il=OPT measures2 -> un_option il [] *)
(* ]]; *)

(* opt_measures:[[ `OPAREN; t=LIST0 cexp SEP `COMMA ;`CPAREN -> t]]; *)

(* opt_measures:[[t=LIST0 cexp SEP `COMMA -> t]];  *)

opt_comma_list:[[t = LIST0 opt_comma SEP `COMMA -> t
]];

opt_comma:[[t = cid ->  P.Var (t, get_pos_camlp4 _loc 1)
  | `INT_LITER (i,_) ->  P.IConst (i, get_pos_camlp4 _loc 1)
  | `FLOAT_LIT (f,_)  -> P.FConst (f, get_pos_camlp4 _loc 1)
   ]];

opt_measures_seq: [[ il = OPT measures_seq -> un_option il [] ]];

measures_seq: [[`OBRACE; t=LIST0 cexp SEP `COMMA; `CBRACE -> t]];

opt_measures_seq_sqr: [[ il = OPT measures_seq_sqr -> un_option il [] ]];

measures_seq_sqr: [[`OSQUARE; t=LIST0 cexp SEP `COMMA; `CSQUARE -> t]];

opt_cexp_list: [[t=LIST0 cexp SEP `COMMA -> t]];

(* cexp_list: [[t=LIST1 cexp SEP `COMMA -> t]]; *)

(********** Procedures and Coercion **********)

checknorm_cmd:
  [[ `CHECKNORM; b=meta_constr -> b ]];

checkeq_cmd:
  [[ `CHECKEQ; `OSQUARE; il=OPT id_list; `CSQUARE; t=meta_constr; `EQV; b=meta_constr ->
    let il = un_option il [] in (il,t,b)
  ]];

opt_list_meta_constr:[[t=LIST0 meta_constr SEP `SEMICOLON -> t]];

checkentail_cmd:
  [[ `CHECKENTAIL; t=meta_constr; `DERIVE; b=extended_meta_constr -> ([t], b, None)
   | `CHECKENTAIL_EXACT; t=meta_constr; `DERIVE; b=extended_meta_constr -> ([t], b, Some true)
   | `CHECKENTAIL_INEXACT; t=meta_constr; `DERIVE; b=extended_meta_constr -> ([t], b, Some false)
   | `CHECKENTAIL; `OBRACE; t=opt_list_meta_constr ; `CBRACE ; `DERIVE; b=extended_meta_constr -> (t, b, None)
  ]];

checksat_cmd:
  [[ `CHECKSAT; t=meta_constr -> t
  ]];

checknondet_cmd:
  [[
    `CHECK_NONDET; `OSQUARE; `IDENTIFIER v; `CSQUARE; f = meta_constr -> (v,f)
  ]];

templ_solve_cmd:
  [[ `TEMPL_SOLVE; il = OPT id_list_w_brace -> un_option il [] ]];

term_infer_cmd:
  [[ `TERM_INFER ]];

term_assume_cmd:
  [[ `TREL_ASSUME; t=meta_constr; `CONSTR; b=meta_constr -> (t, b) ]];

ls_rel_ass: [[`OSQUARE; t = LIST0 rel_ass SEP `SEMICOLON ;`CSQUARE-> t]];

rel_ass : [[ t=meta_constr; `CONSTR; b=meta_constr -> (t, b)]];

validate_entail_state:
  [[
     `OPAREN ; `OSQUARE; il1=OPT id_list;`CSQUARE; `COMMA; ef = meta_constr; `COMMA; ls_ass = ls_rel_ass ; `CPAREN->
         let il1 = un_option il1 [] in
         (il1, ef, ls_ass)
  ]];

validate_list_context:
  [[
     `OSQUARE; t = LIST0 validate_entail_state SEP `SEMICOLON ;`CSQUARE-> t
  ]];

validate_result:
  [[
      `IDENTIFIER ex -> VR_Unknown ex
    | `VALID -> VR_Valid
    | `FAIL -> VR_Fail 0
    | `FAIL_MUST -> VR_Fail 1
    | `FAIL_MAY -> VR_Fail (-1)
    | `SSAT -> VR_Sat
    | `SUNSAT -> VR_Unsat
  ]];
validate_cmd_pair:
    [[ `VALIDATE; vr = validate_result  ->
      (vr, None)
      | `VALIDATE; vr = validate_result; `COMMA; fl=OPT id ->
            (vr, fl)
   ]];

validate_cmd:
  [[ (* `VALIDATE; vr = validate_result; fl=OPT id; lc = OPT validate_list_context  -> *)
      pr = validate_cmd_pair; lc = OPT validate_list_context  ->
          let vr,fl = pr in
          (vr, fl, (un_option lc []))
   ]];

cond_path:
    [[ `OPAREN; il2 = OPT int_list; `CPAREN -> un_option il2 []
    ]];

relassume_cmd:
   [[ `RELASSUME; il2 = OPT cond_path; l=meta_constr; `CONSTR;r=meta_constr -> (un_option il2 [], l, None,  r)
    | `RELASSUME; il2 = OPT cond_path; l=meta_constr; `REL_GUARD; guard = meta_constr; `CONSTR;r=meta_constr ->
           (un_option il2 [], l, Some guard,  r)
   ]];

derv_pred:
[[
   `IDENTIFIER vn;`OPAREN;sl= id_list_opt; `CPAREN -> (vn,sl)
]];

reldefn_cmd:
   [[ `RELDEFN; il2 = OPT cond_path; l=meta_constr; `EQUIV ;r=meta_constr -> (un_option il2 [], l, r, [])
     | `RELDEFN; il2 = OPT cond_path; l=meta_constr; `EQUIV; `EXTENDS;orig_pred = derv_pred; `ATPOS; extn_pos=integer_literal; `WITH ; extn = prop_extn->
           (un_option il2 [], l, MetaForm (F.mkTrue n_flow (get_pos_camlp4 _loc 1)) , [(orig_pred, extn, [extn_pos])])
   ]];

decl_dang_cmd:
   [[ `SHAPE_DECL_DANG; `OSQUARE; il1=OPT id_list ;`CSQUARE -> un_option il1 []
   ]];

decl_unknown_cmd:
   [[ `SHAPE_DECL_UNKNOWN; il2 = OPT cond_path; `OSQUARE; il1= OPT id_list ;`CSQUARE   -> (un_option il2 [], un_option il1 [])
   ]];

shapeinfer_cmd:
   [[ `SHAPE_INFER; `OSQUARE;il1=OPT id_list;`CSQUARE; `OSQUARE; il2=OPT id_list;`CSQUARE ->
   let il1 = un_option il1 [] in
   let il2 = un_option il2 [] in
   (il1,il2)
   ]];

rel_infer_cmd:
   [[ `REL_INFER; `OSQUARE;il1=OPT id_list;`CSQUARE; `OSQUARE; il2=OPT id_list;`CSQUARE ->
   let il1 = un_option il1 [] in
   let il2 = un_option il2 [] in
   (il1, il2)
   ]];

shapedivide_cmd:
   [[ `SHAPE_DIVIDE; `OSQUARE;il1=OPT id_list;`CSQUARE; `OSQUARE; il2=OPT id_list;`CSQUARE ->
   let il1 = un_option il1 [] in
   let il2 = un_option il2 [] in
   (il1,il2)
   ]];
shapeconquer_cmd:
   [[ `SHAPE_CONQUER; `OSQUARE; il2=OPT id_list;`CSQUARE; `OSQUARE; il1=OPT list_int_list ;`CSQUARE ->
   let il1 = un_option il1 [] in
   let il2 = un_option il2 [] in
   (il2, il1)
   ]];

shapelfp_cmd:
   [[ `SHAPE_LFP; `OSQUARE;il1=OPT id_list;`CSQUARE ->
   let il1 = un_option il1 [] in
   il1
   ]];

shaperec_cmd:
   [[ `SHAPE_REC; `OSQUARE;il1=OPT id_list;`CSQUARE ->
   let il1 = un_option il1 [] in
   il1
   ]];


shapepost_obl_cmd:
   [[ `SHAPE_POST_OBL; `OSQUARE;il1=OPT id_list;`CSQUARE; `OSQUARE; il2=OPT id_list;`CSQUARE ->
   let il1 = un_option il1 [] in
   let il2 = un_option il2 [] in
   (il1,il2)
   ]];

shape_sconseq_cmd:
   [[ `SHAPE_STRENGTHEN_CONSEQ; `OSQUARE;il1=OPT id_list;`CSQUARE; `OSQUARE; il2=OPT id_list;`CSQUARE ->
   let il1 = un_option il1 [] in
   let il2 = un_option il2 [] in
   (il1,il2)
   ]];

shape_sante_cmd:
   [[ `SHAPE_WEAKEN_ANTE; `OSQUARE;il1=OPT id_list;`CSQUARE; `OSQUARE; il2=OPT id_list;`CSQUARE ->
   let il1 = un_option il1 [] in
   let il2 = un_option il2 [] in
   (il1,il2)
   ]];

pred_split_cmd:
   [[ `PRED_SPLIT; `OSQUARE;il1=OPT id_list;`CSQUARE->
   let il1 = un_option il1 [] in
   (il1)
   ]];

pred_norm_seg_cmd:
   [[ `PRED_NORM_SEG; `OSQUARE;il1=OPT id_list;`CSQUARE->
   let il1 = un_option il1 [] in
   (il1)
   ]];

pred_norm_disj_cmd:
   [[ `PRED_NORM_DISJ; `OSQUARE;il1=OPT id_list;`CSQUARE->
   let il1 = un_option il1 [] in
   (il1)
   ]];


simplify_cmd:
  [[ `SIMPLIFY; t=meta_constr -> t]];

hull_cmd:
  [[ `SLK_HULL; t=meta_constr -> t]];

pairwise_cmd:
  [[ `SLK_PAIRWISE; t=meta_constr -> t]];

shapeinfer_proper_cmd:
   [[ `SHAPE_INFER_PROP; `OSQUARE;il1=OPT id_list;`CSQUARE; `OSQUARE; il2=OPT id_list;`CSQUARE ->
   let il1 = un_option il1 [] in
   let il2 = un_option il2 [] in
   (il1,il2)
   ]];

shapesplit_base_cmd:
   [[ `SHAPE_SPLIT_BASE; `OSQUARE;il1=OPT id_list;`CSQUARE; `OSQUARE; il2=OPT id_list;`CSQUARE ->
   let il1 = un_option il1 [] in
   let il2 = un_option il2 [] in
   (il1,il2)
   ]];

shapeElim_cmd:
   [[ `PRED_ELIM_USELESS; `OSQUARE;il1=OPT id_list;`CSQUARE ->
   let il1 = un_option il1 [] in
   (il1)
   ]];

shapeReuseSubs_cmd:
   [[ `PRED_REUSE_SUBS; `OSQUARE;il1= shape_selective_id_list;`CSQUARE ->
   (* let il1 = un_option il1 [] in *)
   (il1)
   ]];

predUnfold_cmd:
   [[ `PRED_UNFOLD; arg = qualifier_selective_id_list_bracket ->
      (* `OSQUARE;il1= shape_selective_id_list;`CSQUARE -> *)
   (* let il1 = un_option il1 [] in *)
   ((arg))
   ]];

shapeReuse_cmd:
   [[ `PRED_REUSE; `OSQUARE;il1=shape_selective_id_list;`CSQUARE ; `OSQUARE;il2=shape_selective_id_list;`CSQUARE->
       (il1,il2)
   ]];


shapeExtract_cmd:
   [[ `SHAPE_EXTRACT; `OSQUARE;il1=OPT id_list;`CSQUARE ->
   let il1 = un_option il1 [] in
   (il1)
   ]];

shape_selective_id_list:
  [[ il = OPT id_list -> REGEX_LIST (un_option il [])
   | `STAR -> REGEX_STAR
  ]];

shape_selective_id_star_list:
  [[ il = OPT id_star_list -> REGEX_LIST (un_option il [])
   | `STAR -> REGEX_STAR
  ]];

selective_id_list_bracket:
  [[ `OSQUARE;il1= shape_selective_id_list;`CSQUARE -> il1
  ]];

qualifier_selective_id_list_bracket:
  [[ qual = OPT id; `OSQUARE;il1= shape_selective_id_list;`CSQUARE ->
     (qual,il1)
  ]];

selective_id_star_list_bracket:
  [[ `OSQUARE;il1= shape_selective_id_star_list;`CSQUARE -> il1
  ]];

data_mark_rec_cmd:
  [[ `DATA_MARK_REC; `OSQUARE; il=shape_selective_id_star_list; `CSQUARE
     ->  il
  ]];

shape_add_dangling_cmd:
  [[ `SHAPE_ADD_DANGLING; `OSQUARE; il=shape_selective_id_list; `CSQUARE
     ->  il
  ]];

shape_unfold_cmd:
  [[ `SHAPE_UNFOLD; `OSQUARE; il=shape_selective_id_list; `CSQUARE
     ->  il
  ]];

shape_param_dangling_cmd:
  [[ `SHAPE_PARAM_DANGLING; il=selective_id_list_bracket
                              (* `OSQUARE; il=shape_selective_id_list; `CSQUARE *)
     ->  il
  ]];

shape_simplify_cmd:
  [[ `SHAPE_SIMPLIFY; `OSQUARE; il=shape_selective_id_list; `CSQUARE
     ->  il
  ]];

shape_merge_cmd:
  [[ `SHAPE_MERGE; `OSQUARE; il=shape_selective_id_list; `CSQUARE
     ->  il
  ]];

shape_trans_to_view_cmd:
  [[ `SHAPE_TRANS_TO_VIEW; `OSQUARE; il=shape_selective_id_list; `CSQUARE
     ->  il
  ]];

shape_derive_pre_cmd:
  [[ `SHAPE_DERIVE_PRE; `OSQUARE; il=shape_selective_id_list; `CSQUARE
     ->  il
  ]];

shape_derive_post_cmd:
  [[ `SHAPE_DERIVE_POST; `OSQUARE; il=shape_selective_id_list; `CSQUARE
     ->  il
  ]];

shape_derive_view_cmd:
  [[ `SHAPE_DERIVE_VIEW; `OSQUARE; il=shape_selective_id_list; `CSQUARE
     ->  il
  ]];

shape_extn_view_cmd:
  [[ `SHAPE_EXTN_VIEW; `OSQUARE; il=shape_selective_id_list; `CSQUARE; `WITH; extn=id
     ->  (il, extn)
  ]];

shape_normalize_cmd:
  [[ `SHAPE_NORMALIZE; `OSQUARE; il=shape_selective_id_list; `CSQUARE
     ->  il
  ]];


pred_elim_head_cmd:
  [[ `PRED_ELIM_HEAD; `OSQUARE; il=shape_selective_id_list; `CSQUARE
     ->  il
  ]];

pred_elim_tail_cmd:
  [[ `PRED_ELIM_TAIL; `OSQUARE; il=shape_selective_id_list; `CSQUARE
     ->  il
  ]];

pred_unify_disj_cmd:
  [[ `PRED_UNIFY_DISJ; `OSQUARE; il=shape_selective_id_list; `CSQUARE
     ->  il
  ]];


infer_type:
   [[ `INFER_AT_TERM -> INF_TERM
   | `INFER_AT_TERM_WO_POST -> INF_TERM_WO_POST
   | `INFER_AT_FIELD_IMM -> INF_FIELD_IMM
   | `INFER_AT_PRE -> INF_PRE
   | `INFER_AT_POST -> INF_POST
   | `INFER_AT_CLASSIC -> INF_CLASSIC
   | `INFER_AT_PAR -> INF_PAR
   | `INFER_AT_VER_POST -> INF_VER_POST
   | `INFER_IMM_PRE -> INF_IMM_PRE
   | `INFER_IMM_POST -> INF_IMM_POST
   | `INFER_AT_IMM -> INF_IMM
   | `INFER_AT_PURE_FIELD -> INF_PURE_FIELD
   | `INFER_AT_ARR_AS_VAR -> INF_ARR_AS_VAR
   | `INFER_AT_SHAPE -> INF_SHAPE
   | `INFER_AT_SHAPE_PRE -> INF_SHAPE_PRE
   | `INFER_AT_SHAPE_POST -> INF_SHAPE_POST
   | `INFER_AT_SHAPE_PRE_POST -> INF_SHAPE_PRE_POST
   | `INFER_AT_ERROR -> INF_ERROR
   | `INFER_AT_SIZE -> INF_SIZE
   | `INFER_ANA_NI -> INF_ANA_NI
   | `INFER_AT_EFA -> INF_EFA
   | `INFER_AT_DFA -> INF_DFA
   | `INFER_AT_DE_EXC -> INF_DE_EXC
   | `INFER_AT_ERRMUST_ONLY -> INF_ERR_MUST_ONLY
   | `INFER_AT_ERRMUST -> INF_ERR_MUST
   | `INFER_AT_PREMUST -> INF_PRE_MUST
   | `INFER_AT_ERRMAY -> INF_ERR_MAY
   | `INFER_AT_FLOW -> INF_FLOW
   ]];

infer_id:
  [[ t = infer_type -> [FstAns t]
   | (id, _) = cid; t = OPT infer_extn_for_id ->
      match t with
      | None -> [SndAns id]
      | Some props ->
        let inf_extn = mk_infer_extn id props in
        let inf_extn_obj = INF_EXTN [inf_extn] in
        [SndAns id; FstAns inf_extn_obj]
  ]];

infer_extn_prop:
  [[ `IDENTIFIER prop -> prop ]];

infer_extn_for_id:
  [[ `HASH; prop = infer_extn_prop -> [prop]
   | `HASH; `OBRACE; lst = LIST1 infer_extn_prop SEP `COMMA; `CBRACE -> lst
  ]];

infer_type_list:
    [[ itl = LIST0 infer_id SEP `COMMA -> List.concat itl ]];

(* id_list_w_sqr:                                                     *)
(*     [[ `OSQUARE; il = OPT id_list; `CSQUARE -> un_option il [] ]]; *)

(* id_list_w_itype: *)
(*   [[ `OSQUARE; t = infer_type; `COMMA; il = id_list; `CSQUARE -> (Some t, il)  *)
(*    | `OSQUARE; il = OPT id_list; `CSQUARE -> (None, un_option il []) *)
(*    | `OSQUARE; t = infer_type; `CSQUARE -> (Some t, []) *)
(*   ]]; *)


infer_cmd:
  [[ `INFER; il_w_itype = cid_list_w_itype; t=meta_constr; `DERIVE; b=extended_meta_constr ->
      (* let inf_o = new Globals.inf_obj_sub (\* Globals.clone_sub_infer_const_obj () *\) (\* Globals.infer_const_obj # clone *\) in *)
      (* let (i_consts,ivl) = List.fold_left  *)
      (*   (fun (lst_l,lst_r) e -> match e with FstAns l -> (l::lst_l,lst_r)  *)
      (*     | SndAns r -> (lst_l,r::lst_r)) ([],[]) il_w_itype in *)
      (* let (i_consts,ivl) = (List.rev i_consts,List.rev ivl) in *)
      let (_,i_consts,ivl) = conv_ivars_icmd il_w_itype in
    (* let k, il = un_option il_w_itype (None, [])  *)
      (i_consts,ivl,t,b,None)
    | `INFER_EXACT;  il_w_itype = cid_list_w_itype (* il=OPT id_list *); t=meta_constr; `DERIVE; b=extended_meta_constr ->
      let (_,i_consts,il) = conv_ivars_icmd il_w_itype in
      (* let il = un_option il [] in  *)
      (i_consts,il,t,b,Some true)
    | `INFER_INEXACT; il_w_itype = cid_list_w_itype (* il=OPT id_list *); t=meta_constr; `DERIVE; b=extended_meta_constr ->
      let (_,i_consts,il) = conv_ivars_icmd il_w_itype in
      let i_consts = List.filter (fun i -> i!=INF_CLASSIC) i_consts in
      (* let il = un_option il [] in  *)
      (i_consts,il,t,b,Some false)
  ]];

captureresidue_cmd:
  [[ `CAPTURERESIDUE; `DOLLAR; `IDENTIFIER id -> id ]];

compose_cmd:
  [[ `COMPOSE; `OSQUARE; il=id_list; `CSQUARE; `OPAREN; mc1=meta_constr; `SEMICOLON; mc2=meta_constr; `CPAREN ->(il, mc1, mc2)
   | `COMPOSE; `OPAREN; mc1=meta_constr; `SEMICOLON; mc2=meta_constr; `CPAREN -> ([], mc1, mc2)]];


print_cmd:
  [[ `PRINT; `IDENTIFIER id;
        ilopt=OPT selective_id_star_list_bracket  ->
        (* let ilopt = map_opt (List.map () lst) ilopt in *)
        PCmd (id,ilopt)
   | `PRINT; `DATA;
        ilopt=OPT selective_id_star_list_bracket  ->
        PCmd ("data",ilopt)
   | `PRINT; `DOLLAR; `IDENTIFIER id  -> PVar id
   | `PRINT_LEMMAS  -> PCmd ("lemmas",None)
   (* | `PRINT_VIEW  -> PCmd "view" *)
   (* | `PRINT_VIEW_LONG  -> PCmd "view_long" *)
  ]];

cmp_cmd:
  [[ `CMP; `IDENTIFIER id ; `OSQUARE; il=OPT id_list; `CSQUARE ; `COLON; fl = LIST1 meta_constr SEP `COMMA  ->
  let il = un_option il [] in (il,id,fl)]];

time_cmd:
  [[ `DTIME; `ON; `IDENTIFIER id   -> Time(true, id, get_pos_camlp4 _loc 1)
   | `DTIME; `OFF; `IDENTIFIER id  -> Time(false, id, get_pos_camlp4 _loc 1)]];

let_decl:
  [[ `LET; `DOLLAR; `IDENTIFIER id; `EQ; mc=meta_constr ->	LetDef (id, mc)]];

extended_meta_constr:
  [[ `DOLLAR;`IDENTIFIER id  -> MetaVar id
    | f=  formulas         -> MetaEForm (F.subst_stub_flow_struc n_flow (fst f))
    | f = extended_l2   ->  MetaEForm (F.subst_stub_flow_struc n_flow f)
    | f=  disjunctive_constr     -> MetaEForm (F.formula_to_struc_formula (F.subst_stub_flow n_flow f))
    | f=  spec         -> MetaEForm f
    | c = compose_cmd           -> MetaCompose c]];

meta_constr:
  [[ `DOLLAR; `IDENTIFIER id -> MetaVar id
   | d=disjunctive_constr    -> MetaForm (F.subst_stub_flow n_flow d)
   | c=compose_cmd           -> MetaCompose c]];

coercion_decl:
  [[ on=opt_name; dc1=disjunctive_constr; cd=coercion_direction; dc2=disjunctive_constr ->
      { coercion_type = cd;
        coercion_exact = false;
        coercion_infer_vars = [];
        coercion_infer_obj = new Globals.inf_obj_sub;
        coercion_name = (* on; *)
        (let v=on in (if (String.compare v "")==0 then (fresh_any_name "lem") else v));
        (* coercion_head = dc1; *)
        (* coercion_body = dc2; *)
        (* must remove stub flow from formula - replace with top_flow *)
        (* coercion_head = (F.subst_stub_flow top_flow dc1); *)
        (* coercion_body = (F.subst_stub_flow top_flow dc2); *)
        coercion_head = (F.subst_stub_flow n_flow dc1);
        coercion_body = (F.subst_stub_flow n_flow dc2);
        coercion_proof = Return ({ exp_return_val = None;
                     exp_return_path_id = None ;
                     exp_return_pos = get_pos_camlp4 _loc 1 });
        coercion_type_orig = None;
        coercion_kind = LEM_SAFE;
        coercion_origin = LEM_USER;
      };
  ]];

coercion_decl_list:
    [[
        coerc = LIST1 coercion_decl SEP `SEMICOLON -> {
            coercion_list_elems = coerc;
            coercion_list_kind  = LEM;
        }
    ]];

infer_coercion_decl:
    [[
         ivl_w_itype = cid_list_w_itype (* il=OPT id_list *);  t = coercion_decl ->
        let (inf_o,i_consts,ivl) = conv_ivars_icmd ivl_w_itype in
        (* let () = DD.binfo_hprint (add_str "PPPP inf_obj" (fun e -> e # string_of)) inf_o no_pos in *)
        {t with coercion_infer_vars = ivl; coercion_infer_obj = inf_o;}
    ]];

(* infer_coercion_decl_list: *)
(*     [[ *)
(*         coerc = LIST1 infer_coercion_decl SEP `SEMICOLON -> { *)
(*             coercion_list_elems = coerc; *)
(*             coercion_list_kind  = LEM; *)
(*         } *)
(*     ]]; *)

coerc_decl_aux:
    [[
      `LEMMA TLEM_INFER; t = infer_coercion_decl ->
          let t = {t with coercion_kind = LEM_INFER;} in
          { coercion_list_elems = [t];
            coercion_list_kind  = LEM_INFER }
      | `LEMMA TLEM_INFER_PRED; t = infer_coercion_decl ->
            let t = {t with coercion_kind = LEM_INFER_PRED;} in
          { coercion_list_elems = [t];
          coercion_list_kind  = LEM_INFER_PRED }
      (* | `LEMMA TLEM_INFER; `OSQUARE; t = infer_coercion_decl_list; `CSQUARE ->  *)
      (*     { t with coercion_list_kind = LEM_INFER } *)
      | `LEMMA kind;t = coercion_decl ->
            let k = convert_lem_kind kind in
            let t = {t with coercion_kind = k;} in
          { coercion_list_elems = [t];
            coercion_list_kind  = k }
      | `LEMMA kind; `OSQUARE; t = coercion_decl_list; `CSQUARE ->
            let k = convert_lem_kind kind in
            let t = {t with coercion_list_elems= List.map (fun l -> {l with coercion_kind = k;}) t.coercion_list_elems} in
          { t with coercion_list_kind = k }
    ]];

coercion_direction:
  [[ `LEFTARROW  -> Left
   | `EQUIV      -> Equiv
   | `RIGHTARROW -> Right]];

opt_name: [[t= OPT name-> un_option t ""]];

name:[[ `STRING(_,id)  -> id]];

typ:
  [[ peek_array_type; t=array_type     -> (* An Hoa *) (* let () = print_endline "Parsed array type" in *) t
   | peek_pointer_type; t = pointer_type     -> (*let () = print_endline "Parsed pointer type" in *) t
   | t=non_array_type -> (* An Hoa *) (* let () = print_endline "Parsed a non-array type" in *) t]];

non_array_type:
  [[ `VOID               -> void_type
   | `INT                -> int_type
   | `ANN_KEY           -> ann_type
   | `FLOAT              -> float_type
   | `INFINT_TYPE        -> infint_type
   | `BOOL               -> bool_type
   | `BAG               -> bag_type
   | `ABSTRACT          -> void_type
   | `BAG; `OPAREN; t = non_array_type ; `CPAREN -> BagT t
   | `IDENTIFIER id      -> Named id
   | `OPAREN; t1=non_array_type; `COMMA; t2=non_array_type; `CPAREN -> Tup2 (t1,t2)
   | t=rel_header_view   -> let tl,_ = List.split t.Iast.rel_typed_vars in RelT tl ]];

pointer_type:
  [[ t=non_array_type; r = star_list ->
  let rec create_pointer n =
    if (n<=1) then (Pointer t) else (Pointer (create_pointer (n-1)))
  in
  let pointer_t = create_pointer r in
  (* let () = print_endline ("Pointer: " ^ (string_of_int r) ^ (string_of_typ pointer_t)) in *)
  pointer_t
   ]];

star_list: [[`STAR; s = OPT SELF -> 1 + (un_option s 0)]];

array_type:
  [[ (* t=array_type; r=rank_specifier -> Array (t, None)
  | *) t=non_array_type; r=rank_specifier -> Array (t, r)]];

rank_specifier:
  [[`OSQUARE; c = OPT comma_list; `CSQUARE -> un_option c 1]];

comma_list: [[`COMMA; s = OPT SELF -> 1 + (un_option s 1)]];

id_list_opt:[[t= LIST0 id SEP `COMMA ->t]];

int_list:[[t= LIST1 integer_literal SEP `SEMICOLON ->t]];

list_int_list:[[t= LIST1 int_list SEP `COMMA ->t]];

id_star_list:[[t=LIST1 id_star SEP `COMMA -> t]];

id_list:[[t=LIST1 id SEP `COMMA -> t]];

id_list_w_brace: [[`OBRACE; t=id_list; `CBRACE -> t]];

id:[[`IDENTIFIER id-> id]];

triv_star:[[`STAR -> 1]];

id_star:[[`IDENTIFIER id; v = OPT triv_star ->
          let v = match v with None -> false | Some _ -> true in
          (id,v)]];

(********** Higher Order Preds *******)

hopred_decl:
    [[`HPRED; h=hpred_header; `EXTENDS; b=ext_form
                                      -> mkHoPred  (fst (fst h)) "extends" [(fst b)] (snd (fst h)) (fst (snd h)) (snd (snd h)) (snd b) (P.mkTrue no_pos)
	   | `HPRED; h=hpred_header; `REFINES;  b=ext_form
                                         -> mkHoPred  (fst (fst h)) "refines" [(fst b)] (snd (fst h)) (fst (snd h)) (snd (snd h)) (snd b) (P.mkTrue no_pos)
       | `HPRED; h=hpred_header; `JOIN; s=split_combine
                                      -> mkHoPred (fst (fst h)) "split_combine" [] [] [] [] [] (P.mkTrue no_pos)
	   | `HPRED; h=hpred_header;  `EQEQ; s=shape; oi= opt_inv; `SEMICOLON
           ->
               let (oi, _) = oi in
               mkHoPred (fst (fst h)) "pure_higherorder_pred" [] (snd (fst h)) (fst (snd h)) (snd (snd h)) [s] oi]];

shape: [[ t= formulas -> fst t]];

split_combine:
  [[ h=hpred_header -> ()
   | h=hpred_header; `SPLIT; t=SELF -> ()
   | h=hpred_header; `COMBINE; t=SELF -> ()]];

ext_form: [[ h=hpred_header;	`WITH; `OBRACE; t=ho_fct_def_list; `CBRACE ->("",[])]];

ho_fct_header: [[`IDENTIFIER id; `OPAREN; f= fct_arg_list; `CPAREN -> f]];

ho_fct_def:	[[ h=ho_fct_header; `EQ; s=shape -> ()]];

ho_fct_def_list: [[t = LIST1 ho_fct_def  -> ()]];

hpred_header: [[`IDENTIFIER id; t=opt_type_var_list; `LT; t2=opt_typed_arg_list; `GT; t3=opt_fct_list -> ((id,t),(t2,t3))]];

typed_arg:
   [[ t=typ -> ()
    | `SET;  `OSQUARE; t=typ;  `CSQUARE -> ()
    | `SET;  `OSQUARE; t=typ;  `CSQUARE; `COLON; t3=SELF -> ()
    | t=typ; `OSQUARE; t2=typ; `CSQUARE -> ()
    | t=typ; `OSQUARE; t2=typ; `CSQUARE; `COLON; t3=SELF -> ()
    | t=typ; `COLON;   t2=SELF -> ()]];

opt_typed_arg_list: [[t=LIST0 typed_arg SEP `COMMA -> [] ]];

type_var:
   [[ t= typ -> ()
    | `SET; `OSQUARE; t=typ; `CSQUARE -> ()
    | t=typ; `OSQUARE; t2=typ; `CSQUARE -> ()]];

type_var_list: [[`OSQUARE; t= LIST1 type_var SEP `COMMA; `CSQUARE -> ()]];

opt_type_var_list: [[ t= OPT type_var_list -> [] ]];

fct_arg_list: [[ t=LIST1 cid SEP `COMMA -> t]];

fct_list: [[ `OSQUARE; t=fct_arg_list; `CSQUARE -> [] ]];

opt_fct_list:[[ t = OPT fct_list -> []]];

(*** Function declaration ***)
func_decl:
  [[ fh=func_header -> fh
  ]];

func_typed_id_list_opt: [[ t = LIST1 typed_id_list SEP `COMMA -> t ]];

func_header:
  [[ `FUNC; `IDENTIFIER id; `OPAREN; tl= func_typed_id_list_opt; `CPAREN ->
      let () = func_names # push id in
      { func_name = id;
        func_typed_vars = tl;
      }
  ]];

(************ An Hoa :: Relations ************)
rel_decl:[[ rh=rel_header; `EQEQ; rb=rel_body (* opt_inv *) ->

	{ rh with rel_formula = rb (* (fst $3) *); (* rel_invariant = $4; *) }
	(* [4/10/2011] allow for declaration of relation without body; such relations are constant true and need to be axiomatized using axioms declarations. *)
	| rh=rel_header -> rh
  | rh = rel_header; `EQ -> report_error (get_pos_camlp4 _loc 2) ("use == to define a relation")
]];

typed_id_list:[[ t = typ; `IDENTIFIER id ->  (t,id) ]];

id_part_ann: [[
    `IDENTIFIER id-> (id,-1)
  | `IDENTIFIER id; `COLON; t=integer_literal-> (id, t)
]]
;

(* typed_id_inst_list_old:[[ t = typ; `IDENTIFIER id ->  (t,id, Globals.I)                    *)
(*   |  t = typ; `NI; `IDENTIFIER id->  (t,id, Globals.NI)                                    *)
(*   | t = typ; `RO; `IDENTIFIER id -> let () = pred_root_id := id in (t,id, Globals.I)        *)
(*   |  t = typ; `NI; `RO; `IDENTIFIER id->  let () = pred_root_id := id in (t,id, Globals.NI) *)
(*   |  t = typ; `RO; `NI; `IDENTIFIER id->  let () = pred_root_id := id in (t,id, Globals.NI) *)
(*  ]];                                                                                       *)

typed_id_inst_list:[[ t = typ; id_ann = id_part_ann ->  (t,id_ann, Globals.I)
  |  t = typ; `NI; id_ann = id_part_ann ->  (t,id_ann, Globals.NI)
  | t = typ; `RO; (id,n) = id_part_ann -> let () = pred_root_id := id in (t,(id,n), Globals.I)
  |  t = typ; `NI; `RO; (id,n) = id_part_ann->  let () = pred_root_id := id in (t,(id,n), Globals.NI)
  |  t = typ; `RO; `NI; (id,n) = id_part_ann->  let () = pred_root_id := id in (t,(id,n), Globals.NI)
 ]];


typed_id_list_opt: [[ t = LIST0 typed_id_list SEP `COMMA -> t ]];

typed_id_inst_list_opt: [[ t = LIST0 typed_id_inst_list SEP `COMMA -> t ]];

typed_default_id_list:[[ t = typ  ->  (t,default_rel_id) ]];

typed_default_id_list_opt: [[ t = LIST0 typed_default_id_list SEP `COMMA -> t ]];

rel_header:[[
`REL; `IDENTIFIER id; `OPAREN; tl= typed_id_list_opt; (* opt_ann_cid_list *) `CPAREN  ->
    (* let cids, anns = List.split $4 in
    let cids, br_labels = List.split cids in
	  if List.exists
		(fun x -> match snd x with | Primed -> true | Unprimed -> false) cids
          then
		report_error (get_pos_camlp4 _loc 1)
		  ("variables in view header are not allowed to be primed")
	  else
		let modes = get_modes anns in *)
    let () = rel_names # push id in
		  { rel_name = id;
			rel_typed_vars = tl;
			rel_formula = P.mkTrue (get_pos_camlp4 _loc 1); (* F.mkETrue top_flow (get_pos_camlp4 _loc 1); *)
			}
]];

rel_header_view:[[
  `REL; `OPAREN; tl= typed_default_id_list_opt; (* opt_ann_cid_list *) `CPAREN  ->
  let rd = { rel_name = "";
			rel_typed_vars = tl;
			rel_formula = P.mkTrue (get_pos_camlp4 _loc 1); (* F.mkETrue top_flow (get_pos_camlp4 _loc 1); *)
		 } in
  (* let () = set_tmp_rel_decl rd in *)
  rd
]];

rel_body:[[ (* formulas {
    ((F.subst_stub_flow_struc top_flow (fst $1)),(snd $1)) } *)
	pc=pure_constr -> pc (* Only allow pure constraint in relation definition. *)
]];

(* Template Definition *)
templ_decl: [[ `TEMPLATE; t = typ; `IDENTIFIER id; `OPAREN; tl = typed_id_list_opt; `CPAREN; b = OPT templ_body ->
  let () = templ_names # push id in
  let tdef = {
    templ_name = id;
    templ_ret_typ = t;
    templ_typed_params = tl;
    templ_body = b;
    templ_pos = get_pos_camlp4 _loc 1; } in
  tdef ]];

templ_body: [[ `EQEQ; pc = cexp -> pc ]];

(* Unknown Temporal Definition *)
ut_fname: [[ `AT; `IDENTIFIER fn -> fn ]];

ut_decl:
  [[ `UTPRE; fn = OPT ut_fname; `IDENTIFIER id; `OPAREN; tl = typed_id_list_opt; `CPAREN ->
      let fname = un_option fn "" in
      let () = ut_names # push (id, fname, true) in
      let utdef = {
        ut_name = id;
        ut_fname = fname;
        ut_typed_params = tl;
        ut_is_pre = true;
        ut_pos = get_pos_camlp4 _loc 1; }
      in utdef
  | `UTPOST; fn = OPT ut_fname; `IDENTIFIER id; `OPAREN; tl = typed_id_list_opt; `CPAREN ->
      let fname = un_option fn "" in
      let () = ut_names # push (id, fname, false) in
      let utdef = {
        ut_name = id;
        ut_fname = fname;
        ut_typed_params = tl;
        ut_is_pre = false;
        ut_pos = get_pos_camlp4 _loc 1; }
      in utdef
  ]];

(* Unknown Imm Definition *)
ui_decl:
  [[ `UIPRE; `IDENTIFIER id; `OPAREN; tl= typed_id_list_opt; (* opt_ann_cid_list *) `CPAREN  ->
      let () = ui_names # push (id, true) in
      let () = rel_names # push id in
      let rel = { rel_name = id; rel_typed_vars = tl;
      rel_formula = P.mkTrue (get_pos_camlp4 _loc 1); (* F.mkETrue top_flow (get_pos_camlp4 _loc 1); *) } in
      let uimmdef = {
        ui_rel = rel;
        ui_is_pre = true;
        ui_pos = get_pos_camlp4 _loc 1; }
      in uimmdef
  | `UIPOST; `IDENTIFIER id; `OPAREN; tl= typed_id_list_opt; (* opt_ann_cid_list *) `CPAREN  ->
      let () = ui_names # push (id, false) in
      let () = rel_names # push id in
      let rel = { rel_name = id; rel_typed_vars = tl;
      rel_formula = P.mkTrue (get_pos_camlp4 _loc 1); (* F.mkETrue top_flow (get_pos_camlp4 _loc 1); *) } in
      let uimmdef = {
        ui_rel = rel;
        ui_is_pre = false;
        ui_pos = get_pos_camlp4 _loc 1; }
      in uimmdef
  ]];

axiom_decl:[[
	`AXIOM; lhs=pure_constr; `ESCAPE; rhs=pure_constr ->
		{ axiom_id = fresh_int ();
			axiom_hypothesis = lhs;
		  axiom_conclusion = rhs; }
]];

hp_decl:[[
`HP; `IDENTIFIER id; `OPAREN; tl0= typed_id_inst_list_opt; (* opt_ann_cid_list *) `CPAREN  ->
    let () = hp_names # push id in
    let tl, parts = pred_get_args_partition tl0 in
    let root_pos =  pred_get_root_pos !pred_root_id tl in
    let pos1 = get_pos_camlp4 _loc 1 in
    let () = pred_root_id := "" in
     if !Globals.hrel_as_view_flag then
       mk_hp_decl_w_view id tl (Some root_pos) parts pos1
         (* report_error (get_pos 1) "hrel_as_view : to be implemented (3)" *)
     else mk_hp_decl id tl (Some root_pos) parts pos1
    (*  { *)
    (*     hp_name = id; *)
    (*     hp_typed_inst_vars = tl; *)
    (*     hp_root_pos = root_pos; *)
    (*     hp_part_vars = parts; *)
    (*     hp_is_pre = true; *)
    (*     hp_formula =  F.mkBase F.HEmp (P.mkTrue (get_pos_camlp4 _loc 1)) VP.empty_vperm_sets top_flow [] (get_pos_camlp4 _loc 1); *)
    (* } *)
  | `HPPOST; `IDENTIFIER id; `OPAREN; tl0= typed_id_inst_list_opt; (* opt_ann_cid_list *) `CPAREN  ->
    let () = hp_names # push id in
    let tl, parts = pred_get_args_partition tl0 in
    let root_pos =  pred_get_root_pos !pred_root_id tl in
    let pos1 = get_pos_camlp4 _loc 1 in
    let () = pred_root_id := "" in
     if !Globals.hrel_as_view_flag then
       mk_hp_decl_w_view ~is_pre:false id tl (Some root_pos) parts pos1
       (* report_error (get_pos 1) "hrel_as_view : to be implemented (4)" *)
     else mk_hp_decl ~is_pre:false id tl (Some root_pos) parts pos1
    (* { *)
    (*     hp_name = id; *)
    (*     hp_typed_inst_vars = tl; *)
    (*     hp_part_vars = parts; *)
    (*     hp_root_pos = root_pos; *)
    (*     hp_is_pre = false; *)
    (*     hp_formula =  F.mkBase F.HEmp (P.mkTrue (get_pos_camlp4 _loc 1)) VP.empty_vperm_sets top_flow [] (get_pos_camlp4 _loc 1); *)
    (* } *)
]];

 (*end of sleek part*)
 (*start of hip part*)
hprogn:
  [[ t = opt_decl_list ->
		  let include_defs = ref ([]: string list) in
      let data_defs = ref ([] : data_decl list) in
      let global_var_defs = ref ([] : exp_var_decl list) in
      let logical_var_defs = ref ([] : exp_var_decl list) in
      let enum_defs = ref ([] : enum_decl list) in
      let view_defs = ref ([] : view_decl list) in
      let barrier_defs = ref ([] : barrier_decl list) in
      (* ref ([] : rel_decl list) in (\* An Hoa *\) *)
      let func_defs = new Gen.stack in (* list of ranking functions *)
      let rel_defs = new Gen.stack in(* list of relations *)
      let templ_defs = new Gen.stack in (* List of template definitions *)
      let ut_defs = new Gen.stack in (* List of unknown temporal definitions *)
      let ui_defs = new Gen.stack in (* List of unknown temporal definitions *)
      let hp_defs = new Gen.stack in(* list of heap predicate relations *)
      let axiom_defs = ref ([] : axiom_decl list) in (* [4/10/2011] An Hoa *)
      let proc_defs = ref ([] : proc_decl list) in
      let coercion_defs = ref ([] : coercion_decl_list list) in
      let hopred_defs = ref ([] : hopred_decl list) in
      let choose d = match d with
        | Type tdef -> begin
            match tdef with
            | Data ddef -> data_defs := ddef :: !data_defs
            | Enum edef -> enum_defs := edef :: !enum_defs
            | View vdef -> view_defs := vdef :: !view_defs
            | Hopred hpdef -> hopred_defs := hpdef :: !hopred_defs
            | Barrier bdef -> barrier_defs := bdef :: !barrier_defs
          end
        | Include incl -> include_defs := incl :: !include_defs
        | Func fdef -> func_defs # push fdef
        | Rel rdef -> rel_defs # push rdef
        | Template tdef -> templ_defs # push tdef
        | Ut utdef -> ut_defs # push utdef
        | Ui uidef -> ui_defs # push uidef
        | Hp hpdef -> hp_defs # push hpdef
        | Axm adef -> axiom_defs := adef :: !axiom_defs (* An Hoa *)
        | Global_var glvdef -> global_var_defs := glvdef :: !global_var_defs
        | Logical_var lvdef -> logical_var_defs := lvdef :: !logical_var_defs
        | Proc pdef ->
              let () = List.iter (fun n_hp_decl -> hp_defs # push n_hp_decl) pdef.Iast.proc_hp_decls in
              proc_defs := pdef :: !proc_defs
        | Coercion_list cdef -> coercion_defs := cdef :: !coercion_defs in
    let todo_unk = List.map choose t in
    let obj_def = { data_name = "Object";
                    data_pos = no_pos;
                    data_fields = [];
                    data_parent_name = "";
                    data_invs = []; (* F.mkTrue no_pos; *)
                    data_pure_inv = None;
                    data_is_template = false;
                    data_methods = [] } in
    let string_def = { data_name = "String";
                       data_fields = [];
                       data_pos = no_pos;
                       data_parent_name = "Object";
                       data_pure_inv = None;
                       data_invs = []; (* F.mkTrue no_pos; *)
                       data_is_template = false;
                       data_methods = [] } in
    (* let g_rel_lst = g_rel_defs # get_stk in *)
    let rel_lst = ((rel_defs # get_stk)(* @(g_rel_lst) *)) in
    let templ_lst = templ_defs # get_stk in
    let ut_lst = ut_defs # get_stk in
    let ui_lst = ui_defs # get_stk in
    let hp_lst = hp_defs # get_stk in
    let extra_rels = List.map (fun u -> u.Iast.ui_rel) ui_lst in
    (* WN : how come not executed for loop2.slk? *)
    (* PURE_RELATION_OF_HEAP_PRED *)
    (* to create __pure_of_relation from hp_lst to add to rel_lst *)
    (* rel_lst = rel_lst @ List.map (pure_relation_of_hp_pred) hp_lst *)
    { prog_include_decls = !include_defs;
    prog_data_decls = obj_def :: string_def :: !data_defs;
    prog_global_var_decls = !global_var_defs;
    prog_logical_var_decls = !logical_var_defs;
    prog_enum_decls = !enum_defs;
    (* prog_rel_decls = [];  TODO : new field for array parsing *)
    prog_view_decls = !view_defs;
    prog_func_decls = func_defs # get_stk ;
    prog_ui_decls = ui_lst;
    prog_rel_decls = rel_lst@extra_rels; (* An Hoa *)
    prog_rel_ids = List.map (fun x ->
        let tl,_ = List.split x.rel_typed_vars in
        (RelT tl,x.rel_name)) (rel_lst@extra_rels); (* WN *)
    prog_templ_decls = templ_lst;
    prog_ut_decls = ut_lst;
    prog_hp_decls = hp_lst ;
    prog_hp_ids = List.map (fun x -> (HpT,x.hp_name)) hp_lst; (* l2 *)
    prog_axiom_decls = !axiom_defs; (* [4/10/2011] An Hoa *)
    prog_proc_decls = !proc_defs;
    prog_coercion_decls = List.rev !coercion_defs;
    prog_hopred_decls = !hopred_defs;
    prog_barrier_decls = !barrier_defs;
    prog_test_comps = [];
    } ]];

opt_decl_list: [[t=LIST0 mdecl -> List.concat t]];

mdecl:
	[[ t=macro -> []
	  |t=decl -> [t]]];

decl:
  [[ `HIP_INCLUDE; `PRIME; ic = dir_path ; `PRIME -> Include ic
	|  t=type_decl                  -> Type t
  |  r=func_decl; `DOT -> Func r
  |  r=rel_decl; `DOT -> Rel r (* An Hoa *)
  |  r=templ_decl; `DOT -> Template r
  |  r=ut_decl; `DOT -> Ut r
  |  r=ui_decl; `DOT -> Ui r
  |  r=hp_decl; `DOT -> Hp r
  |  a=axiom_decl; `DOT -> Axm a (* [4/10/2011] An Hoa *)
  |  g=global_var_decl            -> Global_var g
  |  l=logical_var_decl -> Logical_var l
  |  p=proc_decl                  -> Proc p
  | `RLEMMA ; c= coercion_decl; `SEMICOLON    -> let c =  {c with coercion_kind = RLEM} in
                                                 Coercion_list { coercion_list_elems = [c];
                                                                 coercion_list_kind = RLEM}
  | `RLEMMA ; c= coercion_decl; `DOT    -> let c =  {c with coercion_kind = RLEM} in
                                                 Coercion_list { coercion_list_elems = [c];
                                                                 coercion_list_kind = RLEM}
  | `LEMMA kind; c= coercion_decl; `SEMICOLON    ->
        let k = convert_lem_kind kind in
        let c = {c with coercion_kind = k;} in
        Coercion_list
        { coercion_list_elems = [c];
          coercion_list_kind  = k}
  | `LEMMA kind; c= coercion_decl; `DOT    ->
        let k = convert_lem_kind kind in
        let c = {c with coercion_kind = k;} in
        Coercion_list
        { coercion_list_elems = [c];
          coercion_list_kind  = k}
  | `LEMMA kind(* lex *); c = coercion_decl_list; `SEMICOLON    -> Coercion_list {c with (* coercion_exact = false *) coercion_list_kind = convert_lem_kind kind}
  | `LEMMA kind(* lex *); c = coercion_decl_list; `DOT    -> Coercion_list {c with (* coercion_exact = false *) coercion_list_kind = convert_lem_kind kind}
  ]];

dir_path: [[t = LIST1 file_name SEP `DIV ->
    let str  = List.fold_left (fun res str -> res^str^"/") "" t in
    let len = String.length str in
    Str.string_before str (len-1)
           ]];

file_name: [[ `DOTDOT -> ".."
              | `IDENTIFIER id -> id
            ]];

opt_pred:
  [[ OPT [ x = `PRED] -> 1]];
type_decl:
  [[ t= data_decl  -> Data t
   | t= template_data_decl  -> Data t
   | c=class_decl -> Data c
   | e=enum_decl  -> Enum e
   | peek_view_decl; o = opt_pred; v=view_decl; `SEMICOLON -> View v
   | peek_view_decl; o = opt_pred; v=view_decl; `DOT -> View v
   | `PRED_PRIM; v = prim_view_decl; `SEMICOLON    -> View v
   | `PRED_EXT;v= view_decl_ext  ; `SEMICOLON   -> View v
   | b=barrier_decl ; `SEMICOLON   -> Barrier b
   | h=hopred_decl-> Hopred h ]];


(***************** Global_variable **************)
global_var_decl:
  [[ `GLOBAL; lvt=local_variable_type; vd=variable_declarators; `SEMICOLON -> mkGlobalVarDecl lvt vd (get_pos_camlp4 _loc 1)]];

logical_var_decl:
  [[ `LOGICAL; lvt=local_variable_type; vd=variable_declarators; `SEMICOLON ->
        mkLogicalVarDecl lvt vd (get_pos_camlp4 _loc 1)
  ]];

(**************** Class ******************)
class_decl:
  [[ `CLASS; `IDENTIFIER id; par=OPT extends; ml=class_body ->
      let t1, t2, t3 = split_members ml in
		(* An Hoa [22/08/2011] : blindly add the members as non-inline because we do not support inline fields in classes. TODO revise. *)
		let t1 = List.map (fun ((t,id), p) -> ((t,id), p, false, (gen_field_ann t) (* F_NO_ANN *))) t1 in
      let cdef = { data_name = id;
                   data_pos = get_pos_camlp4 _loc 2;
                   data_parent_name = un_option par "Object";
                   data_fields = t1;
                   data_invs = t2;
                   data_pure_inv = None;
                   data_is_template = false;
                   data_methods = t3 } in
      let todo_unk = List.map (fun d -> set_proc_data_decl d cdef) t3 in
      cdef]];

extends: [[`EXTENDS; `IDENTIFIER id -> id]];

class_body:
      [[`OBRACE; fl=member_list; `CBRACE   ->  fl
      | `OBRACE; `CBRACE                             -> []] ];

one_member:
 [[ m= member; `SEMICOLON -> m
  | m = member -> m]];

member_list: [[m = one_member; fl=member_list -> m::fl
             | m=one_member -> [m]]];

member:
 [[ t=typ; `IDENTIFIER id -> Field ((t, id), get_pos_camlp4 _loc 2)
  | `INV;  dc=disjunctive_constr -> Inv (F.subst_stub_flow top_flow dc)
  | pd=proc_decl -> Method pd
  | cd=constructor_decl -> Method cd]];

(*************** Enums ******************)

enum_decl:
  [[ h=enum_header; b=enum_body -> { enum_name = h; enum_fields = b }]];

enum_header: [[`ENUM; `IDENTIFIER n -> n]];

enum_body: [[`OBRACE; l=enum_list; `CBRACE -> l]];

enum_list:[[t=LIST1 enumerator SEP `COMMA -> t]];

enumerator:
  [[ `IDENTIFIER n -> (n, None)
   | `IDENTIFIER n; `EQ;  `INT_LITER(i,_) -> (n, Some i) ]];


(****Specs *******)
opt_sq_clist : [[t = OPT sq_clist -> un_option t []]];

opt_spec_list_file: [[t = LIST0 spec_list_file -> t]];

spec_list_file: [[`IDENTIFIER id; t = opt_spec_list -> (id, t)]];

opt_spec_list: [[t = LIST0 spec_list_grp -> label_struc_groups_auto t]];

spec_list_only : [[t= LIST1 spec_list_grp -> label_struc_list t ]];

spec_list : [[t= LIST1 spec_list_grp -> label_struc_groups t ]];

spec_list_outer : [[t= LIST1 spec_list_grp -> label_struc_groups_auto t ]];

spec_list_grp:
  [[
      (* c=spec -> [(empty_spec_label_def,c)] *)
     t= LIST1 spec -> List.map (fun c -> (Lbl.empty_spec_label_def,c)) t
    | `IDENTIFIER id; `COLON; `OSQUARE;
          t = spec_list_only
          (* LIST0 spec SEP `ORWORD *)
      ; `CSQUARE -> List.map (fun ((n,l),c)-> ((n,id::l),c)) t
    | `OSQUARE;
          t = spec_list_only
      ; `CSQUARE -> List.map (fun ((n,l),c)-> ((n,l),c)) t
  ]];

disj_or_extn_constr:
  [[
      dc= disjunctive_constr ->
	  let f = F.subst_stub_flow n_flow dc in
	  let sf = F.mkEBase [] [] [] f None no_pos in
          (f,sf)
    | dc= extended_constr ->
          let dc = F.subst_stub_flow_struc n_flow dc in
	  let f = F.flatten_post_struc dc (get_pos_camlp4 _loc 1) in
	  (f,dc)
  ]];


spec:
  [[
    `INFER; transpec = opt_transpec; postxf = opt_infer_xpost; postf= opt_infer_post; ivl_w_itype = cid_list_w_itype; s = SELF ->
    (* WN : need to use a list of @sym *)
     (* let inf_o = Globals.infer_const_obj # clone in *)
     (* let inf_o = new Globals.inf_obj_sub in *)
     (* let (i_consts,ivl) = List.fold_left *)
     (*   (fun (lst_l,lst_r) e -> match e with FstAns l -> (l::lst_l,lst_r) *)
     (*     | SndAns r -> (lst_l,r::lst_r)) ([],[]) ivl_w_itype in *)
     (* let (i_consts,ivl) = (List.rev i_consts,List.rev ivl) in *)
     let (inf_o,i_consts,ivl) = conv_ivars_icmd ivl_w_itype in
     let () = List.iter (fun itype -> inf_o # set itype) i_consts in
     let ivl_t = List.map (fun e -> (e,Unprimed)) ivl in
     F.EInfer {
       (* F.formula_inf_tnt = inf_o # get INF_TERM (\* (match itype with | Some INF_TERM -> true | _ -> false) *\); *)
       F.formula_inf_obj = inf_o;
       F.formula_inf_post = postf;
       F.formula_inf_xpost = postxf;
       F.formula_inf_transpec = transpec;
       F.formula_inf_vars = ivl_t;
       F.formula_inf_continuation = s;
       F.formula_inf_pos = get_pos_camlp4 _loc 1;
     }
    | `REQUIRES; cl= opt_sq_clist; dc= disjunctive_constr; s=SELF ->
	  F.EBase {
	      F.formula_struc_explicit_inst =cl;
	      F.formula_struc_implicit_inst = [];
	      F.formula_struc_exists = [];
	      F.formula_struc_base = (F.subst_stub_flow n_flow dc);
              F.formula_struc_is_requires = true;
	      F.formula_struc_continuation = Some s;
	      F.formula_struc_pos = (get_pos_camlp4 _loc 1)}
    | `REQUIRES; cl=opt_sq_clist; dc=disjunctive_constr; `OBRACE; sl=spec_list; `CBRACE ->
	  F.EBase {
	      F.formula_struc_explicit_inst =cl;
	      F.formula_struc_implicit_inst = [];
	      F.formula_struc_exists = [];
	      F.formula_struc_base =  (F.subst_stub_flow n_flow dc);
              F.formula_struc_is_requires = true;
	      F.formula_struc_continuation = Some sl (*if ((List.length sl)==0) then report_error (get_pos_camlp4 _loc 1) "spec must contain ensures"else sl*);
	      F.formula_struc_pos = (get_pos_camlp4 _loc 1)}
              (* F.formula_ext_complete = false;*)
    | `ENSURES; ol= opt_label; (f,sf)= disj_or_extn_constr; `SEMICOLON ->
	  F.mkEAssume f sf (fresh_formula_label ol) None

    (* | `ENSURES; ol= opt_label; dc= disjunctive_constr; `SEMICOLON -> *)
    (*       let f = F.subst_stub_flow n_flow dc in *)
    (*       let sf = F.mkEBase [] [] [] f None no_pos in *)
    (*       F.mkEAssume f sf (fresh_formula_label ol) None *)
    (* | `ENSURES; ol= opt_label; dc= extended_constr; `SEMICOLON -> *)
    (*       let f = F.flatten_post_struc dc (get_pos_camlp4 _loc 1) in *)
    (*       F.mkEAssume (F.subst_stub_flow n_flow f) (F.subst_stub_flow_struc n_flow dc) (fresh_formula_label ol) None *)

    | `ENSURES_EXACT; ol= opt_label; (f,sf)= disj_or_extn_constr; `SEMICOLON ->
	  F.mkEAssume f sf (fresh_formula_label ol) (Some true)

    (* | `ENSURES_EXACT; ol= opt_label; dc= disjunctive_constr; `SEMICOLON -> *)
    (*       let f = F.subst_stub_flow n_flow dc in *)
    (*       let sf = F.mkEBase [] [] [] f None no_pos in *)
    (*       F.mkEAssume f sf (fresh_formula_label ol) (Some true) *)

    | `ENSURES_INEXACT; ol= opt_label; (f,sf)= disj_or_extn_constr; `SEMICOLON ->
	  F.mkEAssume f sf (fresh_formula_label ol) (Some false)

    (* | `ENSURES_INEXACT; ol= opt_label; dc= disjunctive_constr; `SEMICOLON -> *)
    (*       let f = F.subst_stub_flow n_flow dc in *)
    (*       let sf = F.mkEBase [] [] [] f None no_pos in *)
    (*       F.mkEAssume f sf (fresh_formula_label ol) (Some false) *)

    | `CASE; `OBRACE; bl= branch_list; `CBRACE ->F.ECase {F.formula_case_branches = bl; F.formula_case_pos = get_pos_camlp4 _loc 1; }
  ]];

cid_list_w_itype:
  [[ `OSQUARE; t = infer_type_list; `CSQUARE -> t
   (* | `OSQUARE; il = OPT cid_list; `CSQUARE -> (None, un_option il []) *)
   (* | `OSQUARE; t = infer_type_list; `CSQUARE -> (Some t, []) *)
  ]];

(* opt_vlist: [[t = OPT opt_cid_list -> un_option t []]]; *)

branch_list: [[t=LIST1 spec_branch -> List.rev t]];

spec_branch: [[ pc=pure_constr; `LEFTARROW; sl= spec_list -> (pc,sl)]];


 (***********Proc decls ***********)

opt_throws: [[ t = OPT throws -> un_option t []]];
throws: [[ `THROWS; l=cid_list -> List.map fst l]];
flag_arg : [[
	`IDENTIFIER t -> Flag_str t
	| `INT_LITER (i,_)-> Flag_int i
	| `FLOAT_LIT (f,_)-> Flag_float f]];

flag: [[`MINUS; `IDENTIFIER t ; args = OPT flag_arg-> ("-",t, args)
		| `OP_DEC; `IDENTIFIER t ; args = OPT flag_arg-> ("--",t, args)]];

flag_list:[[`ATATSQ; t=LIST1 flag;`CSQUARE -> t]];

opt_flag_list:[[t=OPT flag_list -> un_option t []]];

resource_param: [[ `WITH; `PERCENT; `IDENTIFIER hid ->
  { param_mod = NoMod;
    param_type = FORM;
    param_loc = get_pos_camlp4 _loc 3;
    param_name = hid } ]];

opt_resource_param: [[ hid = OPT resource_param -> hid ]];

proc_decl:
  [[ h=proc_header; flgs=opt_flag_list;b=proc_body ->
      let n_h = genESpec_wNI h (Some b) h.proc_args h.proc_return h.proc_loc in
      { n_h with proc_flags=flgs; proc_body = Some b ; proc_loc = {(h.proc_loc) with end_pos = Parsing.symbol_end_pos()} }
   | h=proc_header; _=opt_flag_list-> h]];

proc_header:
  [[ t=typ; `IDENTIFIER id; `OPAREN; fpl= opt_formal_parameter_list; `CPAREN; hparam = opt_resource_param; ot=opt_throws; osl= opt_spec_list ->
    (*let static_specs, dynamic_specs = split_specs osl in*)
      let cur_file = proc_files # top in
     mkProc cur_file id [] "" None false ot fpl t hparam osl (F.mkEFalseF ()) (get_pos_camlp4 _loc 1) None

  | `VOID; `IDENTIFIER id; `OPAREN; fpl=opt_formal_parameter_list; `CPAREN; ot=opt_throws; osl=opt_spec_list ->
    (*let static_specs, dynamic_specs = split_specs $6 in*)
    let cur_file = proc_files # top in
    mkProc cur_file id [] "" None false ot fpl void_type None osl (F.mkEFalseF ()) (get_pos_camlp4 _loc 1) None]];

constructor_decl:
  [[ h=constructor_header; b=proc_body -> {h with proc_body = Some b}
   | h=constructor_header -> h]];

constructor_header:
  [[ `IDENTIFIER id; `OPAREN; fpl=opt_formal_parameter_list; `CPAREN; ot=opt_throws; osl=opt_spec_list ; flgs=opt_flag_list->
    (*let static_specs, dynamic_specs = split_specs $5 in*)
		(*if Util.empty dynamic_specs then*)
    let cur_file = proc_files # top in
      mkProc cur_file id flgs "" None true ot fpl (Named id) None osl (F.mkEFalseF ()) (get_pos_camlp4 _loc 1) None
    (*	else
		  report_error (get_pos_camlp4 _loc 1) ("constructors have only static speficiations");*) ]];



opt_formal_parameter_list: [[t= LIST0 fixed_parameter SEP `COMMA -> t]];


fixed_parameter:
  [[ t=typ; pm=OPT pass_t; `IDENTIFIER id ->
      { param_mod = un_option pm NoMod;
        param_type = t;
        param_loc = get_pos_camlp4 _loc 3;
        param_name = id }
    | pm=OPT pass_t2; t=typ;  `IDENTIFIER id ->
      { param_mod = un_option pm NoMod;
        param_type = t;
        param_loc = get_pos_camlp4 _loc 3;
        param_name = id }
]];

pass_t2: [[`PASS_REF2 -> RefMod ]];

pass_t: [[`PASS_REF -> RefMod
       | `PASS_COPY -> CopyMod]];

proc_body: [[t=block-> t]];

(*********** Statements ***************)

block:
  [[ `OBRACE; t=statement_list; `CBRACE ->
	  match t with
	  | Empty _ -> Block { exp_block_body = Empty (get_pos_camlp4 _loc 1);
                         exp_block_jump_label = NoJumpLabel;
                         exp_block_local_vars = [];
                         exp_block_pos = get_pos_camlp4 _loc 1 }
	  | _ -> Block { exp_block_body = t;
                   exp_block_jump_label = NoJumpLabel;
                   exp_block_local_vars = [];
                   exp_block_pos = get_pos_camlp4 _loc 1 }
				   ]];

statement_list:
[[ s = statement -> s
  | sl=SELF; s=statement  -> Seq { exp_seq_exp1 = sl;
									 exp_seq_exp2 = s;
									 exp_seq_pos = get_pos_camlp4 _loc 1 }
]];

(* opt_statement_list: [[ t= LIST0 statement SEP `SEMICOLON ->  *)
(*     match t with  *)
(*      | [] ->  Empty no_pos *)
(*      | h::t -> List.fold_left (fun a c-> Seq {exp_seq_exp1 = a; exp_seq_exp2=c; exp_seq_pos =get_pos_camlp4 _loc 1}) h t ]]; *)

statement:
  [[ t=declaration_statement; `SEMICOLON -> t
   | t=labeled_valid_declaration_statement -> t]];

declaration_statement:
  [[peek_try_declarest; t=local_variable_declaration -> t
   | peek_try_declarest; t=local_constant_declaration -> t]];

local_variable_type: [[ t= typ ->  t]];

local_variable_declaration: [[  t1=local_variable_type; t2=variable_declarators -> mkVarDecl t1 t2 (get_pos_camlp4 _loc 1)]];

local_constant_declaration: [[ `CONST; lvt=local_variable_type; cd=constant_declarators ->  mkConstDecl lvt cd (get_pos_camlp4 _loc 1)]];

variable_declarators: [[ t= LIST1 variable_declarator SEP `COMMA -> t]];

variable_declarator:
  [[ `IDENTIFIER id; `EQ; t=variable_initializer  -> (* print_string ("Identifier : "^id^"\n"); *) (id, Some t, get_pos_camlp4 _loc 1)
   | `IDENTIFIER id -> (* print_string ("Identifier : "^id^"\n"); *)(id, None, get_pos_camlp4 _loc 1) ]];

variable_initializer: [[t= expression ->t]];

constant_declarators: [[t=LIST1 constant_declarator SEP `COMMA -> t]];

constant_declarator: [[ `IDENTIFIER id; `EQ; ce=constant_expression -> (id, ce, get_pos_camlp4 _loc 1)]];

labeled_valid_declaration_statement:
	[[ `IDENTIFIER id ; `COLON; t=valid_declaration_statement ->
		(match t with
      | Block	b -> Block { b with exp_block_jump_label = JumpLabel id; }
      | While b -> While { b with exp_while_jump_label = JumpLabel id; }
      | _ -> report_error (get_pos_camlp4 _loc 1) ("only blocks try and while statements can have labels"))
	 (* | t= OPT valid_declaration_statement -> un_option t (Empty (get_pos_camlp4 _loc 1) ) *)
      | t = valid_declaration_statement -> t ]];

valid_declaration_statement:
  [[ t=block -> t
   | t=expression_statement;`SEMICOLON ->t
   | t=selection_statement -> t
   | t=iteration_statement -> t
   | t=try_statement; `SEMICOLON -> t
   | t=java_statement -> t
   | t=jump_statement;`SEMICOLON  -> t
   | t= assert_statement;`SEMICOLON -> t
   | t=dprint_statement;`SEMICOLON  -> t
   (* | t=skip_statement;`SEMICOLON  -> t *)
   | t=debug_statement -> t
   | t=time_statement -> t
   | t=bind_statement -> t
   | t=barr_statement -> t
   | t=par_statement -> t
   | t=unfold_statement -> t]
   | [t= empty_statement -> t]
];

empty_statement: [[`SEMICOLON -> Empty (get_pos_camlp4 _loc 1) ]];

unfold_statement: [[ `UNFOLD; t=cid  ->	Unfold { exp_unfold_var = t; exp_unfold_pos = get_pos_camlp4 _loc 1 }]];

barr_statement : [[`BARRIER; `IDENTIFIER t -> I.Barrier {exp_barrier_recv = t ; exp_barrier_pos = get_pos_camlp4 _loc 1}]];

assert_statement:
  [[ `ASSERT; ol= opt_label; f=formulas ->
       mkAssert (Some ((F.subst_stub_flow_struc n_flow (fst f)),(snd f))) None (fresh_formula_label ol) (Some false) (get_pos_camlp4 _loc 1)
   | `ASSERT_EXACT; ol= opt_label; f=formulas ->
       mkAssert (Some ((F.subst_stub_flow_struc n_flow (fst f)),(snd f))) None (fresh_formula_label ol) (Some true) (get_pos_camlp4 _loc 1)
   | `ASSERT_INEXACT; ol= opt_label; f=formulas ->
       mkAssert (Some ((F.subst_stub_flow_struc n_flow (fst f)),(snd f))) None (fresh_formula_label ol) (Some false) (get_pos_camlp4 _loc 1)
   | `INFER_ASSUME; `OSQUARE;il1=OPT id_list;`CSQUARE ->
       mkAssert ~inf_vars:(un_option il1 []) None None (fresh_formula_label "") None (get_pos_camlp4 _loc 1)
   | `ASSUME; ol=opt_label; dc=disjunctive_constr ->
       mkAssert None (Some (F.subst_stub_flow n_flow dc)) (fresh_formula_label ol) None (get_pos_camlp4 _loc 1)
   | `ASSERT; ol=opt_label; f=formulas; `ASSUME; dc=disjunctive_constr ->
       mkAssert (Some ((F.subst_stub_flow_struc n_flow (fst f)),(snd f))) (Some (F.subst_stub_flow n_flow dc)) (fresh_formula_label ol) (Some false) (get_pos_camlp4 _loc 1)
   | `ASSERT_EXACT; ol=opt_label; f=formulas; `ASSUME; dc=disjunctive_constr ->
       mkAssert (Some ((F.subst_stub_flow_struc n_flow (fst f)),(snd f))) (Some (F.subst_stub_flow n_flow dc)) (fresh_formula_label ol) (Some true) (get_pos_camlp4 _loc 1)
   | `ASSERT_INEXACT; ol=opt_label; f=formulas; `ASSUME; dc=disjunctive_constr ->
       mkAssert (Some ((F.subst_stub_flow_struc n_flow (fst f)),(snd f))) (Some (F.subst_stub_flow n_flow dc)) (fresh_formula_label ol) (Some false) (get_pos_camlp4 _loc 1)]];

debug_statement:
  [[ `DDEBUG; `ON -> Debug { exp_debug_flag = true;	exp_debug_pos = get_pos_camlp4 _loc 2 }
   | `DDEBUG; `OFF -> Debug { exp_debug_flag = false; exp_debug_pos = get_pos_camlp4 _loc 2 }]];

time_statement:
  [[ `DTIME; `ON; `IDENTIFIER id -> I.Time (true,id,get_pos_camlp4 _loc 1)
   | `DTIME; `OFF; `IDENTIFIER id -> I.Time (false,id,get_pos_camlp4 _loc 1)]];

dprint_statement:
  [[ `DPRINT  -> Dprint ({exp_dprint_string = ""; exp_dprint_pos = (get_pos_camlp4 _loc 1)})
   | `DPRINT; `STRING(_,id)  -> Dprint ({exp_dprint_string = id;  exp_dprint_pos = (get_pos_camlp4 _loc 1)})]];

(* skip_statement: *)
(*   [[ `SKIP  -> Empty (get_pos_camlp4 _loc 1); ]]; *)

bind_statement:
  [[ `BIND; `IDENTIFIER id; `TO; `OPAREN; il = id_list_opt; `CPAREN; `IN_T; b= block ->
      Bind { exp_bind_bound_var = id;
             exp_bind_fields = il;
             exp_bind_body = b;
             exp_bind_path_id = None ;
             exp_bind_pos = get_pos_camlp4 _loc 1 }]];

bind_expression:
  [[ `BIND; `IDENTIFIER id; `TO; `OPAREN; il = id_list_opt; `CPAREN; `IN_T; b= expression ->
      Bind { exp_bind_bound_var = id;
             exp_bind_fields = il;
             exp_bind_body = b;
             exp_bind_path_id = None ;
             exp_bind_pos = get_pos_camlp4 _loc 1 }]];

java_statement: [[ `JAVA s -> Java { exp_java_code = s;exp_java_pos = get_pos_camlp4 _loc 1 }]];

(*TO CHECK*)
expression_statement: [[(* t=statement_expression -> t *)
        peek_invocation; t= invocation_expression -> t
      | t= object_creation_expression -> t
      | t= post_increment_expression -> t
      | t= post_decrement_expression -> t
      | t= pre_increment_expression -> t
      | t= pre_decrement_expression -> t
      | peek_exp_st; t= assignment_expression -> t
]];

(*statement_expression:
  [[

  ]];*)

selection_statement: [[t=if_statement -> t]];

embedded_statement: [[t=valid_declaration_statement -> t]];

if_statement:
  [[ `IF; `OPAREN; bc = boolean_expression; `CPAREN; es=embedded_statement ->
	  Cond { exp_cond_condition = bc;
           exp_cond_then_arm = es;
           exp_cond_else_arm = Empty (get_pos_camlp4 _loc 1);
           exp_cond_path_id = None;
           exp_cond_pos = get_pos_camlp4 _loc 1 }
  |`IF;
  `OPAREN; bc=boolean_expression;
  `CPAREN; tb=embedded_statement;
  `ELSE_TT; eb=embedded_statement ->
		Cond { exp_cond_condition = bc;
			   exp_cond_then_arm = tb;
			   exp_cond_else_arm = eb;
			   exp_cond_path_id = None;
			   exp_cond_pos = get_pos_camlp4 _loc 1 }]];

par_statement:
  [[  `PAR; vps = vperm_var_list_opt; lh = OPT heap_constr;
      `OBRACE; pl = par_case_list; `CBRACE ->
      let pos = get_pos_camlp4 _loc 1 in
      let pl = Iast.norm_par_case_list pl pos in
      let lend_pos = get_pos_camlp4 _loc 3 in
      let lend_heap = un_option lh F.HEmp in
      let lend_form =
        F.mkBase lend_heap (P.mkAnd (P.mkTrue lend_pos) (P.mkTrue lend_pos) lend_pos)
          VP.empty_vperm_sets n_flow [] lend_pos
      in
      Par {
        exp_par_vperm = vps;
        exp_par_lend_heap = lend_form;
        exp_par_cases = pl;
        exp_par_pos = pos; }
  ]];

vpid:
  [[
      `IDENTIFIER t -> (VP_Full, sv_of_id t)
    | `IDENTIFIER t; `LEND -> (VP_Lend, sv_of_id t)
  ]];

opt_vpid_list:
  [[ t = LIST0 vpid SEP `COMMA -> VP.vperm_sets_of_anns t ]];

vperm_var_list:
  [[ `OBRACE; vps = opt_vpid_list; `CBRACE -> vps ]];

vperm_var_list_opt:
  [[ vps = OPT vperm_var_list -> un_option vps VP.empty_vperm_sets ]];

par_case:
  [[
     `CASE; vps = vperm_var_list_opt; dc = disjunctive_constr; `LEFTARROW; sl = statement_list ->
      { exp_par_case_cond = Some (F.subst_stub_flow n_flow dc);
        exp_par_case_vperm = vps;
        exp_par_case_body = stmt_list_to_block sl (get_pos_camlp4 _loc 5);
        exp_par_case_else = false;
        exp_par_case_pos = (get_pos_camlp4 _loc 1); }
   | `ELSE_TT; (* vps = vperm_var_list_opt; *) `LEFTARROW; sl = statement_list ->
      { exp_par_case_cond = None;
        exp_par_case_vperm = VP.empty_vperm_sets;
        exp_par_case_body = stmt_list_to_block sl (get_pos_camlp4 _loc 5);
        exp_par_case_else = true;
        exp_par_case_pos = (get_pos_camlp4 _loc 1); }
  ]];

par_case_list: [[ cl = LIST1 par_case SEP `OROR -> cl ]];

iteration_statement: [[t=while_statement -> t]];

while_statement:
  [[ `WHILE; `OPAREN; bc=boolean_expression; `CPAREN; es=embedded_statement ->
        While { exp_while_condition = bc;
            exp_while_body = es;
            exp_while_addr_vars = [];
            (* exp_while_specs = Iast.mkSpecTrue n_flow (get_pos_camlp4 _loc 1); *)
            exp_while_specs = (Iformula.EList []); (*set to generate. if do not want to infer requires true ensures false;*)
            exp_while_jump_label = NoJumpLabel;
            exp_while_path_id = None ;
            exp_while_f_name = "";
            exp_while_wrappings = None;
            exp_while_pos = get_pos_camlp4 _loc 1 }
   | `WHILE; `OPAREN; bc=boolean_expression; `CPAREN; sl=spec_list_outer; es=embedded_statement ->
        While { exp_while_condition = bc;
          exp_while_body = es;
          exp_while_addr_vars = [];
          exp_while_specs = sl;(*List.map remove_spec_qualifier $5;*)
          exp_while_jump_label = NoJumpLabel;
          exp_while_path_id = None ;
          exp_while_f_name = "";
          exp_while_wrappings = None;
          exp_while_pos = get_pos_camlp4 _loc 1 }
   | `WHILE; `OPAREN; bc=boolean_expression; `CPAREN;`OSQUARE; t = id; `CSQUARE; es=embedded_statement ->
         While { exp_while_condition = bc;
         exp_while_body = es;
         exp_while_addr_vars = [];
         (* exp_while_specs = Iast.mkSpecTrue n_flow (get_pos_camlp4 _loc 1); *)
         exp_while_specs = (Iformula.EList []); (*set to generate. if do not want to infer requires true ensures false;*)
         exp_while_jump_label = NoJumpLabel;
         exp_while_path_id = None ;
         exp_while_f_name = t;
         exp_while_wrappings = None;
         exp_while_pos = get_pos_camlp4 _loc 1 }
   | `WHILE; `OPAREN; bc=boolean_expression; `CPAREN; `OSQUARE; t = id; `CSQUARE; sl=spec_list_outer; es=embedded_statement ->
         While { exp_while_condition = bc;
         exp_while_body = es;
         exp_while_addr_vars = [];
         exp_while_specs = sl;(*List.map remove_spec_qualifier $5;*)
         exp_while_jump_label = NoJumpLabel;
         exp_while_path_id = None ;
         exp_while_f_name = t;
         exp_while_wrappings = None;
         exp_while_pos = get_pos_camlp4 _loc 1 }
  ]];

jump_statement:
  [[ t=return_statement -> t
   | t=break_statement -> t
   | t=continue_statement -> t
   | t=raise_statement -> t]];

break_statement:
  [[ `BREAK  ->
        Break {
				  exp_break_jump_label = NoJumpLabel;
				  exp_break_path_id = None;
					exp_break_pos = (get_pos_camlp4 _loc 1);}
	| `BREAK; `IDENTIFIER id  ->
        Break {exp_break_jump_label = (JumpLabel id);
				  		 exp_break_path_id = None;
							exp_break_pos = get_pos_camlp4 _loc 1}]];

continue_statement:
  [[ `CONTINUE  ->
      Continue {exp_continue_jump_label = NoJumpLabel;
							 exp_continue_path_id = None;
							 exp_continue_pos = get_pos_camlp4 _loc 1}
   | `CONTINUE; `IDENTIFIER  id ->
      Continue {exp_continue_jump_label = (JumpLabel id);
							 exp_continue_path_id = None;
							 exp_continue_pos = get_pos_camlp4 _loc 1}]];

return_statement:
  [[ `RETURN; t=opt_expression ->
      Return { exp_return_val = t;
			 		     exp_return_path_id = None;
							 exp_return_pos = get_pos_camlp4 _loc 1 }]];

raise_statement:
	[[ `RAISE; t=expression ->
      Raise { exp_raise_type = Const_flow "" ;
			  exp_raise_val = Some t;
			  exp_raise_use_type = false;
              exp_raise_from_final = false;
              exp_raise_path_id = None;
              exp_raise_pos = get_pos_camlp4 _loc 1 }]];

try_statement:
	[[ `TRY; t=valid_declaration_statement; cl=opt_catch_list; fl=opt_finally->
      Try { exp_try_block = t;
            exp_catch_clauses = cl;
            exp_finally_clause = fl;
            exp_try_path_id = None;
            exp_try_pos = get_pos_camlp4 _loc 1 }]];

opt_catch_list: [[t= LIST0 catch_clause -> t]];

catch_clause:
	[[ `CATCH; `OPAREN; `IDENTIFIER id1; `IDENTIFIER id2; `CPAREN; vds = valid_declaration_statement ->
		  Catch { exp_catch_var = Some id2;
              exp_catch_flow_type = id1;
              exp_catch_flow_var = None;
			  exp_catch_alt_var_type = None;
              exp_catch_body = vds;
              exp_catch_pos = get_pos_camlp4 _loc 1 }]];

opt_finally: [[t =OPT finally_c -> un_option t [] ]];

finally_c: [[`FINALLY; vds=valid_declaration_statement -> [Finally {exp_finally_body = vds;exp_finally_pos = get_pos_camlp4 _loc 1 }]]];

opt_expression: [[t=OPT expression -> t]];


(********** Expressions **********)

object_creation_expression: [[t=object_or_delegate_creation_expression-> t]];

object_or_delegate_creation_expression:
  [[ `NEW; `IDENTIFIER id; `OPAREN; al=opt_argument_list; `CPAREN ->
      New { exp_new_class_name = id;
            exp_new_arguments = al;
            exp_new_pos = get_pos_camlp4 _loc 1 }
	(* An Hoa : Array allocation. *)
	| `NEW; `INT; `OSQUARE; al = argument_list; `CSQUARE ->
		ArrayAlloc { exp_aalloc_etype_name = "int";
					 exp_aalloc_dimensions = al;
					 exp_aalloc_pos = get_pos_camlp4 _loc 1; } ]];

new_expression: [[t=object_or_delegate_creation_expression -> t]];

opt_argument_list : [[t= LIST0 argument SEP `COMMA -> t]];

argument_list : [[t= LIST1 argument SEP `COMMA -> t]];

(* opt_argument_list : [[ t = OPT argument_list -> un_option t [] ]];

argument_list : [[  t = expression -> [t]
				  | arg_list = SELF; `COMMA; t = expression -> t::arg_list
			    ]]; *)

argument: [[t=expression -> t]];

expression:
  [[ t=conditional_expression -> t
   | t= bind_expression -> t
   | t=assignment_expression -> t]];

constant_expression: [[t=expression -> t]];

boolean_expression:  [[t=expression -> t]];

assignment_expression:
  [[ t1= prefixed_unary_expression; `EQ;  t2=expression ->
       mkAssign OpAssign t1 t2 (fresh_branch_point_id "") (get_pos_camlp4 _loc 2)
   | t1=prefixed_unary_expression; `OP_MULT_ASSIGN;t2=expression ->
       mkAssign OpMultAssign t1 t2 (fresh_branch_point_id "") (get_pos_camlp4 _loc 2)
   | t1=prefixed_unary_expression; `OP_DIV_ASSIGN; t2=expression ->
       mkAssign OpDivAssign t1 t2 (fresh_branch_point_id "") (get_pos_camlp4 _loc 2)
   | t1=prefixed_unary_expression; `OP_MOD_ASSIGN; t2=expression ->
       mkAssign OpModAssign t1 t2 (fresh_branch_point_id "") (get_pos_camlp4 _loc 2)
   | t1=prefixed_unary_expression; `OP_ADD_ASSIGN; t2=expression ->
       mkAssign OpPlusAssign t1 t2 (fresh_branch_point_id "") (get_pos_camlp4 _loc 2)
   | t1=prefixed_unary_expression; `OP_SUB_ASSIGN; t2=expression ->
       mkAssign OpMinusAssign t1 t2 (fresh_branch_point_id "") (get_pos_camlp4 _loc 2)]];

conditional_expression:
  [[ t= conditional_or_expression -> t
   (*| t= conditional_or_expression; `INTERR; e1=expression; `COLON; e2=expression ->
          Cond { exp_cond_condition = t;
             exp_cond_then_arm = e1;
             exp_cond_else_arm = e2;
             exp_cond_path_id = None ;
             exp_cond_pos = get_pos_camlp4 _loc 2 }*)]];

conditional_or_expression:
  [[ t=conditional_and_expression -> t
   | t1=SELF; `OROR; t2=conditional_and_expression ->
       mkBinary OpLogicalOr t1 t2 (fresh_branch_point_id "") (get_pos_camlp4 _loc 2)]];

conditional_and_expression:
  [[ t=inclusive_or_expression -> t
   | t1=SELF; `ANDAND; t2=inclusive_or_expression ->
       mkBinary OpLogicalAnd t1 t2 (fresh_branch_point_id "") (get_pos_camlp4 _loc 2)]];

(* bitwise *)
inclusive_or_expression : [[ t=exclusive_or_expression -> t]];

exclusive_or_expression : [[ t=and_expression -> t]];

and_expression : [[t=equality_expression -> t]];

equality_expression :
 [[ t=relational_expression -> t
  | t1=SELF; `EQEQ; t2=relational_expression ->
      mkBinary OpEq t1 t2 (fresh_branch_point_id "") (get_pos_camlp4 _loc 2)
  | t1=SELF; `NEQ; t2=relational_expression ->
      mkBinary OpNeq t1 t2 (fresh_branch_point_id "") (get_pos_camlp4 _loc 2)]];

relational_expression :
 [[ t=shift_expression                 -> t
  | t1=SELF; `LT; t2=shift_expression  ->
      mkBinary OpLt t1 t2 (fresh_branch_point_id "") (get_pos_camlp4 _loc 2)
  | t1=SELF; `GT; t2=shift_expression  ->
      mkBinary OpGt t1 t2 (fresh_branch_point_id "") (get_pos_camlp4 _loc 2)
  | t1=SELF; `LTE; t2=shift_expression ->
      mkBinary OpLte t1 t2 (fresh_branch_point_id "") (get_pos_camlp4 _loc 2)
  | t1=SELF; `GTE; t2=shift_expression ->
      mkBinary OpGte t1 t2 (fresh_branch_point_id "") (get_pos_camlp4 _loc 2)]];

shift_expression: [[t=additive_expression -> t]];

additive_expression:
 [[ t=multiplicative_expression                   -> t
  | t1=SELF; `PLUS; t2=multiplicative_expression  ->
      mkBinary OpPlus t1 t2 (fresh_branch_point_id "") (get_pos_camlp4 _loc 2)
  | t1=SELF; `MINUS; t2=multiplicative_expression ->
      mkBinary OpMinus t1 t2 (fresh_branch_point_id "") (get_pos_camlp4 _loc 2)]];

multiplicative_expression:
 [[ t=unary_expression                            -> t
  | t1=SELF; `STAR; t2=prefixed_unary_expression  ->
      mkBinary OpMult t1 t2 (fresh_branch_point_id "") (get_pos_camlp4 _loc 2)
  | t1=SELF; `DIV;  t2=prefixed_unary_expression  ->
      mkBinary OpDiv t1 t2 (fresh_branch_point_id "") (get_pos_camlp4 _loc 2)
  | t1=SELF; `PERCENT; t2=prefixed_unary_expression ->
      mkBinary OpMod t1 t2 (fresh_branch_point_id "") (get_pos_camlp4 _loc 2)]];

prefixed_unary_expression:
 [[ t=unary_expression -> t]];

pre_increment_expression:
 [[ `OP_INC; t=prefixed_unary_expression ->
      mkUnary OpPreInc t (fresh_branch_point_id "") (get_pos_camlp4 _loc 1)]];

pre_decrement_expression:
 [[ `OP_DEC; t=prefixed_unary_expression ->
      mkUnary OpPreDec t (fresh_branch_point_id "") (get_pos_camlp4 _loc 1)]];

post_increment_expression:
 [[ peek_try_st_in; t=primary_expression; `OP_INC ->
      mkUnary OpPostInc t (fresh_branch_point_id "") (get_pos_camlp4 _loc 2)]];

post_decrement_expression:
 [[ peek_try_st; t=primary_expression; `OP_DEC ->
      mkUnary OpPostDec t (fresh_branch_point_id "") (get_pos_camlp4 _loc 2)]];

unary_expression:
 [[ t=unary_expression_not_plusminus -> t
  | `PLUS; t=SELF ->
      let zero = mkIntLit 0 (get_pos_camlp4 _loc 1) in
      mkBinary OpPlus zero t (fresh_branch_point_id "") (get_pos_camlp4 _loc 1)
  | `MINUS; t=SELF ->
      let zero = mkIntLit 0 (get_pos_camlp4 _loc 1) in
      mkBinary OpMinus zero t (fresh_branch_point_id "") (get_pos_camlp4 _loc 1)
  | `STAR; t=SELF ->   (*Pointers: value-of *v *)
      mkUnary OpVal t (fresh_branch_point_id "") (get_pos_camlp4 _loc 1)
  | `AND; t=SELF ->   (*Pointers: address-of *& *)
      mkUnary OpAddr t (fresh_branch_point_id "") (get_pos_camlp4 _loc 1)
  | t=pre_increment_expression -> t
  | t=pre_decrement_expression -> t]];

unary_expression_not_plusminus:
 [[ t=postfix_expression -> t
  | `NOT; t = prefixed_unary_expression ->
      mkUnary OpNot t (fresh_branch_point_id "") (get_pos_camlp4 _loc 1)
  | t=cast_expression -> t]];

postfix_expression:
 [[ t=primary_expression -> t
  | t=post_increment_expression -> t
  | t=post_decrement_expression -> t]];

cast_expression:
 [[ `OPAREN; e=expression; `CPAREN; ue=unary_expression_not_plusminus ->
	  (match e with
		| Var v -> Cast { exp_cast_target_type = Named v.exp_var_name; (*TODO: fix this *)
                      exp_cast_body = ue;
                      exp_cast_pos = get_pos_camlp4 _loc 1 }
		| _ -> report_error (get_pos_camlp4 _loc 2) ("Expecting a type"))
  | `OPAREN; `INT; `CPAREN; t=unary_expression ->
      Cast { exp_cast_target_type = Int;
             exp_cast_body = t;
             exp_cast_pos = get_pos_camlp4 _loc 1 }
  | `OPAREN; `BOOL; `CPAREN; t=unary_expression ->
      Cast { exp_cast_target_type = Bool;
             exp_cast_body = t;
             exp_cast_pos = get_pos_camlp4 _loc 1 }
  | `OPAREN; `FLOAT; `CPAREN; t=unary_expression ->
      Cast { exp_cast_target_type = Float;
             exp_cast_body = t;
             exp_cast_pos = get_pos_camlp4 _loc 1 }]];

ho_arg: [[ `WITH; dc = disjunctive_constr -> F.subst_stub_flow n_flow dc ]];

opt_ho_arg: [[ oha = OPT ho_arg -> oha ]];

invocation_expression:
 [[ (* peek_invocation; *) qi=qualified_identifier; `OPAREN; oal=opt_argument_list; `CPAREN ->
	  CallRecv { exp_call_recv_receiver = fst qi;
               exp_call_recv_method = snd qi;
               exp_call_recv_arguments = oal;
               exp_call_recv_path_id = None;
               exp_call_recv_pos = get_pos_camlp4 _loc 1 }
  | (* peek_invocation; *) `IDENTIFIER id; l = opt_lock_info ; `OPAREN; oal=opt_argument_list; `CPAREN; oha = opt_ho_arg ->
    let _ =
      if (Iast.is_tnt_prim_proc id) then
        Hashtbl.add Iast.tnt_prim_proc_tbl id id
      else ()
    in
    CallNRecv { exp_call_nrecv_method = id;
                exp_call_nrecv_lock = l;
                exp_call_nrecv_arguments = oal;
                exp_call_nrecv_ho_arg = oha;
                exp_call_nrecv_path_id = None;
                exp_call_nrecv_pos = get_pos_camlp4 _loc 1 }
  ]];

opt_lock_info: [[t = OPT lock_info -> t ]];

(* lock_info: [[`OBRACE; t = id; `CBRACE -> t ]]; *)

lock_info: [[`OSQUARE; t = id; `CSQUARE -> t ]];

qualified_identifier: [[peek_try_st_qi; t=primary_expression; `DOT; `IDENTIFIER id -> (t, id)]];

(* member_access: [[peek_try_st; t=primary_expression; `DOT; `IDENTIFIER id -> *)
(* 	Member { exp_member_base = t; *)
(*            exp_member_fields = [id]; *)
(*            exp_member_path_id = None ; *)
(*            exp_member_pos = get_pos_camlp4 _loc 3 }] *)
(* 		   | [ `IDENTIFIER id ->   Var { exp_var_name = id; exp_var_pos = get_pos_camlp4 _loc 1 } *)
(* 			| `THIS _ -> This{exp_this_pos = get_pos_camlp4 _loc 1}] *)
(* 		   ]; *)

literal:
 [[ t=boolean_literal -> BoolLit { exp_bool_lit_val = t; exp_bool_lit_pos = get_pos_camlp4 _loc 1 }
  | t=integer_literal -> IntLit { exp_int_lit_val = t;exp_int_lit_pos = get_pos_camlp4 _loc 1 }
  | t=real_literal -> FloatLit { exp_float_lit_val = t; exp_float_lit_pos = get_pos_camlp4 _loc 1 }
  | `NULL -> Null (get_pos_camlp4 _loc 1)
  (* | `IMM -> P.AConst (Imm, (get_pos_camlp4 _loc 1))  *)
  (* | `LEND -> P.AConst (Lend, (get_pos_camlp4 _loc 1))  *)
  (* | `MUT -> P.AConst (Mutable, (get_pos_camlp4 _loc 1))  *)
 ]];

real_literal:[[ `FLOAT_LIT (t,_) -> t]];

integer_literal: [[`INT_LITER (t,_) -> t]];

boolean_literal :
  [[ `TRUE -> true
   | `FALSE-> false]];

primary_expression :
 [[ t=parenthesized_expression -> t
  | t=primary_expression_no_parenthesis -> t ]];

parenthesized_expression : [[`OPAREN; e= expression; `CPAREN -> e]];

primary_expression_no_parenthesis :
  [[ peek_array_type; t = arrayaccess_expression -> t
  |  t = primary_expression_no_array_no_parenthesis -> t ]];

primary_expression_no_array_no_parenthesis :
 [[ t= literal -> t
  (*| t= member_access -> t*)
  (*| t= member_name -> t*)
  | t=SELF; `DOT; `IDENTIFIER id ->
	Member { exp_member_base = t;
           exp_member_fields = [id];
           exp_member_path_id = None ;
           exp_member_pos = get_pos_camlp4 _loc 3 }
  | t = new_expression -> t
  | peek_invocation; t = invocation_expression -> t
  | `THIS _ -> This{exp_this_pos = get_pos_camlp4 _loc 1}
  ]
  | [`IDENTIFIER id -> (* print_string ("Variable Id : "^id^"\n"); *)
		let pos = get_pos_camlp4 _loc 1 in
		let res = if (String.contains id '.') then (* Identifier contains "." ==> this must be field access. *)
				let flds = Str.split (Str.regexp "\\.") id in
				(* let () = print_endline "Member field access" in *)
					Member {
						exp_member_base = Var { exp_var_name = List.hd flds;
												exp_var_pos = pos };
						exp_member_fields = List.tl flds; (* TODO merge the field access to match the core representation! *)
						exp_member_path_id = None;
						exp_member_pos = pos }
			else (* let () = print_endline "Simple variable" in *)
				Var { exp_var_name = id; exp_var_pos = pos } in
		(* let () = print_endline ("Parsed expression at " ^ (string_of_loc pos) ^ ": { " ^ (Iprinter.string_of_exp res) ^ " }") in *)
			res
]];

(* An Hoa : array access expression *)
arrayaccess_expression:[[
             id=primary_expression_no_array_no_parenthesis; `OSQUARE; ex = LIST1 expression SEP `COMMA; `CSQUARE ->
			ArrayAt {
				exp_arrayat_array_base = id;
				exp_arrayat_index = ex;
				exp_arrayat_pos = get_pos_camlp4 _loc 1 }
	         ]];
(* member_name : *)
(*  [[ `IDENTIFIER id ->   Var { exp_var_name = id; exp_var_pos = get_pos_camlp4 _loc 1 } *)
(*   | `THIS _ -> This{exp_this_pos = get_pos_camlp4 _loc 1}]]; *)

(*end of hip part*)

(*cp_list*)

cp_list:
  [[ t = opt_cp_list ->
    let hp_defs2 = new Gen.stack in(* list of heap predicate relations *)
    let proc_tcomps  = ref ([] : (ident * test_comps) list) in
    let choose d = match d with
      | Hpdecl hpdef  -> hp_defs2 # push hpdef
      | ProcERes t -> proc_tcomps := t :: !proc_tcomps
    in
    let todo_unk = List.map choose t in
    let hp_lst = hp_defs2 # get_stk in
    (hp_lst, !proc_tcomps)]];

opt_cp_list: [[t=LIST0 cp_comps -> List.concat t]];

cp_comps: [[ t=macro -> []
	  |t=cp_comp -> [t]]];

cp_comp: [[ r=hp_decl; `DOT -> Hpdecl r
	  | t=test -> ProcERes t]];

test:
  [[t = id;`COLON; s = id ; `OSQUARE; tl=test_list; `CSQUARE ->  (t,tl) ]];

test_list: [[t = LIST0 test_ele ->
    let ass  =  ref (None : ((ident list) *(ident list) * (ass list)) option) in
    let hpdefs  = ref (None : ((ident list) * (ident list) *(ass list)) option) in
    let choose d = match d with
      | ExpectedAss t  ->  ass := Some t
      | ExpectedHpDef t ->  hpdefs := Some t
    in
    let todo_unk = List.map choose t in
    {expected_ass = !ass;
      expected_hpdefs = !hpdefs}]];

test_ele:
  [[t = id; `OSQUARE; il=OPT id_list; `CSQUARE; `OSQUARE; sl=OPT id_list; `CSQUARE; `COLON;`OBRACE;cs=constrs;`CBRACE  ->
  let il = un_option il [] in
  let sl = un_option sl [] in
  if(String.compare "ass" t == 0) then ExpectedAss (il,sl,cs)
  else if(String.compare t "hpdefs" == 0) then ExpectedHpDef (il,sl,cs)
  else report_error no_pos "no_case"]];

constrs: [[t = LIST0 constr SEP `SEMICOLON -> t]];


constr : [[ t=disjunctive_constr; `CONSTR; b=disjunctive_constr ->
    {ass_lhs = F.subst_stub_flow n_flow t;
    ass_guard = None;
    ass_rhs = F.subst_stub_flow n_flow b}
  | t=disjunctive_constr; `REL_GUARD; guard = disjunctive_constr; `CONSTR; b=disjunctive_constr ->
        {ass_lhs = F.subst_stub_flow n_flow t;
        ass_guard = Some guard;
        ass_rhs = F.subst_stub_flow n_flow b}
  |  t=disjunctive_constr; `EQUIV; b=disjunctive_constr ->
         {ass_lhs = F.subst_stub_flow n_flow t;
         ass_guard = None;
         ass_rhs = F.subst_stub_flow n_flow b}
]];

(*end of cp_list*)
END;;

let parse_sleek n s =
  SHGram.parse sprog (PreCast.Loc.mk n) s

let parse_hip_with_option n s : (string * Iast.prog_decl) =
  let (slst,p) = SHGram.parse hip_with_option (PreCast.Loc.mk n) s in
  let s = List.fold_left (fun r s -> r^s) "" slst in
  (* let _ = print_endline s in*)
  (s,p)
;;
let parse_sleek n s =
  DD.no_1(* _loop *) "parse_sleek" (fun x -> x) (pr_list string_of_command) (fun n -> parse_sleek n s) n

let parse_hip n s =
  SHGram.parse hprog (PreCast.Loc.mk n) s

let parse_hip n s =
  DD.no_1(* _loop *) "parse_hip" (fun x -> x) (fun _ -> "?") (fun n -> parse_hip n s) n

let parse_sleek_int n s =
  SHGram.parse_string sprog_int (PreCast.Loc.mk n) s

let parse_hip_string n s =
  SHGram.parse_string hprog (PreCast.Loc.mk n) s

let parse_hip_string n s =
  let pr x = x in
  let pr_no x = "?" in DD.no_2 "parse_hip_string" pr pr pr_no parse_hip_string n s

let parse_specs_list s =
  SHGram.parse_string opt_spec_list_file (PreCast.Loc.mk "spec string") s

let parse_spec s = SHGram.parse_string opt_spec_list_file (PreCast.Loc.mk "spec string") s

let parse_cpfile n s = SHGram.parse cp_file (PreCast.Loc.mk n) s

(*****************************************************************)
(******** The function below will be used by CIL parser **********)
(*****************************************************************)

let parse_c_aux_proc (fname: string) (proc: string) =
  (* save states of current parser *)
  let old_parser_mode = !is_cparser_mode in
  (* swith to cparser mode *)
  is_cparser_mode := true;
  (* parse *)
  let res = SHGram.parse_string hproc (PreCast.Loc.mk fname) proc in
  (* restore states of previous parser *)
  is_cparser_mode := old_parser_mode;
  (* return *)
  { res with Iast.proc_is_main = false; }

let parse_c_function_spec (fname: string) (spec: string) (base_loc: file_offset)
                          (* (env : (string, (Cabs2cil.envdata * Cil.location)) Hashtbl.t) *)
                          : F.struc_formula =
  (* save states of current parser *)
  let old_parser_mode = !is_cparser_mode in
  let old_base_loc = !cparser_base_loc in
  (* swith to cparser mode *)
  cparser_base_loc := base_loc;
  is_cparser_mode := true;
  (* parse *)
  let res = SHGram.parse_string opt_spec_list (PreCast.Loc.mk fname) spec in
  (* restore states of previous parser *)
  is_cparser_mode := old_parser_mode;
  cparser_base_loc := old_base_loc;
  (* return *)
  res

let parse_c_program_spec (fname: string) (spec: string) (base_loc: file_offset)
                         : Iast.prog_decl =
  (* save states of current parser *)
  let old_parser_mode = !is_cparser_mode in
  let old_base_loc = !cparser_base_loc in
  (* swith to cparser mode *)
  cparser_base_loc := base_loc;
  is_cparser_mode := true;
  (* parse *)
  let res = SHGram.parse_string hprog (PreCast.Loc.mk fname) spec in
  (* restore states of previous parser *)
  is_cparser_mode := old_parser_mode;
  cparser_base_loc := old_base_loc;
  (* return *)
  res

let parse_c_statement_spec (fname: string) (spec: string) (base_loc: file_offset) =
  (* save states of current parser *)
  let old_parser_mode = !is_cparser_mode in
  let old_base_loc = !cparser_base_loc in
  (* swith to cparser mode *)
  cparser_base_loc := base_loc;
  is_cparser_mode := true;
  (* parse *)
  let res = SHGram.parse_string statement (PreCast.Loc.mk fname) spec in
  (* restore states of previous parser *)
  is_cparser_mode := old_parser_mode;
  cparser_base_loc := old_base_loc;
  (* return *)
  res

(***************** End of CIL parser's functions *****************)
(*****************************************************************)

(* ////////////////////////////////////////////// *)
(* // Prelude for Termination Competition TPDB // *)
(* ////////////////////////////////////////////// *)
(* int __VERIFIER_nondet_int() *)
(*   requires true             *)
(*   ensures true;             *)

(* int __VERIFIER_error()      *)
(*   requires true             *)
(*   ensures res = 0;          *)

let create_tnt_prim_proc id : Iast.proc_decl option =
  let proc_source =
    if String.compare id Globals.nondet_int_proc_name == 0 then
      let () = rel_names # push Globals.nondet_int_rel_name in
      Some (
        "int " ^ Globals.nondet_int_proc_name ^ "()\n" ^
        "  requires true\n" ^
        "  ensures true & " ^ Globals.nondet_int_rel_name ^ "(res)" ^ ";\n")
    else if String.compare id "__VERIFIER_error" == 0 then
      Some (
        "int __VERIFIER_error()\n" ^
        "  requires true\n" ^
        "  ensures res = 0;\n")
    else None
  in map_opt (parse_c_aux_proc "tnt_prim_proc") proc_source

let add_tnt_prim_proc prog id =
  if String.compare id Globals.nondet_int_proc_name == 0 then
    let proc_src =
      "int " ^ Globals.nondet_int_proc_name ^ "()\n" ^
      "  requires true\n" ^
      "  ensures true & " ^ Globals.nondet_int_rel_name ^ "(res)" ^ ";\n"
    in
    let nondet_rel = {
      rel_name = nondet_int_rel_name;
      rel_typed_vars = [(int_type, nondet_int_rel_name ^ "res")];
      rel_formula = P.mkTrue no_pos; }
    in
    let () = rel_names # push Globals.nondet_int_rel_name in
    let proc_decl = parse_c_aux_proc "tnt_prim_proc" proc_src in
    { prog with
      Iast.prog_rel_decls = prog.Iast.prog_rel_decls @ [nondet_rel];
      Iast.prog_proc_decls = prog.Iast.prog_proc_decls @ [proc_decl]; }
  else if String.compare id "__VERIFIER_error" == 0 then
    let proc_src =
      "int __VERIFIER_error()\n" ^
      "  requires true\n" ^
      "  ensures res = 0;\n"
    in
    let proc_decl = parse_c_aux_proc "tnt_prim_proc" proc_src in
    { prog with Iast.prog_proc_decls = prog.Iast.prog_proc_decls @ [proc_decl]; }
  else prog

let create_tnt_stdlib_proc () : Iast.proc_decl list =
  let alloca_proc =
    "void_star __builtin_alloca(int size)\n" ^
    "  case {\n" ^
    "    size <= 0 -> requires true ensures res = null;\n" ^
    "    size >  0 -> requires true ensures res::memLoc<h,s> & (res != null) & h; }\n"
  in
  let lt_proc =
    "int lt___(int_star p, int_star q)\n" ^
    "  requires p::int_star<vp, op> * q::int_star<vq, oq>\n" ^
    "  case {\n" ^
    "    op <  oq -> ensures p::int_star<vp, op> * q::int_star<vq, oq> & res > 0;\n" ^
    "    op >= oq -> ensures p::int_star<vp, op> * q::int_star<vq, oq> & res <= 0; }\n"
  in List.map (parse_c_aux_proc "tnt_stdlib_proc") [alloca_proc; lt_proc]

let create_tnt_prim_proc_list ids : Iast.proc_decl list =
  List.concat (List.map (fun id ->
    match (create_tnt_prim_proc id) with
    | None -> [] | Some pd -> [pd]) ids)

