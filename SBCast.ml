open SBGlobals
open SBLib

module DB = SBDebug

let time_mk_pconj = ref 0.

let time_mk_pdisj = ref 0.

type bin_op =
  | Add
  | Sub
  | Mul
  | Div

type func =
  | Max
  | Min
  | Abs

(** each linear arithmetic term is stored as
    a list of variables with their coefficients and the integer part *)
type lterm = ((int * var) list * int)

type exp =
  | Null of pos
  | Var of (var * pos)
  | IConst of (int * pos)
  | LTerm of (lterm * pos)
  | Func of (func * exp list * pos)
  | BinOp of (bin_op * exp * exp * pos)
  (* TODO: transform BinOp to list-representation
     Add of (exp list * pos)
     Sub of (exp list * pos) *)

type bin_rel =
  | Lt
  | Le
  | Gt
  | Ge
  | Eq
  | Ne

type rel_form = {
  prel_name : string;
  prel_args : exp list;
  prel_pos : pos;
}

type pure_form =
  | BConst of (bool * pos)
  | BinRel of (bin_rel * exp * exp * pos)
  | PRel of rel_form
  | PNeg of (pure_form * pos)
  | PConj of (pure_form list * pos)
  | PDisj of (pure_form list * pos)
  | PForall of (var list * pure_form * pos)
  | PExists of (var list * pure_form * pos)

type heap_origin =
  | HorgInput
  | HorgUnfold
  | HorgHypo
  | HorgTheorem

type heap_id = int

type data_form = {
  dataf_root : exp;
  dataf_name : string;
  dataf_args : exp list;
  dataf_pos : pos;
  dataf_id : heap_id;
  dataf_ancestor_ids : heap_id list;
  dataf_origin : heap_origin;
}

and view_form = {
  viewf_name : string;
  viewf_args : exp list;
  viewf_pos : pos;
  viewf_id : heap_id;
  viewf_ancestor_ids : heap_id list;
  viewf_origin : heap_origin;
}

and heap_atom =
  | HData of data_form
  | HView of view_form

(* keep two list of views and datas, each list is in an increasing order *)
and heap_form =
  | HEmp of pos
  | HAtom of (data_form list * view_form list * pos)
  | HStar of (heap_form * heap_form * pos)
  | HWand of (heap_form * heap_form * pos)

and formula =
  | FBase of (heap_form * pure_form * pos)
  | FExists of (var list * formula * pos)
  | FForall of (var list * formula * pos)

type pure_entail = {
  pent_id : int;
  pent_lhs : pure_form;
  pent_rhs : pure_form;
  pent_pos : pos;
}

type entailment = {
  ent_id : int;
  ent_lhs : formula;
  ent_rhs : formula;
  ent_mode : proof_mode;
  ent_pos : pos;
}

type lemma_origin =
  | LorgUser
  | LorgSynth
  | LorgMutual

type lemma = {
  lm_name : string;
  lm_origin : lemma_origin;
  lm_kind : lemma_kind;
  lm_status : lemma_status;
  lm_lhs : formula;
  lm_rhs : formula;
  lm_pos : pos;
}

type lemmas = lemma list

(* TODO: consider moving to proof.ml to cache stats of lhs, rhs *)
type lemma_template = {
  lmt_lhs : formula;
  lmt_rhs : formula;
  lmt_typ : lemma_typ;
}

type lemma_templates = lemma_template list

type counter_lemma = {
  clm_name : string;
  clm_status : mvlogic;
  clm_lhs : formula;
  clm_rhs : formula;
}

(* unknown coefficients and template *)
type unk_coes_conj = {
  uc_param_coes: var list;
  uc_base_coes: var list;
}

type unk_coes_rel = {
  uc_name: string;
  uc_coes_conjs: unk_coes_conj list;
}

type rel_body_template = {
  templ_unk_coes : unk_coes_rel;
  templ_body : pure_form;
  templ_dummy : bool;
}

type rel_body_form =
  | RbForm of pure_form
  | RbTemplate of rel_body_template
  | RbUnknown

type rel_defn = {
  rel_name : string;
  rel_params : var list;
  rel_body : rel_body_form;
  rel_pos : pos;
}

type rel_defns = rel_defn list

type rel_defnss = rel_defns list

type infer_solver =
  | IsvFarkas
  | IsvIprover
  | IsvDecompose of infer_solver

type data_defn = {
  datad_name: string;
  datad_fields: (typ * string) list;        (* data fields' type and name *)
  datad_pos: pos;
}

(* TODO: add recursive direction into account *)

and view_recur_direction =
  | VrdNone
  | VrdHead
  | VrdTail
  | VrdMid
  | VrdMix

and view_recur_typ =
  | VrtNone
  | VrtSelf
  | VrtMutual of (string list)
  | VrtIndirect of (string list)
  | VrtMix of (string list)
  | VrtUnkn

and view_defn_case = {
  vdc_id : int;
  vdc_form : formula;
  vdc_base_case : bool;
}

and alloc_exp = {
  al_cond : pure_form;
  al_addr : exp;
}

and view_invariant = {
  vinv_arith : pure_form option;
  vinv_pointer : pure_form option;
  vinv_all : pure_form option;
  vinv_user : pure_form option;
}

and view_defn = {
  view_name : string;
  view_params : var list;
  view_defn_cases : view_defn_case list;  (* view formulas and their ids *)
  view_alloc_exps : alloc_exp list;
  view_roots : var list;                  (* roots are members of params *)
  view_inductive_vars : var list;         (* vars appear in sub-views *)
  view_recurd : view_recur_direction;
  view_recurt : view_recur_typ;
  view_data_names : string list;
  view_inv : view_invariant;
  view_min_size : int;
  view_emid_cases : pure_form list;
  view_empty_base_case : bool;
  view_pos : pos;
}

and pred_defn =
  | PredView of view_defn
  | PredRel of rel_defn

and infer_rels = {
  ifr_typ : infer_rels_typ;
  ifr_rels : pure_entail list;
}

and command =
  | CheckEntail of (entailment * status)
  | CheckSat of (formula * sat_solver)
  | InferLemma of (entailment * lemma_typ list)
  | InferEntail of entailment
  | InferRels of infer_rels
  | Process of formula
  | ProcessTwo of (formula * formula)
  | CmdUnkn

and command_stats = {
  cmd_res : string;
  cmd_time : float option;
}

and program = {
  prog_filename : string;
  prog_rels : rel_defn list;
  prog_datas : data_defn list;
  prog_views : view_defn list;
  prog_lemmas : lemma list;
  prog_commands : command list;
  prog_pos: pos;
}

and quantifier =
  | QExists of var list
  | QForall of var list

and subst = (var * exp)         (* old var -> new exp, similar to FOL *)

and psubst = var * (exp list)   (* possible substitution, var -> possible exps *)

and substs = subst list

and renaming = (var * var)        (* old var -> new var *)

and var_pair = (var * var)

(* a list of variables and their values *)
and model = (var * exp) list

exception ERdefnss of rel_defnss

let raise_rdefnss rdss = raise (ERdefnss rdss)

(*******************      printer     ********************)

let pr_bin_op = function
  | Add -> "Add"
  | Sub -> "Sub"
  | Mul -> "Mul"
  | Div -> "Div"

let pr_func = function
  | Max -> "max"
  | Min -> "min"
  | Abs -> "abs"

let pr_var ?(typ=false) (v : var) =
  let vname, vtyp = v in
  if (typ) then "(" ^ vname ^ ":" ^ (pr_typ vtyp) ^ ")"
  else vname

let pr_qvar (v : quantifier) =
  match v with
  | QForall xs -> "forall " ^ (pr_list ~sep:" " pr_var xs)
  | QExists xs -> "exists " ^ (pr_list ~sep:" " pr_var xs)

let pr_qvars (vs : quantifier list) = pr_list pr_qvar vs

let pr_lterm?(typ=false) (t: lterm) =
  let cpart, ipart = t in
  let scpart = List.fold_left (fun acc (c,v) ->
    let tmp =
      if c = 1 || c = -1 then (pr_var ~typ:typ v)
      else (pr_int (abs c)) ^ "\\*" ^ (pr_var ~typ:typ v) in
    if (eq_s acc "") then
      if (c >= 0) then tmp
      else "-" ^ tmp
    else if (c >= 0) then acc ^ "+" ^ tmp
    else acc ^ "-" ^ tmp) "" cpart in
  if (eq_s scpart "") then pr_int ipart
  else if (ipart = 0) then scpart
  else if (ipart > 0) then scpart ^ "+" ^ (pr_int ipart)
  else scpart ^ "-" ^ (pr_int (abs ipart))

let rec pr_exp ?(typ=false) ?(paren=false) (e: exp) = match e with
  | Null _ -> "nil"
  | Var (v, _) -> pr_var ~typ:typ v
  | IConst (i, _) -> pr_int i
  | LTerm (t, _) -> pr_lterm ~typ:typ t
  (* | LTerm (t, _) -> "LTERM: " ^ (pr_lterm ~typ:typ t) *)
  | BinOp (op, e1, e2, _) ->
    let ne1 = (pr_exp ~typ:typ ~paren:paren e1) in
    let ne2 = (pr_exp ~typ:typ ~paren:paren e2) in
    let res = match op with
      | Add -> ne1 ^ "+" ^ ne2
      | Sub -> ne1 ^ "-" ^ ne2
      | Mul -> ne1 ^ "*" ^ ne2
      | Div -> ne1 ^ "/" ^ ne2 in
    if (paren) then "(" ^ res ^ ")"
    else res
  | Func (f, es, _) ->
    (pr_func f) ^ "(" ^ (pr_exps ~sep:"," es) ^ ")"

and pr_exps ?(typ=false) ?(paren=false) ?(sep=", ") es =
  pr_list ~sep:sep ~obrace:"" ~cbrace:""
    (fun x -> pr_exp ~typ:typ ~paren:paren x) es

let rec pr_rform ?(typ=false) (rel: rel_form) =
  let header = rel.prel_name in
  let body = pr_args (pr_exp ~typ:typ) rel.prel_args in
  header ^ "(" ^ body ^ ")"

let rec pr_pure_form ?(typ=false) ?(paren=false) (p : pure_form) = match p with
  | BConst (b, _) -> pr_bool b
  | BinRel (rel, e1, e2, _) ->
    let ne1, ne2 = Pair.fold (pr_exp ~typ:typ ~paren:paren) e1 e2 in
    let res = match rel with
      | Lt -> ne1 ^ "<" ^ ne2
      | Le -> ne1 ^ "<=" ^ ne2
      | Gt -> ne1 ^ ">" ^ ne2
      | Ge -> ne1 ^ ">=" ^ ne2
      | Eq -> ne1 ^ "=" ^ ne2
      | Ne -> ne1 ^ "!=" ^ ne2 in
    if (paren) then "a(" ^ res ^ ")" else res
  | PRel rel -> pr_rform rel
  | PNeg (pf, _) -> "!(" ^ (pr_pure_form ~typ:typ pf) ^ ")"
  | PConj (pfs, _) ->
    let spfs = List.map (fun x ->
      match x with
      | PDisj _ -> pr_pure_form ~typ:typ ~paren:true x
      | _ -> pr_pure_form ~typ:typ ~paren:false x) pfs in
    let res = pr_list ~sep:" & " pr_id spfs in
    if (paren) then "(" ^ res ^ ")" else res
  | PDisj (pfs, _) ->
    let spfs = List.map (fun x ->
      match x with
      | PConj _ -> pr_pure_form ~typ:typ ~paren:true x
      | _ -> pr_pure_form ~typ:typ ~paren:false x) pfs in
    let res = pr_list ~sep:" | " pr_id spfs in
    if (paren) then "(" ^ res ^ ")" else res
  | PForall (vs, pf, _) ->
    let qvars = String.trim (pr_args (pr_var ~typ:typ) vs) in
    let base = pr_pure_form ~typ:typ ~paren:paren pf in
    if (vs = [] ) then "(forall []. " ^ base ^ ")"
    else "(forall " ^ qvars ^ ". " ^ base ^ ")"
  | PExists (vs, pf, _) ->
    let qvars = String.trim (pr_args (pr_var ~typ:typ) vs) in
    let base = pr_pure_form ~typ:typ ~paren:paren pf in
    if (vs = []) then "(exists []. " ^ base ^ ")"
    else "(exists " ^ qvars ^ ". " ^ base ^ ")"

let pr_heap_org = function
  | HorgInput -> "HorgInput"
  | HorgUnfold -> "HorgUnfold"
  | HorgHypo -> "HorgHypo"
  | HorgTheorem -> "HorgTheorem"

let pr_data_form ?(typ=false) (data: data_form) =
  let header = (pr_exp ~typ:typ data.dataf_root) in
  let body = pr_args (pr_exp ~typ:typ) data.dataf_args in
  header ^ "->" ^ data.dataf_name ^ "{" ^ body ^ "}"
  (* let ids = "@ID:" ^ (pr_int data.dataf_id) ^
   *           "@ANS:" ^
   *           (pr_list_sbrace ~sep:"," pr_int data.dataf_ancestor_ids) in
   * header ^ "->" ^ data.dataf_name ^ "{" ^ body ^ "}" ^ ids *)

let pr_view_form ?(typ=false) (view: view_form) =
  let header = view.viewf_name in
  let body = pr_args (pr_exp ~typ:typ) view.viewf_args in
  header ^ "(" ^ body ^ ")"
  (* let ids = "@ID:" ^ (pr_int view.viewf_id) ^
   *           "@ANS:" ^
   *           (pr_list_sbrace ~sep:"," pr_int view.viewf_ancestor_ids) in
   * header ^ "(" ^ body ^ ")" ^ ids *)

let pr_heap_atom ?(typ=false) (ha: heap_atom) =
  match ha with
  | HData df -> pr_data_form ~typ:typ df
  | HView vf -> pr_view_form ~typ:typ vf

let rec pr_heap_form ?(typ=false) ?(paren=false) (hf: heap_form) =
  match hf with
  | HEmp _ -> "emp"
  | HAtom (dfs, vfs, _) ->
    let sdfs = pr_list ~sep:" * " (fun x -> pr_data_form ~typ:typ x) dfs in
    let svfs = pr_list ~sep:" * " (fun x -> pr_view_form ~typ:typ x) vfs in
    if (dfs = [] && vfs = []) then "emp"
    else if (dfs = []) then svfs
    else if (vfs = []) then sdfs
    else sdfs ^ " * " ^ svfs
  | HStar (h1, h2, _) ->
    let s1, s2 = Pair.fold (pr_heap_form ~typ:typ ~paren:paren) h1 h2 in
    let res = "(" ^ s1 ^ ") * (" ^ s2 ^ ")" in
    if (paren) then "(" ^ res ^ ")" else res
  | HWand (h1, h2, _) ->
    let s1, s2 = Pair.fold (pr_heap_form ~typ:typ ~paren:paren) h1 h2 in
    let res = "(" ^ s1 ^ ") --* (" ^ s2 ^ ")" in
    if (paren) then "(" ^ res ^ ")" else res

let rec pr_formula ?(typ=false) ?(paren=false) f =
  match f with
  | FBase (h, BConst (true, _), _) -> pr_heap_form ~typ:typ ~paren:paren h
  | FBase (h, p, _) ->
    let sh = pr_heap_form ~typ:typ ~paren:paren h in
    let sp = pr_pure_form ~typ:typ ~paren:paren p in
    sh ^ " & " ^ sp
  | FExists (vs, f, _) ->
    let base = pr_formula ~typ:typ ~paren:paren f in
    let qvars = String.trim (pr_args (pr_var ~typ:typ) vs) in
    if (eq_s qvars "") then base else ("(exists " ^ qvars ^ ". " ^ base ^ ")")
  | FForall (vs, f, _) ->
    let base = pr_formula ~typ:typ ~paren:paren f in
    let qvars = String.trim (pr_args (pr_var ~typ:typ) vs) in
    if (eq_s qvars "") then base else ("(forall " ^ qvars ^ ". " ^ base ^ ")")

let pr_entailment_lrhs ?(typ=false) ?(paren=false) lhs rhs =
  (pr_formula ~typ:typ ~paren:paren lhs)
  ^ " |- " ^ (pr_formula ~typ:typ ~paren:paren rhs)

let pr_entailment_pair_lrhs ?(typ=false) ?(paren=false) (lhs, rhs) =
  pr_entailment_lrhs ~typ:typ ~paren:paren lhs rhs

let pr_entailment ?(typ=false) ?(paren=false) (ent: entailment) =
  pr_entailment_lrhs ~typ:typ ~paren:paren ent.ent_lhs ent.ent_rhs

let pr_pure_entail ?(typ=false) ?(paren=false) (ent: pure_entail) =
  (pr_pure_form ~typ:typ ~paren:paren ent.pent_lhs)
  ^ " |- " ^ (pr_pure_form ~typ:typ ~paren:paren ent.pent_rhs)

let pr_lemma ?(typ=false) (lm: lemma) =
  let kind = match lm.lm_kind with
    | LmkSafe -> "safe"
    | LmkUnsafe -> "unsafe" in
  "Lemma " ^ lm.lm_name ^ " (" ^ kind ^ "): "
  ^ (pr_formula ~typ:typ lm.lm_lhs) ^ " |- "
  ^ (pr_formula ~typ:typ lm.lm_rhs)

let pr_counter_lemma (clm: counter_lemma) =
  let status = pr_mvl clm.clm_status in
  "Counter-Lemma (" ^ clm.clm_name ^ ", " ^ status ^ "): "
  ^ (pr_formula ~typ:false clm.clm_lhs) ^ " |- "
  ^ (pr_formula ~typ:false clm.clm_rhs)

let pr_lemma_template ?(typ=false) (lmt: lemma_template) =
  let lmtyp = String.uppercase_ascii (pr_lemma_typ lmt.lmt_typ) in
  "LemmaTemplate[" ^ lmtyp ^ "]: "
  ^ (pr_formula ~typ:typ lmt.lmt_lhs) ^ " |- "
  ^ (pr_formula ~typ:typ lmt.lmt_rhs)

let pr_rel_defn ?(typ=false) ?(paren=false) (rel: rel_defn) =
  let header = rel.rel_name in
  let params = pr_args (pr_var ~typ:typ) rel.rel_params in
  let body = match rel.rel_body with
    | RbUnknown -> "Unknown"
    | RbTemplate tmpl -> "Template (" ^ (pr_pure_form tmpl.templ_body) ^ ")"
    | RbForm f -> pr_pure_form f in
  header ^ "(" ^ params ^ ") := " ^ body

let pr_rd = pr_rel_defn ~typ:false ~paren:false
let pr_rds = pr_items ~bullet:"  #" pr_rd
let pr_rdsl = pr_list ~sep:"; " pr_rd
let pr_rdss = pr_items ~bullet:"  +++" pr_rds

let pr_data_defn (data: data_defn) =
  let header = data.datad_name in
  let body = List.fold_left (fun acc (ftyp, fname) ->
    let fstr = "  " ^ (pr_typ ftyp) ^ " " ^ fname ^ ";" in
    acc ^ fstr ^ "\n") "" data.datad_fields in
  header ^ " {\n" ^ body ^ "}"

let pr_alloc_exp ?(typ=false) ?(paren=false) ae =
  (pr_pure_form ~typ:typ ~paren:paren ae.al_cond)
  ^ " => "
  ^ (pr_exp ~typ:typ ~paren:paren ae.al_addr)

let pr_alloc_exps ?(typ=false) ?(paren=false) aes =
  pr_items ~bullet:"  -" (fun x -> pr_alloc_exp ~typ:typ ~paren:paren x) aes

let pr_view_recur_d vrd = match vrd with
  | VrdNone -> "VrdNone"
  | VrdHead -> "VrdHead"
  | VrdTail -> "VrdTail"
  | VrdMid -> "VrdMid"
  | VrdMix -> "VrdMix"

let pr_view_recur vrt = match vrt with
  | VrtNone -> "VrtNone"
  | VrtSelf -> "VrtSelf"
  | VrtMutual vs -> "VrtMutual (" ^ (pr_list pr_id vs) ^ ")"
  | VrtIndirect vs -> "VrtIndirect (" ^ (pr_list pr_id vs) ^ ")"
  | VrtMix vs -> "VrtMix (" ^ (pr_list pr_id vs) ^ ")"
  | VrtUnkn -> "VrtUnkn"

let pr_view_defn_case ?(typ=false) vdc =
  let case_type =
    if vdc.vdc_base_case then "base-case"
    else "inductive-case" in
  case_type ^ " (" ^ (pr_int vdc.vdc_id) ^ "): "
  ^ (pr_formula ~typ:typ vdc.vdc_form)

let pr_view_inv vinv =
  let pr_pfo = pr_opt pr_pure_form in
  "   - inv_arith: " ^ (pr_pfo vinv.vinv_arith) ^ "\n"
  ^ "   - inv_pointer: " ^ (pr_pfo vinv.vinv_pointer) ^ "\n"
  ^ "   - inv_all: " ^ (pr_pfo vinv.vinv_arith) ^ "\n"
  ^ "   - inv_user: " ^ (pr_pfo vinv.vinv_user)

let pr_view_defn ?(typ=false) ?(paren=false) (view: view_defn) =
  let header = view.view_name in
  let params = pr_args (pr_var ~typ:typ) view.view_params in
  let body = match view.view_defn_cases with
    | [] -> ""
    | x::[] -> "[[ " ^ (pr_view_defn_case ~typ:typ x) ^ " ]]"
    | xs ->
      let body = xs |> List.map (pr_view_defn_case ~typ:typ) |>
                 List.map (fun s -> "  # " ^ s) |> String.concat "\n" in
      "[[\n" ^ body ^ "\n ]]"in
  let body = match !DB.debug_normal_mode with
    | true ->
      body ^ "\n ++ view recur type: " ^ (pr_view_recur view.view_recurt)
      ^ "\n ++ view recur direction: " ^ (pr_view_recur_d view.view_recurd)
      ^ "\n ++ view data names: " ^ (pr_ss view.view_data_names)
      ^ "\n ++ view invariant:\n" ^ (pr_view_inv view.view_inv)
      ^ "\n ++ view root: " ^ (pr_list pr_var view.view_roots)
      ^ "\n ++ view inductive vars: " ^ (pr_list pr_var view.view_inductive_vars)
      ^ "\n ++ view min size: " ^ (pr_int view.view_min_size)
      ^ "\n ++ view empty base case: " ^ (pr_bool view.view_empty_base_case)
      ^ "\n ++ view emid cases: "
      ^ (pr_list_sbrace pr_pure_form view.view_emid_cases)
      ^ "\n ++ alloc: \n" ^ (pr_alloc_exps view.view_alloc_exps)
    | false -> body in
  "pred " ^ header ^ "(" ^ params ^ ") := " ^ body

let pr_pred_defn = function
  | PredView vd -> pr_view_defn vd
  | PredRel rl -> pr_rel_defn rl

let pr_cmd ?(typ=false) ?(paren=false) cmd =
  let pr_f = pr_formula ~typ:typ ~paren:paren in
  let pr_ent = pr_entailment ~typ:typ ~paren:paren in
  match cmd with
  | CheckEntail (ent, _) -> "CheckEntail " ^ (pr_ent ent)
  | InferLemma (ent, lmts) ->
    "InferLemma" ^ (pr_list_sbrace pr_lmt lmts) ^ (pr_ent ent)
  | CheckSat (f, sv) -> "CheckSat[" ^ (pr_ssv sv) ^ "] " ^ (pr_f f)
  | InferEntail ent ->
    "InferEntail [" ^ (pr_prm ent.ent_mode) ^ "]: " ^ (pr_ent ent)
  | InferRels ifr ->
    "InferRels[" ^ (pr_ifr ifr.ifr_typ) ^ "]\n"
    ^ (pr_items ~bullet:"  #" pr_pure_entail ifr.ifr_rels)
  | Process f -> "Process " ^ (pr_f f)
  | ProcessTwo (f1, f2) ->
    "ProcessTwo " ^ (pr_f f1) ^ " ~|~ " ^ (pr_f f2)
  | CmdUnkn -> "UnknownCommand"

let pr_program ?(typ=false) ?(paren=false) prog =
  let data_str =
    prog.prog_datas |> List.fold_left (fun acc d ->
      if (!DB.debug_deep_mode) && (is_builtin_data d.datad_name) then acc
      else acc ^ "\n\n" ^ (pr_data_defn d)) "" in
  let rel_str =
    prog.prog_rels |> List.fold_left (fun acc rel ->
      acc ^ "\n\n" ^ (pr_rel_defn ~typ:typ rel)) "" in
  let view_str =
    prog.prog_views |> List.fold_left (fun acc vdefn ->
      acc ^ "\n\n" ^ (pr_view_defn ~typ:typ vdefn)) "" in
  let lemma_str =
    prog.prog_lemmas |> List.fold_left (fun acc lm ->
      acc ^ "\n\n" ^ (pr_lemma ~typ:typ lm)) "" in
  let command_str =
    prog.prog_commands |> List.fold_left (fun acc cmd ->
      acc ^ "\n\n" ^ (pr_cmd ~typ:typ cmd)) "" in
  (* prog *)
  let prog_str = data_str in
  let prog_str = (String.trim prog_str) ^ "\n\n" ^ rel_str in
  let prog_str = (String.trim prog_str) ^ "\n\n" ^ view_str in
  let prog_str = (String.trim prog_str) ^ "\n\n" ^ lemma_str in
  let prog_str = (String.trim prog_str) ^ "\n\n" ^ command_str in
  let prog_str = String.trim prog_str in
  prog_str

(* print program with type information *)
let pr_typed_program prog = pr_program ~typ:true prog

let pr_detail_program prog = pr_program ~paren:true prog

let pr_model = pr_list (pr_pair pr_var pr_exp)

let pr_subst sst =
  let (v, e) = sst in
  "[" ^ (pr_var v) ^ "->" ^ (pr_exp e) ^ "]"

let pr_substs ssts =
  let pr_one sst = let (v, e) = sst in (pr_var v) ^ "->" ^ (pr_exp e) in
  "[" ^ (pr_list ~sep:", " pr_one ssts) ^ "]"

let pr_psubsts ssts =
  let pr_one sst = let (v, es) = sst in (pr_var v) ^ "->" ^ (pr_exps es) in
  "[" ^ (pr_list ~sep:", " pr_one ssts) ^ "]"

let pr_substss x = match x with
  | [] -> "[]"
  | _ -> pr_items ~bullet:"  #" pr_substs x

let pr_renaming rnm =
  let (v, u) = rnm in
  "[" ^ (pr_var v) ^ "->" ^ (pr_var u) ^ "]"

let pr_renamings rnms =
  let pr_one rnm = let (v, u) = rnm in (pr_var v) ^ "->" ^ (pr_var u) in
  "[" ^ (pr_list ~sep:", " pr_one rnms) ^ "]"

let rec pr_infer_solver solver = match solver with
  | IsvFarkas -> "Farkas"
  | IsvIprover -> "Iprover"
  | IsvDecompose isv -> "Decompose (" ^ (pr_infer_solver isv) ^ ")"

(* aliases *)
let pr_lt = pr_lterm ~typ:false
let pr_e = pr_exp ~typ:false ~paren:false
let pr_pf = pr_pure_form ~typ:false ~paren:false
let pr_pfs = pr_list ~obrace:"[" ~cbrace:"]" pr_pf
let pr_hf = pr_heap_form ~typ:false ~paren:false
let pr_ha = pr_heap_atom ~typ:false
let pr_hfs = pr_list ~obrace:"[" ~cbrace:"]" pr_hf
let pr_has = pr_list ~obrace:"[" ~cbrace:"]" pr_ha
let pr_df = pr_data_form ~typ:false
let pr_vf = pr_view_form ~typ:false
let pr_dfs = pr_list pr_df
let pr_vfs = pr_list pr_vf
let pr_rf = pr_rform ~typ:false
let pr_rfs = pr_list (pr_rform ~typ:false)
let pr_f = pr_formula ~typ:false ~paren:false
let pr_fs = pr_items ~bullet:"  #" pr_f
let pr_ent = pr_entailment ~typ:false ~paren:false
let pr_pent = pr_pure_entail ~typ:false ~paren:false
let pr_ents = pr_items ~bullet:"  #" pr_ent
let pr_pents = pr_items ~bullet:"  #" pr_pent
let pr_entlr = pr_entailment_lrhs  ~typ:false ~paren:false
let pr_entp = pr_entailment_pair_lrhs  ~typ:false ~paren:false
let pr_ssts = pr_substs
let pr_sstss = pr_substss
let pr_rnms = pr_renamings
let pr_v = pr_var ~typ:false
let pr_vs = pr_list ~obrace:"[" ~cbrace:"]" pr_v
let pr_vss = pr_items ~bullet:"  +++\n" pr_vs
let pr_funcs = pr_list ~obrace:"[" ~cbrace:"]" pr_func
let pr_pv (v1,v2) = "(" ^ (pr_v v1) ^ "," ^ (pr_v v2) ^ ")"
let pr_pvs pvs = pr_list pr_pv pvs
let pr_lm = pr_lemma ~typ:false
let pr_lms = pr_items ~bullet:"  -" (pr_lemma ~typ:false)
let pr_lmt = pr_lemma_template ~typ:false
let pr_lmts = pr_items ~bullet:"  -" (pr_lemma_template ~typ:false)
let pr_lmtss = pr_items ~bullet:"  #" pr_lmts
let pr_clm = pr_counter_lemma
let pr_ddf = pr_data_defn
let pr_vdf = pr_view_defn ~typ:false ~paren:false
let pr_vdfs = pr_items ~bullet:"  #" pr_vdf
let pr_vdc = pr_view_defn_case
let pr_vdcs = pr_items ~bullet:"  #" pr_vdc
let pr_pdefn = pr_pred_defn
let pr_pdefns = pr_items ~bullet:"  #" pr_pdefn
let pr_prog = pr_program ~typ:false ~paren:false

(************************************************************************)
(***************         function with variable         *****************)

let name_of_var v = fst v

let rec eq_var v1 v2 =
  DB.trace_2 "eq_var" (pr_v, pr_v, pr_bool) v1 v2
    (fun () -> eq_var_x v1 v2)

and eq_var_x v1 v2 =
  let vname1, vname2 = fst v1, fst v2 in
  (eq_s vname1 vname2)

(** compare two var by their name *)
let compare_var v1 v2 =
  let vname1, vname2 = fst v1, fst v2 in
  String.compare vname1 vname2

let mem_vs v vs = List.exists (fun x -> eq_var v x) vs

let subset_vs vs1 vs2 =
  vs1 |> List.for_all (fun v -> mem_vs v vs2)

let equiv_vs vs1 vs2 =
  (subset_vs vs1 vs2) && (subset_vs vs2 vs1)

let disjoint_vs vs1 vs2 =
  vs1 |> List.for_all (fun v -> not (mem_vs v vs2))

let diff_vs vs1 vs2 =
  vs1 |> List.filter (fun x -> List.for_all (fun y -> not (eq_var x y)) vs2)

let intersect_vs vs1 vs2 =
  vs1 |> List.filter (fun x -> List.exists (fun y -> eq_var x y) vs2)

let union_vs vs1 vs2 =
  vs1 |> List.fold_left (fun acc x ->
    if List.exists (eq_var x) acc then acc else acc @ [x]) vs2

let intersected_vs vs1 vs2 =
  List.length (intersect_vs vs1 vs2) > 0

let check_dup_vs vs =
  let rec do_check acc vs = match vs with
    | [] -> true
    | v::vs -> if (mem_vs v acc) then true else do_check (v::acc) vs in
  do_check [] vs

let dedup_vs vs = List.fold_left (fun acc x ->
  if (mem_vs x acc) then acc
  else acc @ [x]) [] vs

(************************************************************************)
(***************         function with functions        *****************)

let eq_func f1 f2 =
  match f1, f2 with
  | Max, Max -> true
  | Min, Min -> true
  | Abs, Abs -> true
  | _ -> false

let mem_funcs f fs = List.exists (fun x -> eq_func x f) fs

let dedup_funcs fs = List.fold_left (fun acc x ->
  if (mem_funcs x acc) then acc
  else acc @ [x]) [] fs


(***************     comparison     ***************)

let eq_lterm lt1 lt2 =
  let (cvs1, i1), (cvs2, i2) = lt1, lt2 in
  if (i1 != i2) then false
  else if (List.length cvs1 != List.length cvs2) then false
  else
    List.for_all2 (fun (c1, v1) (c2, v2) ->
      (c1 = c2) && (eq_var v1 v2)) cvs1 cvs2


(* syntactically compare two expression *)
let rec eq_exp e1 e2 = match e1, e2 with
  | Null _, Null _ -> true
  | Var (v1, _), Var (v2, _) -> eq_var v1 v2
  | LTerm (lt1, _), LTerm (lt2, _) -> eq_lterm lt1 lt2
  | IConst (i1, _), IConst (i2, _) -> i1 = i2
  | BinOp (Add, e11, e12, _), BinOp (Add, e21, e22, _)
  | BinOp (Mul, e11, e12, _), BinOp (Mul, e21, e22, _) ->
    ((eq_exp e11 e21) && (eq_exp e12 e22)) ||
    ((eq_exp e11 e22) && (eq_exp e12 e21))
  | BinOp (Sub, e11, e12, _), BinOp (Sub, e21, e22, _)
  | BinOp (Div, e11, e12, _), BinOp (Div, e21, e22, _) ->
    (eq_exp e11 e21) && (eq_exp e12 e22)
  | _ -> false

let eq_exp_pair (e11, e12) (e21, e22) =
  (eq_exp e11 e21) && (eq_exp e12 e22)

let mem_exps e es = List.exists (fun x -> eq_exp x e) es

let diff_exps es1 es2 =
  List.filter (fun x -> List.for_all (fun y -> not (eq_exp x y)) es2) es1

let compare_exp e1 e2 =
  let se1, se2 = pr_exp e1, pr_exp e2 in
  String.compare se1 se2

let compare_df df1 df2 =
  try
    let cmp_name = String.compare df1.dataf_name df2.dataf_name in
    if (cmp_name != 0) then raise (EInt cmp_name);
    let cmp_root = compare_exp df1.dataf_root df2.dataf_root in
    if (cmp_root != 0) then raise (EInt cmp_root);
    List.iter2 (fun x y ->
      let cmp_arg = compare_exp x y in
      if (cmp_arg != 0) then raise (EInt cmp_arg);
    ) df1.dataf_args df2.dataf_args;
    (* otherwise, they are equal *)
    0
  with EInt res -> res

let compare_vf vf1 vf2 =
  try
    let cmp_name = String.compare vf1.viewf_name vf2.viewf_name in
    if (cmp_name != 0) then raise (EInt cmp_name);
    List.iter2 (fun x y ->
      let cmp_arg = compare_exp x y in
      if (cmp_arg != 0) then raise (EInt cmp_arg);
    ) vf1.viewf_args vf2.viewf_args;
    (* otherwise, they are equal *)
    0
  with EInt res -> res

let compare_ha ha1 ha2 = match ha1, ha2 with
  | HData df1, HData df2 -> compare_df df1 df2
  | HData _, HView _ -> 1
  | HView _, HData _ -> -1
  | HView vf1, HView vf2 -> compare_vf vf1 vf2

let eq_df df1 df2 = (compare_df df1 df2) = 0

let eq_vf vf1 vf2 = (compare_vf vf1 vf2) = 0

let eq_hatom hf1 hf2 = match hf1, hf2 with
  | HData df1, HData df2 -> eq_df df1 df2
  | HView vf1, HView vf2 -> eq_vf vf1 vf2
  | _ -> false

let mem_vfs vf vfs = List.exists (eq_vf vf) vfs

let mem_dfs df dfs = List.exists (eq_df df) dfs

(************************************************************************)
(***************       function with substitution       *****************)

let eq_sst sst1 sst2 =
  let (v1, e1), (v2, e2) = sst1, sst2 in
  (eq_var v1 v2) && (eq_exp e1 e2)

let compare_sst sst1 sst2 =
  let (v1, e1), (v2, e2) = sst1, sst2 in
  let cmp1 = compare_var v1 v2 in
  if (cmp1 != 0) then cmp1
  else compare_exp e1 e2

let mem_ssts sst ssts = List.exists (fun x -> eq_sst x sst) ssts

let eq_ssts ssts1 ssts2 =
  (List.for_all (fun x -> mem_ssts x ssts2) ssts1)
  && (List.for_all (fun x -> mem_ssts x ssts1) ssts2)

let subset_sstss ssts sstss = List.exists (fun x -> eq_ssts x ssts) sstss

let dedup_sstss sstss = List.fold_left (fun acc x ->
  if (subset_sstss x acc) then acc
  else acc @ [x]) [] sstss


(***************   get free vars  *****************)

let fv_lterm t = (fst t) |> List.map snd |> dedup_vs

let rec fv_exp exp = match exp with
  | Null _ | IConst _ -> []
  | Var (v, p) -> [v]
  | LTerm (t, _) -> fv_lterm t
  | BinOp (op, e1, e2, p) -> [e1; e2] |> fv_exps |> dedup_vs
  | Func (_, es, _) -> es |> fv_exps |> dedup_vs

and fv_exps exps =
  exps |> List.map fv_exp |> List.concat |> dedup_vs

let fv_rf rel = rel.prel_args |> fv_exps |> dedup_vs

let fv_rfs rfs =
  rfs |> List.map fv_rf |> List.concat |> dedup_vs

let rec fv_pf f =
  DB.trace_1 "fv_pf" (pr_pf, pr_vs) f
    (fun () -> fv_pf_x f)

and fv_pf_x f =
  let rec fv f = match f with
    | BConst _ -> []
    | BinRel (rel, e1, e2, p) -> [e1; e2] |> fv_exps |> dedup_vs
    | PRel rel -> fv_rf rel
    | PNeg (g, p) -> g |> fv |> dedup_vs
    | PConj (gs, p)
    | PDisj (gs, p) -> gs |> List.map fv |> List.concat |> dedup_vs
    | PForall (vs, g, p)
    | PExists (vs, g, p) -> diff_vs (fv g) vs |> dedup_vs in
  fv f

let fv_pfs pfs = pfs |> List.map fv_pf |> List.concat |> dedup_vs

let fv_df (df: data_form) =
  (df.dataf_root::df.dataf_args) |> fv_exps |> dedup_vs

let fv_dfs dfs = dfs |> List.map fv_df |> List.concat |> dedup_vs

let fv_vf (vf: view_form) =
  vf.viewf_args |> fv_exps |> dedup_vs

let fv_ha (ha: heap_atom) =
  match ha with
  | HData df -> fv_df df
  | HView vf -> fv_vf vf

let fv_has has =
  has |> List.map fv_ha |> List.concat |> dedup_vs

let rec fv_hf f = match f with
  | HEmp _ -> []
  | HAtom (dfs, vfs, _) ->
    let vs1 = dfs |> List.map fv_df |> List.concat |> dedup_vs in
    let vs2 = vfs |> List.map fv_vf |> List.concat |> dedup_vs in
    dedup_vs (vs1 @ vs2)
  | HStar (g1, g2, p)
  | HWand (g1, g2, p) ->
    [g1; g2] |> List.map fv_hf |> List.concat |> dedup_vs

let fv_hfs fs = fs |> List.map fv_hf |> List.concat |> dedup_vs

let rec fv f = SBDebug.trace_1 "fv" (pr_f, pr_vs) f (fun () -> fv_x f)

and fv_x = function
  | FBase (hg, pg, p) -> (fv_hf hg) @ (fv_pf pg) |> dedup_vs
  | FExists (vs, g, p)
  | FForall (vs, g, p) -> (diff_vs (fv_x g) vs) |> dedup_vs

let fv_fs fs = fs |> List.map fv |> List.concat |> dedup_vs

let fv_ent ent =
  ((fv ent.ent_lhs) @ (fv ent.ent_rhs)) |> dedup_vs

let fhv f =
  let rec aux g = match g with
    | FBase (hg, pg, p) -> (fv_hf hg) |> dedup_vs
    | FExists (vs, g, p)
    | FForall (vs, g, p) -> (diff_vs (aux g) vs) |> dedup_vs in
  aux f

let fhv_fs fs =
  fs |> List.map fhv |> List.concat |> dedup_vs

let fhv_ent ent =
  ((fhv ent.ent_lhs) @ (fhv ent.ent_rhs)) |> dedup_vs


(***************   get all vars  *****************)

let rec av_exp exp = match exp with
  | Null _ | IConst _ -> []
  | Var (v, p) -> [v]
  | LTerm (t, _) -> (fst t) |> List.map snd |> dedup_vs
  | BinOp (op, e1, e2, p) -> [e1; e2] |> av_exps |> dedup_vs
  | Func (_, es, _) -> es |> fv_exps |> dedup_vs

and av_exps exps =
  exps |> List.map av_exp |> List.concat |> dedup_vs

let rec av_pf f = match f with
  | BConst _ -> []
  | BinRel (rel, e1, e2, _) ->
    [e1; e2] |> av_exps |> dedup_vs
  | PRel rel ->
    rel.prel_args |> av_exps |> dedup_vs
  | PNeg (g, p) -> dedup_vs (av_pf g)
  | PConj (gs, _)
  | PDisj (gs, _) ->
    gs |> List.map av_pf |> List.concat |> dedup_vs
  | PForall (vs, g, _)
  | PExists (vs, g, _) ->
    (vs @ (av_pf g)) |> dedup_vs

let av_df (df: data_form) = av_exps (df.dataf_root::df.dataf_args)

let av_vf (vf: view_form) = av_exps vf.viewf_args

let rec av_hf f = match f with
  | HEmp _ -> []
  | HAtom (dfs, vfs, _) ->
    let vs1 = dfs |> List.map av_df |> List.concat |> dedup_vs in
    let vs2 = vfs |> List.map av_vf |> List.concat |> dedup_vs in
    (vs1 @ vs2) |> dedup_vs
  | HStar (g1, g2, p)
  | HWand (g1, g2, p) ->
    (av_hf g1) @ (av_hf g2) |> dedup_vs

let rec av f =
  DB.trace_1 "av" (pr_f, pr_vs) f (fun () -> av_x f)

and av_x = function
  | FBase (hg, pg, p) ->
    ((av_hf hg) @ (av_pf pg)) |> dedup_vs
  | FExists (vs, g, p)
  | FForall (vs, g, p) -> (vs @ (av_x g)) |> dedup_vs

let av_rel rel =
  let vs1 = rel.rel_params in
  let vs2 = match rel.rel_body with
    | RbForm pf -> av_pf pf
    | RbTemplate rbt -> av_pf rbt.templ_body
    | _ -> [] in
  (vs1 @ vs2) |> dedup_vs

let av_vdef vd =
  let vs1 = vd.view_params in
  let vs2 = vd.view_defn_cases |> List.map (fun vdc -> av vdc.vdc_form) |>
            List.concat |> dedup_vs in
  (vs1 @ vs2) |> dedup_vs

let av_ent e = ((av e.ent_lhs) @ (av e.ent_rhs)) |> dedup_vs

let av_cmd = function
  | CheckEntail (e, _) -> av_ent e
  | CheckSat (f, _) -> av f
  | InferLemma (e, _) -> av_ent e
  | InferEntail e -> av_ent e
  | InferRels _ -> error "av_cmd: handle later"
  | Process f -> av f
  | ProcessTwo (f1, f2) -> ((av f1) @ (av f2)) |> dedup_vs
  | CmdUnkn -> []

let av_lm lm = ((av lm.lm_lhs) @ (av lm.lm_rhs)) |> dedup_vs

let av_prog p =
  let vs1 = p.prog_lemmas |> List.map av_lm |> List.concat |> dedup_vs in
  let vs2 = p.prog_commands |> List.map av_cmd |> List.concat |> dedup_vs in
  let vs3 = p.prog_views |> List.map av_vdef |> List.concat |> dedup_vs in
  let vs4 = p.prog_rels |> List.map av_rel |> List.concat |> dedup_vs in
  (vs1 @ vs2 @ vs3 @ vs4) |> dedup_vs

let ahv f =
  let rec aux g = match g with
    | FBase (hg, pg, p) -> (av_hf hg) |> dedup_vs
    | FExists (vs, g, p)
    | FForall (vs, g, p) -> (aux g) |> dedup_vs in
  aux f

let ahv_fs fs =
  fs |> List.map ahv |> List.concat |> dedup_vs

let ahv_ent ent =
  ((ahv ent.ent_lhs) @ (ahv ent.ent_rhs)) |> dedup_vs

(***************   get free function  *****************)

let rec ff_exp exp = match exp with
  | Null _ | IConst _ | Var _ | LTerm _ -> []
  | BinOp (op, e1, e2, p) -> [e1; e2] |> ff_exps |> dedup_funcs
  | Func (f, es, _) -> (f::(ff_exps es)) |> dedup_funcs

and ff_exps exps = exps |> List.map ff_exp |> List.concat |> dedup_funcs

let rec ff_pf f =
  DB.trace_1 "ff_pf" (pr_pf, pr_funcs) f
    (fun () -> ff_pf_x f)

and ff_pf_x f =
  let rec ff f = match f with
    | BConst _ -> []
    | BinRel (rel, e1, e2, p) -> [e1; e2] |> ff_exps |> dedup_funcs
    | PRel rel -> rel.prel_args |> ff_exps |> dedup_funcs
    | PNeg (g, p) -> g |> ff |> dedup_funcs
    | PConj (gs, p)
    | PDisj (gs, p) -> gs |> List.map ff |> List.concat |> dedup_funcs
    | PForall (vs, g, p)
    | PExists (vs, g, p) -> g |> ff |> dedup_funcs in
  ff f

let ff_df (df: data_form) =
  (df.dataf_root::df.dataf_args) |> ff_exps |> dedup_funcs

let ff_vf (vf: view_form) =
  vf.viewf_args |> ff_exps |> dedup_funcs

let rec ff_hf f = match f with
  | HEmp _ -> []
  | HAtom (dfs, vfs, _) ->
    let vs1 = dfs |> List.map ff_df |> List.concat |> dedup_funcs in
    let vs2 = vfs |> List.map ff_vf |> List.concat |> dedup_funcs in
    dedup_funcs (vs1 @ vs2)
  | HStar (g1, g2, p)
  | HWand (g1, g2, p) ->
    [g1; g2] |> List.map ff_hf |> List.concat |> dedup_funcs

let rec ff f = SBDebug.trace_1 "ff" (pr_f, pr_funcs) f (fun () -> ff_x f)

and ff_x = function
  | FBase (hg, pg, p) -> (ff_hf hg) @ (ff_pf pg) |> dedup_funcs
  | FExists (vs, g, p)
  | FForall (vs, g, p) -> g |> ff_x |> dedup_funcs

(*****************************************************)
(******************    position    *******************)

let pos_of_exp = function
  | Null p -> p
  | Var (_, p) -> p
  | IConst (_, p) -> p
  | LTerm (_, p) -> p
  | BinOp (_, _, _, p) -> p
  | Func (_, _, p) -> p

let pos_of_pf = function
  | BConst (_, p) -> p
  | BinRel (_, _, _, p) -> p
  | PRel rel -> rel.prel_pos
  | PNeg (_, p) -> p
  | PConj (_, p) -> p
  | PDisj (_, p) -> p
  | PForall (_, _, p) -> p
  | PExists (_, _, p) -> p

let pos_of_ha = function
  | HData df -> df.dataf_pos
  | HView vf -> vf.viewf_pos

let pos_of_hf = function
  | HEmp p -> p
  | HAtom (_, _, p) -> p
  | HStar (_, _, p) -> p
  | HWand (_, _, p) -> p

let pos_of_f = function
  | FBase (_, _, p) -> p
  | FExists (_, _, p) -> p
  | FForall (_, _, p) -> p

let update_pos_exp e p = match e with
  | Null _ -> Null p
  | Var (v, _) -> Var (v, p)
  | IConst (i, _) -> IConst (i, p)
  | LTerm (t, _) -> LTerm (t, p)
  | BinOp (op, e1, e2, _) -> BinOp (op, e1, e2, p)
  | Func (f, es, _) -> Func (f, es, p)

(***************   type   *****************)

let typ_of_var var = snd var

let typ_of_exp = function
  | Null _ -> TNull
  | Var (v, _) -> typ_of_var v
  | IConst _ -> TInt
  | LTerm _ -> TInt
  | BinOp (Add, _, _, _) -> TInt
  | BinOp (Sub, _, _, _) -> TInt
  | BinOp (Mul, _, _, _) -> TInt
  | BinOp (Div, _, _, _) -> TInt
  | Func (Max, _, _) -> TInt
  | Func (Min, _, _) -> TInt
  | Func (Abs, _, _) -> TInt

let typs_of_rdefn rdefn =
  match rdefn.rel_body with
  | RbForm pf -> fv_pf pf |> List.map typ_of_var |> dedup_ts
  | _ -> rdefn.rel_params |> List.map typ_of_var |> dedup_ts

let typ_of_data_form data = TData data.dataf_name

let typ_of_dform = typ_of_data_form

let typ_of_data_defn data = TData data.datad_name

let typ_of_ddefn = typ_of_data_defn

let is_ptr_typ typ = match typ with
  | TNull | TData _ -> true
  | _ -> false

let is_ptr_var var =
  var |> typ_of_var |> is_ptr_typ

let is_int_var var = (typ_of_var var = TInt)

(******************)
(*** expression ***)

let mk_var (name: string) (ty: typ) = (name, ty)

let mk_null pos = Null pos

let mk_exp_var ?(pos=no_pos) v = Var (v, pos)

let mk_iconst ?(pos=no_pos) i = IConst (i, pos)

let mk_add_lterm (t1: lterm) (t2: lterm) : lterm =
  let rec sum t1 t2 = match t1, t2 with
    | ([], i1), ([], i2) -> ([], i1 + i2)
    | (k, i1), ([], i2) -> (k, i1 + i2)
    | ([], i1), (k, i2) -> (k, i1 + i2)
    | ((c1, v1) :: k1, i1), ((c2, v2) :: k2, i2) ->
      if (compare_var v1 v2 = 0) then
        let (k, i) = sum (k1, i1) (k2, i2) in
        if (c1 + c2 = 0) then (k, i)
        else ((c1 + c2, v1) :: k, i)
      else if (compare_var v1 v2 < 0) then
        let (k, i) = sum (k1, i1) ((c2, v2) :: k2, i2) in
        ((c1, v1) :: k, i)
      else
        let (k, i) = sum ((c1, v1) :: k1, i1) (k2, i2) in
        ((c2, v2) :: k, i) in
  sum t1 t2

let mk_mult_lterm (c: int) (t: lterm) : lterm =
  if (c = 0) then ([], 0)
  else
    let (k, i) = t in
    let nk = List.map (fun (t, v) -> (t * c, v)) k in
    (nk, c * i)

let mk_subt_lterm (t1: lterm) (t2: lterm) : lterm =
  let nt2 = mk_mult_lterm (-1) t2 in
  mk_add_lterm t1 nt2

(** convert an exp to a linear arithmetic term and an inconvertible expression*)
let rec convert_exp_to_lterm (e: exp) : lterm * (exp option) =
  let pr_res (x, y) = (pr_lterm x) ^ ", " ^ (pr_opt pr_exp y) in
  DB.trace_1 "convert_exp_to_lterm" (pr_e, pr_res) e
    (fun () -> convert_exp_to_lterm_x e)

and convert_exp_to_lterm_x (e: exp) : lterm * (exp option) =
  let rec convert e = match e with
    | IConst (i, _) -> (([], i), None)
    (* | Var (v, _) when (typ_of_var v) = TInt -> (([(1, v)], 0), None) *)
    | Var (v, _) -> (([(1, v)], 0), None)
    | LTerm (t, _) -> (t, None)
    | BinOp (Add, e1, e2, p) ->
      let ((k1, i1), e1o) = convert e1 in
      let ((k2, i2), e2o) = convert e2 in
      let nt = mk_add_lterm (k1, i1) (k2, i2) in
      let neo = match e1o, e2o with
        | None,_ -> e2o
        | _,None -> e1o
        | Some ue1o, Some ue2o -> Some (BinOp (Add, ue1o, ue2o, p)) in
      (nt, neo)
    | BinOp (Sub, e1, e2, p) ->
      let ((k1, i1), o1) = convert e1 in
      let ((k2, i2), o2) = convert e2 in
      let nt = mk_subt_lterm (k1, i1) (k2, i2) in
      let neo = match o1, o2 with
        | None, None -> None
        | None, Some x2 -> Some (BinOp (Sub, mk_iconst 0, x2, p))
        | Some _, None -> o1
        | Some x1, Some x2 -> Some (BinOp (Sub, x1, x2, p)) in
      (nt, neo)
    | BinOp (Mul, e1, e2, p) ->
      let ((k1, i1), o1) = convert e1 in
      let ((k2, i2), o2) = convert e2 in
      if (k1 = [] && o1 = None) then
        let nt = mk_mult_lterm i1 (k2, i2) in
        let ne = match o2 with
          | None -> None
          | Some x2 ->
            if (i1 = 0) then None
            else if (i1 = 1) then o2
            else Some (BinOp (Mul, mk_iconst i1, x2, p)) in
        (nt,ne)
      else if (k2 = [] && o2 = None) then
        let nt = mk_mult_lterm i2 (k1, i1) in
        let ne = match o1 with
          | None -> None
          | Some x1 ->
            if (i2 = 0) then None
            else if (i2 = 1) then o1
            else Some (BinOp (Mul, mk_iconst i2, x1, p)) in
        (nt,ne)
      else (([], 0), Some e)
    | _ -> (([], 0), Some e) in
  convert e

let mk_lterm_exp ?(pos=no_pos) lterm =
  let (cvs, i) = lterm in
  if (i != 0) then LTerm (lterm, pos)
  else match cvs with
    | [(1, v)] -> mk_exp_var v ~pos:pos
    | _ -> LTerm (lterm, pos)

let rec mk_bin_op ?(pos=no_pos) op e1 e2 =
  DB.trace_3 "mk_bin_op" (pr_bin_op, pr_e, pr_e, pr_e) op e1 e2
    (fun () -> mk_bin_op_x op e1 e2 ~pos:pos)

and mk_bin_op_x ?(pos=no_pos) op e1 e2 =
  let res = match op with
    | Add -> (
        let t1, neo1 = convert_exp_to_lterm e1 in
        let t2, neo2 = convert_exp_to_lterm e2 in
        let ne = mk_lterm_exp (mk_add_lterm t1 t2) ~pos:pos in
        match neo1, neo2 with
        | None, None -> ne
        | None, Some x -> BinOp (Add, ne, x, pos)
        | Some x, None -> BinOp (Add, ne, x, pos)
        | Some x, Some y -> BinOp (Add, ne, BinOp (Add, x, y, pos), pos))
    | Sub -> (
        let t1, neo1 = convert_exp_to_lterm e1 in
        let t2, neo2 = convert_exp_to_lterm e2 in
        let ne = mk_lterm_exp (mk_subt_lterm t1 t2) ~pos:pos in
        match neo1, neo2 with
        | None, None -> ne
        | None, Some x -> BinOp (Sub, ne, x, pos)
        | Some x, None -> BinOp (Add, ne, x, pos)
        | Some x, Some y -> BinOp (Add, ne, BinOp (Sub, x, y, pos), pos))
    | Mul -> (
        let t1, neo1 = convert_exp_to_lterm e1 in
        let t2, neo2 = convert_exp_to_lterm e2 in
        let p1, p2 = pos_of_exp e1, pos_of_exp e2 in
        let net1, net2 = mk_lterm_exp t1 ~pos:p1, mk_lterm_exp t2 ~pos:p2 in
        match neo1, neo2 with
        | None, None -> (match t1, t2 with
          | ([], i1), _ -> mk_lterm_exp (mk_mult_lterm i1 t2) ~pos:pos
          | _, ([], i2) -> mk_lterm_exp (mk_mult_lterm i2 t1) ~pos:pos
          | _ -> BinOp (Mul, LTerm (t1, p1), LTerm (t2, p2), pos))
        | None, Some x -> BinOp (Mul, net1, BinOp (Add, net2, x, p2), pos)
        | Some x, None -> BinOp (Mul, BinOp (Add, net1, x, p1), net2, pos)
        | Some x, Some y ->
          BinOp (Mul, BinOp (Add, net1, x, p1), BinOp (Add, net2, x, p2), pos))
    | Div -> (
        match e2 with
        | IConst (1, _) -> e1
        | IConst (-1, _) -> mk_bin_op Mul e1 e2 ~pos:pos
        | IConst (0, _) ->
          error ("mk_bin_op: Div by 0: e1" ^ (pr_e e1) ^ ", e2: " ^ (pr_e e2))
        | _ -> BinOp (Div, e1, e2, pos)) in
  match res with
  | LTerm (([(1, v)], 0), _) -> mk_exp_var v
  | _ -> res

let mk_func ?(pos=no_pos) func args = Func (func, args, pos)

let mk_abs ?(pos=no_pos) (e: exp) = mk_func ~pos:pos Abs [e]

let mk_abs_var ?(pos=no_pos) (v: var) = mk_abs ~pos:pos (mk_exp_var ~pos:pos v)

(***************   queries   *****************)

let is_zero_lterm (vs, i) = (vs == []) && (i == 0)

let is_iconst_exp = function
  | IConst _ -> true
  | LTerm (([], _), _) -> true
  | _ -> false

let rec is_const_exp = function
  | Null _ -> true
  | IConst _ -> true
  | LTerm (([], _), _) -> true
  | BinOp (_, e1, e2, _) -> (is_const_exp e1) && (is_const_exp e2)
  | _ -> false

let is_var_exp = function Var _ -> true | _ -> false

let is_int_exp e = (typ_of_exp e) = TInt

let zero = mk_iconst 0

let one = mk_iconst 1

let rec is_zero_exp = function
    IConst (0, _) -> true
  | LTerm (t, _) -> is_zero_lterm t
  | BinOp (op, e1, e2, _) -> (match op with
    | Add | Sub -> (is_zero_exp e1) && (is_zero_exp e2)
    | Mul -> (is_zero_exp e1) || (is_zero_exp e2)
    | Div -> (is_zero_exp e1))
  | _ -> false

let is_positive_exp = function
  | IConst (i, _) | LTerm (([], i), _) -> i > 0
  | _ -> false

let is_negative_exp = function
  | IConst (i, _) | LTerm (([], i), _) -> i<0
  | _ -> false

let is_non_zero_exp = function
  | IConst (i, _) | LTerm (([], i), _) -> i!=0
  | _ -> false

let is_non_positive_exp = function
  | IConst (i, _) | LTerm (([], i), _) -> i<=0
  | _ -> false

let is_non_negative_exp = function
  | IConst (i, _) | LTerm (([], i), _) -> i>=0
  | _ -> false

let is_null_exp = function
  | Null _ -> true
  | _ -> false

let rec is_true_pf = function
  | BConst (true, _) -> true
  | BConst (false, _) | BinRel _ | PRel _ -> false
  | PNeg (g, _) -> is_false_pf g
  | PConj (gs, _) -> List.for_all is_true_pf gs
  | PDisj (gs, _) -> List.exists is_true_pf gs
  | PForall (_, g, _) | PExists (_, g, _) -> is_true_pf g

and is_false_pf = function
  | BConst (false, _) -> true
  | BConst (true, _) | BinRel _ | PRel _  -> false
  | PNeg (g, _) -> is_true_pf g
  | PConj (gs, _) -> List.exists is_false_pf gs
  | PDisj (gs, _) -> List.for_all is_false_pf gs
  | PForall (_, g, _) | PExists (_, g, _) -> is_false_pf g

let is_patom pf = match pf with
  | BConst _ | BinRel _ | PRel _ -> true
  | _ -> false

(* TODO: need to improve more *)
let eq_patom f1 f2 =
  let normalize_bin_rel g = match g with
    | BinRel (Lt, e1, e2, p) ->
      BinRel (Lt, mk_bin_op Sub e1 e2, zero, p)
    | BinRel (Le, e1, e2, p) ->
      BinRel (Lt, mk_bin_op Sub (mk_bin_op Sub e1 e2) one, zero, p)
    | BinRel (Gt, e1, e2, p) ->
      BinRel (Lt, mk_bin_op Sub e2 e1, zero, p)
    | BinRel (Ge, e1, e2, p) ->
      BinRel (Lt, mk_bin_op Sub (mk_bin_op Sub e2 e1) one, zero, p)
    | _ -> g in
  let f1, f2 = Pair.fold normalize_bin_rel f1 f2 in
  match f1, f2 with
  | PNeg _, _ | PConj _, _ | PDisj _, _ | PForall _, _ | PExists _, _
  | _, PNeg _ | _, PConj _ | _, PDisj _ | _, PForall _ | _, PExists _ -> false
  | BConst (b1, _), BConst (b2, _) -> b1 = b2
  | BinRel (Eq, e11, e12, _), BinRel (Eq, e21, e22, _)
  | BinRel (Ne, e11, e12, _), BinRel (Ne, e21, e22, _) ->
    if (is_int_exp e11) then
      let e1 = mk_bin_op Sub e11 e12 in
      let e2 = mk_bin_op Sub e21 e22 in
      eq_exp e1 e2
    else
      ((eq_exp e11 e21) && (eq_exp e12 e22)) ||
      ((eq_exp e11 e22) && (eq_exp e12 e21))
  | BinRel (Lt, e1, _, _), BinRel (Lt, e2, _, _) -> eq_exp e1 e2
  | PRel r1, PRel r2 ->
    (eq_s r1.prel_name r2.prel_name) &&
    (List.length r1.prel_args = List.length r2.prel_args) &&
    (List.for_all2 eq_exp r1.prel_args r2.prel_args)
  | _ -> false

(* check if the rel_form rf is an instance of the rel_defn rdefn *)
let is_rf_instance rf rdefn = eq_s rf.prel_name rdefn.rel_name

let is_rform_pf pf = match pf with
  | PRel _ -> true
  | _ -> false

let is_unk_rdefn rel =
  match rel.rel_body with
  | RbUnknown -> true
  | _ -> false

let is_known_rdefn rel =
  match rel.rel_body with
  | RbForm _ -> true
  | _ -> false

let is_template_rdefn rel =
  match rel.rel_body with
  | RbTemplate _ -> true
  | _ -> false

let get_rel_body rel =
  match rel.rel_body with
  | RbForm f -> f
  | RbTemplate tmpl -> tmpl.templ_body
  | RbUnknown -> error "get_rel_body: unknown definition"

let is_hatom_df = function HData _ -> true | _ -> false

let is_hatom_vf = function HView _ -> true | _ -> false

let rec is_emp_hf = function
  | HEmp _ -> true
  | HAtom (dfs, vfs, _) -> (dfs = []) && (vfs = [])
  | HStar (h1, h2, _)
  | HWand (h1, h2, _) -> (is_emp_hf h1) && (is_emp_hf h2)

let is_false_hf h =
  let rec check_overlaid_datas acc = function
    | [] -> (false, [])
    | x::xs ->
      if (mem_exps x.dataf_root acc) then (true, [])
      else check_overlaid_datas (x.dataf_root :: acc) xs in
  let rec check_false h = match h with
    | HEmp _ | HWand _ -> false
    | HAtom (dfs, _, _) -> fst (check_overlaid_datas [] dfs)
    | HStar (HAtom _, _, _) | HStar (_, HAtom _, _) ->
      error ("is_false_hf: not expect HAtom inside HStar: " ^ (pr_hf h))
    | HStar (h1, h2, _) -> (check_false h1) || (check_false h2) in
  check_false h

let is_hatom_same_type ha1 ha2 = match ha1, ha2 with
  | HData df1, HData df2 -> eq_s df1.dataf_name df2.dataf_name
  | HView vf1, HView vf2 -> eq_s vf1.viewf_name vf2.viewf_name
  | _ -> false

let rec is_pure_f = function
  | FBase (h, p, _) -> (is_emp_hf h)
  | FExists (_, f, _) | FForall (_, f, _) -> (is_pure_f f)

let rec is_false_f = function
  | FBase (h, p, _) -> (is_false_pf p) || (is_false_hf h)
  | FExists (_, f, _) | FForall (_, f, _) -> is_false_f f

let is_same_type_df df1 df2 = eq_s df1.dataf_name df2.dataf_name

let is_same_root_df df1 df2 = eq_exp df1.dataf_root df2.dataf_root

let is_common_args_df df1 df2 =
  if not (eq_s df1.dataf_name df2.dataf_name) then false
  else List.exists2 eq_exp df1.dataf_args df2.dataf_args

let is_same_type_vf vf1 vf2 = eq_s vf1.viewf_name vf2.viewf_name

let is_vf_instance vf vdefn = eq_s vf.viewf_name vdefn.view_name

let is_common_args_vf vf1 vf2 =
  if not (eq_s vf1.viewf_name vf2.viewf_name) then false
  else List.exists2 eq_exp vf1.viewf_args vf2.viewf_args

let rec has_emp_hf = function
  | HEmp _ -> true
  | HAtom (dfs, vfs, _) -> (dfs = []) && (vfs = [])
  | HStar (h1, h2, _)
  | HWand (h1, h2, _) -> (has_emp_hf h1) || (has_emp_hf h2)

let rec has_data_hf = function
  | HEmp _
  | HAtom ([], _, _) -> false
  | HAtom (_, _, _) -> true
  | HStar (h1, h2, _) -> (has_data_hf h1) ||  (has_data_hf h2)
  | HWand _ -> error "has_data_hf: handle Wand later"

let rec has_view_hf = function
  | HEmp _
  | HAtom (_, [], _) -> false
  | HAtom (_, _, _) -> true
  | HStar (h1, h2, _) -> (has_view_hf h1) ||  (has_view_hf h2)
  | HWand _ -> error "has_view_hf: handle Wand later"

let rec has_emp_f = function
  | FBase (h, p, _) -> has_emp_hf h
  | FExists (_, g, _) | FForall (_, g, _) -> has_emp_f g

let rec has_data_f = function
  | FBase (h, p, _) -> has_data_hf h
  | FExists (_, g, _) | FForall (_, g, _) -> has_data_f g

let rec has_view_f = function
  | FBase (h, p, _) -> has_view_hf h
  | FExists (_, g, _) | FForall (_, g, _) -> has_view_f g

let has_int_arg_vf vf =
  List.exists (fun e -> (typ_of_exp e) = TInt) vf.viewf_args

let has_const_arg_vf vf =
  List.exists (is_const_exp) vf.viewf_args

let has_int_const_arg_vf vf =
  List.exists (fun e -> (is_const_exp e) && (is_int_exp e)) vf.viewf_args

let has_const_arg_df df =
  List.exists (is_const_exp) df.dataf_args

let rec has_int_operator_exp = function
  | Null _ | IConst _ -> false
  | LTerm (([], _), _) | LTerm (([_], 0), _) -> false
  | LTerm _ -> true
  | BinOp (_, e1, e2, _) -> true
  | _ -> false

(********************)
(*** pure formula ***)

let mk_true pos = BConst (true, pos)

let mk_false pos = BConst (false, pos)

let mk_bconst ?(pos=no_pos) b = BConst (b, pos)

let mk_bin_rel ?(norm=true) ?(pos=no_pos) rel e1 e2 =
  match rel with
  | Lt | Le -> BinRel (rel, e1, e2, pos)
  | Gt ->
    if norm then BinRel (Lt, e2, e1, pos)
    else BinRel (rel, e1, e2, pos)
  | Ge ->
    if norm then BinRel (Le, e2, e1, pos)
    else BinRel (rel, e1, e2, pos)
  | Ne | Eq -> BinRel (rel, e1, e2, pos)

let mk_rel_lt ?(norm=true) ?(pos=no_pos) e1 e2 =
  mk_bin_rel ~norm:norm ~pos:pos Lt e1 e2

let mk_rel_le ?(norm=true) ?(pos=no_pos) e1 e2 =
  mk_bin_rel ~norm:norm ~pos:pos Le e1 e2

let mk_rel_gt ?(norm=true) ?(pos=no_pos) e1 e2 =
  mk_bin_rel ~norm:norm ~pos:pos Gt e1 e2

let mk_rel_ge ?(norm=true) ?(pos=no_pos) e1 e2 =
  mk_bin_rel ~norm:norm ~pos:pos Ge e1 e2

let mk_rel_eq ?(norm=true) ?(pos=no_pos) e1 e2 =
  mk_bin_rel ~norm:norm ~pos:pos Eq e1 e2

let mk_rel_ne ?(norm=true) ?(pos=no_pos) e1 e2 =
  mk_bin_rel ~norm:norm ~pos:pos Ne e1 e2

let mk_rform ?(pos=no_pos) rel_name args =
  { prel_name = rel_name;
    prel_args = args;
    prel_pos = pos; }

let mk_prel prel = PRel prel


let mk_eq_exp ?(pos=no_pos) e1 e2 = mk_bin_rel Eq e1 e2 ~pos:pos

let mk_neq_exp ?(pos=no_pos) e1 e2 = mk_bin_rel Ne e1 e2 ~pos:pos

let mk_pneg ?(pos=no_pos) p =
  match p with
  | BConst (b, pos) -> BConst (not b, pos)
  | BinRel (Lt, e1, e2, p) -> BinRel (Ge, e1, e2, p)
  | BinRel (Le, e1, e2, p) -> BinRel (Gt, e1, e2, p)
  | BinRel (Eq, e1, e2, p) -> BinRel (Ne, e1, e2, p)
  | BinRel (Ne, e1, e2, p) -> BinRel (Eq, e1, e2, p)
  | BinRel (Ge, e1, e2, p) -> BinRel (Lt, e1, e2, p)
  | BinRel (Gt, e1, e2, p) -> BinRel (Le, e1, e2, p)
  | _ -> PNeg (p, pos)

let mk_eq_var ?(pos=no_pos) v1 v2 =
  mk_bin_rel Eq (mk_exp_var v1 ~pos:pos) (mk_exp_var v2 ~pos:pos) ~pos:pos

let mk_neq_var ?(pos=no_pos) v1 v2 =
  mk_bin_rel Ne (mk_exp_var v1 ~pos:pos) (mk_exp_var v2 ~pos:pos) ~pos:pos

let mk_neq_var_exp ?(pos=no_pos) v e =
  mk_bin_rel Ne (mk_exp_var v ~pos:pos) e ~pos:pos

let mk_eq_null ?(pos=no_pos) e = mk_eq_exp e (mk_null pos) ~pos:pos

let mk_eq_null_var ?(pos=no_pos) v =
  mk_eq_null (mk_exp_var v ~pos:pos) ~pos:pos

let mk_eq_iconst ?(pos=no_pos) e i =
  mk_eq_exp e (mk_iconst i) ~pos:pos

let mk_eq_iconst_var ?(pos=no_pos) v i =
  mk_eq_iconst (mk_exp_var v ~pos:pos) i ~pos:pos

let mk_neq_null ?(pos=no_pos) e =
  mk_pneg (mk_eq_exp e (mk_null pos) ~pos:pos) ~pos:pos

let mk_neq_null_var ?(pos=no_pos) v =
  mk_neq_null (mk_exp_var v ~pos:pos) ~pos:pos

let mk_neq_iconst ?(pos=no_pos) e i =
  mk_neq_exp e (mk_iconst i) ~pos:pos

let mk_neq_iconst_var ?(pos=no_pos) v i =
  mk_neq_iconst (mk_exp_var v ~pos:pos) i ~pos:pos

let combine_pfs_pf pfs pf = pfs @ [pf]

(** conjoin pure formulas and simplify the result *)
let rec mk_pconj ?(pos=no_pos) pfs =
  DB.trace_1 "mk_pconj"
    (pr_pfs, pr_pf) pfs
    (fun () -> mk_pconj_x pfs)

and mk_pconj_x ?(pos=no_pos) pfs =
  let rec merge_conj acc g = match acc with
    | None -> None
    | Some ps ->
      if is_true_pf g then acc
      else match g with
        | BConst (false, _) -> None
        | BinRel _ | PRel _ -> Some (combine_pfs_pf ps g)
        | PConj (gs, _) -> List.fold_left (fun x y -> merge_conj x y) acc gs
        | PDisj ([g], _) -> merge_conj acc g
        | _ -> Some (ps @ [g]) in
  let pfs = match pfs with
    | [] | _::[] -> Some pfs
    | g::gs ->
      let init_pfs = match (is_true_pf g), g with
        | true, _ -> []
        | _, PConj (gs0, _) -> gs0
        | _ -> [g] in
      List.fold_left (fun acc g -> merge_conj acc g) (Some init_pfs) gs in
  match pfs with
  | None -> BConst (false, pos)
  | Some [] -> BConst (true, pos)
  | Some [p] -> p
  | Some pfs -> PConj (pfs, pos)

let mk_pconj_rfs rfs =
  rfs |> List.map mk_prel |> mk_pconj

(** disjoin pure formulas and simplify the result *)
let rec mk_pdisj ?(pos=no_pos) pfs =
  DB.trace_1 "mk_pdisj" (pr_pfs, pr_pf) pfs
    (fun () -> mk_pdisj_x pfs)

and mk_pdisj_x ?(pos=no_pos) pfs =
  let rec merge_disj acc g = match acc with
    | None -> None
    | Some ps -> match g with
      | BConst (true, _) -> None
      | BConst (false, _) -> acc
      | BinRel _ | PRel _ -> Some (combine_pfs_pf ps g)
      | PConj ([g], _) -> merge_disj acc g
      | PConj _ -> Some (g :: ps)
      | PDisj (gs, _) -> List.fold_left (fun x y -> merge_disj x y) acc gs
      | PNeg _ | PForall _ | PExists _ -> Some (ps @ [g]) in
  let pfs = match pfs with
    | [] | _::[] -> Some pfs
    | g::gs ->
      let init_pfs = match g with | PDisj (gs0, _) -> gs0 | _ -> [g] in
      List.fold_left (fun acc g -> merge_disj acc g) (Some init_pfs) gs in
  match pfs with
  | None -> BConst (true, pos)
  | Some [] -> BConst (false, pos)
  | Some [p] -> p
  | Some pfs -> PDisj (pfs, pos)

let mk_pimpl ?(pos=no_pos) p1 p2 =
  mk_pdisj [(mk_pneg p1 ~pos:pos); p2] ~pos:pos

let rec mk_pexists ?(pos=no_pos) vs p =
  let vs = intersect_vs vs (fv_pf p) in
  match vs with
  | [] -> p
  | _ -> match p with
    | PExists (us, g, pos) -> mk_pexists (vs @ us) g ~pos:pos
    | _ -> PExists (vs, p, pos)

let rec mk_pforall ?(pos=no_pos) vs p =
  let vs = intersect_vs vs (fv_pf p) in
  match vs with
  | [] -> p
  | _ -> match p with
    | PForall (us, g, pos) -> mk_pforall (vs @ us) g ~pos:pos
    | _ -> PForall (vs, p, pos)

(** heap formula *)

let mk_view_form ?(pos=no_pos) ?(ancestor_ids=[]) name args =
  { viewf_name = name;
    viewf_args = args;
    viewf_pos = pos;
    viewf_id = fresh_heap_id ();
    viewf_ancestor_ids = ancestor_ids;
    viewf_origin = HorgInput; }

let mk_data_form ?(pos=no_pos) ?(ancestor_ids=[]) root name args =
  { dataf_root = root;
    dataf_name = name;
    dataf_args = args;
    dataf_pos = pos;
    dataf_id = fresh_heap_id ();
    dataf_ancestor_ids = ancestor_ids;
    dataf_origin = HorgInput; }

let mk_hview ?(pos=no_pos) ?(ancestor_ids=[]) name args =
  HView (mk_view_form name args ~ancestor_ids:ancestor_ids ~pos:pos)

let mk_hdata ?(pos=no_pos) ?(ancestor_ids=[]) root name args =
  HData (mk_data_form root name args ~ancestor_ids:ancestor_ids ~pos:pos)

let mk_hemp pos = HEmp pos

let mk_hform ?(pos=no_pos) dfs vfs =
  let dfs = List.sort compare_df dfs in
  let vfs = List.sort compare_vf vfs in
  HAtom (dfs, vfs, pos)

let mk_hform_df df = mk_hform [df] []

let mk_hform_vf vf = mk_hform [] [vf]

let mk_hform_ha ha = match ha with
  | HData df -> mk_hform_df df
  | HView vf -> mk_hform_vf vf

let mk_hform_has has =
  let dfs, vfs = has |> List.fold_left (fun (adfs, avfs) ha ->
    match ha with
    | HData df -> (adfs @ [df], avfs)
    | HView vf -> (adfs, avfs @ [vf])) ([], []) in
  mk_hform dfs vfs

let mk_hatom_df df = HData df

let mk_hatom_vf vf = HView vf

(* assume that heap_atom is ordered increasingly in the HAtom type *)
let mk_hstar ?(pos=no_pos) h1 h2 =
  let rec merge compare xs ys =
    match xs, ys with
    | [], _ -> ys
    | _, [] -> xs
    | u :: us, v :: vs ->
      if (compare u v <= 0) then u :: (merge compare us ys)
      else v :: (merge compare xs vs) in
  let rec star h1 h2 pos = match h1, h2 with
    | HEmp _, _ -> h2
    | _, HEmp _ -> h1
    | HAtom (dfs1, vfs1, _), HAtom (dfs2, vfs2, _) ->
      let dfs = merge compare_df dfs1 dfs2 in
      let vfs = merge compare_vf vfs1 vfs2 in
      HAtom (dfs, vfs, pos)
    | HStar (h11, h12, p), _ -> star (star h11 h12 p) h2 pos
    | _, HStar (h21, h22, p) -> star h1 (star h21 h22 p) pos
    | HWand _, _
    | _, HWand _ -> error "mh_hstar: handle HWand later" in
  star h1 h2 pos

let mk_hstar_f_hf f hf =
  let hvs = fv_hf hf in
  let rec hstar g hg = match g with
    | FBase (hg0, pg, p) -> FBase (mk_hstar hg hg0, pg, p)
    | FExists (vs, g0, p) ->
      let _ = if (intersected_vs vs hvs) then
          warning ("mk_hstar_f_hf: unsafe quantifiers: "
            ^ (pr_f f) ^ " +++ " ^  (pr_hf hf)) in
      FExists (vs, hstar g0 hg, p)
    | FForall (vs, g0, p) ->
      let _ = if (intersected_vs vs hvs) then
          warning ("mk_hstar_f_hf: unsafe quantifiers: "
            ^ (pr_f f) ^ " +++ " ^  (pr_hf hf)) in
      FForall (vs, hstar g0 hg, p) in
  hstar f hf

let mk_hstar_hf_vf hf vf = mk_hstar (mk_hform_vf vf) hf

let mk_hstar_hf_f hf f = mk_hstar_f_hf f hf

let mk_hstar_f_df f df = mk_hstar_f_hf f (mk_hform_df df)

let mk_hstar_f_vf f vf = mk_hstar_f_hf f (mk_hform_vf vf)

let mk_hstar_f_pf f pf =
  let pvs = fv_pf pf in
  let rec hstar g pg = match g with
    | FBase (hg, pg0, p) -> FBase (hg, mk_pconj [pg0; pg] ~pos:p , p)
    | FExists (vs, g0, p) ->
      let _ = if (intersected_vs vs pvs) then
          warning ("mk_hstar_f_pf: unsafe quantifiers: "
            ^ (pr_f f) ^ " +++ " ^  (pr_pf pf)) in
      FExists (vs, hstar g0 pg, p)
    | FForall (vs, g0, p) ->
      let _ = if (intersected_vs vs pvs) then
          warning ("mk_hstar_f_pf: unsafe quantifiers: "
            ^ (pr_f f) ^ " +++ " ^  (pr_pf pf)) in
      FForall (vs, hstar g0 pg, p) in
  hstar f pf

let mk_hstar_pf_f pf f = mk_hstar_f_pf f pf

let mk_hstar_f_f f1 f2 =
  let vs1 = fv f1 in
  let rec hstar acc g = match g with
    | FBase (hg, pg, p) ->
      mk_hstar_f_hf (mk_hstar_f_pf acc pg) hg
    | FExists (vs, g0, p) ->
      let _ = if (intersected_vs vs vs1) then
          warning ("mk_hstar_f_f: unsafe quantifiers: "
            ^ (pr_f f1) ^ " +++ " ^  (pr_f f2)) in
      FExists (vs, hstar acc g0, p)
    | FForall (vs, g0, p) ->
      let _ = if (intersected_vs vs vs1) then
          warning ("mk_hstar_f_f: unsafe quantifiers: "
            ^ (pr_f f1) ^ " +++ " ^  (pr_f f2)) in
      FForall (vs, hstar acc g0, p) in
  hstar f1 f2

let mk_hstar_fs fs = match fs with
  | [] -> error "mk_hstar_fs: expect at least 1 formula"
  | [g] -> g
  | g::gs -> List.fold_left (fun acc x -> mk_hstar_f_f acc x) g gs

let mk_hstar_hfs hfs =
  List.fold_left (fun acc x -> mk_hstar acc x) (mk_hemp no_pos) hfs

let mk_hstar_dfs dfs = HAtom (List.sort compare_df dfs, [], no_pos)

let mk_hstar_vfs vfs = HAtom ([], List.sort compare_vf vfs, no_pos)

let rec mk_hstar_hatoms has =
  let dfs, vfs = List.fold_left (fun (adfs, avfs) ha ->
    match ha with
    | HData df -> (df :: adfs, avfs)
    | HView vf -> (adfs, vf :: avfs)) ([], []) has in
  let dfs = List.sort compare_df dfs in
  let vfs = List.sort compare_vf vfs in
  if (dfs = [] && vfs = []) then mk_hemp no_pos
  else HAtom (dfs, vfs, no_pos)

let mk_hwand ?(pos=no_pos) h1 h2 = HWand (h1, h2, pos)

(** symbolic-heap formula *)

let mk_fbase ?(pos=no_pos) hf pf = FBase (hf, pf, pos)

let mk_fheap ?(pos=no_pos) hf = FBase (hf, mk_true pos, pos)

let mk_fpure ?(pos=no_pos) pf = FBase (mk_hemp pos, pf, pos)

let mk_fexists ?(pos=no_pos) vs f =
  let vs = intersect_vs vs (fv f) in
  match vs with
  | [] -> f
  | _ -> match f with
    | FBase (hf, pf, p) ->
      let hvs = fv_hf hf in
      let qvs, pqvs = List.partition (fun x -> mem_vs x hvs) vs in
      if qvs = [] then FBase (hf, mk_pexists pqvs pf, p)
      else FExists (qvs, FBase (hf, mk_pexists pqvs pf, p), p)
    | FExists (us, g, p) -> FExists (vs @ us, g, p)
    | FForall _ -> FExists (vs, f, pos)

let mk_fforall ?(pos=no_pos) vs f =
  let vs = intersect_vs vs (fv f) in
  match vs with
  | [] -> f
  | _ -> match f with
    | FBase (hf, pf, p) ->
      let hvs = fv_hf hf in
      let qvs, pqvs = List.partition (fun x -> mem_vs x hvs) vs in
      if qvs = [] then FBase (hf, mk_pforall pqvs pf, p)
      else FForall (qvs, FBase (hf, mk_pforall pqvs pf, p), p)
    | FForall (us, g, p) -> FForall (vs @ us, g, p)
    | FExists _ -> FForall (vs, f, pos)

let mk_fexists_all f =
  mk_fexists (fv f) f

let mk_qexists vs = QExists vs

let mk_qforall vs = QForall vs

let mk_ffalse pos = mk_fpure (mk_false pos)

let mk_ftrue pos = mk_fpure (mk_true pos)

let mk_qform vs f =
  List.fold_right (fun v acc -> match v with
    | QExists vs -> mk_fexists vs acc
    | QForall vs -> mk_fforall vs acc) vs f

let mk_qform_pf vs f =
  List.fold_right (fun v acc -> match v with
    | QExists vs -> mk_pexists vs acc
    | QForall vs -> mk_pforall vs acc) vs f

let mk_pure_entail ?(pos=no_pos) ante conseq =
  { pent_id = new_entail_id ();
    pent_lhs = ante;
    pent_rhs = conseq;
    pent_pos = pos }

let mk_entailment ?(pos=no_pos) ?(mode=PrfEntail) ante conseq  =
  { ent_id = new_entail_id ();
    ent_lhs = ante;
    ent_rhs = conseq;
    ent_mode = mode;
    ent_pos = pos }

let mk_lemma name lhs rhs status origin =
  { lm_name = name;
    lm_origin = origin;
    lm_kind = LmkSafe;
    lm_status = status;
    lm_lhs = lhs;
    lm_rhs = rhs;
    lm_pos = no_pos; }

let mk_lemma_template lhs rhs typ =
  { lmt_lhs = lhs;
    lmt_rhs = rhs;
    lmt_typ = typ; }

let mk_lemma_ent name ent status origin =
  mk_lemma name ent.ent_lhs ent.ent_rhs status origin

let mk_counter_lemma id status lhs rhs =
  { clm_name = string_of_int id;
    clm_status = status;
    clm_lhs = lhs;
    clm_rhs = rhs; }

let mk_rel_defn ?(pos=no_pos) name params body =
  { rel_name = name;
    rel_params = params;
    rel_body = body;
    rel_pos = pos; }

let mk_rel_defn_unknown ?(pos=no_pos) name params =
  { rel_name = name;
    rel_params = params;
    rel_body = RbUnknown;
    rel_pos = pos; }

let mk_data_defn name fields pos =
  { datad_name = name;
    datad_fields = fields;
    datad_pos = pos; }

let mk_view_invariant () =
  { vinv_arith = None;
    vinv_pointer = None;
    vinv_all = None;
    vinv_user = None; }

let mk_view_defn name params body pos =
  { view_name = name;
    view_params = params;
    view_defn_cases = body;
    view_alloc_exps = [];
    view_recurt = VrtNone;
    view_recurd = VrdNone;
    view_data_names = [];
    view_roots = [];
    view_inductive_vars = [];
    view_inv = mk_view_invariant ();
    view_min_size = 0;
    view_empty_base_case = false;
    view_emid_cases = [];
    view_pos = pos; }

let mk_program filename =
  { prog_filename = filename;
    prog_rels = [];
    prog_datas = [];
    prog_views = [];
    prog_lemmas = [];
    prog_commands = [];
    prog_pos = no_pos }

(***************   simultaneous substitution   *****************)

let proof_check_consistency_subst ssts : unit =
  if not !proof_check_consistency then ()
  else
    let old_vars, _ = List.split ssts in
    if not (check_dup_vs old_vars) then ()
    else error ("debug: inconsistent substitution: " ^ (pr_ssts ssts))

let filter_substs ssts vars =
  List.filter (fun (x,_) -> not (mem_vs x vars)) ssts

let subst_var ?(pos=no_pos) ssts v =
  try
    let _ = proof_check_consistency_subst ssts in
    let _, e = List.find (fun (x,y) -> eq_var x v) ssts in
    update_pos_exp e pos
  with _ -> Var (v, pos)

let subst_vars ?(pos=no_pos) ssts vs = vs |> List.map (subst_var ssts)

let rec subst_exp ssts exp = match exp with
  | Null _ | IConst _ -> exp
  | Var (v,p) -> subst_var ssts v ~pos:p
  | LTerm (t, p) ->
    let cpart, ipart = t in
    let tmp = List.fold_left (fun acc (c, v) ->
      let ne = subst_var ssts v ~pos:p |>
               mk_bin_op Mul (mk_iconst c) ~pos:p in
      mk_bin_op Add acc ne ~pos:p) (mk_iconst 0 ~pos:p) cpart in
    mk_bin_op Add tmp (mk_iconst ipart ~pos:p)
  | BinOp (op, e1, e2, p) ->
    let ne1 = e1 |> subst_exp ssts in
    let ne2 = e2 |> subst_exp ssts in
    mk_bin_op op ne1 ne2 ~pos:p
  | Func (f, es, p) -> Func (f, List.map (subst_exp ssts) es, p)

let subst_exps ssts exps = List.map (subst_exp ssts) exps

let rec subst_pf ssts f =
  DB.trace_2 "subst_pf" (pr_ssts, pr_pf, pr_pf) ssts f
    (fun () -> subst_pf_x ssts f)

and subst_pf_x ssts f =
  let rec subst ssts f = match f with
    | BConst _ -> f
    | BinRel (rel, e1, e2, p) ->
      let ne1, ne2 = subst_exp ssts e1, subst_exp ssts e2 in
      BinRel (rel, ne1, ne2, p)
    | PRel rel ->
      let nargs = List.map (subst_exp ssts) rel.prel_args in
      PRel {rel with prel_args = nargs}
    | PNeg (g, p) -> mk_pneg (subst ssts g) ~pos:p
    | PConj (gs, p) -> PConj (List.map (subst ssts) gs, p)
    | PDisj (gs, p) -> PDisj (List.map (subst ssts) gs, p)
    | PForall (vs, g, p) ->
      let nssts = filter_substs ssts vs in
      PForall (vs, subst nssts g, p)
    | PExists (vs, g, p) ->
      let nssts = filter_substs ssts vs in
      PExists (vs, subst nssts g, p) in
  subst ssts f

let subst_df ssts (df: data_form) =
  let nroot = subst_exp ssts df.dataf_root in
  let nargs = subst_exps ssts df.dataf_args in
  {df with dataf_root = nroot; dataf_args = nargs}

let subst_vf ssts (vf: view_form) =
  let nargs = subst_exps ssts vf.viewf_args in
  {vf with viewf_args = nargs}

let rec subst_ha ssts f = match f with
  | HData df -> HData (subst_df ssts df)
  | HView vf -> HView (subst_vf ssts vf)

let rec subst_hf ssts f = match f with
  | HEmp _ -> f
  | HAtom (dfs, vfs, p) ->
    let dfs = List.map (subst_df ssts) dfs in
    let vfs = List.map (subst_vf ssts) vfs in
    HAtom (dfs, vfs, p)
  | HStar (g1, g2, p) -> HStar (subst_hf ssts g1, subst_hf ssts g2, p)
  | HWand (g1, g2, p) -> HWand (subst_hf ssts g1, subst_hf ssts g2, p)

let rec subst ssts f =
  SBDebug.trace_2 "subst" (pr_ssts, pr_f, pr_f) ssts f
    (fun () -> subst_x ssts f)

and subst_x ssts f =
  let rec do_subst ssts f = match f with
    | FBase (hf, pf, p) -> FBase (subst_hf ssts hf, subst_pf ssts pf, p)
    | FExists (vs, g, p) ->
      let nssts = filter_substs ssts vs in
      FExists (vs, do_subst nssts g, p)
    | FForall (vs, g, p) ->
      let nssts = filter_substs ssts vs in
      FForall (vs, do_subst nssts g, p) in
  do_subst ssts f


(***************   simultaneous rename variables   *****************)

let proof_check_consistency_renaming rnms : unit =
  if not !proof_check_consistency then ()
  else
    let old_vars, _ = List.split rnms in
    if not (check_dup_vs old_vars) then ()
    else error ("proof_check_consistency: inconsistent renaming: "
        ^ (pr_rnms rnms))

let filter_renamings rnms vars =
  List.filter (fun (x,_) -> not (mem_vs x vars)) rnms

let mk_renaming ?(suffix=index_var) vars =
  let nvars = List.map (fresh_var ~suffix:suffix) vars in
  List.combine vars nvars

let rename_var rnms var =
  try
    let _ = proof_check_consistency_renaming rnms in
    snd (List.find (fun (x, y) -> eq_var x var) rnms)
  with _ -> var

let rec rename_var_exp rnms exp = match exp with
  | Null _ | IConst _ -> exp
  | Var (v, p) -> Var (rename_var rnms v, p)
  | LTerm ((cpart, ipart), p) ->
    let ncpart = cpart |> List.map (fun (c, v) -> (c, rename_var rnms v)) in
    LTerm ((ncpart, ipart), p)
  | BinOp (op, e1, e2, p) ->
    let ne1, ne2 = rename_var_exp rnms e1, rename_var_exp rnms e2 in
    BinOp (op, ne1, ne2, p)
  | Func (f, es, p) ->
    Func (f, List.map (rename_var_exp rnms) es, p)

let rename_var_exps rnms exps = List.map (rename_var_exp rnms) exps

let rec rename_var_pf rnms f = match f with
  | BConst _ -> f
  | BinRel (rel, e1, e2, p) ->
    let ne1, ne2 = rename_var_exp rnms e1, rename_var_exp rnms e2 in
    BinRel (rel, ne1, ne2, p)
  | PRel rel ->
    let nargs = List.map (rename_var_exp rnms) rel.prel_args in
    PRel {rel with prel_args = nargs}
  | PNeg (g, p) -> mk_pneg (rename_var_pf rnms g) ~pos:p
  | PConj (gs, p) -> PConj (List.map (rename_var_pf rnms) gs, p)
  | PDisj (gs, p) -> PDisj (List.map (rename_var_pf rnms) gs, p)
  | PForall (vs, g, p) ->
    let nrnms = filter_renamings rnms vs in
    PForall (vs, rename_var_pf nrnms g, p)
  | PExists (vs, g, p) ->
    let nrnms = filter_renamings rnms vs in
    PExists (vs, rename_var_pf nrnms g, p)

let rename_var_df rnms (df: data_form) =
  let nroot = rename_var_exp rnms df.dataf_root in
  let nargs = rename_var_exps rnms df.dataf_args in
  {df with dataf_root = nroot; dataf_args = nargs}

let rename_var_vf rnms (vf: view_form) =
  let nargs = rename_var_exps rnms vf.viewf_args in
  {vf with viewf_args = nargs}

let rec rename_var_ha rnms f = match f with
  | HData df -> HData (rename_var_df rnms df)
  | HView vf -> HView (rename_var_vf rnms vf)

let rec rename_var_hf rnms f = match f with
  | HEmp _ -> f
  | HAtom (dfs, vfs, p) ->
    let dfs = List.map (rename_var_df rnms) dfs in
    let vfs = List.map (rename_var_vf rnms) vfs in
    HAtom (dfs, vfs, p)
  | HStar (g1, g2, p) -> HStar (rename_var_hf rnms g1, rename_var_hf rnms g2, p)
  | HWand (g1, g2, p) -> HWand (rename_var_hf rnms g1, rename_var_hf rnms g2, p)

let rec rename_var_f rnms f = match f with
  | FBase (hf, pf, p) -> FBase (rename_var_hf rnms hf, rename_var_pf rnms pf, p)
  | FExists (vs, g, p) ->
    let nrnms = filter_renamings rnms vs in
    FExists (vs, rename_var_f nrnms g, p)
  | FForall (vs, g, p) ->
    let nrnms = filter_renamings rnms vs in
    FForall (vs, rename_var_f nrnms g, p)

(***************   rename freshly all quantifier variables   *****************)

let rec rename_all_qvars_pf ?(suffix=index_var) f = match f with
  | BConst _ | BinRel _ | PRel _ -> f
  | PNeg (g, p) ->
    mk_pneg (rename_all_qvars_pf ~suffix:suffix g) ~pos:p
  | PConj (gs, p) ->
    PConj (List.map (rename_all_qvars_pf ~suffix:suffix) gs, p)
  | PDisj (gs, p) ->
    PDisj (List.map (rename_all_qvars_pf ~suffix:suffix) gs, p)
  | PForall (vs, g, p) ->
    let nvs = List.map (fresh_var ~suffix:suffix) vs in
    let ng = rename_all_qvars_pf ~suffix:suffix g in
    let rnms = List.combine vs nvs in
    let ng = rename_var_pf rnms ng in
    PForall (nvs, ng, p)
  | PExists (vs, g, p) ->
    let nvs = List.map (fresh_var ~suffix:suffix) vs in
    let ng = rename_all_qvars_pf g ~suffix:suffix in
    let rnms = List.combine vs nvs in
    let ng = rename_var_pf rnms ng in
    PExists (nvs, ng, p)

let rec rename_all_qvars ?(suffix=index_var) f =
  SBDebug.trace_1 "rename_all_qvars" (pr_f, pr_f) f
    (fun () -> rename_all_qvars_x ~suffix:suffix f)

and rename_all_qvars_x ?(suffix=index_var) f =
  let rec rename f =  match f with
    | FBase (hf, pf, p) ->
      FBase (hf, rename_all_qvars_pf ~suffix:suffix pf, p)
    | FExists (vs, g, p) ->
      let ng = rename_all_qvars ~suffix:suffix g in
      let nvs = List.map (fresh_var ~suffix:suffix) vs in
      let rnms = List.combine vs nvs in
      let ng = rename_var_f rnms ng in
      FExists (nvs, ng, p)
    | FForall (vs, g, p) ->
      let ng = rename_all_qvars ~suffix:suffix g in
      let nvs = List.map (fresh_var ~suffix:suffix) vs in
      let rnms = List.combine vs nvs in
      let ng = rename_var_f rnms ng in
      FForall (nvs, ng, p) in
  rename f


(***************   rename freshly all  variables   *****************)

(** freshly rename all of its variables *)
let rename_all_var_entail ?(suffix=index_var) lhs rhs =
  let lhs, rhs = Pair.fold (rename_all_qvars ~suffix:suffix) lhs rhs in
  let renaming = [lhs; rhs] |> fv_fs |> mk_renaming in
  let lhs, rhs = Pair.fold (rename_var_f renaming) lhs rhs in
  (lhs, rhs, renaming)

(** freshly rename all of its variables *)
let rename_all_var_entail_pure ?(suffix=index_var) lhs rhs =
  let lhs, rhs = Pair.fold (rename_all_qvars_pf ~suffix:suffix) lhs rhs in
  let renaming = [lhs; rhs] |> fv_pfs |> mk_renaming in
  let lhs, rhs = Pair.fold (rename_var_pf renaming) lhs rhs in
  (lhs, rhs, renaming)

let rename_all_var ?(suffix=index_var) f =
  let f = rename_all_qvars ~suffix:suffix f in
  let renaming = f |> fv |> mk_renaming in
  let f = rename_var_f renaming f in
  (f, renaming)

(***************   map functions   *****************)

let rec map_e fe e : exp =
  match fe e with
  | Some ne -> ne
  | None -> match e with
    | IConst _ | Null _ | Var _ -> e
    | LTerm _ -> e
    | BinOp (op, e1, e2, p) -> BinOp (op, map_e fe e1, map_e fe e2, p)
    | Func (f, es, p) -> Func (f, List.map (map_e fe) es, p)

let rec map_p ((fp, fe) as fa) p : pure_form =
  match fp p with
  | Some np -> np
  | None -> match p with
    | BConst _ -> p
    | BinRel (rel, e1, e2, pos) -> BinRel (rel, map_e fe e1, map_e fe e2, pos)
    | PRel rel ->
      let nargs = List.map (map_e fe) rel.prel_args in
      PRel {rel with prel_args = nargs}
    | PNeg (p0, pos) -> mk_pneg (map_p fa p0) ~pos:pos
    | PConj (ps, pos) -> PConj (List.map (map_p fa) ps, pos)
    | PDisj (ps, pos) -> PDisj (List.map (map_p fa) ps, pos)
    | PForall (v, p0, pos) -> PForall (v, map_p fa p0, pos)
    | PExists (v, p0, pos) -> PExists (v, map_p fa p0, pos)

let rec map_h ((fh, fv, fd, fe) as fa) h : heap_form =
  let map_df df = match fd df with
    | Some df -> df
    | None -> {df with dataf_root = map_e fe df.dataf_root;
                       dataf_args = List.map (map_e fe) df.dataf_args} in
  let map_vf vf = match fv vf with
    | Some vf -> vf
    | None -> {vf with viewf_args = List.map (map_e fe) vf.viewf_args} in
  match fh h with
  | Some nh -> nh
  | None -> match h with
    | HEmp _ -> h
    | HAtom (dfs, vfs, p) ->
      let dfs = List.map map_df dfs in
      let vfs = List.map map_vf vfs in
      HAtom (dfs, vfs, p)
    | HStar (h1, h2, pos) -> HStar (map_h fa h1, map_h fa h2, pos)
    | HWand (h1, h2, pos) -> HWand (map_h fa h1, map_h fa h2, pos)

let rec map_f ((ff, fh, fv, fd, fp, fe) as fa) f : formula =
  match ff f with
  | Some nf -> nf
  | None -> match f with
    | FBase (h, p, pos) ->
      let nh = map_h (fh, fv, fd, fe) h in
      let np = map_p (fp, fe) p in
      FBase (nh, np, pos)
    | FExists (v, f0, pos) -> FExists (v, map_f fa f0, pos)
    | FForall (v, f0, pos) -> FForall (v, map_f fa f0, pos)

(***************   iter functions   *****************)

let rec iter_e fe e : unit =
  match fe e with
  | Some ne -> ne
  | None -> match e with
    | IConst _ | Null _ | Var _ -> ()
    | LTerm _ -> ()
    | BinOp (op, e1, e2, _) -> iter_e fe e1; iter_e fe e2
    | Func (f, es, _) -> List.iter (iter_e fe) es

let rec iter_p ((fp, fe) as fa) p : unit =
  match fp p with
  | Some np -> np
  | None -> match p with
    | BConst _ -> ()
    | BinRel (_, e1, e2, _) -> iter_e fe e1; iter_e fe e2
    | PRel rel -> List.iter (iter_e fe) rel.prel_args
    | PConj (ps,_) | PDisj (ps, _)-> List.iter (iter_p fa) ps
    | PNeg (p0, _) | PForall (_, p0, _) | PExists (_, p0, _) -> iter_p fa p0

let rec iter_h ((fh, fe) as fa) h : unit =
  let iter_df df = List.iter (iter_e fe) (df.dataf_root::df.dataf_args) in
  let iter_vf vf = List.iter (iter_e fe) vf.viewf_args in
  match fh h with
  | Some nh -> nh
  | None -> match h with
    | HEmp _ -> ()
    | HAtom (dfs, vfs, p) ->
      List.iter iter_df dfs;
      List.iter iter_vf vfs
    | HStar (h1, h2, _)
    | HWand (h1, h2, _) ->
      iter_h fa h1;
      iter_h fa h2

let rec iter_f ((ff, fh, fp, fe) as fa) f : unit =
  match ff f with
  | Some nf -> nf
  | None -> match f with
    | FBase (h, p, _) ->
      iter_h (fh, fe) h;
      iter_p (fp, fe) p
    | FExists (_, f0, _)
    | FForall (_, f0, _) -> iter_f fa f0

(***************   fold_left functions   *****************)

type 'a fold_v_t = 'a -> var -> 'a option
type 'a fold_e_t = 'a -> exp -> 'a option
type 'a fold_p_t = 'a -> pure_form -> 'a option
type 'a fold_h_t = 'a -> heap_form -> 'a option
type 'a fold_f_t = 'a -> formula -> 'a option
type 'a fold_e_v_t = 'a fold_e_t * 'a fold_v_t
type 'a fold_p_e_v_t = 'a fold_p_t * 'a fold_e_t * 'a fold_v_t
type 'a fold_h_e_v_t = 'a fold_h_t * 'a fold_e_t * 'a fold_v_t
type 'a fold_f_h_p_e_v_t =
  'a fold_f_t * 'a fold_h_t * 'a fold_p_t * 'a fold_e_t * 'a fold_v_t

let rec fold_v (fv: 'a fold_v_t) (acc: 'a) (v: var) : 'a =
  match fv acc v with
  | Some res -> res
  | None -> acc

let rec fold_e ((fe, fv) as fa : 'a fold_e_v_t) (acc: 'a) (e: exp) : 'a =
  match fe acc e with
  | Some res -> res
  | None -> match e with
    | IConst _ | Null _ -> acc
    | Var (v, _) -> fold_v fv acc v
    | LTerm ((cvs, _), _) ->
      List.fold_left (fun acc2 (c, v) -> fold_v fv acc2 v) acc cvs
    | BinOp (op, e1, e2, _) -> let acc = fold_e fa acc e1 in fold_e fa acc e2
    | Func (f, es, _) -> List.fold_left (fun acc2 e -> fold_e fa acc2 e) acc es

let rec fold_p ((fp, fe, fv) as fa : 'a fold_p_e_v_t) acc p : 'a =
  match fp acc p with
  | Some res -> res
  | None -> match p with
    | BConst _ -> acc
    | BinRel (rel, e1, e2, pos) ->
      let x = fold_e (fe, fv) acc e1 in fold_e (fe, fv) x e2
    | PRel rel ->
      List.fold_left (fun acc2 x -> fold_e (fe, fv) acc2 x) acc rel.prel_args
    | PNeg (p0, pos) -> fold_p fa acc p0
    | PConj (ps, pos) | PDisj (ps, pos) ->
      List.fold_left (fun x y -> fold_p fa x y) acc ps
    | PForall (v, p0, pos) -> fold_p fa acc p0
    | PExists (v, p0, pos) -> fold_p fa acc p0

let rec fold_h ((fh, fe, fv) as fa : 'a fold_h_e_v_t) acc h : 'a =
  let fev = (fe, fv) in
  let fold_df acc df =
    let args = df.dataf_root :: df.dataf_args in
    List.fold_left (fold_e fev) acc args in
  let fold_vf acc vf = List.fold_left (fold_e fev) acc vf.viewf_args in
  match fh acc h with
  | Some nh -> nh
  | None -> match h with
    | HEmp _ -> acc
    | HAtom (dfs, vfs, p) ->
      let acc = List.fold_left (fun x df -> fold_df x df) acc dfs in
      List.fold_left (fun x vf -> fold_vf x vf) acc vfs
    | HStar (h1, h2, pos) -> let acc = fold_h fa acc h1 in fold_h fa acc h2
    | HWand (h1, h2, pos) -> let acc = fold_h fa acc h1 in fold_h fa acc h2

let rec fold_f ((ff, fh, fp, fe, fv) as fa : 'a fold_f_h_p_e_v_t) acc f : 'a =
  let fhev, fpev = (fh, fe, fv), (fp, fe, fv) in
  match ff acc f with
  | Some nf -> nf
  | None -> match f with
    | FBase (h, p, pos) -> let x = fold_h fhev acc h in fold_p fpev x p
    | FExists (v, f0, pos) -> fold_f fa acc f0
    | FForall (v, f0, pos) -> fold_f fa acc f0

(*****************************************************************************)
(**********************       utilities functions      ***********************)

let change_origin_hf org hf =
  let rec change hf = match hf with
    | HEmp _ -> hf
    | HAtom (dfs, vfs, p) ->
      let dfs = dfs |> List.map (fun df -> {df with dataf_origin = org}) in
      let vfs = vfs |> List.map (fun vf -> {vf with viewf_origin = org}) in
      HAtom (dfs, vfs, p)
    | HStar (g1, g2, p) -> HStar (change g1, change g2, p)
    | HWand (g1, g2, p) -> HWand (change g1, change g2, p) in
  change hf

let change_origin org f =
  let rec change f = match f with
    | FBase (hg, pg, p) -> FBase (change_origin_hf org hg, pg, p)
    | FExists (vs, g, p) -> FExists (vs, change g, p)
    | FForall (vs, g, p) -> FForall (vs, change g, p) in
  change f

let get_hatom_origin ha = match ha with
  | HData df -> df.dataf_origin
  | HView vf -> vf.viewf_origin

let get_hatom_name ha = match ha with
  | HData df -> df.dataf_name
  | HView vf -> vf.viewf_name

let get_hatom_args ha = match ha with
  | HData df -> df.dataf_root::df.dataf_args
  | HView vf -> vf.viewf_args

let update_hatom_args ha args = match ha with
  | HData df -> HData {df with dataf_root = List.hd args;
                               dataf_args = List.tl args;}
  | HView vf -> HView {vf with viewf_args = args;}

let update_unfolding_id_hf origin_vf hf =
  let ancestor_ids = origin_vf.viewf_ancestor_ids @ [origin_vf.viewf_id] in
  let update_df df = {df with dataf_id = fresh_heap_id ();
                              dataf_ancestor_ids = ancestor_ids} in
  let update_vf vf = {vf with viewf_id = fresh_heap_id ();
                              viewf_ancestor_ids = ancestor_ids} in
  let rec update hf = match hf with
    | HEmp _ -> hf
    | HAtom (dfs, vfs, p) ->
      let dfs = dfs |> List.map (fun df -> update_df df) in
      let vfs = vfs |> List.map (fun vf -> update_vf vf) in
      HAtom (dfs, vfs, p)
    | HStar (g1, g2, p) -> HStar (update g1, update g2, p)
    | HWand (g1, g2, p) -> HWand (update g1, update g2, p) in
  update hf

let update_unfolding_id origin_vf f =
  let rec update f = match f with
    | FBase (hg, pg, p) -> FBase (update_unfolding_id_hf origin_vf hg, pg, p)
    | FExists (vs, g, p) -> FExists (vs, update g, p)
    | FForall (vs, g, p) -> FForall (vs, update g, p) in
  update f

let collect_pure_atom_pf f =
  let rec collect g = match g with
    | BConst _ | BinRel _ | PRel _ -> [g]
    | PNeg (g0, _) | PForall (_, g0, _) | PExists (_, g0, _) ->
      collect g0
    | PConj (gs, _) | PDisj (gs, _) ->
      gs |> List.map collect |> List.concat in
  collect f

let collect_pure_conjuncts_pf f =
  let rec collect g = match g with
    | PConj (gs, _) -> gs |> List.map collect |> List.concat
    | PDisj ([g0], _) -> collect g0
    | _ -> [g] in
  collect f

let collect_pure_conjuncts = function
  | FBase (_, pf, _) -> collect_pure_conjuncts_pf pf
  | _ -> []

let collect_pure_conjuncts_ent ent =
  (collect_pure_conjuncts ent.ent_lhs)
  @ (collect_pure_conjuncts ent.ent_rhs)

let collect_pure_conjuncts_pent pent =
  (collect_pure_conjuncts_pf pent.pent_lhs)
  @ (collect_pure_conjuncts_pf pent.pent_rhs)

let rec collect_view_form_hf = function
  | HEmp _ -> []
  | HAtom (_, vfs, _) -> vfs
  | HStar (g1, g2, _) -> (collect_view_form_hf g1) @ (collect_view_form_hf g2)
  | HWand _ -> error "collect_view_form_hf: handle Wand later"

let rec collect_view_form = function
  | FBase (g, _, _) -> collect_view_form_hf g
  | FExists (_, g, _) -> collect_view_form g
  | FForall (_, g, _) -> collect_view_form g

let rec collect_data_form_hf = function
  | HEmp _ -> []
  | HAtom (dfs, _, _) -> dfs
  | HStar (g1, g2, _) -> (collect_data_form_hf g1) @ (collect_data_form_hf g2)
  | HWand _ -> error "collect_data_form_hf: handle Wand later"

let rec collect_data_form f = match f with
  | FBase (g, _, _) -> collect_data_form_hf g
  | FExists (_, g, _) -> collect_data_form g
  | FForall (_, g, _) -> collect_data_form g

let rec collect_hatom_hf f = match f with
  | HEmp _ -> []
  | HAtom (dfs, vfs, _) ->
    (List.map (fun x -> HData x) dfs) @ (List.map (fun x -> HView x) vfs)
  | HStar (g1, g2, _) -> (collect_hatom_hf g1) @ (collect_hatom_hf g2)
  | HWand _ -> error "collect_hatom_hf: handle Wand later"

let rec collect_hatom f = match f with
  | FBase (g, _, _) -> collect_hatom_hf g
  | FExists (_, g, _) -> collect_hatom g
  | FForall (_, g, _) -> collect_hatom g

let rec collect_hatom_ent ent =
  (collect_hatom ent.ent_lhs) @ (collect_hatom ent.ent_rhs)

let collect_rform_pf (pf: pure_form) : rel_form list =
  let rec collect = function
    | BConst _ | BinRel _ -> []
    | PRel rel -> [rel]
    | PDisj (gs, _) | PConj (gs, _) -> gs |> List.map collect |> List.concat
    | PNeg (g, _) | PForall (_, g, _) | PExists (_, g, _) -> collect g in
  collect pf

let collect_rform (f: formula) : rel_form list =
  let rec collect = function
    | FBase (_, g, _) -> collect_rform_pf g
    | FExists (_, g, _) | FForall (_, g, _) -> collect g in
  collect f

let extract_rform (f: formula) : formula =
  f |> collect_rform |> mk_pconj_rfs |> mk_fpure

let collect_rform_fs (fs: formula list) : rel_form list =
  fs |> List.map collect_rform |> List.concat

let collect_rform_ent (ent: entailment) : rel_form list =
  (collect_rform ent.ent_lhs) @ (collect_rform ent.ent_rhs)

let collect_rform_pent (pent: pure_entail) : rel_form list =
  (collect_rform_pf pent.pent_lhs) @ (collect_rform_pf pent.pent_rhs)

let collect_typ_pf pf =
  pf |> fv_pf |>
  List.map typ_of_var |> dedup_ts

let collect_typ_df df =
  let exps = df.dataf_root :: df.dataf_args in
  exps |> List.map typ_of_exp |> dedup_ts

let collect_typ_vf vf =
  vf.viewf_args |> List.map typ_of_exp |> dedup_ts

let collect_typ_hf hf =
  let typs1 = hf |> collect_data_form_hf |>
              List.map collect_typ_df |> List.concat |> dedup_ts in
  let typs2 = hf |> collect_view_form_hf |>
              List.map collect_typ_vf |> List.concat |> dedup_ts in
  dedup_ts (typs1 @ typs2)

let collect_typ_ha ha = match ha with
  | HView vf -> collect_typ_vf vf
  | HData df -> collect_typ_df df

let collect_typ_has has =
  has |> List.map collect_typ_ha |> List.concat |> dedup_ts

let collect_typ_hfs hfs =
  hfs |> List.map collect_typ_hf |> List.concat |> dedup_ts

let rec extract_pf = function
  | FBase (_, pf, _) -> pf
  | FExists (vs, f, p) -> mk_pexists vs (extract_pf f) ~pos:p
  | FForall (vs, f, p) -> mk_pforall vs (extract_pf f) ~pos:p

let rec extract_hf = function
  | FBase (hf, _, _) -> hf
  | FExists (_, f, _) | FForall (_, f, _) -> extract_hf f

let rec extract_components_f = function
  | FBase (hf, pf, _) -> [], hf, pf
  | FExists (vs, g, _) ->
    let qvs, hf, pf = extract_components_f g in
    let nqvs = (QExists vs) :: qvs in
    nqvs, hf, pf
  | FForall (vs, g, _) ->
    let qvs, hf, pf = extract_components_f g in
    let nqvs = (QExists vs) :: qvs in
    nqvs, hf, pf

let mk_hstar_inject_pf f pf =
  let fqvs, fhf, fpf = extract_components_f f in
  mk_qform fqvs (mk_fbase fhf (mk_pconj [fpf; pf]))

let get_exists_vars qvars =
  qvars |>
  List.map (fun qv -> match qv with
    | QExists vs -> vs
    | _ -> []) |>
  List.concat

let get_forall_vars qvars =
  qvars |>
  List.map (fun qv -> match qv with
    | QForall vs -> vs
    | _ -> []) |>
  List.concat

let vars_of_qvars qvars =
  qvars |>
  List.map (fun qv -> match qv with
    | QForall vs | QExists vs -> vs) |>
  List.concat

let diff_qvs qvars vs =
  qvars |>
  List.map (function
    | QForall xs ->
      let nxs = diff_vs xs vs in
      if (nxs = []) then []
      else [QForall nxs]
    | QExists xs ->
      let nxs = diff_vs xs vs in
      if (nxs = []) then []
      else [QExists nxs]) |>
  List.concat

let mk_eq_el ?(pos=no_pos) el1 el2 =
  let rec mk_eq xs ys = match xs, ys with
    | [], [] -> mk_true pos
    | [], _ | _, [] -> error "mk_eq_exp: two exp list of different size"
    | x::xs, y::ys ->
      let tmp1, tmp2 = mk_eq_exp x y ~pos:pos, mk_eq xs ys in
      if (is_true_pf tmp2) then tmp1
      else mk_pconj [tmp1; tmp2] ~pos:pos in
  mk_eq el1 el2

let mk_eq_vl ?(pos=no_pos) vl1 vl2 =
  let rec mk_eq xs ys = match xs, ys with
    | [], [] -> mk_true pos
    | [], _ | _, [] -> error "mk_eq_vl: two var list of different size"
    | x::xs, y::ys when (eq_var x y) -> mk_eq xs ys
    | x::xs, y::ys ->
      let tmp1, tmp2 = mk_eq_var x y ~pos:pos, mk_eq xs ys in
      if (is_true_pf tmp2) then tmp1
      else mk_pconj [tmp1; tmp2] ~pos:pos in
  mk_eq vl1 vl2

let find_data_defn datas dname : data_defn =
  try List.find (fun x -> eq_s x.datad_name dname) datas
  with Not_found -> failwith ("find_data_defn: not found: " ^ dname)

let find_view_defn views vname : view_defn =
  try List.find (fun x -> eq_s x.view_name vname) views
  with Not_found -> failwith ("find_view_defn: not found: " ^ vname)

let find_rel_defn rels rname : rel_defn =
  try List.find (fun x -> eq_s x.rel_name rname) rels
  with Not_found -> failwith ("find_rel_defn: not found: " ^ rname)

let remove_rel_defn rels rname =
  List.filter (fun rel -> not (eq_s rel.rel_name rname)) rels

let update_rel_defn rels rdefn =
  (remove_rel_defn rels rdefn.rel_name) @ [rdefn]

let insert_prog_rdefns prog rdefns =
  let dup_names =
    rdefns |>
    List.filter (fun r ->
      List.exists (fun s -> eq_s r.rel_name s.rel_name) prog.prog_rels) |>
    List.map (fun r -> r.rel_name) in
  if dup_names != [] then
    error ("insert_prog_rdefns: duplicated name: " ^ (pr_ids dup_names));
  {prog with prog_rels = prog.prog_rels @ rdefns}

(* find relation definition which are used in a pure_form *)
let find_rel_defn_pf rels (pf: pure_form): rel_defn list =
  pf |> collect_rform_pf |>
  List.map (fun rel -> rel.prel_name) |> dedup_ss |>
  List.map (fun rname -> find_rel_defn rels rname)

let find_rel_defn_pf rels (pf: pure_form): rel_defn list =
  DB.trace_1 "find_rel_defn_pf" (pr_pf, pr_list pr_rel_defn) pf
    (fun () -> find_rel_defn_pf rels pf)

let find_rel_defn_pfs rels (pfs: pure_form list): rel_defn list =
  pfs |> List.map collect_rform_pf |> List.concat |>
  List.map (fun rel -> rel.prel_name) |> dedup_ss |>
  List.map (fun rname -> find_rel_defn rels rname)

let find_rel_defn_pents rels (pents: pure_entail list): rel_defn list =
  pents |>
  List.map (fun p -> [p.pent_lhs; p.pent_rhs]) |> List.concat |>
  find_rel_defn_pfs rels

let find_template_rel_names rels (pents: pure_entail list): string list =
  pents |> find_rel_defn_pents rels |>
  List.filter (fun rdefn -> is_template_rdefn rdefn) |>
  List.map (fun rdefn -> rdefn.rel_name) |> dedup_ss

let has_unk_rform_pf rels pf =
  find_rel_defn_pf rels pf |>
  List.exists (fun rd -> match rd.rel_body with
    | RbForm _ -> false
    | RbTemplate _ -> false
    | RbUnknown -> true)

let has_known_rform_pf rels pf =
  find_rel_defn_pf rels pf |>
  List.exists (fun rd -> match rd.rel_body with
    | RbForm _ -> true
    | RbTemplate _ -> true
    | RbUnknown -> false)

let has_unk_rform rels f = extract_pf f |> has_unk_rform_pf rels

let has_known_rform rels f = extract_pf f |> has_known_rform_pf rels

(** unfold relation formula *)
let rec unfold_rform_rf rdefns (rf: rel_form) : pure_form =
  SBDebug.trace_1 "unfold_rform_rf" (pr_rf, pr_pf) rf
    (fun () -> unfold_rform_rf_x rdefns rf)

and unfold_rform_rf_x rdefns rf : pure_form =
  try
    let rdefn = find_rel_defn rdefns rf.prel_name in
    let vd_params, rf_args = rdefn.rel_params, rf.prel_args in
    let ssts = List.combine vd_params rf_args in
    match rdefn.rel_body with
    | RbTemplate tmpl ->
      tmpl.templ_body |> rename_all_qvars_pf |> subst_pf ssts
    | RbForm f -> f |> rename_all_qvars_pf |> subst_pf ssts
    | RbUnknown -> PRel rf
  with _ -> failwith ("unfold_rform_rf: fail to unfold " ^ (pr_rf rf))

let unfold_rform_rfs rdefns rfs =
  rfs |> List.map (unfold_rform_rf rdefns) |> mk_pconj

(** unfold relation formula *)
let rec unfold_rform_pf rdefns pf : pure_form =
  SBDebug.trace_1 "unfold_rform_pf" (pr_pf, pr_pf) pf
    (fun () -> unfold_rform_pf_x rdefns pf)

and unfold_rform_pf_x rdefns pf : pure_form =
  let rec unfold g = match g with
    | BConst _ | BinRel _ -> g
    | PRel rel -> unfold_rform_rf rdefns rel
    | PNeg (g, p) -> PNeg (unfold g, p)
    | PConj (gs, p) -> PConj (List.map unfold gs, p)
    | PDisj (gs, p) -> PDisj (List.map unfold gs, p)
    | PExists (vs, g, p) -> PExists (vs, unfold g, p)
    | PForall (vs, g, p) -> PForall (vs, unfold g, p) in
  unfold pf

(** unfold relation formula *)
let rec unfold_rform rdefns (f: formula) : formula =
  SBDebug.trace_1 "unfold_rform" (pr_f, pr_f) f
    (fun () -> unfold_rform_x rdefns f)

and unfold_rform_x rdefns f : formula =
  let rec unfold g = match g with
    | FBase (hf, pf, p) -> FBase (hf, unfold_rform_pf rdefns pf, p)
    | FExists (vs, g, p) -> FExists (vs, unfold g, p)
    | FForall (vs, g, p) -> FForall (vs, unfold g, p) in
  unfold f

let replace_prog_rdefns ?(norm_unk=false) prog rdefns =
  let ordefns = prog.prog_rels |> List.filter (fun rd ->
    List.for_all (fun re -> not (eq_s rd.rel_name re.rel_name)) rdefns) in
  let prog = {prog with prog_rels = ordefns @ rdefns} in
  match norm_unk with
  | false -> prog
  | true ->
    let rdefns = prog.prog_rels |> List.map (fun rd ->
      match rd.rel_body with
      | RbUnknown -> {rd with rel_body = RbForm (mk_true no_pos)}
      | _ -> rd) in
    {prog with prog_rels = rdefns}

(** unfold view formula *)
let rec unfold_vform vdefns (vf: view_form) : view_defn_case list =
  SBDebug.trace_1 "unfold_vform" (pr_vf, pr_vdcs) vf
    (fun () -> unfold_vform_x vdefns vf)

and unfold_vform_x vdefns vf : view_defn_case list =
  try
    let vdefn = find_view_defn vdefns vf.viewf_name in
    let vd_params, vf_args = vdefn.view_params, vf.viewf_args in
    let ssts = List.combine vd_params vf_args in
    let vf_cases = List.map (fun vdc ->
      let nf = vdc.vdc_form |> rename_all_qvars |> subst ssts |>
               change_origin HorgUnfold |> update_unfolding_id vf in
      {vdc with vdc_form = nf}) vdefn.view_defn_cases in
    vf_cases
  with _ -> error ("unfold_vform: fail to unfold " ^ (pr_vf vf))

(** unfold view formula *)
let rec unfold_all_vform vdefns (depth: int) (f: formula) : formula list =
  SBDebug.trace_2 "unfold_all_vform" (pr_f, pr_int, pr_fs) f depth
    (fun () -> unfold_all_vform_x vdefns depth f)

and unfold_all_vform_x vdefns depth f : formula list =
  let rec unfold_hf hf : formula list =
    match hf with
    | HEmp _ -> [(mk_fheap hf)]
    | HAtom (dfs, vfs, p) ->
      let nvfs = vfs |> List.map (fun vf ->
        let vdcs = unfold_vform vdefns vf in
        List.map (fun vdc -> vdc.vdc_form) vdcs
      ) |> Comb.gen_cartesian |> List.map mk_hstar_fs in
      let fdf = dfs |> mk_hstar_dfs |> mk_fheap in
      let nfs = match nvfs with
        | [] -> [fdf]
        | _ -> nvfs |> List.map (mk_hstar_f_f fdf) in
      nfs
    | HStar (hf1, hf2, p) ->
      [hf1; hf2] |> List.map unfold_hf |> Comb.gen_cartesian |>
      List.map mk_hstar_fs
    | HWand _ -> error "unfold_all_vform: handle HWand later" in
  let rec unfold f depth =
    if (depth > 0) then
      let qvs, hf, pf = extract_components_f f in
      hf |> unfold_hf |>
      List.map (fun f -> mk_qform qvs (mk_hstar_f_pf f pf)) |>
      List.map (fun f -> unfold f (depth - 1)) |> List.concat
    else [f] in
  unfold f depth

let get_view_recur_type vdefns vf =
  try
    let vdefn = find_view_defn vdefns vf.viewf_name in
    vdefn.view_recurt
  with _ -> VrtUnkn

let get_view_recur_direction vdefns vf =
  try
    let vdefn = find_view_defn vdefns vf.viewf_name in
    vdefn.view_recurd
  with _ -> VrdNone

let get_view_root vdefns vf : exp list =
  try
    let vdefn = find_view_defn vdefns vf.viewf_name in
    let ssts = List.combine vdefn.view_params vf.viewf_args in
    List.map (subst_var ssts) vdefn.view_roots
  with _ -> []

let get_alloc_exps vdefns hatom = match hatom with
  | HData df -> [{al_cond = mk_true no_pos; al_addr = df.dataf_root}]
  | HView vf ->
    let vdef = find_view_defn vdefns vf.viewf_name in
    let ssts = List.combine vdef.view_params vf.viewf_args in
    List.map (fun ae ->
      {al_cond = subst_pf ssts ae.al_cond;
       al_addr = subst_exp ssts ae.al_addr}) vdef.view_alloc_exps

let get_view_inductive_vars vdefns vf : var list =
  try
    let vdefn = find_view_defn vdefns vf.viewf_name in
    let ssts = List.combine vdefn.view_params vf.viewf_args in
    vdefn.view_inductive_vars |> List.map (subst_var ssts) |>
    List.map fv_exp |> List.concat |> dedup_vs
  with _ -> []

let get_ancestor_ids ha = match ha with
  | HData df -> df.dataf_ancestor_ids
  | HView vf -> vf.viewf_ancestor_ids

let is_recur_mutual_vf vdefns vf =
  let recur = get_view_recur_type vdefns vf in
  match recur with
  | VrtMutual _ -> true
  | _ -> false

let is_recur_self recur = match recur with
  | VrtSelf -> true
  | _ -> false

let is_recur_direct recur = match recur with
  | VrtSelf -> true
  | VrtMutual _ -> true
  | VrtMix _ -> true
  | _ -> false

let is_recur_indirect recur = match recur with
  | VrtIndirect _ -> true
  | _ -> false

let is_recur recur =
  (is_recur_direct recur) || (is_recur_indirect recur)

let is_recur_vd vdefn = match vdefn.view_recurt with
  | VrtMutual _ -> true
  | VrtSelf -> true
  | VrtIndirect _ -> true
  | VrtMix _ -> true
  | _ -> false

let is_recur_direct_vd vdefn =
  is_recur_direct vdefn.view_recurt

let is_recur_vf vdefns vf =
  match get_view_recur_type vdefns vf with
  | VrtMutual _ -> true
  | VrtSelf -> true
  | VrtIndirect _ -> true
  | VrtMix _ -> true
  | _ -> false

let is_recur_self_vf vdefns vf =
  vf |> get_view_recur_type vdefns |> is_recur_self

let is_recur_direct_vf vdefns vf =
  vf |> get_view_recur_type vdefns |> is_recur_direct

let is_recur_indirect_vf vdefns vf =
  try
    let vrt = get_view_recur_type vdefns vf in
    match vrt with
    | VrtIndirect _ -> true
    | _ -> false
  with _ -> false

let is_derived_heap_origin  = function
  | HorgHypo -> true
  | HorgTheorem -> true
  | HorgUnfold -> true
  | _ -> false

let is_derived_df df = is_derived_heap_origin df.dataf_origin

let is_derived_vf vf = is_derived_heap_origin vf.viewf_origin

let is_origin_input_df df = df.dataf_origin = HorgInput

let get_excl_mid_cases vdefns vf =
  try
    let vdefn = find_view_defn vdefns vf.viewf_name in
    let ssts = List.combine vdefn.view_params vf.viewf_args in
    List.map (subst_pf ssts) vdefn.view_emid_cases
  with _ -> []

let is_qform_pf pf =
  let rec check = function
    | BConst _ | BinRel _ | PRel _ -> false
    | PExists _ | PForall _ -> true
    | PNeg (g, _) -> check g
    | PConj (gs, _)| PDisj (gs, _) -> List.exists check gs in
  check pf

let is_qfree_pf pf =
  let rec check = function
    | BConst _ | BinRel _ | PRel _ -> true
    | PExists _ | PForall _ -> false
    | PNeg (g, _) -> check g
    | PConj (gs, _)| PDisj (gs, _) -> List.exists check gs in
  check pf

let is_qform f = match f with
  | FForall _ | FExists _ -> true
  | FBase _ -> false

let is_qfree f = match f with
  | FForall _ | FExists _ -> false
  | FBase _ -> true

let rec has_qvars_pf pf = match pf with
  | BConst _ | BinRel _ | PRel _ -> false
  | PNeg (g, _) -> has_qvars_pf g
  | PConj (gs, _) | PDisj (gs, _) -> List.exists has_qvars_pf gs
  | PForall (_, g, _) | PExists (_, g, _) -> true

let rec has_qhvars_f f = match f with
  | FBase _ -> false
  | FExists _ | FForall _ -> true

let rec has_pdisj_pf pf = match pf with
  | BConst _ | BinRel _ | PRel _ -> false
  | PDisj _ -> true
  | PNeg (g, _) | PForall(_, g, _) | PExists (_, g, _) -> has_pdisj_pf g
  | PConj (gs, _) -> List.exists has_pdisj_pf gs

let rec has_neq_pf pf = match pf with
  | BinRel (Ne, _, _, _) -> true
  | BConst _ | BinRel _ | PRel _ -> false
  | PNeg (g, _) | PForall(_, g, _) | PExists (_, g, _) -> has_neq_pf g
  | PConj (gs, _) | PDisj (gs, _) -> List.exists has_neq_pf gs

let rec is_pure_entail ent =
  DB.trace_1 "is_pure_entail" (pr_ent, pr_bool) ent
    (fun () -> is_pure_entail_x ent)

and is_pure_entail_x ent =
  let ha, hc = Pair.fold extract_hf ent.ent_lhs ent.ent_rhs in
  if (is_emp_hf ha) && (is_emp_hf hc) then true
  else false

let is_ptr_pure_entail pent =
  let rels =
    (collect_rform_pf pent.pent_lhs) @ (collect_rform_pf pent.pent_rhs) in
  List.exists (fun rel -> List.exists (fun arg ->
    is_ptr_typ (typ_of_exp arg)) rel.prel_args) rels

let is_empty_model (m: model) = m = []

let compare_pure_entail_by_size pent1 pent2 =
  let size1 =
    List.length (collect_pure_atom_pf pent1.pent_lhs)
    + List.length (collect_pure_atom_pf pent1.pent_rhs) in
  let size2 =
    List.length (collect_pure_atom_pf pent2.pent_lhs)
    + List.length (collect_pure_atom_pf pent2.pent_rhs) in
  if (size1 > size2) then 1
  else if (size1 = size2) then 0
  else -1

let compare_f_by_heap_size f1 f2 =
  let datas1, views1 = collect_data_form f1, collect_view_form f1 in
  let datas2, views2 = collect_data_form f2, collect_view_form f2 in
  let num_datas1, num_datas2 = List.length datas1, List.length datas2 in
  let num_views1, num_views2 = List.length views1, List.length views2 in
  if (num_views1 > num_views2) then 1
  else if (num_views1 < num_views2) then -1
  else if (num_datas1 > num_datas2) then 1
  else if (num_datas1 < num_datas2) then -1
  else 0

let dedup_vdefns vds =
  List.dedup (fun vd1 vd2 -> eq_s vd1.view_name vd2.view_name) vds

let collect_view_defn_vfs vdefns vfs =
  let vnames = vfs |> List.map (fun vf -> vf.viewf_name) in
  let vds = vnames |> List.map (find_view_defn vdefns) in
  let mvds =
    vds |> List.map (fun vd -> match vd.view_recurt with
      | VrtMutual vns -> vns
      | VrtIndirect vns -> vns
      | VrtMix vns -> vns
      | _ -> []) |>
    List.concat |> dedup_ss |> (fun ns -> diff_ss ns vnames) |>
    List.map (find_view_defn vdefns) in
  dedup_vdefns (vds @ mvds)

let collect_view_defn vdefns f =
  f |> collect_view_form |> (collect_view_defn_vfs vdefns)

let collect_view_defn_direct_recur vdefns f =
  f |> collect_view_defn vdefns |> List.filter is_recur_direct_vd

let collect_view_defn_direct_recur_vfs vdefns vfs =
  vfs |> collect_view_defn_vfs vdefns |> List.filter is_recur_direct_vd

let collect_view_defn_recur vdefns f =
  f |> collect_view_defn vdefns |> List.filter is_recur_vd

let collect_view_defn_recur_vfs vdefns vfs =
  vfs |> collect_view_defn_vfs vdefns |> List.filter is_recur_vd

let check_same_data_vdefn vd1 vd2 =
  intersected_ss vd1.view_data_names vd2.view_data_names

let check_recur_vdefn vd1 vd2 =
  let vnames1 = match vd1.view_recurt with
    | VrtMutual vns -> vns
    | VrtSelf -> [vd1.view_name]
    | VrtIndirect vns -> vns
    | VrtMix vns -> vns
    | _ -> [] in
  let vnames2 = match vd2.view_recurt with
    | VrtMutual vns -> vns
    | VrtSelf -> [vd2.view_name]
    | VrtIndirect vns -> vns
    | VrtMix vns -> vns
    | _ -> [] in
  (mem_ss vd1.view_name vnames2) || (mem_ss vd2.view_name vnames1)

let check_hatom_link vdefns ha1 ha2 =
  let args = match ha1 with
    | HData hd -> hd.dataf_args
    | HView hv ->
      let roots = get_view_root vdefns hv in
      List.diff eq_exp hv.viewf_args roots in
  let roots = match ha2 with
    | HData hd -> [hd.dataf_root]
    | HView hv -> get_view_root vdefns hv in
  (* DB.hprint "check_hatom_link: roots: " pr_exps roots; *)
  (* DB.hprint "check_hatom_link: args: " pr_exps args; *)
  let link = List.exists_pair (eq_exp) args roots in
  (* DB.hprint "check_hatom_link: ha1: " pr_ha ha1; *)
  (* DB.hprint "check_hatom_link: ha2: " pr_ha ha2; *)
  (* DB.hprint "check_hatom_link: link: " pr_bool link; *)
  link

let has_int_operator_vd vdefn =
  vdefn.view_defn_cases |> List.exists (fun vd ->
    let args = vd.vdc_form |> collect_view_form |>
               List.map (fun vf -> vf.viewf_args) |> List.concat in
    List.exists (has_int_operator_exp) args)

let collect_data_defn prog f =
  f |> collect_data_form |>
  List.map (fun df -> df.dataf_name) |> dedup_ss |>
  List.map (find_data_defn prog.prog_datas)

let compare_pent_by_unk_rform pent1 pent2 =
  try
    let rfs1 = collect_rform_pent pent1 in
    let rfs2 = collect_rform_pent pent2 in
    let num_rfs1, num_rfs2 = List.length rfs1, List.length rfs2 in
    if (num_rfs1 > num_rfs2) then raise_int (-1);
    if (num_rfs1 < num_rfs2) then raise_int 1;
    let rfvs1 = rfs1 |> fv_rfs |> dedup_vs in
    let rfvs2 = rfs2 |> fv_rfs |> dedup_vs in
    let num_rfvs1, num_rfvs2 = List.length rfvs1, List.length rfvs2 in
    if (num_rfvs1 > num_rfvs2) then raise_int 1;
    if (num_rfvs1 < num_rfvs2) then raise_int (-1);
    let pfs1 = collect_pure_conjuncts_pent pent1 in
    let pfs2 = collect_pure_conjuncts_pent pent2 in
    let num_pfs1, num_pfs2 = List.length pfs1, List.length pfs2 in
    if (num_pfs1 > num_pfs2) then raise_int 1;
    if (num_pfs1 < num_pfs2) then raise_int (-1);
    (* default *)
    0
  with EInt res -> res

let fresh_vform ?(suffix=index_var) ?(sfsep="_") ?(ancestor_ids=[]) vdefn =
  let args = vdefn.view_params |>
             List.map (fresh_var ~suffix:suffix ~sfsep:sfsep) |>
             List.map mk_exp_var in
  mk_view_form vdefn.view_name args ~ancestor_ids:ancestor_ids

let fresh_vform_vf ?(suffix=index_var) ?(sfsep="_") ?(ancestor_ids=[]) vf =
  let args = vf.viewf_args |>
             List.map (fun arg ->
               arg |> typ_of_exp |>
               fresh_var_of_typ ~suffix:suffix ~sfsep:sfsep) |>
             List.map mk_exp_var in
  mk_view_form vf.viewf_name args ~ancestor_ids:ancestor_ids

let fresh_dform ?(suffix=index_var) ?(sfsep="_") ?(ancestor_ids=[]) ddefn =
  let name = ddefn.datad_name in
  let root = mk_var (fresh_var_anonym_name ~suffix:suffix ~sep:sfsep ())
               (TData ddefn.datad_name) in
  let args = ddefn.datad_fields |> List.map (fun (x, y) -> mk_var y x) |>
             List.map (fresh_var ~suffix:suffix) |> List.map mk_exp_var in
  mk_data_form (mk_exp_var root) name args ~ancestor_ids:ancestor_ids

let fresh_dform_df ?(suffix=index_var) ?(sfsep="_") ?(ancestor_ids=[]) df =
  let name = df.dataf_name in
  let root = df.dataf_root |> typ_of_exp |>
             fresh_var_of_typ ~suffix:suffix ~sfsep:sfsep |> mk_exp_var in
  let args = df.dataf_args |>
             List.map (fun arg ->
               arg |> typ_of_exp |>
               fresh_var_of_typ ~suffix:suffix ~sfsep:sfsep) |>
             List.map mk_exp_var in
  mk_data_form root name args ~ancestor_ids:ancestor_ids

let fresh_form ?(suffix=index_var) ?(sfsep="_") has =
  has |> List.map (function
    | HData df ->
      df |> fresh_dform_df ~suffix:suffix ~sfsep:sfsep |> mk_hform_df
    | HView vf ->
      vf |> fresh_vform_vf ~suffix:suffix ~sfsep:sfsep |> mk_hform_vf) |>
  mk_hstar_hfs |> mk_fheap

let fresh_dform_infer ddefn =
  fresh_dform ddefn ~suffix:index_var_infer ~sfsep:""

let fresh_dform_df_infer dform =
  fresh_dform_df dform ~suffix:index_var_infer ~sfsep:""

let fresh_vform_infer vdefn =
  fresh_vform vdefn ~suffix:index_var_infer ~sfsep:""

let fresh_vform_vf_infer vform =
  fresh_vform_vf vform ~suffix:index_var_infer ~sfsep:""

let fresh_forms_infer has =
  has |> List.map (function
    | HData df -> df |> fresh_dform_df_infer |> mk_hform_df
    | HView vf -> vf |> fresh_vform_vf_infer |> mk_hform_vf) |>
  mk_hstar_hfs |> mk_fheap

let check_ict_pf ict pf =
  let vs = fv_pf pf in
  List.for_all (check_ict_var ict) vs

let check_ict_exp ict exp =
  check_ict_typ ict (typ_of_exp exp)

let choose_ict_f f =
  f |> extract_hf |> collect_typ_hf |>
  choose_ict_typs

let choose_ict_fs fs =
  fs |> List.map extract_hf |>
  List.map collect_typ_hf |> List.concat |>
  choose_ict_typs

let is_equality_rdefn rel =
  match rel.rel_body with
  | RbForm f ->
    f |> collect_pure_conjuncts_pf |>
    List.for_all (function
      | BinRel (Eq, _, _, _) -> true
      | _ -> false)
  | _ -> false

let remove_all_rform_pf pf : pure_form =
  let rec remove pf = match pf with
    | BConst _ | BinRel _ -> [pf]
    | PRel rel -> []
    | PDisj (gs, p) ->
      let ngs = gs |> List.map remove |> List.concat in
      if ngs = [] then []
      else [PDisj (ngs, p)]
    | PConj (gs, p) ->
      let ngs = gs |> List.map remove |> List.concat in
      if ngs = [] then []
      else [PConj (ngs, p)]
    | PNeg (g, p) ->
      let ngs = remove g in
      if ngs = [] then []
      else [PNeg (List.hd ngs, p)]
    | PForall (vs, g, p) ->
      let ngs = remove g in
      if ngs = [] then []
      else [PForall (vs, List.hd ngs, p)]
    | PExists (vs, g, p) ->
      let ngs = remove g in
      if ngs = [] then []
      else [PExists (vs, List.hd ngs, p)] in
  match remove pf with
  | [] -> mk_true no_pos
  | [pf] -> pf
  | pfs -> herror "remove_all_rform_pf: not expect result: " pr_pfs pfs

let remove_all_rform (f: formula) : formula =
  let rec remove f = match f with
    | FBase (hf, pf, p) -> FBase (hf, remove_all_rform_pf pf, p)
    | FExists (vs, f, p) -> FExists (vs, remove f, p)
    | FForall (vs, f, p) -> FForall (vs, remove f, p) in
  remove f

let check_syntax_equiv_pf pf1 pf2 =
  let str1 = pf1 |> collect_pure_conjuncts_pf |> List.map pr_pf |>
             List.sort String.compare |> String.concat " * " in
  let str2 = pf2 |> collect_pure_conjuncts_pf |> List.map pr_pf |>
             List.sort String.compare |> String.concat " * " in
  eq_s str1 str2

let check_syntax_equiv_pent pent1 pent2 =
  (check_syntax_equiv_pf pent1.pent_lhs pent2.pent_lhs) &&
  (check_syntax_equiv_pf pent1.pent_rhs pent2.pent_rhs)

let check_syntax_equiv_hf hf1 hf2 =
  let str1 = hf1 |> collect_hatom_hf |> List.map pr_ha |>
             List.sort String.compare |> String.concat " * " in
  let str2 = hf2 |> collect_hatom_hf |> List.map pr_ha |>
             List.sort String.compare |> String.concat " * " in
  eq_s str1 str2

let check_syntax_equiv f1 f2 =
  let qvs1, hf1, pf1 = extract_components_f f1 in
  let qvs2, hf2, pf2 = extract_components_f f2 in
  let is_equiv_qvs =
    let str1 = qvs1 |> List.map pr_qvar |> List.sort String.compare |>
               String.concat " " in
    let str2 = qvs2 |> List.map pr_qvar |> List.sort String.compare |>
               String.concat " " in
    eq_s str1 str2 in
  is_equiv_qvs &&
  (check_syntax_equiv_hf hf1 hf2) &&
  (check_syntax_equiv_pf pf1 pf2)

let check_syntax_equiv_ent ent1 ent2 =
  (check_syntax_equiv ent1.ent_lhs ent2.ent_lhs) &&
  (check_syntax_equiv ent1.ent_rhs ent2.ent_rhs)

let dedup_pents pents =
  pents |> List.fold_left (fun acc pent ->
    if List.exists (check_syntax_equiv_pent pent) acc then acc
    else acc @ [pent]) []

let compute_min_size_vf vds vf =
  let vd = find_view_defn vds vf.viewf_name in
  vd.view_min_size

let compute_min_size_f vds f =
  f |> collect_hatom |>
  List.map (fun ha -> match ha with
    | HData _ -> 1
    | HView vf -> compute_min_size_vf vds vf) |>
  List.fold_left (+) 0

let create_formula_name f  =
  f |> collect_hatom |>
  List.map (function
    | HData df -> df.dataf_name
    | HView vf -> vf.viewf_name) |>
  List.sorti String.compare |>
  String.concat "_"
