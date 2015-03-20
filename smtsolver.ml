#include "xdebug.cppo"
open Globals
open GlobProver
open Gen.Basic
open VarGen
module CP = Cpure

module StringSet = Set.Make(String)

let set_prover_type () = Others.last_tp_used # set Others.Z3

let set_generated_prover_input = ref (fun _ -> ())
let set_prover_original_output = ref (fun _ -> ())

(* Pure formula printing function, to be intialized by cprinter module *)

let print_pure = ref (fun (c:CP.formula) -> " printing not initialized")
let print_ty_sv = ref (fun (c:CP.spec_var) -> " printing not initialized")

(***************************************************************
                  GLOBAL VARIABLES & TYPES
 **************************************************************)

(* Types for relations and ax(ioms*)
type rel_def = {
  rel_name : ident;
  rel_vars : CP.spec_var list;
  related_rels : ident list;
  related_axioms : int list;
  rel_cache_smt_declare_fun : string;
}

(* TODO use hash table for fast retrieval *)
let global_rel_defs = ref ([] : rel_def list)

type axiom_type = 
  | IMPLIES
  | IFF

type axiom_def = {
  axiom_direction   : axiom_type;
  axiom_hypothesis  : CP.formula;
  axiom_conclusion  : CP.formula;
  related_relations : ident list;
  axiom_cache_smt_assert : string;
}

(* TODO use hash table for fast retrieval *)
let global_axiom_defs = ref ([] : axiom_def list)

(* Record of information on a formula *)
type formula_info = {
  relations          : ident list; (* list of relations that the formula mentions *)
  axioms             : int list; (* list of related axioms (in form of position in the global list of axiom definitions) *)
}

let print_pure = ref (fun (c:CP.formula)-> " printing not initialized")

(***************************************************************
            TRANSLATE CPURE FORMULA TO SMT FORMULA              
 **************************************************************)

(* Construct [f(1) ... f(n)] *)
let rec generate_list n f =
  if (n = 0) then []
  else (generate_list (n-1) f) @ [f n]

(* Compute the n-th element of the sequence f0, f1, ..., fn defined by f0 = b and f_n = f(f_{n-1}) *)
let rec compute f n b =
  if (n = 0) then b
  else f (compute f (n-1) b)

let rec smt_of_typ t =
  match t with
  | Bool -> "Int" (* Use integer to represent Bool : 0 for false and > 0 for true. *)
  | Float -> "Real" (* Currently, do not support real arithmetic! *)
  | Tree_sh -> "Int"
  | Int -> "Int"
  | AnnT -> "Int"
  | UNK ->  "Int" (* illegal_format "z3.smt_of_typ: unexpected UNKNOWN type" *)
  | NUM -> "Int" (* Use default Int for NUM *)
  | BagT _ -> "Int"
  | Tup2 _ -> "Int" (*TODO: handle this*)
  | TVar _ -> "Int"
  | Void -> "Int"
  | List _ | FORM -> illegal_format ("z3.smt_of_typ: "^(string_of_typ t)^" not supported for SMT")
  | Named _ -> "Int" (* objects and records are just pointers *)
  | Array (et, d) -> compute (fun x -> "(Array Int " ^ x  ^ ")") d (smt_of_typ et)
  | FuncT (t1, t2) -> "(" ^ (smt_of_typ t1) ^ ") " ^ (smt_of_typ t2) 
  (* TODO *)
  | RelT _ -> "Int"
  | UtT -> "Int"
  | HpT -> "Int"
  (* | SLTyp *)
  | INFInt 
  | Pointer _ -> Error.report_no_pattern ()
  | Bptyp -> "int-triple"

let smt_of_typ t =
  Debug.no_1 "smt_of_typ" string_of_typ idf smt_of_typ t

let smt_of_spec_var sv =
  (CP.name_of_spec_var sv) ^ (if CP.is_primed sv then "_primed" else "")

let smt_of_typed_spec_var sv =
  try
    "(" ^ (smt_of_spec_var sv) ^ " " ^ (smt_of_typ (CP.type_of_spec_var sv)) ^ ")"
  with _ ->
    illegal_format ("z3.smt_of_typed_spec_var: problem with type of"^(!print_ty_sv sv))

let rec smt_of_exp a =
  let str = !Cpure.print_exp a in
  match a with
  | CP.Null _ -> "0"
  | CP.Var (sv, _) -> smt_of_spec_var sv
  | CP.Level _ -> illegal_format ("z3.smt_of_exp: level should not appear here")
  | CP.IConst (i, _) -> if i >= 0 then string_of_int i else "(- 0 " ^ (string_of_int (0-i)) ^ ")"
  | CP.AConst (i, _) -> string_of_int(int_of_heap_ann i)  (*string_of_heap_ann i*)
  | CP.FConst (f, _) -> string_of_float f 
  | CP.Add (a1, a2, _) -> "(+ " ^(smt_of_exp a1)^ " " ^ (smt_of_exp a2)^")"
  | CP.Subtract (a1, a2, _) -> "(- " ^(smt_of_exp a1)^ " " ^ (smt_of_exp a2)^")"
  | CP.Mult (a1, a2, _) -> "(* " ^ (smt_of_exp a1) ^ " " ^ (smt_of_exp a2) ^ ")"
  | CP.Div (a1, a2, _) -> "(/ " ^ (smt_of_exp a1) ^ " " ^ (smt_of_exp a2) ^ ")"
  | CP.Max _
  | CP.Min _ -> illegal_format ("z3.smt_of_exp: min/max should not appear here")
  | CP.TypeCast (_, e1, _) -> smt_of_exp e1 (* illegal_format ("z3.smt_of_exp: TypeCast should not appear here") *)
  | CP.Bag ([], _)
  | CP.Tup2 _ 
  | CP.Bag _
  | CP.BagUnion _
  | CP.BagIntersect _
  | CP.BagDiff _ -> illegal_format ("z3.smt_of_exp: ERROR in constraints (set/tup2) should not appear here : "  ^ str)
  | CP.List _ 
  | CP.ListCons _
  | CP.ListHead _
  | CP.ListTail _
  | CP.ListLength _
  | CP.ListAppend _
  | CP.ListReverse _ -> illegal_format ("z3.smt_of_exp: ERROR in constraints (lists should not appear here)")
  | CP.Func _ -> illegal_format ("z3.smt_of_exp: ERROR in constraints (func should not appear here)")
  | CP.Tsconst _ -> illegal_format ("z3.smt_of_exp: ERROR in constraints (tsconst should not appear here)")
  | CP.Bptriple _ -> illegal_format ("z3.smt_of_exp: ERROR in constraints (Bptriple should not appear here)")
  | CP.ArrayAt (a, idx, l) -> 
      List.fold_left (fun x y -> "(select " ^ x ^ " " ^ (smt_of_exp y) ^ ")") (smt_of_spec_var a) idx
  | CP.NegInfConst _ 
  | CP.InfConst _ -> illegal_format ("z3.smt_of_exp: ERROR in constraints (infconst should not appear here)")
  | CP.Template t -> smt_of_exp (CP.exp_of_template t)

let rec smt_of_b_formula b =
  let (pf,_) = b in
  match pf with
    | CP.Frm (sv, _) -> "(> " ^(smt_of_spec_var sv) ^ " 0)"
    | CP.BConst (c, _) -> if c then "true" else "false"
    | CP.XPure _ -> "true"
    | CP.BVar (sv, _) -> "(> " ^(smt_of_spec_var sv) ^ " 0)"
    | CP.Lt (a1, a2, _) -> "(< " ^(smt_of_exp a1) ^ " " ^ (smt_of_exp a2) ^ ")"
    | CP.SubAnn (a1, a2, _) -> "(<= " ^(smt_of_exp a1) ^ " " ^ (smt_of_exp a2) ^ ")"
    | CP.Lte (a1, a2, _) -> "(<= " ^(smt_of_exp a1) ^ " " ^ (smt_of_exp a2) ^ ")"
    | CP.Gt (a1, a2, _) -> "(> " ^(smt_of_exp a1) ^ " " ^ (smt_of_exp a2) ^ ")"
    | CP.Gte (a1, a2, _) -> "(>= " ^(smt_of_exp a1) ^ " " ^ (smt_of_exp a2) ^ ")"
    | CP.Eq (a1, a2, _) -> 
      if CP.is_null a2 then
        "(< " ^(smt_of_exp a1)^ " 1)"
      else if CP.is_null a1 then
        "(< " ^(smt_of_exp a2)^ " 1)"
      else
        "(= " ^(smt_of_exp a1) ^ " " ^ (smt_of_exp a2) ^ ")"
  | CP.Neq (a1, a2, _) ->
      if CP.is_null a2 then
        "(> " ^(smt_of_exp a1)^ " 0)"
      else if CP.is_null a1 then
        "(> " ^(smt_of_exp a2)^ " 0)"
      else
        "(not (= " ^(smt_of_exp a1) ^ " " ^ (smt_of_exp a2) ^ "))"
  | CP.EqMax (a1, a2, a3, _) ->
      let a1str = smt_of_exp a1 in
      let a2str = smt_of_exp a2 in
      let a3str = smt_of_exp a3 in
      "(or (and (= " ^ a1str ^ " " ^ a2str ^ ") (>= "^a2str^" "^a3str^")) (and (= " ^ a1str ^ " " ^ a3str ^ ") (< "^a2str^" "^a3str^")))"
  | CP.EqMin (a1, a2, a3, _) ->
      let a1str = smt_of_exp a1 in
      let a2str = smt_of_exp a2 in
      let a3str = smt_of_exp a3 in
      "(or (and (= " ^ a1str ^ " " ^ a2str ^ ") (< "^a2str^" "^a3str^")) (and (= " ^ a1str ^ " " ^ a3str ^ ") (>= "^a2str^" "^a3str^")))"
  (* UNHANDLED *)
  | CP.BagIn (v, e, l)    -> " in(" ^ (smt_of_spec_var v) ^ ", " ^ (smt_of_exp e) ^ ")"
  | CP.BagNotIn (v, e, l) -> " NOT(in(" ^ (smt_of_spec_var v) ^ ", " ^ (smt_of_exp e) ^"))"
  | CP.BagSub (e1, e2, l) -> " subset(" ^ smt_of_exp e1 ^ ", " ^ smt_of_exp e2 ^ ")"
  | CP.BagMax _ | CP.BagMin _ -> 
      illegal_format ("z3.smt_of_b_formula: BagMax/BagMin should not appear here.\n")
  (* | CP.VarPerm _ -> illegal_format ("z3.smt_of_b_formula: Vperm should not appear here.\n") *)
  | CP.ListIn _ | CP.ListNotIn _ | CP.ListAllN _ | CP.ListPerm _ -> 
      illegal_format ("z3.smt_of_b_formula: ListIn ListNotIn ListAllN ListPerm should not appear here.\n")
  | CP.LexVar _ ->
      illegal_format ("z3.smt_of_b_formula: LexVar should not appear here.\n")
  | CP.RelForm (r, args, l) ->
      let smt_args = List.map smt_of_exp args in 
      (* special relation 'update_array' translate to smt primitive store in array theory *)
      let rn = CP.name_of_spec_var r in
      if Cpure.is_update_array_relation rn then
        let orig_array = List.nth smt_args 0 in
        let new_array = List.nth smt_args 1 in
        let value = List.nth smt_args 2 in
        let index = List.rev (List.tl (List.tl (List.tl smt_args))) in
        let last_index = List.hd index in
        let rem_index = List.rev (List.tl index) in
        let arr_select = List.fold_left (fun x y -> let k = List.hd x in ("(select " ^ k ^ " " ^ y ^ ")") :: x) [orig_array] rem_index in
        let arr_select = List.rev arr_select in
        let fl = List.map2 (fun x y -> (x,y)) arr_select (rem_index @ [last_index]) in
        let result = List.fold_right (fun x y -> "(store " ^ (fst x) ^ " " ^ (snd x) ^ " " ^ y ^ ")") fl value in
        "(= " ^ new_array ^ " " ^ result ^ ")"
      else
        "(" ^ (CP.name_of_spec_var r) ^ " " ^ (String.concat " " smt_args) ^ ")"
  (* | CP.XPure _ -> Error.report_no_pattern () *)

let rec smt_of_formula pr_w pr_s f =
  let () = x_dinfo_hp (add_str "f(smt)" !CP.print_formula) f no_pos in
  let rec helper f= (
    match f with
    | CP.BForm ((b,_) as bf,_) -> (
        match (pr_w b) with
        | None -> let () = x_dinfo_pp ("NONE #") no_pos in (smt_of_b_formula bf)
        | Some f -> let () = x_dinfo_pp ("SOME #") no_pos in helper f
      )
    | CP.AndList _ -> Gen.report_error no_pos "smtsolver.ml: encountered AndList, should have been already handled"
    | CP.And (p1, p2, _) -> "(and " ^ (helper p1) ^ " " ^ (helper p2) ^ ")"
    | CP.Or (p1, p2,_, _) -> "(or " ^ (helper p1) ^ " " ^ (helper p2) ^ ")"
    | CP.Not (p,_, _) -> "(not " ^ (smt_of_formula pr_s pr_w p) ^ ")"
    | CP.Forall (sv, p, _,_) ->
        "(forall (" ^ (smt_of_typed_spec_var sv) ^ ") " ^ (helper p) ^ ")"
    | CP.Exists (sv, p, _,_) ->
        "(exists (" ^ (smt_of_typed_spec_var sv) ^ ") " ^ (helper p) ^ ")"
  ) in
  helper f

let smt_of_formula pr_w pr_s f =
  let () = set_prover_type () in
  Debug.no_1 "smt_of_formula"  !CP.print_formula idf
    (fun _ -> smt_of_formula pr_w pr_s f) f


let smt_of_formula pr_w pr_s f =
  Debug.no_1 "smt_of_formula" !print_pure pr_id (fun _ -> smt_of_formula pr_w pr_s f) f

(***************************************************************
                       FORMULA INFORMATION                      
 **************************************************************)

(* Default info, returned in most cases *)
let default_formula_info = { 
  relations = []; 
  axioms = [];
}

(* Collect information about a formula f or combined information about 2 formulas *)
let rec collect_formula_info f = 
  let info = collect_formula_info_raw f in
  let indirect_relations = List.flatten (List.map (fun x -> if (List.mem x.rel_name info.relations) then x.related_rels else []) !global_rel_defs) in
  let all_relations = Gen.BList.remove_dups_eq (=) (info.relations @ indirect_relations) in
  let all_axioms = List.flatten (List.map (fun x -> if (List.mem x.rel_name all_relations) then x.related_axioms else []) !global_rel_defs) in
  let all_axioms = Gen.BList.remove_dups_eq (=) all_axioms in
  { relations = all_relations;
    axioms = all_axioms;}

and collect_combine_formula_info f1 f2 = 
  compact_formula_info (combine_formula_info (collect_formula_info f1) (collect_formula_info f2))

(* Recursively collect the information based on the structure of 
 * the formula. This information might not be complete due to cross reference.
 * For instance, a relation definition might refers to other relations. This
 * function is only used mainly in pre-computing information of relation and
 * axiom definition.
 * The information is to be corrected by the function collect_formula_info.
 *)
and collect_formula_info_raw f = match f with
  | CP.BForm ((b,_),_) -> collect_bformula_info b
  | CP.And (f1,f2,_) | CP.Or (f1,f2,_,_) -> 
      collect_combine_formula_info_raw f1 f2
  | CP.AndList _ -> Gen.report_error no_pos "smtsolver.ml: encountered AndList, should have been already handled"
  | CP.Not (f1,_,_) -> collect_formula_info_raw f1
  | CP.Forall (svs,f1,_,_) | CP.Exists (svs,f1,_,_) -> collect_formula_info_raw f1

and collect_combine_formula_info_raw f1 f2 = 
  combine_formula_info (collect_formula_info_raw f1) (collect_formula_info_raw f2)

and collect_bformula_info b = match b with
  | CP.RelForm (r,args,_) -> 
      let r = CP.name_of_spec_var r in
      if r = "update_array" then
        default_formula_info 
      else 
        { default_formula_info with relations = [r]; }
  | _ -> default_formula_info



and combine_formula_info if1 if2 =
  { relations = List.append if1.relations if2.relations;
    axioms = Gen.BList.remove_dups_eq (=) (List.append if1.axioms if2.axioms); }

and compact_formula_info info =
  { relations = Gen.BList.remove_dups_eq (=) info.relations;
    axioms = Gen.BList.remove_dups_eq (=) info.axioms; }

(***************************************************************
                      AXIOMS AND RELATIONS
 **************************************************************)

(* Interface function to add a new axiom *)
let add_axiom h dir c =
  (* let () = print_endline ("Add axiom : " ^ (!print_pure h) ^ (match dir with |IFF -> " <==> " | _ -> " ==> ") ^ (!print_pure c)) in *)
  let info = collect_combine_formula_info_raw h c in
  (* let () = print_endline ("Directly related relations : " ^ (String.concat "," info.relations)) in *)
  (* assumption: at the time of adding this axiom, all relations in global_rel_defs has their related axioms computed *)
  let indirectly_related_relations = List.filter (fun x -> List.mem x.rel_name info.relations) !global_rel_defs in
  let indirectly_related_relations = List.map (fun x -> x.related_rels) indirectly_related_relations in
  let related_relations = info.relations @ (List.flatten indirectly_related_relations) in
  let related_relations = Gen.BList.remove_dups_eq (=) related_relations in
  (* let () = print_endline ("All related relations found : " ^ (String.concat ", " related_relations) ^ "\n") in *)
  let aindex = List.length !global_axiom_defs in (
    (* Modifying every relations appearing in h and c by
       1)   Add reference to 'h dir c' as a related axiom
       2)   Add all other relations (appearing in h and c) to the list of related relations *)
    global_rel_defs := List.map (fun x ->
      if (List.mem x.rel_name related_relations) then
        let rs = Gen.BList.remove_dups_eq (fun s1 s2 -> String.compare s1 s2 =0) (x.related_rels @ related_relations) in
        { x with 
          related_rels = rs;
          related_axioms = x.related_axioms @ [aindex]; }
      else x
    ) !global_rel_defs;
    (* Cache the SMT input for 'h dir c' so that we do not have to generate this over and over again *)
    let params = List.append (CP.fv h) (CP.fv c) in
    (* let _ = print_endline ("params : " ^ (!CP.print_svl params) ^ "\n") in *)
    let rel_ids = List.map (fun r -> CP.SpecVar(RelT[],r.rel_name,Unprimed)) !global_rel_defs in
    let params = Gen.BList.difference_eq CP.eq_spec_var params rel_ids in
    (* let _ = print_endline ("params : " ^ (!CP.print_svl params) ^ "\n") in *)
    let params = Gen.BList.remove_dups_eq CP.eq_spec_var params in
    let smt_params = String.concat " " (List.map smt_of_typed_spec_var params) in
    let op = match dir with 
      | IMPLIES -> "=>" 
      | IFF -> "=" in
    let (pr_w,pr_s) = CP.drop_complex_ops_z3 in
    let cache_smt_input = (
      "(assert " ^ 
      (if params = [] then "" else "(forall (" ^ smt_params ^ ")\n") ^
      "\t(" ^ op ^ " " ^ (smt_of_formula pr_w pr_s h) ^ 
      "\n\t" ^ (smt_of_formula pr_w pr_s c) ^ ")" ^ (* close the main part of the axiom *)
      (if params = [] then "" else ")") (* close the forall if added *) ^ ")\n" (* close the assert *) 
    ) in
    (* Add 'h dir c' to the global axioms *)
    (* let _ = print_endline ("cache_smt_input : " ^ cache_smt_input ^ "\n") in *)
    let new_axiom = {
      axiom_direction = dir;
      axiom_hypothesis = h;
      axiom_conclusion = c;
      related_relations = related_relations (* info.relations TODO must we compute closure ? *);
      axiom_cache_smt_assert = cache_smt_input; 
    } in
    global_axiom_defs := !global_axiom_defs @ [new_axiom];
  )

(* Interface function to add a new relation *)
let add_relation (rname1:string) rargs rform =
  let rname = CP.SpecVar(RelT[],rname1,Unprimed) in
  if (Cpure.is_update_array_relation rname1) then 
    ()
  else (
    (* let rname1 = CP.name_of_spec_var rname in *)
    (* Cache the declaration for this relation *)
    let cache_smt_input = (
      let signature = List.map CP.type_of_spec_var rargs in
      let smt_signature = String.concat " " (List.map smt_of_typ signature) in
      (* Declare the relation in form of a function --> Bool *)
      "(declare-fun " ^ rname1 ^ " (" ^ smt_signature ^ ") Bool)\n"
    ) in
    let rdef = {
      rel_name = rname1; 
      rel_vars = rargs;
      related_rels = []; (* to be filled up by add_axiom *)
      related_axioms = []; (* to be filled up by add_axiom *)
      rel_cache_smt_declare_fun = cache_smt_input;
    } in
    global_rel_defs := !global_rel_defs @ [rdef];
      (* Note that this axiom must be NEW i.e. no relation with this name is added earlier so that add_axiom is correct *)
    match rform with
    | CP.BForm ((CP.BConst (true, no_pos), None), None) (* no definition supplied *) -> (* do nothing *) ()
    | _ -> (* add an axiom to describe the definition *)
        let h = CP.BForm ((CP.RelForm (rname, List.map (fun x -> CP.mkVar x no_pos) rargs, no_pos), None), None) in
        add_axiom h IFF rform;
  )

(* Interface function to add a new hp relation *)
let add_hp_relation (rname1:string) rargs rform =
  (* let rname = CP.SpecVar(HpT,rname1,Unprimed) in *)
    (* Cache the declaration for this relation *)
  let cache_smt_input = (
    let signature = List.map CP.type_of_spec_var rargs in
    let smt_signature = String.concat " " (List.map smt_of_typ signature) in
      (* Declare the relation in form of a function --> Bool *)
    "(declare-fun " ^ rname1 ^ " (" ^ smt_signature ^ ") Bool)\n"
  ) in
  let rdef = { rel_name = rname1; 
             rel_vars = rargs;
             related_rels = []; (* to be filled up by add_axiom *)
             related_axioms = []; (* to be filled up by add_axiom *)
             rel_cache_smt_declare_fun = cache_smt_input; } in
  global_rel_defs := !global_rel_defs @ [rdef];
  (* Note that this axiom must be NEW i.e. no relation with this name is added earlier so that add_axiom is correct *)

(***************************************************************
                            INTERACTION
 **************************************************************)

type sat_type = 
  | Sat    (* solver returns sat *)
  | UnSat    (* solver returns unsat *)
  | Unknown  (* solver returns unknown or there is an exception *)
  | Aborted (* solver returns an exception *)

(* Record structure to store information parsed from the output 
 * of the SMT solver.
 * This change is to make development extensible in later stage.
 *)
type smt_output = {
  original_output_text : string list;   (* original (command line) output text of the solver; included in order to support printing *)
  sat_result : sat_type; (* satisfiability information *)
  (* expand with other information : proof, time, error, warning, ... *)
}

let string_of_smt_output output =
  (String.concat "\n" output.original_output_text)

let rec icollect_output2 chn accumulated_output : string list =
  let output =
    try
      let line = input_line chn in
      if (line = "unsat") then
        let todo_var_unknown = input_line chn in
        accumulated_output @ [line]
      else if (line = ")") then
        accumulated_output @ [line]
      else
        icollect_output2 chn (accumulated_output @ [line])
    with
      | End_of_file -> accumulated_output in
  output

(* Collect all Z3's output into a list of strings *)
let rec icollect_output chn accumulated_output : string list =
  let output =
    try
      let line = input_line chn in
      (* let () = print_endline ("locle2" ^ line) in *)
      if ((String.length line) > 7) then (*something diff to sat/unsat/unknown, retry-may lead to timeout here*)
        icollect_output chn (accumulated_output @ [line])
      else accumulated_output @ [line]
    with | End_of_file -> accumulated_output in
  output

(* let count_paren str =                                *)
(*   let len = String.length str in                     *)
(*   let rec helper i =                                 *)
(*     if i == len then (0, 0)                          *)
(*     else                                             *)
(*       let o, c = helper (i + 1) in                   *)
(*       if str.[i] == '(' then (o + 1, c)              *)
(*       else if str.[i] == ')' then (o, c + 1)         *)
(*       else (o, c)                                    *)
(*   in helper 0                                        *)

(* let icollect_model chn: string list =                *)
(*   let rec helper cnt accumulated_output =            *)
(*     try                                              *)
(*       let line = input_line chn in                   *)
(*       (* let () = print_endline line in *)            *)
(*       let cnt_open, cnt_close = count_paren line in  *)
(*       let cnt = cnt + cnt_open - cnt_close in        *)
(*       if (cnt == 0) then accumulated_output @ [line] *)
(*       else helper cnt (accumulated_output @ [line])  *)
(*     with _ -> accumulated_output                     *)
(*   in                                                 *)
(*   let first_line = input_line chn in                 *)
(*   (* let () = print_endline first_line in *)          *)
(*   helper 0 [first_line]                              *)
  
let rec collect_output chn accumulated_output : string list =
  let output =
    try
      let line = input_line chn in
      (* let () = print_endline ("locle: " ^ line) in *)
      collect_output chn (accumulated_output @ [line])
    with | End_of_file -> accumulated_output in
  output

let sat_type_from_string r input =
  if (String.compare r "sat" == 0) then Sat
  else if (String.compare r "unsat" == 0) then UnSat
  else
    try
      let todo_var_unknown:int = Str.search_forward (Str.regexp "unexpected") r 0 in
      (print_string "Z3 translation failure!";
      Error.report_error { 
        Error.error_loc = no_pos; 
        Error.error_text =("Z3 translation failure!!\n"^r^"\n input: "^input)})
    with
      | Not_found -> Unknown

let parse_model_to_pure_formula model =
  let rec helper acc model =
    let line = List.hd model in
    if line = ")" then acc
    else
      let line2 = List.hd (List.tl model) in
      let var = String.sub line 14 ((String.rindex line '(') - 15) in
      let var = Cpure.mkVar (Cpure.mk_typed_spec_var Globals.Int var) no_pos in
      let value = String.sub line2 4 ((String.length line2) - 5) in
      let value =
        try
          let i = String.index value '-' in
          let l = String.length value in
          Cpure.mkIConst (0 - (int_of_string (String.sub value (i + 2) (l - i - 3)))) no_pos
        with Not_found -> Cpure.mkIConst (int_of_string value) no_pos
      in
      let pf = Cpure.mkEqExp var value no_pos in
      let new_acc = Cpure.mkAnd acc pf no_pos in
      helper new_acc (List.tl (List.tl model))
  in
  let pf = helper (Cpure.mkTrue no_pos) (List.tl model) in
  let () = x_binfo_pp ("counter example: " ^ (!print_pure pf)) no_pos in
  pf

let iget_answer2 chn input =
  let output = icollect_output2 chn [] in
  let solver_sat_result = List.hd output (* List.nth output (List.length output - 1) *) in
  let () = x_binfo_pp ("solver_sat_result: " ^ solver_sat_result) no_pos in
  let model = List.tl output in
  let () = x_binfo_pp "model:" no_pos in
  let unknown = List.map (fun s -> x_binfo_pp s no_pos) model in
  let _ =
    if solver_sat_result = "sat" then
      parse_model_to_pure_formula model
    else
      Cpure.mkTrue no_pos
  in
  { original_output_text = output;
    sat_result = sat_type_from_string solver_sat_result input; }

let iget_answer chn input =
  let check_error_msg s=
    try
      (* let _ = print_endline ("s : " ^ s) in *)
      let _ = Str.search_forward (Str.regexp "error ") s 0 in
      let _ = Error.report_warning { Error.error_loc = no_pos; Error.error_text =("Z3 error message: "^s)} in
      true
    with _ -> false
  in
  let output = icollect_output chn [] in
  let solver_sat_result = List.nth output (List.length output - 1) in
  let last_z3_sat_type = sat_type_from_string solver_sat_result input in
  let st = if List.length output > 1 then
    try
      let b = List.fold_left (fun old_b s -> old_b || (check_error_msg s)) false output in
      (* if b then Sat else *) last_z3_sat_type
    with _ -> last_z3_sat_type
  else last_z3_sat_type
  in
  { original_output_text = output;
    sat_result =  st; }

let get_answer chn input =
  let output = collect_output chn [] in
  let solver_sat_result = List.nth output (List.length output - 1) in
  { original_output_text = output;
    sat_result = sat_type_from_string solver_sat_result input; }

let remove_file filename =
  try Sys.remove filename;
  with | e -> ignore e

type smtprover = Z3

(* Global settings *)
let infile = "/tmp/in" ^ (string_of_int (Unix.getpid ())) ^ ".smt2"
let outfile = "/tmp/out" ^ (string_of_int (Unix.getpid ()))
let z3_sat_timeout_limit = 2.0
let prover_pid = ref 0

let z3_call_count: int ref = ref 0
let is_z3_running = ref false
let is_local_solver = ref (false: bool)

let smtsolver_name = ref ("z3": string)

let prover_process = ref {
  name = !smtsolver_name;
  pid = 0;
  inchannel = stdin;
  outchannel = stdout;
  errchannel = stdin 
}


let smtsolver_path = if !compete_mode then ref "./z3-4.3.2" else ref "z3-4.3.2" (* "z3" *)


let local_oc = "./z3-4.3.2"
let global_oc = "/usr/bin/z3-4.3.2"

let smtsolver_path = 
  if (Sys.file_exists local_oc) then ref local_oc
  else if (Sys.file_exists global_oc)  then ref global_oc
  else 
    begin
      print_endline_quiet ("ERROR : "^global_oc^" cannot be found!!"); ref (global_oc^"_cannot_be_found":string)
    end

(***********)
let test_number = ref 0
let last_test_number = ref 0
let log_all_flag = ref false
let z3_restart_interval = ref (-1)
let log_all = open_log_out ("allinput.z3")


let set_process (proc: prover_process_t) = 
  prover_process := proc

(*for z3-2.19*)
let command_for prover = (
  match !smtsolver_name with
  | "z3" -> (!smtsolver_path, [| !smtsolver_name; "-smt2"; infile; ("> " ^ outfile) |])
  | "./z3" -> ("./z3", [|!smtsolver_name; "-smt2"; infile; ("> "^ outfile) |] )
  | "z3-2.19" -> ("z3-2.19", [| !smtsolver_name; "-smt2"; infile; ("> " ^ outfile) |])
  | "z3-4.2" -> ("z3-4.2", [|!smtsolver_name; "-smt2"; infile; ("> "^ outfile) |] )
  | "z3-4.3.1" -> ("./z3-4.3.1", [|!smtsolver_name; "-smt2"; infile; ("> "^ outfile) |] )
  | _ -> illegal_format ("z3.command_for: ERROR, unexpected solver name")
)

(* Runs the specified prover and returns output *)
let run st prover input timeout =
  (*let () = print_endline "z3-2.19" in*)
  let out_stream = open_out infile in
  (* let () = print_endline ("input: " ^ input) in *)
  output_string out_stream input;
  close_out out_stream;
  let (cmd, cmd_arg) = command_for prover in
  let set_process proc = prover_process := proc in
  let fnc () = (
    let () = Procutils.PrvComms.start false stdout (cmd, cmd, cmd_arg) set_process (fun () -> ()) in
    get_answer !prover_process.inchannel input
  ) in
  let res = (
    try
      Procutils.PrvComms.maybe_raise_timeout fnc () timeout
    with
      | _ -> (* exception : return the safe result to ensure soundness *)
          print_backtrace_quiet ();
          print_endline_quiet ("WARNING for "^st^" : Restarting prover due to timeout");
          Unix.kill !prover_process.pid 9;
          ignore (Unix.waitpid [] !prover_process.pid);
          { original_output_text = []; sat_result = Aborted; }
  ) in
  let () = Procutils.PrvComms.stop false stdout !prover_process 0 9 (fun () -> ()) in
  remove_file infile;
  remove_file outfile;
  res

(*for z3-3.2*)
let rec prelude () = ()

(* start z3 system in a separated process and load redlog package *)
and start() =
  try (
    if not !is_z3_running then (
      print_string_if (not !compete_mode (* && not !Globals.web_compile_flag *)) "Starting z3... \n"; flush stdout;
      last_test_number := !test_number;
      let () = (
        if !smtsolver_name = "z3-2.19" then
          Procutils.PrvComms.start !log_all_flag log_all (!smtsolver_name, !smtsolver_name, [|!smtsolver_name; "-smt2"|]) set_process (fun () -> ())
        else if !smtsolver_name = "z3-4.2" then
          Procutils.PrvComms.start !log_all_flag log_all (!smtsolver_name, "z3-4.2", [|!smtsolver_name; "-smt2";"-in"|]) set_process prelude
        else if !smtsolver_name = "z3-4.3.1" then
          Procutils.PrvComms.start !log_all_flag log_all (!smtsolver_name, "./z3-4.3.1", [|!smtsolver_name; "-smt2";"-in"|]) set_process prelude
        else
          Procutils.PrvComms.start !log_all_flag log_all (!smtsolver_name, !smtsolver_path, [|!smtsolver_path; "-smt2"; "-in"|]) set_process prelude
      ) in
      is_z3_running := true;
    )
  )
  with e -> (
    if (!compete_mode) then (
      print_endline_quiet "Unable to run the prover Z3!";
      print_endline_quiet ("Please make sure its executable file (" ^ !smtsolver_name ^ ") is installed")
    );
    raise e
  )

(* stop Z3 system *)
let stop () =
  if !is_z3_running then (
    let num_tasks = !test_number - !last_test_number in
    print_string_if !Globals.enable_count_stats ("Stop z3... "^(string_of_int !z3_call_count)^" invocations "); flush stdout;
    let () = Procutils.PrvComms.stop !log_all_flag log_all !prover_process num_tasks Sys.sigkill (fun () -> ()) in
    is_z3_running := false;
  )

(* restart Z3 system *)
let restart reason =
  if !is_z3_running then (
    let () = print_string_if !Globals.enable_count_stats (reason^" Restarting z3 after ... "^(string_of_int !z3_call_count)^" invocations. ") in
    Procutils.PrvComms.restart !log_all_flag log_all reason "z3" start stop
  ) else (
    let () = print_string_if !Globals.enable_count_stats (reason^" not restarting z3 ... "^(string_of_int !z3_call_count)^" invocations ") in
    ()
  )

(* send formula to z3 and receive result -true/false/unknown*)
let check_formula f timeout =
  let tstartlog = Gen.Profiling.get_time () in 
  if not !is_z3_running then start ()
  else if (!z3_call_count = !z3_restart_interval) then (
    restart("Regularly restart:1 ");
    z3_call_count := 0;
  );
  let fnc f = (
    let () = incr z3_call_count in
    (*due to global stack - incremental, push current env into a stack before working and
      removing it after that. may be improved *)
    let new_f = "(push)\n" ^ f ^ "(pop)\n" in
    let _= if(!proof_logging_txt) then add_to_z3_proof_log_list new_f in
    output_string (!prover_process.outchannel) new_f;
    flush (!prover_process.outchannel);
    if (!Globals.get_model && !smtsolver_name="z3-4.2") then
      iget_answer2 (!prover_process.inchannel) f
    else
      iget_answer (!prover_process.inchannel) f
  ) in
  let fail_with_timeout () = (
    (* let () = print_endline ("#### fail_with_timeout f = " ^ f) in *)
      let to_msg = if !compete_mode then "" else "[smtsolver.ml]Timeout when checking sat!" ^ (string_of_float timeout) in
    restart (to_msg);
    { original_output_text = []; sat_result = Unknown; } 
  ) in
  let res = Procutils.PrvComms.maybe_raise_and_catch_timeout fnc f timeout fail_with_timeout in
  let tstoplog = Gen.Profiling.get_time () in
  let _= Globals.z3_time := !Globals.z3_time +. (tstoplog -. tstartlog) in 
  res

let check_formula f timeout =
  Debug.no_2 "Z3:check_formula" idf string_of_float string_of_smt_output
    check_formula f timeout

let check_formula f timeout =
  Gen.Profiling.no_2 "smt_check_formula" check_formula f timeout

(***************************************************************
   GENERATE SMT INPUT FOR IMPLICATION/SATISFIABILITY CHECKING   
 **************************************************************)


(**
 * Logic types for smt solvers
 * based on smt-lib benchmark specs
 *)
type smtlogic =
  | QF_LIA    (* quantifier free linear integer arithmetic *)
  | QF_NIA    (* quantifier free nonlinear integer arithmetic *)
  | AUFLIA    (* arrays, uninterpreted functions and linear integer arithmetic *)
  | UFNIA     (* uninterpreted functions and nonlinear integer arithmetic *)

let string_of_logic logic =
  match logic with
  | QF_LIA -> "QF_LIA"
  | QF_NIA -> "QF_NIA"
  | AUFLIA -> "AUFLIA"
  | UFNIA -> "UFNIA"

(* output for smt-lib v2.0 format *)
let to_smt_v2 pr_weak pr_strong ante conseq fvars0 info =
  (* Variable declarations *)
  (*let _ = List.map (fun c -> print_string(" "^(!print_ty_sv c))) fvars in*)
  let fvars = List.filter (fun sv -> not (Cpure.is_rel_typ sv)) (Cpure.remove_dups_svl fvars0) in
  let smt_var_decls = List.map (fun v ->
    let tp = (CP.type_of_spec_var v)in
    let t = smt_of_typ tp in
    match tp with
    | FuncT _ -> "(declare-fun " ^ (smt_of_spec_var v) ^ " " ^ t ^ ")\n"
    | _ -> "(declare-fun " ^ (smt_of_spec_var v) ^ " () " ^ (t) ^ ")\n"
  ) fvars in
  let smt_var_decls = String.concat "" smt_var_decls in
  (* Relations that appears in the ante and conseq *)
  let used_rels = info.relations in
  let rel_decls = String.concat "" (List.map (fun x -> x.rel_cache_smt_declare_fun) !global_rel_defs) in
  (* let _ = Debug.info_hprint (add_str "rel_decls" (pr_id)) rel_decls no_pos in *)
  let rel_decls = String.concat "" (List.map (fun x -> if (List.mem x.rel_name used_rels) then x.rel_cache_smt_declare_fun else "") !global_rel_defs) in
  (* Necessary axioms *)
  (* let axiom_asserts = String.concat "" (List.map (fun x -> x.axiom_cache_smt_assert) !global_axiom_defs) in *) (* Add all axioms; in case there are bugs! *)
  let axiom_asserts = String.concat "" (List.map (fun ax_id ->
      (* let _ = Debug.info_hprint (add_str " ax_id" (string_of_int))  ax_id no_pos in *)
      let ax = List.nth !global_axiom_defs ax_id in
      ax.axiom_cache_smt_assert) info.axioms) in
  (* Antecedent and consequence : split /\ into small asserts for easier management *)
  let ante_clauses = CP.split_conjunctions ante in
  let ante_clauses = Gen.BList.remove_dups_eq CP.equalFormula ante_clauses in
  let ante_strs = List.map (fun x -> "(assert " ^ (smt_of_formula pr_weak pr_strong x) ^ ")\n") ante_clauses in
  let ante_str = String.concat "" ante_strs in
  let conseq_str = smt_of_formula pr_weak pr_strong conseq in (
    ";Variables declarations\n" ^ 
      smt_var_decls ^
    ";Relations declarations\n" ^ 
      rel_decls ^
    ";Axioms assertions\n" ^ 
      axiom_asserts ^
    ";Antecedent\n" ^ 
      ante_str ^
    ";Negation of Consequence\n" ^ "(assert (not " ^ conseq_str ^ "))\n" ^
    "(check-sat)" ^
    (if (!Globals.get_model && !smtsolver_name="z3-4.2") then "\n(get-model)" else "")
  )

(* output for smt-lib v1.2 format *)
and to_smt_v1 ante conseq logic fvars =
  let rec defvars vars = match vars with
    | [] -> ""
    | var::rest -> "(" ^ (smt_of_spec_var var) ^ " Int) " ^ (defvars rest)
  in
  (* let () = print_endline ("#### ante = " ^ (!CP.print_formula ante)) in *)
  let (pr_w,pr_s) = CP.drop_complex_ops in
  let ante = smt_of_formula pr_w pr_s ante in
  let conseq = smt_of_formula pr_w pr_s conseq in
  (*--------------------------------------*)
  let extrafuns = 
    if fvars = [] then "" 
    else ":extrafuns (" ^ (defvars fvars) ^ ")\n"
  in (
    "(benchmark blahblah \n" ^
    ":status unknown\n" ^
    ":logic " ^ (string_of_logic logic) ^ "\n" ^
    extrafuns ^
    ":assumption " ^ ante ^ "\n" ^
    ":formula (not " ^ conseq ^ ")\n" ^
    ")"
  )

(* Converts a core pure formula into SMT-LIB format which can be run through various SMT provers. *)
let to_smt pr_weak pr_strong (ante : CP.formula) (conseq : CP.formula option) (prover: smtprover) : string =
  let conseq = match conseq with
    (* We don't have conseq part in is_sat checking *)
    | None -> CP.mkFalse no_pos
    | Some f -> f
  in
  (* (*drop VarPerm beforehand*)                        *)
  (* let ante,conseq =                                  *)
  (*   if (!Globals.ann_vp) then                        *)
  (*     let conseq = CP.drop_varperm_formula conseq in *)
  (*     let ante = CP.drop_varperm_formula ante in     *)
  (*     (ante,conseq)                                  *)
  (*   else (ante,conseq)                               *)
  (* in                                                 *)
  (*-----------------------------*)
  let conseq_info = collect_formula_info conseq in
  (* remove occurences of dom in ante if conseq has nothing to do with dom *)
  let ante = 
    if (not (List.mem "dom" conseq_info.relations)) then
      CP.remove_primitive (fun x -> 
        match x with 
        | CP.RelForm (r, _ , _) -> CP.name_of_spec_var r = "dom" 
        | _ -> false
      ) ante 
    else ante in
  let _ = Debug.ninfo_hprint (add_str "ante" !CP.print_formula) ante no_pos in
  let ante_info = collect_formula_info ante in
  let info = combine_formula_info ante_info conseq_info in
  let ante_fv = CP.fv ante in
  let conseq_fv = CP.fv conseq in
  let all_fv = Gen.BList.remove_dups_eq (=) (ante_fv @ conseq_fv) in
  let res = to_smt_v2 pr_weak pr_strong ante conseq all_fv info in
    (* let () = print_endline (" ### res = \n " ^ res) in *)
    res
  
let to_smt pr_weak pr_strong (ante : CP.formula) (conseq : CP.formula option) (prover: smtprover) = 
  Debug.no_1 "to_smt" (fun _ -> "") (fun c -> c) (fun c-> to_smt pr_weak pr_strong ante conseq prover) prover

(***************************************************************
                         CONSOLE OUTPUT                         
 **************************************************************)

type output_configuration = {
    (* transferred to Globals *)
  (* print_original_solver_input                   : bool ref; (\* print generated SMT input *\) *)
  (* print_original_solver_output : bool ref; (\* print solver original output *\) *)
  print_implication            : bool ref; (* print the implication problems sent to this smt_imply *)
  suppress_print_implication   : bool ref; (* temporary suppress all printing *)
}

(* Global collection of printing control switches, set by scriptarguments *)
let outconfig = {
  (* print_original_solver_input = ref false; *)
  (* print_original_solver_output = ref false; *)
  print_implication = ref false; 
  suppress_print_implication = ref false;
}

(* Function to suppress and unsuppress all output of this modules *)

let suppress_all_output () = outconfig.suppress_print_implication := true

let unsuppress_all_output () = outconfig.suppress_print_implication := false

let process_stdout_print ante conseq input output res =
  if (not !(outconfig.suppress_print_implication)) then
  begin
    if !(outconfig.print_implication) then 
      print_endline_quiet ("CHECKING IMPLICATION:\n\n" ^ (!print_pure ante) ^ " |- " ^ (!print_pure conseq) ^ "\n");
    if !(Globals.print_original_solver_input) then (
      print_endline_quiet (">>> GENERATED SMT INPUT:\n\n" ^ input);
      flush stdout;
    );
    if !(Globals.print_original_solver_output) then (
      print_endline_quiet (">>> Z3 OUTPUT RECEIVED:\n" ^ (string_of_smt_output output));
      print_endline_quiet (match output.sat_result with
        | UnSat -> ">>> VERDICT: UNSAT/VALID!"
        | Sat -> ">>> VERDICT: FAILED!"
        | Unknown -> ">>> VERDICT: UNKNOWN! CONSIDERED AS FAILED."
        | Aborted -> ">>> VERDICT: ABORTED! CONSIDERED AS FAILED.");
      flush stdout;
    );
    if (!(outconfig.print_implication) || !(Globals.print_original_solver_input) || !(Globals.print_original_solver_output)) then
      print_string "\n";
  end

(**************************************************************
   MAIN INTERFACE : CHECKING IMPLICATION AND SATISFIABILITY    
 *************************************************************)

let try_induction = ref false
let max_induction_level = ref 0

(** 
 * Select the candidates to do induction on. Just find all
 * relation dom(_,low,high) that appears and collect the 
 * { high - low } such that ante |- low <= high.
 *)
let rec collect_induction_value_candidates (ante : CP.formula) (conseq : CP.formula) : (CP.exp list) =
  (*let () = print_string ("collect_induction_value_candidates :: ante = " ^ (!print_pure ante) ^ "\nconseq = " ^ (!print_pure conseq) ^ "\n") in*)
  match conseq with
  | CP.BForm (b,_) -> (
    let (p, _) = b in match p with
      | CP.RelForm (r,[value],_) -> 
          if (CP.name_of_spec_var r) ="induce" then [value]
          else []
      | _ -> []
    )
  | CP.And (f1,f2,_) -> (collect_induction_value_candidates ante f1) @ (collect_induction_value_candidates ante f2)
  | CP.AndList _ -> Gen.report_error no_pos "smtsolver.ml: encountered AndList, should have been already handled"
  | CP.Or (f1,f2,_,_) -> (collect_induction_value_candidates ante f1) @ (collect_induction_value_candidates ante f2)
  | CP.Not (f,_,_) -> (collect_induction_value_candidates ante f)
  | CP.Forall _ | CP.Exists _ -> []
        
(** 
    * Select the value to do induction on.
    * A simple approach : induct on the length of an array.
*)
and choose_induction_value (ante : CP.formula) (conseq : CP.formula) (vals : CP.exp list) : CP.exp =  List.hd vals


(** 
    * Create a variable totally different from the ones in vlist.
*)
and create_induction_var (vlist : CP.spec_var list) : CP.spec_var =
  (*let () = print_string "create_induction_var\n" in*)
  (* We select the appropriate variable with name "omg_i"*)
  (* with i minimal natural number such that omg_i is not in vlist *)
  let rec create_induction_var_helper vlist i = (
    match vlist with
    | [] -> i
    | hd :: tl -> 
        let v = CP.SpecVar (Int,"omg_" ^ (string_of_int i),Unprimed) in
        if List.mem v vlist then
          create_induction_var_helper tl (i+1)
        else 
          create_induction_var_helper tl i
  ) in let i = create_induction_var_helper vlist 0 in
  CP.SpecVar (Int,"omg_" ^ (string_of_int i),Unprimed)
	  
(** 
    * Generate the base case, induction hypothesis and induction case
    * for a formula phi(v,v_1,v_2,...) with new induction variable v.
    * v = expression of v_1,v_2,...
*)
(*and gen_induction_formulas (f : formula) (indval : exp) : 
  (formula * formula * formula) =
  let p = fv f in (* collect free variables in f *)
  let v = create_induction_var p in (* create induction variable *)
  let fv = mkAnd f (mkEqExp (mkVar v no_pos) indval no_pos) no_pos in (* fv(v) = f /\ (v = indval) *)
  let f0 = apply_one_term (v, mkIConst 0 no_pos) fv in (* base case fv[v/0] *)
  let fhyp = mkForall p fv None no_pos in (* induction hypothesis, add universal quantifiers to all free variables in f *)
  let fvp1 = apply_one_term (v, mkAdd (mkVar v no_pos) (mkIConst 1 no_pos) no_pos) fv in (* inductive case fv[v/v+1], we try to prove fhyp --> fv[v/v+1] *)
  (f0, fhyp, fvp1)*)

(** 
    * Generate the base case, induction hypothesis and induction case
    * for Ante -> Conseq
*)
and gen_induction_formulas (ante : CP.formula) (conseq : CP.formula) (indval : CP.exp) : 
	  ((CP.formula * CP.formula) * (CP.formula * CP.formula)) =
  (*let () = print_string "gen_induction_formulas\n" in*)
  let p = CP.fv ante @ CP.fv conseq in
  let v = create_induction_var p in 
  (* let () = print_string ("Inductiom variable = " ^ (CP.string_of_spec_var v) ^ "\n") in *)
  let ante = CP.mkAnd (CP.mkEqExp (CP.mkVar v no_pos) indval no_pos) ante no_pos in
  (* base case ante /\ v = 0 --> conseq *)
  let ante0 = CP.apply_one_term (v, CP.mkIConst 0 no_pos) ante in
  (* let () = print_string ("Base case: ante = "	^ (!print_pure ante0) ^ "\nconseq = " ^ (!print_pure conseq) ^ "\n") in *)
  (* ante --> conseq *)
  let aimpc = (CP.mkOr (CP.mkNot ante None no_pos) conseq None no_pos) in
  (* induction hypothesis = \forall {v_i} : (ante -> conseq) with v_i in p *)
  let indhyp = CP.mkForall p aimpc None no_pos in
  (* let () = print_string ("Induction hypothesis: ante = "	^ (!print_pure indhyp) ^ "\n") in *)
  let vp1 = CP.mkAdd (CP.mkVar v no_pos) (CP.mkIConst 1 no_pos) no_pos in
  (* induction case: induction hypothesis /\ ante(v+1) --> conseq(v+1) *)
  let ante1 = CP.mkAnd indhyp (CP.apply_one_term (v, vp1) ante) no_pos in
  let conseq1 = CP.apply_one_term (v, vp1) conseq in
  (* let () = print_string ("Inductive case: ante = "	^ (!print_pure ante1) ^ "\nconseq = " ^ (!print_pure conseq1) ^ "\n") in *)
  ((ante0,conseq),(ante1,conseq1))

(** 
    * Check implication with induction heuristic.
*)
and smt_imply_with_induction (ante : CP.formula) (conseq : CP.formula) (prover: smtprover) : bool =
  (*let () = print_string (" :: smt_imply_with_induction : ante = "	^ (!print_pure ante) ^ "\nconseq = " ^ (!print_pure conseq) ^ "\n") in*)
  let vals = collect_induction_value_candidates ante (CP.mkAnd ante conseq no_pos) in
  if (vals = []) then false (* No possible value to do induction on *)
  else (
    let indval = choose_induction_value ante conseq vals in
    let bc,ic = gen_induction_formulas ante conseq indval in
    let a0 = fst bc in
    let c0 = snd bc in
    (* check the base case first *)
    let (pr_w,pr_s) = Cpure.drop_complex_ops in
    let bcv = smt_imply pr_w pr_s a0 c0 prover 15.0 in
    if bcv then (* base case is valid *)
      let a1 = fst ic in
      let c1 = snd ic in
      let (pr_w,pr_s) = CP.drop_complex_ops in
      smt_imply pr_w pr_s a1 c1 prover 15.0 (* check induction case *)
    else 
      false
  )

(**
   * Test for validity
   * To check the implication P -> Q, we check the satisfiability of
   * P /\ not Q
   * If it is satisfiable, then the original implication is false.
   * If it is unsatisfiable, the original implication is true.
   * We also consider unknown is the same as sat
*)

and smt_imply pr_weak pr_strong (ante : Cpure.formula) (conseq : Cpure.formula) (prover: smtprover) timeout : bool =
  let pr = !print_pure in
  Debug.no_2(* _loop *) "smt_imply" (pr_pair pr pr) string_of_float string_of_bool
      (fun _ _-> smt_imply_x  pr_weak pr_strong ante conseq prover timeout) (ante, conseq) timeout

and smt_imply_x pr_weak pr_strong (ante : Cpure.formula) (conseq : Cpure.formula) (prover: smtprover) timeout : bool =
  (* let () = print_endline ("smt_imply : " ^ (!print_pure ante) ^ " |- " ^ (!print_pure conseq) ^ "\n") in *)
  (* (*drop VarPerm beforehand*)                        *)
  (* let ante,conseq = (                                *)
  (*   if (!Globals.ann_vp) then                        *)
  (*     let conseq = CP.drop_varperm_formula conseq in *)
  (*     let ante = CP.drop_varperm_formula ante in     *)
  (*     (ante,conseq)                                  *)
  (*   else                                             *)
  (*     (ante,conseq)                                  *)
  (* ) in                                               *)
  (*--------------------------------------*)
  (* let () = print_endline ("#### [smt_imply] ante = " ^ (!CP.print_formula ante)) in *)
  (* let () = print_endline ("#### [smt_imply] conseq = " ^ (!CP.print_formula conseq)) in *)
  let res, should_run_smt = (
    (* (false, true) in                                                             *)
    (* if (has_exists conseq) then                                                  *)
    (*   let (pr_w,pr_s) = CP.drop_complex_ops in                                   *)
    (*   try (                                                                      *)
    (*     match (Omega.imply_with_check_ops pr_w pr_s ante conseq "" timeout) with *)
    (*     | None -> (false, true)                                                  *)
    (*     | Some r -> (r, false)                                                   *)
    (*   ) with                                                                     *)
    (*     | _ -> (false, true)                                                     *)
    (* else                                                                         *)
      (false, true) 
  ) in
  if (should_run_smt) then
    let input = to_smt pr_weak pr_strong ante (Some conseq) prover in
    (* let input = if (Cpure.contains_exists conseq) then ("(set-option :mbqi true)\n" ^ input) else input in *)
    let () = !set_generated_prover_input input in
    let output = 
      if !smtsolver_name = "z3-2.19" then
        run "is_imply" prover input timeout
      else
        check_formula input timeout
    in
    let () = !set_prover_original_output (String.concat "\n" output.original_output_text) in
    let res = (
      match output.sat_result with
      | Sat -> false
      | UnSat -> true
      | Unknown -> false
      | Aborted -> false
    ) in
    let () = process_stdout_print ante conseq input output res in
    res
  else
    res

and has_exists conseq =
  match conseq with
  | CP.Exists _ -> true
  | _ -> false


let instantiate_array_vars_before_imply pr_w pr_s ante conseq prover timeout =
  let c_arr_vars = List.filter CP.is_arr_typ (CP.fv conseq) in
  let a_arr_vars = List.filter CP.is_arr_typ (CP.fv ante) in
  let rec helper l1 l2 = match l1 with
    | [] -> []
    | x::xs -> (List.map (fun c -> (x,c)) l2)@(helper xs l2) in
  let all_pairs = helper a_arr_vars c_arr_vars in
  let all_insts = List.map (fun (a,c) -> CP.mkEqVar a c no_pos) all_pairs in 
  (*let () = print_endline ("Ante1 : "^ !print_pure ante) in*)
  List.exists (fun p -> smt_imply pr_w pr_s (CP.mkAnd ante p no_pos) conseq prover timeout) all_insts
  
(* For backward compatibility, use Z3 as default *
 * Probably, a better way is modify the tpdispatcher.ml to call imply with a
 * specific smt-prover argument as well *)
let imply ante conseq timeout =
  let (pr_w,pr_s) = CP.drop_complex_ops in
  let f  = smt_imply pr_w pr_s ante conseq Z3 timeout in
  (*let () = print_endline ("Ante3 : "^ !print_pure ante) in*)
  if (not f && !Globals.allow_array_inst) then instantiate_array_vars_before_imply pr_w pr_s ante conseq Z3 timeout
  else f

let imply ante conseq timeout =
  Gen.Profiling.no_3 "smt_imply" imply ante conseq timeout

let imply_ops pr_weak pr_strong ante conseq timeout = 
  let f = smt_imply pr_weak pr_strong ante conseq Z3 timeout in
  (*let () = print_endline ("Ante2 : "^ !print_pure ante) in*)
  if (not f && !Globals.allow_array_inst) then instantiate_array_vars_before_imply pr_weak pr_strong ante conseq Z3 timeout
  else f

(*
let imply_ops pr_weak pr_strong ante conseq timeout = 
  Gen.Profiling.do_6 "smt_imply_ops" smt_imply pr_weak pr_strong ante conseq Z3 timeout
*)
let imply_with_check (ante : CP.formula) (conseq : CP.formula) (imp_no : string) timeout: bool option =
  CP.do_with_check2 "" (fun a c -> imply a c timeout) ante conseq

let imply (ante : CP.formula) (conseq : CP.formula) timeout: bool =
  try
    imply ante conseq timeout
  with Illegal_Prover_Format s -> (
    print_endline_quiet ("\nWARNING : Illegal_Prover_Format for :"^s);
    print_endline_quiet ("Apply z3.imply on ante Formula :"^(!print_pure ante));
    print_endline_quiet ("and conseq Formula :"^(!print_pure conseq));
    flush stdout;
    failwith s
  )

let imply (ante : CP.formula) (conseq : CP.formula) timeout: bool =
  Debug.no_1(* _loop *) "smt.imply" string_of_float string_of_bool
      (fun _ -> imply ante conseq timeout) timeout

(**
 * Test for satisfiability
 * We also consider unknown is the same as sat
 *)
let smt_is_sat pr_weak pr_strong (f : Cpure.formula) (sat_no : string) (prover: smtprover) timeout : bool =
  (* let () = print_endline ("smt_is_sat : " ^ (!print_pure f) ^ "\n") in *)
  (* (*drop VarPerm beforehand*)                           *)
  (* let f =                                               *)
  (*   if (!Globals.ann_vp) then CP.drop_varperm_formula f *)
  (*   else f                                              *)
  (* in                                                    *)
  (*--------------------------------------*)
  (* let () = print_endline ("#### [smt_is_sat] f = " ^ (!CP.print_formula f)) in *)
  let res, should_run_smt = (
    (* (false, true) in *)
    (* if (Cpure.contains_exists f) then                                    *)
    (*   try                                                                *)
    (*     let (pr_w,pr_s) = CP.drop_complex_ops in                         *)
    (*     let optr = (Omega.is_sat_with_check_ops pr_w pr_s f sat_no) in ( *)
    (*     match optr with                                                  *)
    (*       | Some r -> (r, false)                                         *)
    (*       | None -> (true, false)                                        *)
    (*     )                                                                *)
    (*   with                                                               *)
    (*     | _ -> (true, false)                                             *)
    (* else                                                                 *)
      (false, true)
  ) in
  if (should_run_smt) then
    let input = to_smt pr_weak pr_strong f None prover in
    (* let input = if (Cpure.contains_exists f) then ("(set-option :mbqi true)\n" ^ input) else input in *)
    let output = (
      if !smtsolver_name = "z3-2.19" then run "is_unsat" prover input timeout
      else check_formula input timeout
    ) in
    let res = match output.sat_result with
      | UnSat -> false
      | _ -> true in
    let () = process_stdout_print f (CP.mkFalse no_pos) input output res in
    res
  else
    res

(*let default_is_sat_timeout = 2.0*)
let is_sat_ops_x pr_weak pr_strong f sat_no = 
  smt_is_sat pr_weak pr_strong f sat_no Z3 z3_sat_timeout_limit

(* see imply *)
let is_sat f sat_no =
  let (pr_w,pr_s) = CP.drop_complex_ops in
  smt_is_sat pr_w pr_s f sat_no Z3 z3_sat_timeout_limit

let is_sat_ops pr_weak pr_strong f sat_no =
  let pr1 = !CP.print_formula in
  Debug.no_1 "z3.is_sat_ops" pr1 string_of_bool
      (fun _ -> is_sat_ops_x pr_weak pr_strong f sat_no) f

let is_sat_with_check (pe : CP.formula) sat_no : bool option = CP.do_with_check "" (fun x -> is_sat x sat_no) pe 

let is_sat (pe : CP.formula) sat_no : bool =
  try
    is_sat pe sat_no
  with Illegal_Prover_Format s -> 
    print_endline_quiet ("\nWARNING : Illegal_Prover_Format for :"^s);
    print_endline_quiet ("Apply z3.is_sat on formula :"^(!print_pure pe));
    flush stdout;
    failwith s

let is_sat f sat_no = Debug.no_2(* _loop *) "z3.is_sat" (!print_pure) (fun x->x) string_of_bool is_sat f sat_no


(**
 * To be implemented
 *)
let simplify (f: CP.formula) : CP.formula = 
  (* let () = print_endline "locle: simplify" in *)
  try
    (Omega.simplify f)
  with
    | _ -> f


let simplify (pe : CP.formula) : CP.formula =
  match (CP.do_with_check "" simplify pe) with
  | None -> pe
  | Some f -> f

let simplify (pe : CP.formula) : CP.formula =
  let pr = !CP.print_formula in
  Debug.no_1 "simplify" pr pr simplify pe 

let hull (f: CP.formula) : CP.formula = f

let pairwisecheck (f: CP.formula): CP.formula = f

(* Template Solving by Z3 *)
open Z3m

let smt_timeout = ref 5.0

let push_smt_input inp timeout f_timeout = 
  let tstartlog = Gen.Profiling.get_time () in 
  if not !is_z3_running then start ()
  else if (!z3_call_count = !z3_restart_interval) then (
    restart("Regularly restart: 1 ");
    z3_call_count := 0;
  );
  let fnc f = (
    let () = incr z3_call_count in
    let new_f = "(push)\n" ^ f ^ "(pop)\n" in
    let () = if (!proof_logging_txt) then add_to_z3_proof_log_list new_f in
    output_string (!prover_process.outchannel) new_f;
    flush (!prover_process.outchannel)) in
  let res = Procutils.PrvComms.maybe_raise_and_catch_timeout fnc inp timeout f_timeout in
  let tstoplog = Gen.Profiling.get_time () in
  let () = Globals.z3_time := !Globals.z3_time +. (tstoplog -. tstartlog) in 
  res

let get_model is_linear vars assertions =
  (* Variable declarations *)
  let smt_var_decls = List.map (fun v ->
    let typ = (CP.type_of_spec_var v)in
    let t = smt_of_typ typ in
    "(declare-const " ^ (smt_of_spec_var v) ^ " " ^ t ^ ")\n"
  ) vars in
  let smt_var_decls = String.concat "" smt_var_decls in

  let (pr_w, pr_s) = CP.drop_complex_ops_z3 in
  let smt_asserts = List.map (fun a ->
    "(assert " ^ (smt_of_formula pr_w pr_s a) ^ ")\n") assertions in
  let smt_asserts = String.concat "" smt_asserts in
  let smt_inp = 
    ";Variables Declarations\n" ^ smt_var_decls ^
    ";Assertion Declations\n" ^ smt_asserts ^
    (if is_linear then "(check-sat)" else "(check-sat-using qfnra-nlsat)") ^ "\n" ^
    (* "(check-sat)\n" ^ *)
    "(get-model)\n"
  in
  
  (* let () = print_endline ("smt_inp: \n" ^ smt_inp) in *)

  let fail_with_timeout _ = (
    restart ("[smtsolver.ml] Timeout when getting model!" ^ (string_of_float !smt_timeout))
  ) in
  let () = push_smt_input smt_inp !smt_timeout fail_with_timeout in

  let r =
    try
      let lexbuf = Lexing.from_channel !prover_process.inchannel in
      Z3mparser.output Z3mlexer.tokenizer lexbuf
    with _ -> Sat_or_Unk []
  in r

let get_model is_linear vars assertions =
  let pr1 = pr_list !CP.print_formula in
  let pr2 = string_of_z3m_res in
  Debug.no_1 "z3_get_model" pr1 pr2
  (fun _ -> get_model is_linear vars assertions) assertions

let norm_model (m: (string * z3m_val) list): (string * int) list =
  let vl, il = List.split m in
  let il = z3m_val_to_int il in
  let m = List.combine vl il in
  m
  (* let mi = List.map (fun (_, i) -> i) m in   *)
  (* let gcd_mi = abs (gcd_l mi) in             *)
  (* List.map (fun (v, i) -> (v, i / gcd_mi)) m *)

let norm_model (m: (string * z3m_val) list): (string * int) list =
  let pr1 = pr_list (pr_pair idf string_of_z3m_val) in
  let pr2 = pr_list (pr_pair idf string_of_int) in
  Debug.no_1 "z3_norm_model" pr1 pr2
  norm_model m
