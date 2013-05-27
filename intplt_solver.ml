open Globals
module S = Smtlib_syntax
module C = Cpure

(* interpolant solver by Shengyi Wang*)
let (--) i j = 
  let rec aux n acc =
    if n < i then acc else aux (n-1) (n :: acc)
  in aux j []

let rec sublist b e l = 
  match l with
    [] -> failwith "sublist"
  | h :: t -> 
     let tail = if e=0 then [] else sublist (b-1) (e-1) t in
     if b>0 then tail else h :: tail

let write_interpolant filename intplts=
  let oc = open_out filename in
  List.iter (fun x -> Printf.fprintf oc "%s\n" x) intplts;
  close_out oc;;

let read_interpolant filename =
  let lines = ref [] in
  let chan = open_in filename in
  try
    while true; do
      lines := input_line chan :: !lines
    done; []
  with End_of_file ->
    close_in chan;
    List.rev !lines ;;

let test_term (term:S.term) =
  match term with
    S.TermSpecConst _ -> Printf.printf "S.TermSpecConst\n"
  | S.TermQualIdentifier _ -> Printf.printf "S.TermQualIdentifier\n"
  | S.TermQualIdTerm _ -> Printf.printf "S.TermQualIdTerm\n"
  | S.TermLetTerm _ -> Printf.printf "S.TermLetTerm\n"
  | S.TermForAllTerm _ -> Printf.printf "S.TermForAllTerm\n"
  | S.TermExistsTerm _ -> Printf.printf "S.TermExistsTerm\n"
  | S.TermExclimationPt _ -> Printf.printf "S.TermExclimationPt\n"

let get_qualidentifier (s:S.qualidentifier) : string = 
  match s with
    S.QualIdentifierId (_, S.IdSymbol (_, S.Symbol(_, x))) -> x
  | _ -> illegal_format "other identifier not supported yet";;

let convert_to_pform (s:string) (sub_terms: S.term list) : C.p_formula =
  match s with
  "true" -> C.BConst (true, no_pos)
  | _ -> C.BConst (false, no_pos)

let convert_identifier (s:string) : C.formula = 
  match s with
    "true" -> C.BForm ((C.BConst (true, no_pos), None), None, [[]])
  | "false" -> C.BForm ((C.BConst (false, no_pos), None), None, [[]])
  | _ -> illegal_format "other identifier not supported yet";;

let rec convert_exp (t:S.term) : C.exp =
  match t with
    S.TermQualIdTerm (_, s,(_, sub_terms)) -> convert_to_exp (get_qualidentifier s) sub_terms
  | S.TermSpecConst (_,S.SpecConstNum (_, x)) -> C.IConst (int_of_string x, no_pos)
  | S.TermSpecConst _ -> illegal_format "const not supported yet"
  | S.TermQualIdentifier (_, S.QualIdentifierId(_, S.IdSymbol (_, S.Symbol(_, x)))) -> C.Var(C.SpecVar(Int,x,Unprimed),[])
  | S.TermQualIdentifier _ -> illegal_format "identifier not supported"
  | S.TermLetTerm _ -> illegal_format "S.TermLetTerm not supported yet\n"
  | S.TermForAllTerm _ -> illegal_format "S.TermForAllTerm not supported yet\n"
  | S.TermExistsTerm _ -> illegal_format "S.TermExistsTerm not supported yet\n"
  | S.TermExclimationPt _ -> illegal_format "S.TermExclimationPt not supported yet\n" 

and convert_to_exp (s:string) (sub_terms: S.term list) : C.exp = 
  let term1 = List.hd sub_terms in
  let term2 = if (List.length sub_terms == 2) 
    then
      Some(List.hd (List.tl sub_terms))
    else
      None
  in
  match s with
    "+" -> C.Add (convert_exp term1, convert_exp (Option.get(term2)), no_pos);
  | "-" -> 
    (match term2 with
      None -> C.Subtract (C.IConst(0,no_pos), convert_exp term1, no_pos)
    | Some t -> C.Subtract (convert_exp term1, convert_exp t, no_pos));
  | "*" -> C.Mult (convert_exp term1, convert_exp (Option.get(term2)), no_pos)
  | "/" -> C.Div (convert_exp term1, convert_exp (Option.get(term2)), no_pos)
  | _ -> illegal_format "Other operator not supported yet"

let convert_to_pform (s:string) (sub_terms: S.term list) : C.p_formula =
  let term1 = List.hd sub_terms in
  let term2 = List.hd (List.tl sub_terms) in
  match s with
    "<" -> C.Lt (convert_exp term1, convert_exp term2, no_pos)
  | "<=" -> C.Lte (convert_exp term1, convert_exp term2, no_pos)
  | ">" -> C.Gt (convert_exp term1, convert_exp term2, no_pos)
  | ">=" -> C.Gte (convert_exp term1, convert_exp term2, no_pos)
  | "=" -> C.Eq (convert_exp term1, convert_exp term2, no_pos)
  | _ -> illegal_format "other operation not supported yet" 

let rec convert_to_pure (s:string) (sub_terms: S.term list) : C.formula =
  match s with
    "and" -> 
      if (List.length sub_terms = 2) 
      then
        C.And (convert_term (List.hd sub_terms), convert_term (List.hd (List.tl sub_terms)), no_pos)
      else
        C.AndList (List.map (fun x -> ([], convert_term x)) sub_terms);
  | "or" -> C.Or (convert_term (List.hd sub_terms), convert_term (List.hd (List.tl sub_terms)), None, no_pos)
  | "not" -> C.Not (convert_term (List.hd sub_terms), None, no_pos)
  | _ -> C.BForm ((convert_to_pform s sub_terms, None), None, [[]])

and convert_term (term:S.term):C.formula = 
    match term with
      S.TermQualIdTerm (_, s,(_, sub_terms)) -> convert_to_pure (get_qualidentifier s) sub_terms
    | S.TermSpecConst _ -> illegal_format "S.TermSpecConst not supported yet\n"
    | S.TermQualIdentifier (_, S.QualIdentifierId(_, S.IdSymbol (_, S.Symbol(_, x)))) -> convert_identifier x
    | S.TermLetTerm (_,(_, varbinding),sub_term )-> combine_binding_term (convert_bindings varbinding) (convert_term sub_term)
    | S.TermForAllTerm _ -> illegal_format "S.TermForAllTerm not supported yet\n"
    | S.TermExistsTerm _ -> illegal_format "S.TermExistsTerm not supported yet\n"
    | S.TermExclimationPt _ -> illegal_format "S.TermExclimationPt not supported yet\n" 
    | _ -> illegal_format "Not supported"

and convert_bindings bindings:C.formula =
  match (List.length bindings) with
    1 -> convert_binding (List.hd bindings)
  | 2 -> C.And (convert_binding (List.hd bindings), convert_binding (List.hd (List.tl bindings)), no_pos)
  | _ -> C.AndList (List.map (fun x -> ([],convert_binding x)) bindings)

and convert_binding binding:C.formula = 
  match binding with
    S.VarBindingSymTerm (_, (S.Symbol (_,s)), term) -> C.BForm ((C.Eq(C.Var(C.SpecVar(Int,s,Unprimed),[]), convert_exp term,no_pos),None), None, [[]])
  | _ -> illegal_format "SymbolWithOr not supported"

and combine_binding_term (binding_formula:C.formula) (term_formula:C.formula) : C.formula = 
  C.And (binding_formula, term_formula, no_pos)

let convert_interpolant (cmd:S.term) : (C.formula list) = 
  match cmd with
    S.TermQualIdTerm (_, _, (_,x)) -> List.map convert_term x
  | _ -> illegal_format "Not well formed formula"

let get_interpolant (cmds:S.commands) : (C.formula list) =
  (* let _ = Smtlib_pp.pp cmds in *)
  let S.Commands (_, (_, asserts)) = cmds in
  match (List.hd asserts) with
    S.CommandAssert (_, x) -> convert_interpolant x
  | _ -> []      

let gen_interpolant (ante:C.formula) (conseq:C.formula) : bool = 
  let (pr_weak,pr_strong) = C.drop_complex_ops in
  let fml_str = Smtsolver.to_smt pr_weak pr_strong ante (Some conseq) Smtsolver.Z3 in
  (* let _ = Printf.printf "%s\n" fml_str in *)
  let formula_list = Str.split (Str.regexp "\n") fml_str in
  let assert_regexp = Str.regexp "(assert .+" in
  let (asserts, nonasserts) = List.partition (fun x -> Str.string_match assert_regexp x 0) formula_list in
  let nonasserts = List.append ["(set-option :print-success false)";"(set-option :produce-proofs true)";"(set-logic QF_LIA)"] nonasserts in
  let nonasserts = sublist 0 (List.length nonasserts - 2) nonasserts in
  let ass_len = String.length "(assert " in
  let ass_not_len = String.length "(assert (not " in
  let ante_list = List.rev (List.tl (List.rev asserts)) in
  let conseq_alone = List.hd (List.rev asserts) in
  let ante_list = List.map (fun x -> String.sub x ass_len ((String.length x)- ass_len - 1)) ante_list in
  let conseq_alone = String.sub conseq_alone ass_not_len ((String.length conseq_alone)- ass_not_len - 2) in
  let asserts = List.append ante_list [conseq_alone] in
  let asserts = List.map2 (fun x i -> "(assert (! " ^ x ^ " :named IP_" ^ (string_of_int i)^"))") asserts (1--(List.length asserts)) in
  let formula_list = List.append nonasserts asserts in
  let ips = List.map (fun x -> "IP_"^(string_of_int x)) (1--(List.length asserts)) in
  let intplt_str = "(get-interpolants "^ (String.concat " " ips)^")" in
  let formula_list = List.append formula_list ["(check-sat)"; intplt_str] in
  let _ = write_interpolant "interpolant.input" formula_list in
  let _ = Unix.system "java -jar /usr/java/smtinterpol.jar interpolant.input > interpolant.out" in
  let result = read_interpolant "interpolant.out" in
  let last_line = List.hd (List.rev result) in
  (* let last_line = "((<= input 41) (<= y 5) (<= y (- 5)))" in *)
  let interpolant_formula = "(assert (and" ^ (String.sub last_line 1 (String.length last_line - 1)) ^ ")" in
  (* let _ = Printf.printf "%s\n" interpolant_formula in *)
  let lexbuf = Lexing.from_string interpolant_formula in
  let parsed = Smtlib_parse.main Smtlib_lex.token lexbuf in
  let returned_formula = 
    match parsed with
      None -> []
    | Some (x) -> get_interpolant x in
  let _ = List.map (fun x -> Printf.printf "%s\n" (Cprinter.string_of_pure_formula x)) returned_formula in
  let _ = print_string "\n" in
  true

