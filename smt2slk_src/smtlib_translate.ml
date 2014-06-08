open Smtlib_syntax;;

(* let tbl_paradef : (string, string) Hashtbl.t = Hashtbl.create 1 *)

let tbl_preddef : (string, string) Hashtbl.t = Hashtbl.create 1

let tbl_selfdef : (string, string) Hashtbl.t = Hashtbl.create 1

(* let tbl_sortdef : (string, string) Hashtbl.t = Hashtbl.create 1 *)

let tbl_sortdef : (string, string list) Hashtbl.t = Hashtbl.create 1

let tbl_vardef  : (string, string) Hashtbl.t = Hashtbl.create 1

let checkentail = ref 0

type status = | Valid | Fail | Unknown

let expected_res = ref Unknown

let string_of_status = function
  | Valid -> "Valid"
  | Fail -> "Fail"
  | _ -> ""

let rec dummy () = ()

and same_symbol sy1 so =
  match so with
      | SortIdSortMulti (_, _, (_, sol)) ->
            let so = List.hd sol in (
            match so with
              | SortIdentifier (_, id) -> (
                    match id with
                      | IdSymbol (_ , sy2) -> (
                            match (sy1,sy2) with
                              | (Symbol (_, str1), Symbol (_, str2)) -> str1 = str2
                              | _ -> false )
                      | _ -> false )
              | _ -> false )
      | _ -> false

and collect_sort_data sy cl =
  let helper c =
    match c with
      | CommandDeclareFun (_, fsy, _, so) ->
            if same_symbol sy so
            then (
                let s1 = trans_sort so in
                let s2 = trans_symbol fsy in
                let s3 = ";\n" in
                s1 ^ s2 ^ s3
            ) else
              ""
      | _ -> ""
  in
  List.fold_left (fun s c -> s ^ (helper c)) "" cl

and get_str_symbol sy =
  let str = match sy with
    | Symbol (_ , str) -> str
    | SymbolWithOr (_, str) -> str
  in (
      try
        let self = Hashtbl.find tbl_selfdef str in
        self
      with Not_found -> (
          if String.contains str '?'
          then
            String.sub str 1 ((String.length str) - 1)
          else if str = "nil"
          then
            "null"
          else
            str
      )
  )
  (* | Symbol (_ , str) -> str *)
  (* | SymbolWithOr (_ , str) -> str *)

and get_str_id id =
  match id with
    | IdSymbol (_ , sy) -> get_str_symbol sy
    | IdUnderscoreSymNum (_, sy, _) -> get_str_symbol sy

and get_str_var v =
  match v with
    | SortedVarSymSort (_,sy,_) -> get_str_symbol sy

and get_str_term t =
  match t with
    | TermQualIdentifier (_, qualId) ->
          ( match qualId with
            | QualIdentifierId (_, id) -> get_str_id id
            | QualIdentifierAs (_, id, _) -> get_str_id id
          )
    | _ -> "?in"

and get_str_sort s =
  match s with
    | SortIdentifier (pd, id) -> get_str_id id
    | SortIdSortMulti (pd, id, (_, sol)) ->
          let so = List.hd (List.tl sol) in
          get_str_sort so

and get_sort v =
  match v with
    | SortedVarSymSort (_,_,so) -> so

and get_data_fields sy cl =
  let helper c =
    match c with
      | CommandDeclareFun (_, fsy, _, so) ->
            if same_symbol sy so
            then (
                (* let s1 = trans_sort so in *)
                (* let s2 = trans_symbol fsy in *)
                (* let s3 = ";\n" in *)
                (* s1 ^ s2 ^ s3 *)
                [trans_symbol fsy]
            ) else
              []
      | _ -> []
  in
  List.fold_left (fun s c -> s@(helper c)) [] cl

and get_pto_fields t =
  match t with
    | TermQualIdTerm (_, qualId, (_, tl)) ->
          let op =
            ( match qualId with
              | QualIdentifierId (_, id) -> get_str_id id
              | QualIdentifierAs (_, id, so) -> get_str_id id
            )
          in
          if op = "ref"
          then
            [trans_term (List.hd tl)]
          else if op = "sref"
          then
            List.fold_left (fun tl t ->
                tl@(get_pto_fields t)) [] tl
          else
            []
    | _ -> []

(* and is_pure t = *)
(*   match t with *)
(*     | TermQualIdTerm (_, qualId, (_, tl)) -> *)
(*           let op = *)
(*             ( match qualId with *)
(*               | QualIdentifierId (_, id) -> get_str_id id *)
(*               | QualIdentifierAs (_, id, _) -> get_str_id id *)
(*             ) *)
(*           in *)
(*           not (op = "tobool") *)
(*     (\* | TermQualIdentifier (_, qualId) -> *\) *)
(*     (\*       let id = *\) *)
(*     (\*         ( match qualId with *\) *)
(*     (\*           | QualIdentifierId (_, id) -> get_str_id id *\) *)
(*     (\*           | QualIdentifierAs (_, id, _) -> get_str_id id *\) *)
(*     (\*         ) *\) *)
(*     (\*       in *\) *)
(*     (\*       not (id = "emp") *\) *)
(*     | _ -> false *)

(* and is_heap t = *)
(*   match t with *)
(*     | TermQualIdTerm (_, qualId, (_, tl)) -> *)
(*           let op = *)
(*             ( match qualId with *)
(*               | QualIdentifierId (_, id) -> get_str_id id *)
(*               | QualIdentifierAs (_, id, _) -> get_str_id id *)
(*             ) *)
(*           in *)
(*           op = "tobool" *)
(*     (\* | TermQualIdentifier (_, qualId) -> *\) *)
(*     (\*       let id = *\) *)
(*     (\*         ( match qualId with *\) *)
(*     (\*           | QualIdentifierId (_, id) -> get_str_id id *\) *)
(*     (\*           | QualIdentifierAs (_, id, _) -> get_str_id id *\) *)
(*     (\*         ) *\) *)
(*     (\*       in *\) *)
(*     (\*       id = "emp" *\) *)
(*     | _ -> false *)

and get_pure_tl tl =
  let rec helper tl =
    match tl with
      | [] -> []
      | fst_t::other_t ->
            match fst_t with
              | TermQualIdTerm (_, qualId, (_, new_tl)) ->
                    let op =
                      ( match qualId with
                        | QualIdentifierId (_, id) -> get_str_id id
                        | QualIdentifierAs (_, id, _) -> get_str_id id
                      )
                    in
                    if (op = "tobool") then
                      helper other_t
                    else if (op = "and") then
                      (helper new_tl)@(helper other_t)
                    else
                      fst_t::(helper other_t)
              | _ -> fst_t::(helper other_t)
  (*     | _ -> tl *)
  (* List.filter (fun t -> is_pure t) tl *)
  in
  helper tl

and get_heap_tl tl =
  let rec helper tl =
    match tl with
      | [] -> []
      | fst_t::other_t ->
            match fst_t with
              | TermQualIdTerm (_, qualId, (_, new_tl)) ->
                    let op =
                      ( match qualId with
                        | QualIdentifierId (_, id) -> get_str_id id
                        | QualIdentifierAs (_, id, _) -> get_str_id id
                      )
                    in
                    if (op = "tobool") then
                      fst_t::(helper other_t)
                    else if (op = "and") then
                      (helper new_tl)@(helper other_t)
                    else
                      helper other_t
               | _ -> helper other_t
  in
  helper tl
(* and get_heap_tl tl = *)
(*   List.filter (fun t -> is_heap t) tl *)

and trans_command c cl =
  match c with
    | CommandSetLogic _ -> ""
    | CommandSetOption _ -> ""
    | CommandSetInfo (_, attr) -> 
          let _ = trans_attr attr in "" 
    | CommandDeclareSort (_, sy, _) ->
          let s1 =  "\ndata " in
          let sy_str = get_str_symbol sy in
          (* let _ = Hashtbl.add tbl_sortdef sy_str sy_str in *)
          let s2 = trans_symbol sy in
          let s3 = " {\n" in
          let s4 = collect_sort_data sy cl in
          let data_fields = get_data_fields sy cl in
          let _ = Hashtbl.add tbl_sortdef sy_str data_fields in
          (* let _ = List.iter (fun s -> print_endline ("data: " ^ s)) data_fields in *)
          let s5 = "}.\n" in
          s1 ^ s2 ^ s3 ^ s4 ^ s5
    | CommandDefineFun (_, sy, (_, vl), so, t) ->
          let s1 = "\npred " in
          let s2 = trans_symbol sy in
          let pred_name = get_str_symbol sy in
          let _ = Hashtbl.add tbl_preddef pred_name pred_name in
          let self_name = get_str_var (List.hd vl) in
          let _ = Hashtbl.add tbl_selfdef self_name "self" in
          let _ = Hashtbl.add tbl_vardef self_name (get_str_sort (get_sort (List.hd vl))) in
          let s3 = "<" in
          (* let s4 = trans_var_list (List.tl vl) in *)
          let s4 = trans_para_list (List.tl vl) in
          let s5 = "> ==\n" in
          let s6 = trans_term t in
          let s7 = ".\n" in
          let _ = Hashtbl.reset tbl_selfdef in
          (* Hashtbl.reset tbl_paradef; *)
          let _ = Hashtbl.reset tbl_vardef in
          s1 ^ s2 ^ s3 ^ s4 ^ s5 ^ s6 ^ s7
    | CommandDeclareFun (_, sy, _, so) -> (
          match so with
            | SortIdentifier (_, id) ->
                  Hashtbl.add tbl_vardef (get_str_symbol sy) (get_str_id id);
                  ""
            | SortIdSortMulti _ -> "" )
    | CommandAssert (_, term) ->
          if (!checkentail = 0)
          then (
              checkentail := 1;
              "\ncheckentail_exact " ^ (trans_term term)
          ) else (
              checkentail := 2;
              "\n         |- " ^ (trans_term term) ^ ".";
          )
    | CommandCheckSat _ ->
          (if (!checkentail = 1)
          then "\n         |- false."
          else "") ^ (
            match !expected_res with
            | Unknown -> ""
            | _ -> "\n\n" ^ "expect " ^ (string_of_status !expected_res) ^ "."
          )
    | _ -> "translate later\n"

and trans_attr attr = 
  match attr with
  | AttributeKeywordValue (_, ":status", value) ->
    begin match value with
    | AttributeValSymbol (_, symb) ->
      begin match symb with
      | Symbol (_, status)
      | SymbolWithOr (_, status) ->
        if ((String.compare status "unsat") == 0) then
          expected_res := Valid
        else if ((String.compare status "sat") == 0) then
          expected_res := Fail
        else ()
      end
    | _ -> () end
  | _ -> ()

and trans_term t =
  match t with
    | TermSpecConst (_, const) ->
          trans_const const
    | TermQualIdentifier (_, qualId) -> (
          match qualId with
            | QualIdentifierId (_, id) ->
                  (trans_id id)
            | QualIdentifierAs (_, id, so) ->
                  (trans_id id) ^ (trans_sort so)
      )
    | TermQualIdTerm (_, qualId, (_, tl)) ->
          let op =
            ( match qualId with
              | QualIdentifierId (_, id) -> get_str_id id
              | QualIdentifierAs (_, id, so) -> get_str_id id
            )
          in
          if op = "or"
          then (
              let s1 = " " in
              let s2 = trans_term (List.hd tl) in
              let s3 = List.fold_left (fun s t -> s ^ "\nor " ^ (trans_term t)) "" (List.tl tl) in
              s1 ^ s2 ^ s3
          ) else if op = "="
          then (
              (* print_string " "; *)
              let s1 = trans_term (List.hd tl) in
              let s2 = List.fold_left (fun s t -> s ^ " = " ^ (trans_term t)) "" (List.tl tl) in
              s1 ^ s2
          ) else if op = "pto"
          then (
              let s1 = trans_term (List.hd tl) in
              let s2 = "::" in
              (* try *)
              (*   let sort = Hashtbl.find tbl_paradef (get_str_term (List.hd tl)) in *)
              (*   print_string sort; *)
              (*   print_string "<"; *)
              (*   List.iter (fun t -> trans_term t) (List.tl tl); *)
              (*   print_string ">" *)
              (* with Not_found -> ( *)
              let s3 =
                  try
                    let sort = Hashtbl.find tbl_vardef (get_str_term (List.hd tl)) in
                    let ss1 = sort in
                    let ss2 = "<" in
                    let ss3 = List.fold_left (fun s t -> s ^ (trans_term t)) "" (List.tl tl) in
                    let pto_fields = get_pto_fields (List.hd (List.tl tl)) in
                    let data_fields = Hashtbl.find tbl_sortdef sort in
                    let ss4 = List.fold_left (fun s df ->
                        if not (List.mem df pto_fields)
                        then
                          s ^ "," ^ df ^ " = _"
                        else
                          ""
                    ) "" data_fields in
                    (* let _ = List.iter (fun t -> print_endline (trans_term t)) tmp1 in *)
                    (* let tmp2 = Hashtbl.find tbl_sortdef sort in *)
                    (* let _ = List.iter (fun t -> print_endline ("data: " ^ t)) tmp2 in *)
                    let ss5 = ">" in
                    ss1 ^ ss2 ^ ss3 ^ ss4 ^ ss5
                  with Not_found -> ""
              in
              s1 ^ s2 ^ s3
              (* ) *)
          ) else if (op = "ssep" || op = "sep")
          then (
              (* print_string " "; *)
              let s1 = trans_term (List.hd tl) in
              let s2 = List.fold_left (fun s t -> s ^ " * " ^ (trans_term t)) "" (List.tl tl) in
              s1 ^ s2
          ) else if op = "and"
          then (
              let tl1 = get_heap_tl tl in
              let tl2 = get_pure_tl tl in
              let tl = tl1@tl2 in
              let s1 = trans_term (List.hd tl) in
              let s2 = List.fold_left (fun s t -> s ^ " & " ^ (trans_term t)) "" (List.tl tl) in
              s1 ^ s2
          ) else if op = "ref"
          then (
              (trans_term (List.hd tl)) ^ " = " ^ (trans_term (List.hd (List.tl tl)))
          ) else if op = "distinct"
          then (
              (trans_term (List.hd tl)) ^ " != " ^ (trans_term (List.hd (List.tl tl)))
          ) else if op = "index"
          then (
              trans_term (List.hd (List.tl tl))
          ) else if (op = "+" || op = "-" || op = "*")
          then (
              (trans_term (List.hd tl)) ^ op ^ (trans_term_list (List.tl tl))
          ) else if not ( op = "tobool" ||
                  op = "tospace" ||
                  op = "sref" ||
                  op = "not" ||
                  op = "loop"
          )
          then (
              (* try *)
              (*   let _ = Hashtbl.find tbl_preddef op in *)
              (trans_term (List.hd tl)) ^ "::" ^ op ^ "<" ^ (trans_term_list (List.tl tl)) ^ ">"
              (* with Not_found -> ( *)
                  (* trans_term_list tl; *)
              (* ) *)
          ) else (
              trans_term_list tl;
          )
    | TermLetTerm _ ->
          "let\n"
    | TermForAllTerm _ ->
          "forall\n"
    | TermExistsTerm (_, (_, vl), t) ->
          let s1 = trans_var_list vl in
          let s2 = trans_term t in
          "(exists " ^ s1 ^  ": " ^ s2 ^ ")"
    | TermExclimationPt _ ->
          "exclimation\n"

and trans_term_list tl =
  if (List.length tl > 0) then (
      let s1 = trans_term (List.hd tl) in
      let s2 = List.fold_left (fun s t ->
          s ^ "," ^ (trans_term t)) "" (List.tl tl) in
      s1 ^ s2
  ) else
    ""

and trans_para p =
   match p with
    | SortedVarSymSort (_,sy,so) ->
          Hashtbl.add tbl_vardef (get_str_symbol sy) (get_str_sort so);
          let s1 = trans_symbol sy in
          let s2 = ":" in
          let s3 = trans_sort so in
          s1 ^ s2 ^ s3

and trans_para_list pl =
  if (List.length pl > 0) then (
      let s1 = trans_para (List.hd pl) in
      let s2 = List.fold_left (fun s p ->
        s ^ "," ^ (trans_para p)) "" (List.tl pl) in
      s1 ^ s2
  ) else
    ""

and trans_var v =
  match v with
    | SortedVarSymSort (_,sy,so) ->
          Hashtbl.add tbl_vardef (get_str_symbol sy) (get_str_sort so);
          trans_symbol sy

and trans_var_list vl =
  if (List.length vl > 0) then (
      let s1 = trans_var (List.hd vl) in
      let s2 = List.fold_left (fun s v ->
        s ^ "," ^ (trans_var v)) "" (List.tl vl) in
      s1 ^ s2
  ) else
    ""

and trans_const const =
  match const with
    | SpecConstsDec(_, str) -> str
    | SpecConstNum(_, str) -> str
    | SpecConstString(_, str) -> str
    | SpecConstsHex(_, str) -> str
    | SpecConstsBinary(_, str) -> str
    | SpecConstDate(_, str) -> str

and trans_symbol sy =
  let str = match sy with
  | Symbol (_ , str) -> str
  | SymbolWithOr (_, str) -> str
  in (
      if String.contains str '?'
      then
        let new_str = String.sub str 1 ((String.length str) - 1) in
        try
          let self = Hashtbl.find tbl_selfdef new_str in
          self
        with Not_found -> new_str
      else if str = "nil"
      then
        "null"
      else
        str
  )

and trans_sort so =
  match so with
    | SortIdentifier (pd, id) ->
          let id = trans_id id in
          if id = "Int"
          then "int"
          else id
    | SortIdSortMulti (pd, id, (_, sol)) ->
          let so = List.hd (List.tl sol) in
          "  " ^ (trans_sort so) ^ " "

and trans_id = function
  | IdSymbol (_ , sy) ->
        trans_symbol sy
  | IdUnderscoreSymNum (_, sy, _) ->
        trans_symbol sy

and trans_commands e =
  match e with
    | Commands(_,(_, cl)) ->
          List.fold_left (fun s c -> s ^ (trans_command c cl)) "" cl

let trans e =
  let s = trans_commands e in
  s ^ "\n\n"
  (* print_string (s ^ "\n") *)
