#include "xdebug.cppo"
open VarGen
open Globals
open Gen
open Cpure

module CP = Cpure

type lp_solver = 
  | Clp
  | LPSolve
  | Glpk

type lp_res = 
  | Sat of (string * int) list
  | Unsat
  | Unknown
  | Aborted

let string_of_lp_res = function
  | Sat m -> "sat" ^ (pr_list (pr_pair idf string_of_int) m)
  | Unsat -> "unsat"
  | Unknown -> "unknown"
  | Aborted -> "aborted"

let rec lp_of_typ solver t =
  match t with
  | Int -> 
    begin match solver with
      | LPSolve -> "int"
      | Clp | Glpk -> "Integer"
    end
  | _ -> "free" 

let lp_of_spec_var sv =
  (CP.name_of_spec_var sv) ^ 
  (if CP.is_primed sv then "_primed" else "")

let lp_of_typed_spec_var solver sv =
  (lp_of_typ solver (CP.type_of_spec_var sv)) ^ " " ^ (lp_of_spec_var sv)

let dummy_var = SpecVar (Int, "dummy", Unprimed)

let rec lp_of_exp a =
  match a with
  | CP.Var (sv, _) -> lp_of_spec_var sv
  | CP.IConst (i, _) ->
    (* Print i with sign *)
    if i >= 0 then "+" ^ (string_of_int i) else string_of_int i
  | CP.FConst (f, _) -> string_of_float f 
  | CP.Add (e1, e2, _) -> (lp_of_exp e1) ^ " " ^ (lp_of_exp e2)
  | CP.Mult (e1, e2, _) -> (lp_of_exp e1) ^ " " ^ (lp_of_exp e2)
  (* UNHANDLED *)
  | _ -> print_endline_quiet (!print_exp a); Error.report_no_pattern ()

let rec lp_of_b_formula b =
  let (pf, _) = b in
  match pf with
  | CP.Lte (e1, e2, _) -> (lp_of_exp e1) ^ " <= " ^ (lp_of_exp e2)
  | CP.Gte (e1, e2, _) -> (lp_of_exp e1) ^ " >= " ^ (lp_of_exp e2)
  | CP.Eq (e1, e2, _) -> (lp_of_exp e1) ^ " = " ^ (lp_of_exp e2)
  (* UNHANDLED *)
  | _ -> print_endline_quiet (!print_b_formula b); Error.report_no_pattern ()

let lp_of_formula f =
  match f with
  | CP.BForm ((b,_) as bf,_) -> lp_of_b_formula bf
  | _ -> print_endline_quiet (!print_formula f); Error.report_no_pattern ()

let rec split_add (e: exp): exp list =
  match e with 
  | Add (e1, e2, _) -> (split_add e1) @ (split_add e2)
  | Subtract (e1, e2, _) -> 
    let pos = pos_of_exp e2 in
    (split_add e1) @ 
    (List.map (fun e -> mkMult (mkIConst (-1) pos) e pos) (split_add e2))
  | _ -> [e]

let rec split_mult (e: exp): exp list =
  match e with
  | Mult (e1, e2, _) -> (split_mult e1) @ (split_mult e2)
  | _ -> [e]

let norm_mult_exp in_lhs e =
  let pos = pos_of_exp e in
  let el = split_mult e in
  let cl, el = List.partition is_int el in
  let c = List.fold_left (fun a c -> a * (to_int_const c Ceil)) 1 cl in
  if el = [] then
    (* Move const to rhs *)
    None, if in_lhs then -c else c
  else
    (* Move var exp to lhs *)
    Some (List.fold_left (fun a e -> mkMult a e pos) 
            (mkIConst (if in_lhs then c else -c) pos) el), 0

let norm_add_exp in_lhs e =
  let pos = pos_of_exp e in
  let el = split_add e in
  let cl, el = List.partition is_int el in
  let c = List.fold_left (fun a c -> a + (to_int_const c Ceil)) 0 cl in
  let vl, cl = List.split (List.map (norm_mult_exp in_lhs) el) in
  let c = List.fold_left (fun a c -> a + c) (if in_lhs then -c else c) cl in
  let vl = List.fold_left (fun a v -> match v with Some e -> a @ [e] | _ -> a) [] vl in
  vl, if c == 0 then None else Some c

(* e1 {<, <=, >, >=, =} e2 --> f(vars) = const *)  
let norm_formula f =
  let rec f_b b =
    let (pf, _) = b in

    let norm_exp e_l e_r pos = 
      let v_l, c_l = norm_add_exp true e_l in
      let v_r, c_r = norm_add_exp false e_r in
      let c = match c_l, c_r with
        | None, None -> 0
        | Some c_l, None -> c_l
        | None, Some c_r -> c_r
        | Some c_l, Some c_r -> c_l + c_r
      in
      let v = match v_l @ v_r with
        | [] -> mkMult (mkIConst 0 pos) (mkVar dummy_var pos) pos 
        | e::es -> List.fold_left (fun a e -> mkAdd a e pos) e es 
      in v, mkIConst c pos
    in
    let rec helper pf = match pf with
      | Lt (e1, e2, p) -> helper (mkLte e1 (mkAdd e2 (mkIConst (-1) p) p) p)
      | Gt (e1, e2, p) -> helper (mkGte (mkAdd e1 (mkIConst (-1) p) p) e2 p)
      | Lte (e1, e2, p) -> let v, c = norm_exp e1 e2 p in mkLte v c p
      | Gte (e1, e2, p) -> let v, c = norm_exp e1 e2 p in mkGte v c p
      | Eq (e1, e2, p) -> let v, c = norm_exp e1 e2 p in mkEq v c p
      | _ -> pf
    in Some (helper pf, None)
  in transform_formula (nonef, nonef, nonef, f_b, nonef) f

let norm_formula f =
  let pr = !print_formula in
  Debug.no_1 "lp_norm_formula" pr pr norm_formula f

let option_of_lp = function
  | Clp -> "-solv -solution stdout"
  | LPSolve -> ""
  | Glpk -> "--write-stdout"

let cmd_of_lp = function
  | Clp -> "clp"
  | LPSolve -> "lp_solve"
  | Glpk -> "glpsol --lp"

let syscall cmd = 
  let in_chn, out_chn = Unix.open_process cmd in
  let buf = Buffer.create 16 in
  (try
     while true do
       Buffer.add_channel buf in_chn 1
     done
   with End_of_file -> ());
  let todo_unk = Unix.close_process (in_chn, out_chn) in
  Buffer.contents buf

let search_backward keyword str pos = 
  Str.search_backward (Str.regexp keyword) str pos

let search_forward keyword str pos = 
  Str.search_backward (Str.regexp keyword) str pos

exception Parse_error

let clp_process_output lp_output =
  let len = String.length lp_output in
  try
    let todo_unk = search_backward "ERROR" lp_output (len - 1) in
    Aborted
  with Not_found ->
    try 
      let todo_unk = search_backward "infeasible" lp_output (len - 1) in
      Unsat
    with Not_found -> 
      try
        let p = search_backward "optimal" lp_output (len - 1) in
        let lp_res = Str.string_after lp_output p in
        (* let lexbuf = Lexing.from_string lp_res in *)
        (* let sol = Lpparser.input Lplexer.tokenizer lexbuf in *)
        (* Sat sol *) 
        let out_ls = Str.split (Str.regexp "[\n]+") lp_res in
        match out_ls with
        | _::_::str_model -> begin
            try
              let model = List.map (fun m -> Str.split (Str.regexp "[ \t]+") m) str_model in
              let model = List.map (fun l -> match l with
                  | _::v::i::_::[] -> (v, int_of_string i) | _ -> raise Parse_error) model in
              Sat model
            with _ -> Unknown end
        | _ -> Unknown

      with Not_found -> Unknown

let glpk_process_output lp_output =
  let len = String.length lp_output in
  try
    let p = search_backward "Optimal" lp_output (len - 1) in
    let lp_res = Str.string_after lp_output p in
    let out_ls = Str.split (Str.regexp "[\n]+") lp_res in
    match out_ls with
    | _::str_model -> begin
        try
          let model = List.map (fun m -> Str.split (Str.regexp "[ \t]+") m) str_model in
          let model = List.map (fun l -> match l with
              | v::i::[] -> (v, int_of_string i) | _ -> raise Parse_error) model in
          Sat model
        with _ -> Unknown end
    | _ -> Unknown
  with Not_found -> Unknown

let lpsolve_process_output lp_output =
  let out_ls = Str.split (Str.regexp "[\n]+") lp_output in
  match out_ls with
  | _::_::str_model -> begin
      try
        let model = List.map (fun m -> Str.split (Str.regexp "[ \t]+") m) str_model in
        let model = List.map (fun l -> match l with
            | v::i::[] -> (v, int_of_string i) | _ -> raise Parse_error) model in
        Sat model
      with _ -> Unknown end
  | _ -> Unknown

let process_output solver lp_output = 
  match solver with
  | Clp -> clp_process_output lp_output
  | LPSolve -> lpsolve_process_output lp_output
  | Glpk -> glpk_process_output lp_output

let run solver input =
  let lp_input = "logs/allinput.lp" in 
  let out_chn = open_out lp_input in
  Printf.fprintf out_chn "%s" input;
  flush out_chn;
  close_out out_chn;

  let lp_output = syscall (String.concat " " 
                             [cmd_of_lp solver; lp_input; option_of_lp solver]) in
  lp_output

let gen_clp_input obj_vars assertions =
  let obj_stmt = match obj_vars with
    | [] -> ""
    | _ -> "Minimize\n" ^ (String.concat " + " (List.map lp_of_spec_var obj_vars))
  in
  let model_stmt = match assertions with
    | [] -> ""
    | _ -> "Subject To\n" ^ (String.concat "\n" 
                               (List.map (fun f -> lp_of_formula (norm_formula f)) assertions))
  in
  let var_decls = String.concat "\n" (List.map (fun v ->
      (lp_of_typed_spec_var Clp v)) obj_vars)
  in
  let clp_inp = obj_stmt ^ "\n" ^ model_stmt ^ "\n" ^ var_decls ^ "\nEnd\n" in
  clp_inp

let gen_lpsolve_input obj_vars assertions =
  let obj_stmt = match obj_vars with
    | [] -> ""
    | _ -> "min: " ^ (String.concat " + " (List.map lp_of_spec_var obj_vars)) ^ ";"
  in
  let model_stmt = String.concat "\n" (List.map (fun f ->
      (lp_of_formula (norm_formula f)) ^ ";") assertions)
  in
  let var_decls = String.concat "\n" (List.map (fun v ->
      (lp_of_typed_spec_var LPSolve v) ^ ";") obj_vars)
  in
  let lp_inp = obj_stmt ^ "\n\n" ^ model_stmt ^ "\n\n" ^ var_decls ^ "\n" in
  lp_inp

let gen_lp_input solver obj_vars assertions =
  match solver with
  | Clp 
  | Glpk -> gen_clp_input obj_vars assertions
  | LPSolve -> gen_lpsolve_input obj_vars assertions

let get_model solver obj_vars assertions =
  let lp_inp = gen_lp_input solver obj_vars assertions in
  let lp_out = run solver lp_inp in

  let () = 
    x_tinfo_pp ">>>>>>> get_model_lp <<<<<<<" no_pos;
    x_tinfo_hp (add_str "lp input:\n " idf) lp_inp no_pos;
    x_tinfo_hp (add_str "lp output: " idf) lp_out no_pos 
  in

  process_output solver lp_out

let get_model solver obj_vars assertions =
  let pr1 = pr_list !print_formula in 
  let pr2 = string_of_lp_res in
  Debug.no_1 "lp_get_model" pr1 pr2
    (fun _ -> get_model solver obj_vars assertions) assertions


