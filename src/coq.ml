#include "xdebug.cppo"
(*
  Create the input file for Coq
*)

open Globals
open Gen.Basic
open VarGen
open GlobProver
module CP = Cpure
module Err = Error

let set_prover_type () = Others.last_tp_used # set Others.Coq

let coq_file_number = ref 0
let result_file_name = "res"
let log_all_flag = ref false
let log_file = open_log_out "allinput.v"
let max_flag = ref false
let choice = ref 1
let bag_flag = ref false
let coq_running = ref false
let coq_timeout = ref 5.0
let coq_channels = ref (stdin, stdout)

let print_p_f_f = ref (fun (c:CP.formula)-> " formula printing not initialized")  

let rec coq_of_typ = function
  | Bool          -> "int"
  | Float         -> "float"	(* all types will be ints. *)
  | Int | INFInt  -> "int"
  | AnnT          -> "int"
  | Void          -> "unit" 	(* all types will be ints. *)
  | BagT t		   -> "("^(coq_of_typ t) ^") set"
  | List _		  -> "list"
  | Pointer _
  | Tree_sh 	  -> "int"
  | Tup2 _ -> illegal_format ("coq_of_typ: Tup2 type not supported for Coq")
  | FORM -> illegal_format ("coq_of_typ: FORMULA type not supported for Coq")
  | Bptyp -> failwith ("coq_of_typ: Bptyp type not supported for Coq")
  | UNK | NUM | TVar _ | Named _ | Array _ | RelT _ | FuncT _ | UtT _ | HpT (* | SLTyp *) ->
    Error.report_error {Err.error_loc = no_pos; 
                        Err.error_text = "type var, array and named type not supported for Coq"}
;;

(* pretty printing for spec_vars *)
let coq_of_spec_var (sv : CP.spec_var) = match sv with
  | CP.SpecVar (_, v, p) -> v ^ (if CP.is_primed sv then Oclexer.primed_str else "")

let coq_type_of_spec_var (sv : CP.spec_var) = match sv with
  | CP.SpecVar (t, _, _) -> begin match t with
      | List _ -> "list Z"
      | _ -> "Z"
    end

(*----------------------------------*)
(* checking if exp contains bags *)
let rec is_bag_exp e0 = match e0 with
  | CP.Var (CP.SpecVar(t, _, _), _) ->
    if (CP.is_int_type t) then true
    else false
  | CP.Bag (_, _)
  | CP.BagUnion (_, _)
  | CP.BagIntersect (_, _)
  | CP.BagDiff (_, _, _) -> true
  | _ -> false


(* checking if b formula contains bags *)
and is_bag_b_formula b = match b with
  | CP.Eq (a1, a2, _)
  | CP.Neq (a1, a2, _) -> ((is_bag_exp a1) || (is_bag_exp a2))
  | CP.BagIn (_, _, _)
  | CP.BagNotIn (_, _, _)
  | CP.BagSub (_, _, _)
  | CP.BagMin (_, _, _)
  | CP.BagMax (_, _, _) -> true
  | _ -> false

(*----------------------------------*)

(* pretty printing for expressions *)
and coq_of_exp e0 =
  match e0 with
  | CP.Null _ -> "0"
  | CP.Var (sv, _) -> coq_of_spec_var sv
  | CP.IConst (i, _) -> string_of_int i
  | CP.Tsconst _ -> failwith ("tsconst not supported in coq, should have already been handled")
  | CP.Bptriple _ | CP.Tup2 _ ->  illegal_format "coq_of_exp : bptriple/Tup2 cannot be handled"
  | CP.AConst (i, _) -> string_of_heap_ann i
  | CP.FConst (f, _) -> illegal_format "coq_of_exp : float cannot be handled"
  | CP.Add (a1, a2, _) ->  " ( " ^ (coq_of_exp a1) ^ " + " ^ (coq_of_exp a2) ^ ")"
  | CP.Subtract (a1, a2, _) ->  " ( " ^ (coq_of_exp a1) ^ " - " ^ (coq_of_exp a2) ^ ")"
  | CP.Mult (a1, a2, _) -> "(" ^ (coq_of_exp a1) ^ " * " ^ (coq_of_exp a2) ^ ")"
  | CP.Div (a1, a2, _) -> "(" ^ (coq_of_exp a1) ^ " / " ^ (coq_of_exp a2) ^ ")"
  | CP.Max _
  | CP.Min _ -> illegal_format "coq_of_exp : min/max cannot be handled"
  | CP.TypeCast _ -> illegal_format "coq_of_exp : TypeCast cannot be handled"
  (* lists *)
  | CP.List (alist, pos) -> 
    begin match alist with
      | [] -> "(@nil Z)"
      | a::t -> "(" ^ (coq_of_exp a) ^ " :: " ^ (coq_of_exp (CP.List (t, pos))) ^ ")"
    end
  | CP.ListAppend (alist, pos) ->
    begin match alist with
      | [] -> "(@nil Z)"
      | a::[] -> coq_of_exp a
      | a::t -> "(" ^ (coq_of_exp a) ^ " ++ " ^ (coq_of_exp (CP.ListAppend (t, pos))) ^ ")"
    end
  | CP.ListCons (a1, a2, _) -> " ( " ^ (coq_of_exp a1) ^ " :: " ^ (coq_of_exp a2) ^ ")"
  | CP.ListHead (a, _) -> " ( hd 0 " ^ (coq_of_exp a) ^ ")"
  | CP.ListLength (a, _) -> " ( Z_of_nat ( length " ^ (coq_of_exp a) ^ "))"
  | CP.ListTail (a, _) -> " ( tail " ^ (coq_of_exp a) ^ ")"
  | CP.ListReverse (a, _) -> " ( rev " ^ (coq_of_exp a) ^ ")"
  (* bags *)
  | CP.Bag (alist, pos) -> 
    begin match alist with
      | [] -> "ZSets.empty"
      | a::t -> "( ZSets.add " ^ (coq_of_exp a) ^ " " ^ (coq_of_exp (CP.Bag (t, pos))) ^ ")"
    end
  | CP.BagUnion (alist, pos) ->
    begin match alist with
      | [] -> "ZSets.empty"
      | a::[] -> coq_of_exp a
      | a::t -> "( ZSets.union " ^ (coq_of_exp a) ^ " " ^ (coq_of_exp (CP.BagUnion (t, pos))) ^ ")"
    end
  | CP.BagIntersect (alist, pos) ->
    begin match alist with
      | [] -> "ZSets.empty"
      | a::[] -> coq_of_exp a
      | a::t -> "( ZSets.inter " ^ (coq_of_exp a) ^ " " ^ (coq_of_exp (CP.BagIntersect (t, pos))) ^ ")"
    end
  | CP.BagDiff (a1, a2, _) -> " ( ZSets.diff " ^ (coq_of_exp a1) ^ " " ^ (coq_of_exp a2) ^ ")"
  | CP.Func _ -> 
    illegal_format "coq_of_exp : function cannot be handled"
  | CP.Level _ -> 
    illegal_format "coq_of_exp : level should not be here"
  | CP.ArrayAt _ -> 
    illegal_format "coq_of_exp : array cannot be handled"
  (* failwith ("Arrays are not supported in Coq") (\* An Hoa *\) *)
  | CP.NegInfConst _
  | CP.InfConst _ -> illegal_format "coq_of_exp : \inf cannot be handled"
  | CP.Template t -> coq_of_exp (CP.exp_of_template t)

(* pretty printing for a list of expressions *)
and coq_of_formula_exp_list l = match l with
  | []         -> ""
  | h::[]      -> coq_of_exp h
  | h::t       -> (coq_of_exp h) ^ ", " ^ (coq_of_formula_exp_list t)

(* pretty printing for boolean vars *)
and coq_of_b_formula b =
  let (pf,_) = b in
  match pf with
  | CP.Frm (fv, _) -> " (" ^ (coq_of_spec_var fv) ^ " = 1)"
  | CP.BConst (c, _) -> if c then "True" else "False"
  | CP.XPure _ -> "True" (* WN : weakening - need to translate> *)
  | CP.BVar (bv, _) -> " (" ^ (coq_of_spec_var bv) ^ " = 1)"
  | CP.Lt (a1, a2, _) -> " ( " ^ (coq_of_exp a1) ^ " < " ^ (coq_of_exp a2) ^ ")"
  | CP.SubAnn (a1, a2, _) -> " ( " ^ (coq_of_exp a1) ^ " <= " ^ (coq_of_exp a2) ^ ")"
  | CP.Lte (a1, a2, _) -> " ( " ^ (coq_of_exp a1) ^ " <= " ^ (coq_of_exp a2) ^ ")"
  | CP.Gt (a1, a2, _) -> " ( " ^ (coq_of_exp a1) ^ " > " ^ (coq_of_exp a2) ^ ")"
  | CP.Gte (a1, a2, _) -> "(" ^ (coq_of_exp a1) ^ " >= " ^ (coq_of_exp a2) ^ ")"
  | CP.Eq (a1, a2, _) -> " ( " ^ (coq_of_exp a1) ^ " = " ^ (coq_of_exp a2) ^ ")"
  | CP.Neq (a1, a2, _) -> "( " ^ (coq_of_exp a1) ^ " <> " ^ (coq_of_exp a2) ^ ")"
  | CP.EqMax (a1, a2, a3, _) ->
    let a1str = coq_of_exp a1 in
    let a2str = coq_of_exp a2 in
    let a3str = coq_of_exp a3 in
    "((" ^ a1str ^ " = " ^ a3str ^ " /\\ " ^ a3str ^ " > " ^ a2str ^ ") \\/ ("
    ^ a2str ^ " >= " ^ a3str ^ " /\\ " ^ a1str ^ " = " ^ a2str ^ "))"
  | CP.EqMin (a1, a2, a3, _) ->
    let a1str = coq_of_exp a1 in
    let a2str = coq_of_exp a2 in
    let a3str = coq_of_exp a3 in
    "((" ^ a1str ^ " = " ^ a3str ^ " /\\ " ^ a2str ^ " >= " ^ a3str ^ ") \\/ ("
    ^ a2str ^ " <= " ^ a3str ^ " /\\ " ^ a1str ^ " = " ^ a2str ^ "))"
  (* lists *)
  | CP.ListIn (a1, a2, _) -> " ( In " ^ (coq_of_exp a1) ^ " " ^ (coq_of_exp a2) ^ ")"
  | CP.ListNotIn (a1, a2, _) ->  " ( not ( In " ^ (coq_of_exp a1) ^ " " ^ (coq_of_exp a2) ^ "))"
  | CP.ListAllN (a1, a2, _) -> " ( alln " ^ (coq_of_exp a2) ^ " " ^ (coq_of_exp a1) ^ ")"
  | CP.ListPerm (a1, a2, _) -> " ( Permutation " ^ (coq_of_exp a1) ^ " " ^ (coq_of_exp a2) ^ ")"
  (* bags *)
  | CP.BagIn (sv, a, _) -> " ( ZSets.mem " ^ (coq_of_spec_var sv) ^ " " ^ (coq_of_exp a) ^ " = true)"
  | CP.BagNotIn (sv, a, _) -> " ( ZSets.mem " ^ (coq_of_spec_var sv) ^ " " ^ (coq_of_exp a) ^ " = false)"
  | CP.BagSub (a1, a2, _) -> " ( ZSets.subset " ^ (coq_of_exp a1) ^ " " ^ (coq_of_exp a2) ^ " = true)"
  | CP.BagMin _
  | CP.BagMax _ -> 
    illegal_format "coq_of_exp : bags cannot be handled"
  (* failwith ("No bags in Coq yet") *)
  | CP.RelForm _ -> 
    (* failwith ("No relations in Coq yet") (\* An Hoa *\) *)
    illegal_format "coq_of_exp : relation cannot be handled"
  | CP.ImmRel _ -> illegal_format "coq_of_exp : ImmRel cannot be handled"
  | CP.LexVar _ -> illegal_format "coq_of_exp : lexvar cannot be handled"
                     (* | CP.VarPerm _ -> *)
                     illegal_format "coq_of_exp : VarPerm cannot be handled"

(* pretty printing for formulas *)
and coq_of_formula pr_w pr_s f =
  let rec helper f = 
    match f with
    | CP.BForm ((b,_) as bf,_) -> 		
      begin
        match (pr_w b) with
        | None -> "(" ^ (coq_of_b_formula bf) ^ ")"
        | Some f -> helper f
      end
    (* | CP.BForm (b,_) ->  *)
    (*       "(" ^ (coq_of_b_formula b) ^ ")" *)
    | CP.Not (p, _,_) ->
      begin match p with
        | CP.BForm ((CP.BVar (bv, _),_),_) -> (coq_of_spec_var bv) ^ " = 0"
        | _ -> " (~ (" ^ (coq_of_formula pr_s pr_w p) ^ ")) "
      end
    | CP.Forall (sv, p, _, _) ->
      " (forall " ^ (coq_of_spec_var sv) ^ "," ^ (helper p) ^ ") "
    | CP.Exists (sv, p,  _,_) ->
      " (exists " ^ (coq_of_spec_var sv) ^ ":"^(coq_type_of_spec_var sv) ^"," ^ (helper p) ^ ") "
    | CP.And (p1, p2, _) ->
      "(" ^ (helper p1) ^ " /\\ " ^ (helper p2) ^ ")"
    | CP.AndList _ -> Gen.report_error no_pos "coq.ml: encountered AndList, should have been already handled"
    | CP.Or (p1, p2, _, _) ->
      "(" ^ (helper p1) ^ " \\/ " ^ (helper p2) ^ ")"
  in helper f

let coq_of_formula pr_w pr_s f =
  let () = set_prover_type () in
  coq_of_formula pr_w pr_s f

let coq_of_formula pr_w pr_s f = 
  Debug.no_1 "coq_of_formula" (fun _ -> "Input") (fun c -> c)
    (fun _ -> coq_of_formula pr_w pr_s f) pr_w

(* checking the result given by Coq *)
let rec check fd coq_file_name : bool=
  try while true do
      let line = input_line fd in
      if line = "No subgoals!" then raise Exit else ()
    done; false
  with Exit -> 
    if !log_all_flag==true then
      output_string log_file ("[coq.ml]: --> SUCCESS\n");
    (*ignore (Sys.remove coq_file_name);*)
    true
     | _ ->
       if !log_all_flag==true then
         output_string log_file ("[coq.ml]: --> Error in file " ^ coq_file_name ^ "\n");
       (*ignore (Sys.remove coq_file_name);	*)
       false
;;

let coq_of_var_list l = String.concat "" (List.map (fun sv -> "forall " ^ (coq_of_spec_var sv) ^ ":" ^ (coq_type_of_spec_var sv) ^ ", ") l)

let decidez_vo_dir = Gen.get_path Sys.executable_name

(* starting Coq in interactive mode *)
let start () =
  coq_channels := Unix.open_process ("coqtop -require " ^ decidez_vo_dir ^ "decidez 2> /dev/null");
  coq_running := true;
  print_string "Coq started\n"; flush stdout

let start_prover_debug () =
  Debug.no_1 "stack coq prover" (fun () -> "") (fun () -> "") start ()

(* stopping Coq *)
let stop () =
  if !coq_running then begin
    (* print_string "stopping \n";  *) (* without this prover stops early*)
    output_string (snd !coq_channels) ("Quit.\n"); flush (snd !coq_channels);
    ignore (Unix.close_process !coq_channels);
    coq_running := false;
    print_string "Coq stopped\n"; flush stdout
  end

let stop_prover_debug () =
  print_string "stop coq prover"; 
  Debug.no_1 "stop coq prover" (fun () -> "") (fun () -> "") stop ()

(* sending Coq a formula; nr = nr. of retries *)
let rec send_formula (f : string) (nr : int) : bool =
  try
    let fnc () = 
      output_string (snd !coq_channels) f;
      output_string (snd !coq_channels) ("decidez.\nQed.\n");
      flush (snd !coq_channels);
      let result = ref false in
      let finished = ref false in  
      while not !finished do 
        let line = input_line (fst !coq_channels) in
        if !log_all_flag==true then output_string log_file ("[coq.ml]: >>"^line^"\n");
        if line = "test" ^ string_of_int !coq_file_number ^ " is defined" then begin
          result := true;
          finished := true;
          if !log_all_flag==true then output_string log_file ("[coq.ml]: --> SUCCESS\n");
        end else if String.length line > 5 && String.sub line 0 5 = "Error" then begin
          result := false;
          finished := true;
          output_string (snd !coq_channels) ("Abort.\n");
          flush (snd !coq_channels);
          if !log_all_flag==true then output_string log_file ("[coq.ml]: --> FAIL\n");
        end;
      done;
      !result
    in
    try  
      let answ = Procutils.PrvComms.maybe_raise_timeout_num 11 fnc () !coq_timeout in
      answ
    with 
    | Procutils.PrvComms.Timeout -> 
      begin
        print_string("\n[coq.ml]:Timeout exception\n");flush stdout;
        false;
      end
    with
      _ -> ignore (Unix.close_process !coq_channels);
      coq_running := false;
      print_string "\nCoq crashed\n"; flush stdout;
      start ();
      if nr > 1 then send_formula f (nr - 1) else false


(* writing the Coq file *)
let write pr_w pr_s (ante : CP.formula) (conseq : CP.formula) : bool =
  (*  print_string "*"; flush stdout; *)
  (*  print_endline ("formula " ^ string_of_int !coq_file_number ^ ": " ^ (Cprinter.string_of_pure_formula ante) ^ " -> " ^ (Cprinter.string_of_pure_formula conseq)); *)
  let vstr = coq_of_var_list (Gen.BList.remove_dups_eq (=) ((CP.fv ante) @ (CP.fv conseq))) in
  let astr = coq_of_formula pr_w pr_s ante in
  let cstr = coq_of_formula pr_s pr_w conseq in

  coq_file_number.contents <- !coq_file_number + 1;
  if !coq_running == false then start ();

  (* if log_all_flag is on -> writing the formula in the coq log file  *)
  if !log_all_flag == true then	begin
    output_string log_file ("  Lemma test" ^ string_of_int !coq_file_number ^ " : (" ^ vstr ^ astr ^ " -> " ^ cstr ^ ")%Z.\n");
    flush log_file;
  end;

  (*let () = print_string ("[coq.ml] write " ^ ("Lemma test" ^ string_of_int !coq_file_number ^ " : (" ^ vstr ^ astr ^ " -> " ^ cstr ^ ")%Z.\n")) in*)
  send_formula ("Lemma test" ^ string_of_int !coq_file_number ^ " : (" ^ vstr ^ astr ^ " -> " ^ cstr ^ ")%Z.\n") 2


let write  pr_w pr_s (ante : CP.formula) (conseq : CP.formula) : bool =
  Debug.no_2 "coqwrite" !print_p_f_f !print_p_f_f
    string_of_bool (write pr_w pr_s) ante conseq

let imply_ops pr_w pr_s (ante : CP.formula) (conseq : CP.formula) : bool =
  if !log_all_flag == true then
    output_string log_file "\n[coq.ml]: #imply\n";
  max_flag := false;
  choice := 1;
  try 
    write pr_w pr_s ante conseq;
  with Illegal_Prover_Format s -> 
    begin
      print_endline_quiet ("\nWARNING coq.imply : Illegal_Prover_Format for :"^s);
      print_endline_quiet ("ante:"^(!print_p_f_f ante));
      print_endline_quiet ("conseq:"^(!print_p_f_f conseq));
      flush stdout;
      failwith s
    end
(*write (CP.mkOr (CP.mkNot ante None no_pos) conseq None no_pos)*)

let imply_ops pr_w pr_s (ante : CP.formula) (conseq : CP.formula) : bool =
  Debug.no_2 "coqimplyops" !print_p_f_f !print_p_f_f
    string_of_bool (imply_ops pr_w pr_s) ante conseq

let imply (ante : CP.formula) (conseq : CP.formula) : bool =
  let pr x = None in
  imply_ops pr pr ante conseq


let is_sat_ops pr_w pr_s (f : CP.formula) (sat_no : string) : bool =
  if !log_all_flag == true then
    output_string log_file ("\n[coq.ml]: #is_sat " ^ sat_no ^ "\n");
  let tmp_form = (imply_ops pr_w pr_s f (CP.BForm((CP.BConst(false, no_pos), None), None))) in
  match tmp_form with
  | true ->
    if !log_all_flag == true then output_string log_file "[coq.ml]: is_sat --> false\n";
    false
  | false ->
    if !log_all_flag == true then output_string log_file "[coq.ml]: is_sat --> true\n";
    true

let is_sat_ops pr_w pr_s (f:CP.formula) (sat_no :string) : bool = 
  Debug.no_2 "coqsimplops" !print_p_f_f (fun x -> x) 
    string_of_bool (is_sat_ops pr_w pr_s) f sat_no

let is_sat (f : CP.formula) (sat_no : string) : bool =
  let pr x = None in
  is_sat_ops pr pr f sat_no

let building_image _ = ()

(* TODO: implement the following procedures; now they are only dummies *)
let hull (pe : CP.formula) : CP.formula = begin
  if !log_all_flag == true then
    output_string log_file "\n[coq.ml]: #hull\n";
  pe
end
let pairwisecheck (pe : CP.formula) : CP.formula = begin
  if !log_all_flag == true then
    output_string log_file "\n[coq.ml]: #pairwisecheck\n";
  pe
end
let simplify (pe : CP.formula) : CP.formula = begin
  if !log_all_flag == true then
    output_string log_file "\n[coq.ml]: #simplify\n";
  pe
end
