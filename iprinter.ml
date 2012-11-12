(* pretty printing for iast *)

(* open the needed modules *)
open Iast
open Globals
open Lexing
open Gen.Basic
open Label_only

module F = Iformula
module P = Ipure

(* function to enclose a string s into parenthesis *)
let parenthesis s = "(" ^ s ^ ")"
;;

(* function to concatenate the elements of a list of strings and puts c betwwen then (for field access)*)
let rec concatenate_string_list l c = match l with 
 | [] -> ""
 | h::[] -> h 
 | h::t -> h ^ c ^ (concatenate_string_list t c)
;;

(* pretty printing for unary operators *)
let string_of_unary_op = function 
  | OpUMinus       -> "-"
  | OpPreInc       -> "++"
  | OpPreDec       -> "--"
  | OpPostInc      -> "++"
  | OpPostDec      -> "--"
  | OpNot          -> "!"                                   
;;    

(* pretty priting for binary operators *)
let string_of_binary_op = function 
  | OpPlus         -> " + "
  | OpMinus        -> " - "
  | OpMult         -> " * "
  | OpDiv          -> " / "
  | OpMod          -> " % "
  | OpEq           -> " == "
  | OpNeq          -> " != "                                 
  | OpLt           -> " < "
  | OpLte          -> " <= "
  | OpGt           -> " > "
  | OpGte          -> " >= "
  | OpLogicalAnd   -> " && "                                 
  | OpLogicalOr    -> " || "
  | OpIsNull       -> " == "
  | OpIsNotNull    -> " != "
;;

(* pretty printing for assign operators *)
let string_of_assign_op = function 
  | OpAssign      -> " = "
  | OpPlusAssign  -> " += "
  | OpMinusAssign -> " -= "
  | OpMultAssign  -> " *= "
  | OpDivAssign   -> " /= "
  | OpModAssign   -> " %= "
;;

let string_of_primed = function 
	| Unprimed -> ""
	| Primed -> "'";;

(* function used to decide if parentrhesis are needed or not *)
let need_parenthesis = function 
    | P.Null _ | P.Var _ | P.IConst _ | P.Max _ | P.Min _  -> false
    | _                                                    -> true
;; 

let string_of_label = function 
  | NoJumpLabel      -> ""
  | JumpLabel l  -> l^" : "
;;

let string_of_formula_label (i,s) s2:string = ("("^(string_of_int i)^", "^s^"):"^s2)
let string_of_spec_label = Lab_List.string_of
let string_of_spec_label_def = Lab2_List.string_of

let string_of_formula_label_opt h s2:string = match h with | None-> s2 | Some s -> string_of_formula_label s s2
let string_of_control_path_id (i,s) s2:string = string_of_formula_label (i,s) s2
let string_of_control_path_id_opt h s2:string = string_of_formula_label_opt h s2

let string_of_var (c1,c2) = c1^(string_of_primed c2);;

let string_of_var_list vl = String.concat " " (List.map string_of_var vl);;


let string_of_typed_var (t,id) = "(" ^ (string_of_typ t) ^ "," ^  id  ^ ")";;

let rec string_of_typed_var_list l = match l with 
  | [] -> ""
  | h::[] -> (string_of_typed_var h) 
  | h::t -> (string_of_typed_var h) ^ ";" ^ (string_of_typed_var_list t)

let string_of_id (id,p) = id ^ (string_of_primed p)
;;

(* pretty printing for an expression for a formula *)
let rec string_of_formula_exp = function 
  | P.Null l                  -> "null"
  | P.Ann_Exp (e,t) -> (string_of_formula_exp e)^":"^(string_of_typ t)
  | P.Var (x, l)        -> string_of_id x
  | P.IConst (i, l)           -> string_of_int i
  | P.AConst (i, l)           -> string_of_heap_ann i
  | P.Tsconst (i,l)			  -> Tree_shares.Ts.string_of i
  | P.FConst (f, _) -> string_of_float f
  | P.Add (e1, e2, l)	      -> (match e1 with 
	  | P.Null _ 
	  | P.Var _ 
	  | P.IConst _ 
	  | P.Max _ 
	  | P.Min _   -> (string_of_formula_exp e1) ^ "+"   			      
	  | _  -> "(" ^ (string_of_formula_exp e1) ^ ")+") 
		^ (match e2 with 
		  | P.Null _ | P.Var _ | P.IConst _ | P.Max _ | P.Min _ -> string_of_formula_exp e2
		  | _                                                   -> "(" ^ (string_of_formula_exp e2) ^ ")")
  | P.Subtract (e1, e2, l)    -> if need_parenthesis e1
    then 
      if need_parenthesis e2
      then  "(" ^ (string_of_formula_exp e1) ^ ")-(" ^ (string_of_formula_exp e2) ^ ")"  			      
	  else "(" ^ (string_of_formula_exp e1) ^ ")-" ^ (string_of_formula_exp e2)
    else 
	  (string_of_formula_exp e1) 
	  ^ "-" ^ (string_of_formula_exp e2)										    
  | P.Mult (e1, e2, _) ->
        "(" ^ (string_of_formula_exp e1) ^ ") * (" ^ (string_of_formula_exp e2) ^ ")"
  | P.Div (e1, e2, _) ->
        "(" ^ (string_of_formula_exp e1) ^ ") / (" ^ (string_of_formula_exp e2) ^ ")"
  | P.Max (e1, e2, l)         -> "max(" ^ (string_of_formula_exp e1) ^ "," ^ (string_of_formula_exp e2) ^ ")"
  | P.Min (e1, e2, l)         -> "min(" ^ (string_of_formula_exp e1) ^ "," ^ (string_of_formula_exp e2) ^ ")" 
  | P.List (elist, l)		-> "[|" ^ (string_of_formula_exp_list elist) ^ "|]"
  | P.ListAppend (elist, l) -> "app(" ^ (string_of_formula_exp_list elist) ^ ")"
  | P.ListCons (e1, e2, l)	-> (string_of_formula_exp e1) ^ ":::" ^ (string_of_formula_exp e2)
  | P.ListHead (e, l)		-> "head(" ^ (string_of_formula_exp e) ^ ")"
  | P.ListTail (e, l)		-> "tail(" ^ (string_of_formula_exp e) ^ ")"
  | P.ListLength (e, l)		-> "len(" ^ (string_of_formula_exp e) ^ ")"
  | P.ListReverse (e, l)	-> "rev(" ^ (string_of_formula_exp e) ^ ")"
  | P.Func (a, i, _)     ->  
        a ^ "(" ^ (string_of_formula_exp_list i) ^ ")"
  | P.ArrayAt ((a, p), i, _)     ->  
        (* An Hoa : print the array access *)
        a ^ (match p with 
          | Primed -> "'["
          | Unprimed -> "[") 
        ^ (string_of_formula_exp_list i) ^ "]"
  | P.Bag (el, l)		-> "Bag("^(string_of_formula_exp_list el) ^ ")"
  | P.BagUnion (el, l)		-> "BagUnion("^(string_of_formula_exp_list el) ^ ")"
  | P.BagIntersect (el, l)		-> "BagIntersect("^(string_of_formula_exp_list el) ^ ")"
  | P.BagDiff (e1, e2, l)         -> "BagDiff(" ^ (string_of_formula_exp e1) ^ "," ^ (string_of_formula_exp e2) ^ ")"
        (* | _ -> "bag constraint"   *)

(* | Bag of (exp list * loc) *)
(* | BagUnion of (exp list * loc) *)
(* | BagIntersect of (exp list * loc) *)
(* | BagDiff of (exp * exp * loc) *)

(* pretty printing for a list of pure formulae *)
and string_of_formula_exp_list l = match l with 
  | []                         -> ""
  | h::[]                      -> string_of_formula_exp h
  | h::t                       -> (string_of_formula_exp h) ^ ", " ^ (string_of_formula_exp_list t)
;;

   
(* pretty printing for boolean constraints *)
let string_of_slicing_label sl =
  match sl with
	| None -> ""
	| Some (il, lbl, el) -> "<" ^ (if il then "IL, " else ", ")
	  ^ (string_of_int lbl) ^ ", " ^ (string_of_formula_exp_list el) ^ ">"

let string_of_b_formula (pf,il) =
  (string_of_slicing_label il) ^ match pf with 
  | P.BConst (b,l)              -> string_of_bool b 
  | P.BVar (x, l)               -> string_of_id x
  | P.SubAnn (e1,e2, l)        -> 
        (string_of_formula_exp e1)^"<:"^(string_of_formula_exp e2)
  | P.LexVar (t_ann, ls1, ls2, l) ->
      let ann = string_of_term_ann t_ann in
      (match t_ann with
      | Term -> 
          let opt = if ls2==[] then "" else
            "{"^(pr_list string_of_formula_exp ls2)^"}"
          in ann ^ " LexVar["^(pr_list string_of_formula_exp ls1)^"]"^opt
      | _ -> ann)
  | P.Lt (e1, e2, l)            -> if need_parenthesis e1 
                                   then if need_parenthesis e2 then "(" ^ (string_of_formula_exp e1) ^ ") < (" ^ (string_of_formula_exp e2) ^ ")"
                                                               else "(" ^ (string_of_formula_exp e1) ^ ") < " ^ (string_of_formula_exp e2)
                                   else (string_of_formula_exp e1) ^ " < " ^ (string_of_formula_exp e2)
  | P.Lte (e1, e2, l)           -> if need_parenthesis e1 
                                   then if need_parenthesis e2 then "(" ^ (string_of_formula_exp e1) ^ ") <= (" ^ (string_of_formula_exp e2) ^ ")"
                                                               else "(" ^ (string_of_formula_exp e1) ^ ") <= " ^ (string_of_formula_exp e2)
                                   else (string_of_formula_exp e1) ^ " <= " ^ (string_of_formula_exp e2)
  | P.Gt (e1, e2, l)            -> if need_parenthesis e1 
                                   then if need_parenthesis e2 then "(" ^ (string_of_formula_exp e1) ^ ") > (" ^ (string_of_formula_exp e2) ^ ")"
                                                               else "(" ^ (string_of_formula_exp e1) ^ ") > " ^ (string_of_formula_exp e2)
                                   else (string_of_formula_exp e1) ^ " > " ^ (string_of_formula_exp e2)
  | P.Gte (e1, e2, l)           -> if need_parenthesis e1 
                                   then if need_parenthesis e2 then "(" ^ (string_of_formula_exp e1) ^ ") >= (" ^ (string_of_formula_exp e2) ^ ")"
                                                               else "(" ^ (string_of_formula_exp e1) ^ ") >= " ^ (string_of_formula_exp e2)
                                   else (string_of_formula_exp e1) ^ " >= " ^ (string_of_formula_exp e2)
  | P.Eq (e1, e2, l)            -> if need_parenthesis e1 
                                   then if need_parenthesis e2 then "(" ^ (string_of_formula_exp e1) ^ ") = (" ^ (string_of_formula_exp e2) ^ ")"
                                                               else "(" ^ (string_of_formula_exp e1) ^ ") = " ^ (string_of_formula_exp e2)
                                   else (string_of_formula_exp e1) ^ " = " ^ (string_of_formula_exp e2)	
  | P.Neq (e1, e2, l)           -> if need_parenthesis e1 
                                   then if need_parenthesis e2 then "(" ^ (string_of_formula_exp e1) ^ ") != (" ^ (string_of_formula_exp e2) ^ ")"
                                                               else "(" ^ (string_of_formula_exp e1) ^ ") != " ^ (string_of_formula_exp e2)
                                   else (string_of_formula_exp e1) ^ " != " ^ (string_of_formula_exp e2)
  | P.EqMax (e1, e2, e3, l)     -> (string_of_formula_exp e1) ^" = max(" ^ (string_of_formula_exp e2) ^ "," ^ (string_of_formula_exp e3) ^ ")"
  | P.EqMin (e1, e2, e3, l)     -> (string_of_formula_exp e1) ^" = min(" ^ (string_of_formula_exp e2) ^ "," ^ (string_of_formula_exp e3) ^ ")"
  | P.ListIn (e1, e2, l)		-> (string_of_formula_exp e1) ^ " inlist " ^ (string_of_formula_exp e2)
  | P.ListNotIn (e1, e2, l)		-> (string_of_formula_exp e1) ^ " notinlist " ^ (string_of_formula_exp e2)
  | P.ListAllN (e1, e2, l)		-> "alln(" ^ (string_of_formula_exp e1) ^ ", " ^ (string_of_formula_exp e2) ^ ")"
  | P.ListPerm (e1, e2, l)		-> "perm(" ^ (string_of_formula_exp e1) ^ ", " ^ (string_of_formula_exp e2) ^ ")"
  | P.RelForm (r, args, _) ->
          (* An Hoa : relations *)
          r ^ "(" ^ (String.concat "," (List.map string_of_formula_exp args)) ^ ")"
  | P.VarPerm (t,ls,l) -> (string_of_vp_ann t) ^ "[" ^ (pr_list string_of_id ls)^"]"
  | P.BagIn (i, e , l) -> "BagIn("^(string_of_id i)^","^(string_of_formula_exp e)^")"
  | P.BagNotIn (i, e , l) -> "BagNotIn("^(string_of_id i)^","^(string_of_formula_exp e)^")"
  | P.BagMin (i1, i2 , l) -> "BagMin("^(string_of_id i1)^","^(string_of_id i2)^")"
  | P.BagMax (i1, i2 , l) -> "BagMax("^(string_of_id i1)^","^(string_of_id i2)^")"
  | P.BagSub (e1, e2 , l) -> "BagSub("^(string_of_formula_exp e1)^","^(string_of_formula_exp e2)^")"
   (* | _ -> "bag constraint" *)
;;

(*  | BagIn of ((ident * primed) * exp * loc)
  | BagNotIn of ((ident * primed) * exp * loc)
  | BagSub of (exp * exp * loc)
  | BagMin of ((ident * primed) * (ident * primed) * loc)
  | BagMax of ((ident * primed) * (ident * primed) * loc)	
	  (* lists and list formulae *)
*)

let concat_string_list_string strings =
    ""

(* pretty printing for a pure formula *)
let rec string_of_pure_formula = function 
  | P.BForm (bf,lbl)                    -> string_of_b_formula bf 
  | P.And (f1, f2, l)             -> "(" ^ (string_of_pure_formula f1) ^ ") & (" ^ (string_of_pure_formula f2) ^ ")"  
  | P.AndList b -> List.fold_left  (fun a (l,c)-> 
		let l_s = (string_of_spec_label l) ^": " in
		a ^ "\n" ^ (if a = "" then "" else " && ") ^ "\n" ^ l_s^(string_of_pure_formula c)) "" b
  | P.Or (f1, f2,lbl, l)              -> "(" ^ (string_of_pure_formula f1) ^ ") | (" ^ (string_of_pure_formula f2) ^ ")"
  | P.Not (f,lbl, l)                  -> "!(" ^ (string_of_pure_formula f) ^ ")"
  | P.Forall (x, f,lbl, l)            -> "all " ^ (string_of_id x)
        ^ " (" ^ (string_of_pure_formula f) ^ ")"
  | P.Exists (x, f,lbl, l)            -> "ex " ^ (string_of_id x)
        ^ " (" ^ (string_of_pure_formula f) ^ ")"
;;    

(* TOCHECK : what is the purpose? *)
let is_bool_f = function 
  | F.HTrue | F.HFalse | F.HEmp -> true 
  | _                  -> false 
;;

(*can not put this in perm.ml 
because we do not have separate printer
for ipure and iformula*)
let string_of_iperm perm =
      let perm_str =   match perm with
        | None -> ""
        | Some f -> string_of_formula_exp f
      in
      if (Perm.allow_perm ()) then "(" ^ perm_str ^ ")" else ""
;;

(* pretty printing for a heap formula *)
let rec string_of_h_formula = function 
  | F.Star ({F.h_formula_star_h1 = f1;
             F.h_formula_star_h2 = f2;
             F.h_formula_star_pos = l} ) ->
      if is_bool_f f1 then 
        if is_bool_f f2 then (string_of_h_formula f1) ^ " * " ^ (string_of_h_formula f2)
        else (string_of_h_formula f1) ^ " * (" ^ (string_of_h_formula f2) ^ ")"
      else
        "(" ^ (string_of_h_formula f1) ^ ") * (" ^ (string_of_h_formula f2) ^ ")"
  | F.Conj ({F.h_formula_conj_h1 = f1;
             F.h_formula_conj_h2 = f2;
             F.h_formula_conj_pos = l} ) ->
      if is_bool_f f1 then 
        if is_bool_f f2 then (string_of_h_formula f1) ^ " & " ^ (string_of_h_formula f2)
        else (string_of_h_formula f1) ^ " & (" ^ (string_of_h_formula f2) ^ ")"
      else
        "(" ^ (string_of_h_formula f1) ^ ") & (" ^ (string_of_h_formula f2) ^ ")"
  | F.Phase ({F.h_formula_phase_rd = f1;
              F.h_formula_phase_rw = f2;
              F.h_formula_phase_pos = l} ) ->
      if is_bool_f f1 then 
        if is_bool_f f2 then (string_of_h_formula f1) ^ " ; " ^ (string_of_h_formula f2)
        else (string_of_h_formula f1) ^ " ; (" ^ (string_of_h_formula f2) ^ ")"
      else
        "(" ^ (string_of_h_formula f1) ^ ") ; (" ^ (string_of_h_formula f2) ^ ")"
  | F.HeapNode ({F.h_formula_heap_node = x;
                 F.h_formula_heap_name = id;
                 F.h_formula_heap_perm = perm; (*LDK*)
                 F.h_formula_heap_arguments = pl;
                 F.h_formula_heap_imm = imm;
                 F.h_formula_heap_label = pi;
                 F.h_formula_heap_pos = l}) ->
      let perm_str = string_of_iperm perm in
      ((string_of_id x)
        ^ "::" ^ id ^ perm_str ^ "<" ^ (string_of_formula_exp_list pl) ^ ">" ^ (string_of_imm imm)^"[HeapNode1]")
  | F.HeapNode2 ({F.h_formula_heap2_node = xid;
                  F.h_formula_heap2_name = id;
                  F.h_formula_heap2_label = pi;
                  F.h_formula_heap2_imm = imm;
                  F.h_formula_heap2_perm = perm; (*LDK*)
                  F.h_formula_heap2_arguments = args}) ->
      let tmp1 = List.map (fun (f, e) -> f ^ "=" ^ (string_of_formula_exp e)) args in
      let tmp2 = String.concat ", " tmp1 in
      let perm_str = string_of_iperm perm in
      string_of_formula_label_opt pi
        ((string_of_id xid)
         ^ "::" ^ id ^perm_str ^  "<" ^ tmp2 ^ ">"  ^ (string_of_imm imm)^"[HeapNode2]")
  | F.HTrue -> "htrue"
  | F.HFalse -> "hfalse"
  | F.HEmp -> "emp"

and string_of_imm imm = match imm with
  | Iformula.ConstAnn(Imm) -> "@I"
  | Iformula.ConstAnn(Lend) -> "@L"
  | Iformula.ConstAnn(Mutable) -> "@M"
  | Iformula.PolyAnn(v, _) -> "@" ^ (string_of_var v)

(* and string_of_imm imm = match imm with *)
(*   | Imm -> "@I" *)
(*   | Lend -> "@L" *)
(*   | _ -> "@M" *)
;;
 
(* let string_of_identifier (d1,d2) = d1^(match d2 with | Primed -> "&&'" | Unprimed -> "");;  *)

let string_of_one_formula (f:F.one_formula) =
  let h,p,th,pos = F.split_one_formula f in
  let sh = string_of_h_formula h in
  let sp = string_of_pure_formula p in
  let sth = match th with
    | None -> ("thread = None")
    | Some (v,_) ->("thread = " ^ v)  in
  ( "<" ^ sth^ ">" 
    ^ "*" ^ "(" ^ sh ^ ")" 
    ^ "*" ^ "(" ^ sp ^ ")" )

let rec string_of_one_formula_list (f:F.one_formula list) =
  String.concat "\n AND" (List.map string_of_one_formula f)

(* pretty printing for formulae *) 
let rec string_of_formula = function 
  | Iast.F.Base ({F.formula_base_heap = hf;
                  F.formula_base_pure = pf;
                  F.formula_base_flow = fl;
                  F.formula_base_and = a;
                  F.formula_base_pos = l}) ->
      let sa = if a == [] then "" else "\nAND " in
      let sa = sa ^ (string_of_one_formula_list a) in
      let rs = 
        let s = string_of_pure_formula pf in
        (if s = "" then  (string_of_h_formula hf)
         else "(" ^ (string_of_h_formula hf) ^ ")*(" ^ (string_of_pure_formula pf) ^ ")( FLOW "^fl^")")
      in rs ^ sa
  | Iast.F.Or ({F.formula_or_f1 = f1;
                F.formula_or_f2 = f2;
                F.formula_or_pos = l}) ->
      (string_of_formula f1) ^ "\nor" ^ (string_of_formula f2)
  | Iast.F.Exists ({F.formula_exists_qvars = qvars;
                    F.formula_exists_heap = hf;
                    F.formula_exists_flow = fl;
                    F.formula_exists_and = a;
                    F.formula_exists_pure = pf}) ->
      let sa = if a==[] then "" else "\nAND " in
      let sa = sa ^ string_of_one_formula_list a in
      let rs= "(EX " ^ (string_of_var_list qvars) ^ " . "
              ^ (let s = string_of_pure_formula pf in
                 if s = "" then  (string_of_h_formula hf)
                 else "(" ^ (string_of_h_formula hf) ^ ")*(" ^ (string_of_pure_formula pf) ^ ")( FLOW "^fl^")")
              ^ ")"
      in rs^sa
;;

let rec string_of_struc_formula c = match c with 
	| F.ECase {
			F.formula_case_branches  =  case_list ;
		} -> 
			let impl = List.fold_left (fun a (c1,c2) -> a^"\n\t "^(string_of_pure_formula c1)^"->"^(string_of_struc_formula c2)^"\n") "ECase:\n" case_list in
			("case{"^impl^"}")
	|F.EBase {
		 	F.formula_struc_implicit_inst = ii;
			F.formula_struc_explicit_inst = ei;
		 	F.formula_struc_base = fb;
		 	F.formula_struc_continuation = cont;	
		} -> 
				let l1 = List.fold_left (fun a c-> a^" "^ string_of_var c) "" ii in
				let l2 = List.fold_left (fun a c -> a^" "^ string_of_var c) "" ei in
				let b = string_of_formula fb in
				let c = match cont with | None -> "" | Some l -> ("{"^(string_of_struc_formula l)^"}") in
				"EBase: ["^l1^"]["^l2^"]"^b^" "^c
	| F.EAssume (b,(n1,n2))-> "EAssume: "^(string_of_int n1)^","^n2^":"^(string_of_formula b)
	| F.EInfer{F.formula_inf_vars = lvars;
			   F.formula_inf_post = postf;
         F.formula_inf_xpost = postxf;
			   F.formula_inf_continuation = continuation;} ->
        let ps =if (lvars==[] && postf) then "@post " else "" in
		let string_of_inf_vars = Cprinter.str_ident_list (List.map (fun v -> fst v) lvars) in
		let string_of_continuation = string_of_struc_formula continuation in
		"EInfer "^ps^string_of_inf_vars^ " "^string_of_continuation 
	| F.EOr b-> (string_of_struc_formula b.F.formula_struc_or_f1) ^ "\nEOr" ^ (string_of_struc_formula b.F.formula_struc_or_f2)
	| F.EList b ->   List.fold_left  (fun a (l,c)-> 
		let l_s = (string_of_spec_label_def l) ^": " in
		a ^ "\n" ^ (if a = "" then "" else "||") ^ "\n" ^ l_s^(string_of_struc_formula c)) "" b
		(*let sl = if b then "("^(string_of_int (fst l))^",\""^(snd l)^"\"): " else "" in*)
		
	
;;

(* pretty printing for a list of formulae (f * f) list *)
let rec string_of_form_list l = match l with 
 | []               -> ""
 | (f1, f2)::[]      -> let s = (string_of_formula f1) in
                          (match s with 
							| ""  -> "   ensures " ^ (string_of_formula f2) ^ "\n"
							| _   -> "   requires " ^ s ^ "\n   ensures " ^ (string_of_formula f2) ^ "\n" )
 | (f1, f2)::t      -> let s = (string_of_formula f1) in
                         (match s with 
						   | ""  -> (string_of_form_list t)
                           | _   -> "   requires " ^ s ^ "\n   ensures " ^ (string_of_formula f2) ^ ";\n" ^ (string_of_form_list t) )  
;;

(*  | Assert of F.formula * F.formula option * loc
  | While of exp * exp * F.formula * F.formula * loc *)

(* function used to decide if parentrhesis are needed or not *)
let need_parenthesis2 = function 
  | Var _ | BoolLit _ | IntLit _ | FloatLit _ | Member _ -> false
  | _  -> true
;; 


(* pretty printing for expressions *)
let rec string_of_exp = function 
	| ArrayAt ({exp_arrayat_array_base = a;
	     exp_arrayat_index = e}) ->
				(string_of_exp a) ^ "[" ^ (string_of_exp_list e ",") ^ "]" (* An Hoa *)
  | Unfold ({exp_unfold_var = (v, p)}) -> "unfold " ^ v
  | Java ({exp_java_code = code}) -> code
  | Label ((pid,_),e) -> 
          string_of_control_path_id_opt pid(string_of_exp e)
  | Bind ({exp_bind_bound_var = v;
		   exp_bind_fields = vs;
		   exp_bind_path_id = pid;
		   exp_bind_body = e})-> 
          string_of_control_path_id_opt pid ("bind " ^ v ^ " to (" ^ (String.concat ", " vs) ^ ") in { " ^ (string_of_exp e) ^ " }")	   
  | Block ({
    exp_block_local_vars = lv;
    exp_block_body = e;
    })-> 
    "{" ^(match lv with
        | [] -> ""
        | _ -> "local: "^
          (String.concat "," (List.map (fun (c1,c2,c3)->(string_of_typ c2)^" "^c1) lv))^"\n")
        ^ (string_of_exp e) ^ "}\n"
  | Break b -> string_of_control_path_id_opt b.exp_break_path_id ("break "^(string_of_label b.exp_break_jump_label))
  | Barrier b -> "barrier "^b.exp_barrier_recv
  | Cast e -> "(" ^ (string_of_typ e.exp_cast_target_type) ^ ")" ^ (string_of_exp e.exp_cast_body)
  | Continue b -> string_of_control_path_id_opt b.exp_continue_path_id ("continue "^(string_of_label b.exp_continue_jump_label))
  | Catch c -> ("catch (" ^ (match c.exp_catch_var with | Some x-> x | None -> "") ^ ": " ^ c.exp_catch_flow_type ^")\n"^(string_of_exp c.exp_catch_body))
  | Empty l -> ""
  | Finally c->  ("finally "^(string_of_exp c.exp_finally_body))
  | Unary ({exp_unary_op = o;
			exp_unary_exp = e;
			exp_unary_pos = l})-> 
          (match o with 
            | OpPostInc | OpPostDec -> 
              (if need_parenthesis2 e then (parenthesis (string_of_exp e)) ^ (string_of_unary_op o)
               else (string_of_exp e) ^ (string_of_unary_op o))
            | _ -> 
              (if need_parenthesis2 e then (string_of_unary_op o) ^ (parenthesis (string_of_exp e))
               else (string_of_unary_op o) ^ (string_of_exp e)))
  | Binary ({exp_binary_op = o;
			 exp_binary_oper1 = e1;
			 exp_binary_oper2 = e2;
			 exp_binary_pos = l})-> 
          if need_parenthesis2 e1 then 
            if need_parenthesis2 e2 then (parenthesis (string_of_exp e1)) ^ (string_of_binary_op o) ^ (parenthesis (string_of_exp e2))
            else (parenthesis (string_of_exp e1)) ^ (string_of_binary_op o) ^ (string_of_exp e2)
          else  (string_of_exp e1) ^ (string_of_binary_op o) ^ (string_of_exp e2)
  | CallNRecv ({exp_call_nrecv_method = id;
                exp_call_nrecv_lock = lock;
				exp_call_nrecv_path_id = pid;
				exp_call_nrecv_arguments = el})-> 
          let lock_info = match lock with |None -> "" | Some id -> ("[" ^ id ^ "]") in
          string_of_control_path_id_opt pid (id ^ lock_info ^"(" ^ (string_of_exp_list el ",") ^ ")")
  | CallRecv ({exp_call_recv_receiver = recv;
			   exp_call_recv_method = id;
			   exp_call_recv_path_id = pid;
			   exp_call_recv_arguments = el})-> 
          string_of_control_path_id_opt pid ( (string_of_exp recv) ^ "." ^ id ^ "(" ^ (string_of_exp_list el ",") ^ ")")
	(* An Hoa *)
	| ArrayAlloc ({exp_aalloc_etype_name = elm_type;
		  exp_aalloc_dimensions = dims})  -> "new " ^ elm_type ^ "[" ^ (string_of_exp_list dims ",") ^ "]"
  | New ({exp_new_class_name = id;
		  exp_new_arguments = el})  -> "new " ^ id ^ "(" ^ (string_of_exp_list el ",") ^ ")" 
  | Var ({exp_var_name = v}) -> v
  | Member ({exp_member_base = e;
			 exp_member_fields = idl})-> (* An Hoa *) "member access " ^ (string_of_exp e) ^ "~~>" ^ (concatenate_string_list idl "~~>")
  | Assign ({exp_assign_op = op;
			 exp_assign_lhs = e1;
			 exp_assign_rhs = e2})  -> (string_of_exp e1) ^ (string_of_assign_op op) ^ (string_of_exp e2)
  | Cond ({exp_cond_condition = e1;
		   exp_cond_then_arm = e2;
		   exp_cond_path_id = pid;
		   exp_cond_else_arm = e3}) -> 
        string_of_control_path_id_opt pid ("if " ^ (parenthesis (string_of_exp e1)) ^ " { \n  " ^ (string_of_exp e2) ^ ";\n}" ^ 
        (match e3 with 
          | Empty ll -> ""
          | _        -> "\nelse { \n  " ^ (string_of_exp e3) ^ ";\n}"))
  | While ({exp_while_condition = e1;
			exp_while_body = e2;
			exp_while_jump_label = lb;
			exp_while_specs = li}) -> 
        (string_of_label lb)^" while " ^ (parenthesis (string_of_exp e1)) ^ " \n" ^ (string_of_struc_formula li)^" \n"^ "{\n"^ (string_of_exp e2) ^ "\n}"          
  | Return ({exp_return_val = v; exp_return_path_id = pid})  -> 
        string_of_control_path_id_opt pid ("return " ^ 
          (match v with 
            | None   -> ""
            | Some e -> (string_of_exp e)) )
  | Seq ({exp_seq_exp1 = e1;
		  exp_seq_exp2 = e2})-> 
          (string_of_exp e1) ^ ";\n" ^ (string_of_exp e2) ^ ";"  
  | VarDecl ({exp_var_decl_type = t;
			  exp_var_decl_decls = l})
                                   -> (string_of_typ t) ^ " " ^ (string_of_assigning_list l) ^ ";";
  | ConstDecl ({exp_const_decl_type = t;
				exp_const_decl_decls = l}) 
                                   -> "const " ^ (string_of_typ t) ^ " " ^ (string_of_cassigning_list l)
  | BoolLit ({exp_bool_lit_val = b})
                                   -> string_of_bool b 
  | IntLit ({exp_int_lit_val = i}) -> string_of_int i
  | FloatLit ({exp_float_lit_val = f})
                                   -> string_of_float f
  | Null l                         -> "null"
  | Assert l                       -> 
        snd(l.exp_assert_path_id)^" :assert "^
          (match l.exp_assert_asserted_formula with
            | None -> (" assume: ")
            | Some f-> (string_of_struc_formula (fst f))^"\n assume: ") ^
          (match l.exp_assert_assumed_formula with
            | None -> ""
            | Some f -> (string_of_formula f))^"\n"
  | Dprint l                       -> "dprint" 
  | Debug ({exp_debug_flag = f})   -> "debug " ^ (if f then "on" else "off")
  | This _ -> "this"
  | Time (b,s,_) -> ("Time "^(string_of_bool b)^" "^s)
  | Raise ({exp_raise_type = tb;
			exp_raise_path_id = pid;
			exp_raise_val = b;}) -> 
        let ft = match tb with 
                      | Const_flow cf-> "CF"^cf
                      | Var_flow cf -> "VF"^cf in
        string_of_control_path_id_opt pid 
				("raise "^(match b with 
                  | None -> ft
                  | Some bs-> "EXPR:"^ft^(string_of_exp bs))^ "\n")
  | Try ({	exp_try_block = bl;
			exp_catch_clauses = cl;
			exp_finally_clause = fl;})
				-> "try {"^(string_of_exp bl)^"\n}"^(List.fold_left (fun a b -> a^"\n"^(string_of_exp b)) "" cl)^
									(List.fold_left (fun a b -> a^"\n"^(string_of_exp b)) "" fl)
							
and 
   (* function to transform a list of expression in a string *)
   string_of_exp_list l c = match l with  
     | []                          -> ""
     | h::[]                       -> string_of_exp h
     | h::t 	                   -> (string_of_exp h) ^ c ^ " " ^ (string_of_exp_list t c)			    
and 
   (* function to transform in a string such a list : ((ident * exp option * loc) list *)
   string_of_assigning_list l = match l with 
     | []                          -> ""
     | (id, eo, l)::[]             -> id ^ (match eo with 
       | None    -> ""
       | Some e  -> " = " ^ (string_of_exp e))
     | (id, eo, l)::t 	           -> id ^ (match eo with 
       | None    -> ""
       | Some e  -> " = " ^ (string_of_exp e)) ^ ", " ^ (string_of_assigning_list t)
and 
   string_of_cassigning_list l = match l with 
     | []                          -> ""
     | (id, e, l)::[]              -> id ^ "=" ^ (string_of_exp e)
     | (id, e, l)::t 	           -> id ^ "=" ^ (string_of_exp e) ^ ", " ^ (string_of_cassigning_list t)

;;

(* pretty printing for one data declaration*)
let string_of_decl (d, pos, il) = match d with (* An Hoa [22/08/2011] Add inline component *)
  | (t, i)             -> (if il then "inline " else "") ^ (string_of_typ t) ^ " " ^ i
;;           

(* function to print a list of typed _ident *) 
let rec string_of_decl_list l c = match l with 
  | []               -> ""
  | h::[]            -> "  " ^ string_of_decl h 
  | h::t             -> "  " ^ (string_of_decl h) ^ ";" ^ c ^ (string_of_decl_list t c)
;;

(* pretty printing for a data declaration *)
let string_of_data_decl d = "data " ^ d.data_name ^ " {\n" ^ (string_of_decl_list d.data_fields "\n") ^ "\n}"
;;

(* pretty printing for a global variable declaration *)
let string_of_global_var_decl d = "global " ^ (string_of_exp (VarDecl d))
;;


let string_of_barrier_decl b = 
	let pr_trans (s,d,l) = 
		"("^(string_of_int s)^"->"^(string_of_int d)^
		",[{ "^(String.concat "}\n{" (List.map string_of_struc_formula l)^"}")^")" in
	"barrier: "^b.barrier_name^"<"^(string_of_int b.barrier_thc)^";"^(string_of_typed_var_list b.barrier_shared_vars) ^
	"\n transitions: \n ["^(String.concat "\n " (List.map pr_trans b.barrier_tr_list))^ "]\n";;

(* pretty printig for view declaration *)
let string_of_view_decl v = v.view_name ^ "<" ^ (concatenate_string_list v.view_vars ",") ^ "> == " ^ 
                            (string_of_struc_formula v.view_formula) ^ " inv " ^ (string_of_pure_formula v.view_invariant) ^ " inv_lock: " ^ (pr_opt string_of_formula v.view_inv_lock) ^" view_data_name: " ^ v.view_data_name                  (* incomplete *)
;;

let string_of_view_vars v_vars = (concatenate_string_list v_vars ",")

let string_of_coerc_type c = match c with 
  | Left -> "<="
  | Equiv -> "<=>"
  | Right -> "=>"

let string_of_coerc_decl c = (string_of_coerc_type c.coercion_type)^"coerc "^c.coercion_name^"\n\t head: "^(string_of_formula c.coercion_head)^"\n\t body:"^
							 (string_of_formula c.coercion_body)^"\n" 

(* pretty printing for one parameter *) 
let string_of_param par = match par.param_mod with 
 | NoMod          -> (string_of_typ par.param_type) ^ " " ^ par.param_name
 | RefMod         -> "ref " ^ (string_of_typ par.param_type) ^ " " ^ par.param_name
;;

(* pretty printing for a list of parameters *)
let rec string_of_param_list l = match l with 
 | []        -> ""
 | h::[]     -> (string_of_param h) 
 | h::t      -> (string_of_param h) ^ ", " ^ (string_of_param_list t)
;;


(* pretty printing for procedure *)                                                                                              
let string_of_proc_decl p = 
  let body = match p.proc_body with 
	| None     -> ""
	| Some e   -> "{\n" ^ (string_of_exp e) ^ "\n}" in
 (* let locstr = (string_of_full_loc p.proc_loc)  
  in	*)
    (if p.proc_constructor then "" else (string_of_typ p.proc_return) ^ " ")
	^ p.proc_name ^ "(" ^ (string_of_param_list p.proc_args) ^ ")\n" 
	^ ( "static " ^ (string_of_struc_formula  p.proc_static_specs)
		^ "\ndynamic " ^ (string_of_struc_formula  p.proc_dynamic_specs) ^ "\n" ^ body)
;;

let string_of_rel_decl p = 
  let pr = pr_list (pr_pair string_of_typ (fun x -> x)) in
    p.rel_name ^ "(" ^ (pr p.rel_typed_vars) ^ ")"
;;


(* proc_pre_post_list : (F.formula * F.formula) list; *)

(* pretty printing for a list of data_decl *)
let rec string_of_data_decl_list l = match l with 
 | []        -> ""
 | h::[]     -> (string_of_data_decl h) 
 | h::t      -> (string_of_data_decl h) ^ "\n" ^ (string_of_data_decl_list t)
;;

(* pretty printing for a list of proc_decl *)
let rec string_of_proc_decl_list l = match l with 
 | []        -> ""
 | h::[]     -> (string_of_proc_decl h) 
 | h::t      -> (string_of_proc_decl h) ^ "\n" ^ (string_of_proc_decl_list t)
;;

(* pretty printing for a list of view_decl *)
let rec string_of_view_decl_list l = match l with 
 | []        -> ""
 | h::[]     -> (string_of_view_decl h) 
 | h::t      -> (string_of_view_decl h) ^ "\n" ^ (string_of_view_decl_list t)
;;

(* pretty printing for a list of barrier_decl *)
let rec string_of_barrier_decl_list l = match l with 
 | []        -> ""
 | h::[]     -> (string_of_barrier_decl h) 
 | h::t      -> (string_of_barrier_decl h) ^ "\n" ^ (string_of_barrier_decl_list t)
;;

(* pretty printing for a list of coerc_decl *)
let rec string_of_coerc_decl_list l = match l with 
 | []        -> ""
 | h::[]     -> (string_of_coerc_decl h) 
 | h::t      -> (string_of_coerc_decl h) ^ "\n" ^ (string_of_coerc_decl_list t)
;;

(* pretty printing for an element of type (ident * int option) *)
let string_of_const_decl c = match c with 
 | (id, io)  -> id ^ (match io with 
   | Some i -> " = " ^ (string_of_int i) 
   | None   -> "" )
;;

(* pretty printing for a list of elements of type (ident * int option) *)
let rec string_of_const_decl_list l = match l with 
 | []       -> ""
 | h::[]    -> string_of_const_decl h 
 | h::t     -> (string_of_const_decl h) ^ "," ^ (string_of_const_decl_list t)
;;   

(* pretty printing for constants declaration (enum) *)
let string_of_enum_decl ed = "enum " ^ ed.enum_name ^ "{" ^ (string_of_const_decl_list ed.enum_fields) ^ "}"
;;

(* pretty printing for a list of constant declarations *)
let rec string_of_enum_decl_list l = match l with 
 | []       -> ""
 | h::[]    -> string_of_enum_decl h 
 | h::t     -> (string_of_enum_decl h) ^ "\n" ^ (string_of_enum_decl_list t)
;;   

(* pretty printing for a list of global variable declarations *)
let rec string_of_global_var_decl_list l = 
  match l with
  | []    -> ""
  | h::[] -> string_of_global_var_decl h
  | h::t  -> (string_of_global_var_decl h) ^ "\n" ^ (string_of_global_var_decl_list t)
;;

(* An Hoa : print relations *)
let string_of_rel_decl_list rdecls = 
	String.concat "\n" (List.map (fun r -> "relation " ^ r.rel_name) rdecls)

(* An Hoa : print axioms *)
let string_of_axiom_decl_list adecls = 
	String.concat "\n" (List.map (fun a -> "axiom " ^ (string_of_pure_formula a.axiom_hypothesis) ^ " |- " ^ (string_of_pure_formula a.axiom_conclusion)) adecls)

let string_of_data cdef = 
  let meth_str = String.concat "\n" (List.map string_of_proc_decl cdef.data_methods) in
  let field_str = String.concat ";\n" 
	(List.map (fun f -> ((* An Hoa [22/08/2011] : convert hard coded information extraction to function calls to make code extensible *) (string_of_typ (get_field_typ f)) ^ " " ^ (get_field_name f))) cdef.data_fields) in
  let inv_str = String.concat ";\n" (List.map (fun i -> "inv " ^ (string_of_formula i)) cdef.data_invs) in
	"class " ^ cdef.data_name ^ " extends " ^ cdef.data_parent_name ^ " {\n"
	^ field_str ^ "\n" ^ inv_str ^ "\n" ^ meth_str ^ "\n}"

(* pretty printing for program *)
let string_of_program p = (* "\n" ^ (string_of_data_decl_list p.prog_data_decls) ^ "\n\n" ^  *)
  (String.concat "\n\n" (List.map string_of_data p.prog_data_decls)) ^ "\n\n" ^
  (string_of_global_var_decl_list p.prog_global_var_decls) ^ "\n" ^
  (string_of_enum_decl_list p.prog_enum_decls) ^"\n" ^
  (string_of_view_decl_list p.prog_view_decls) ^"\n" ^
  (string_of_barrier_decl_list p.prog_barrier_decls) ^ "\n" ^
  (string_of_rel_decl_list p.prog_rel_decls) ^"\n" ^
  (string_of_axiom_decl_list p.prog_axiom_decls) ^"\n" ^
  (string_of_coerc_decl_list p.prog_coercion_decls) ^ "\n\n" ^ 
  (string_of_proc_decl_list p.prog_proc_decls) ^ "\n"
;;

Iformula.print_one_formula := string_of_one_formula;;
Iformula.print_h_formula :=string_of_h_formula;;
Iformula.print_formula :=string_of_formula;;
Iformula.print_struc_formula :=string_of_struc_formula;;
Iast.print_struc_formula := string_of_struc_formula;;
Iast.print_view_decl := string_of_view_decl;
Ipure.print_formula :=string_of_pure_formula;

