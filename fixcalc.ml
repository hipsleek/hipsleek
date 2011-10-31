(*
  Call Fixpoint Calculator, send input to it
*)

open Globals
open Gen.Basic
open Cformula
open Format
open Globals 
open Lexing 
open Cast 

module P = Cpure
module MP = Mcpure

let output = "fixcalc.inp";;
let oc = ref (open_out output);;

let is_short n = (n==2);;

let is_medium n = (n==1);;

let is_long n = (n==0);;

(** the formatter that fmt- commands will use *)
let fmt = ref (std_formatter)
let pr_mem = ref true

(** primitive formatter comands *)
let fmt_string x = Printf.fprintf (!oc) "%s" x
let fmt_bool x = Printf.fprintf (!oc) "%b" x
let fmt_int x = Printf.fprintf (!oc) "%d" x
let fmt_float x = Printf.fprintf (!oc) "%f" x
let fmt_char x = Printf.fprintf (!oc) "%c" x
let fmt_space x = Printf.fprintf (!oc) " "
let fmt_break x = pp_print_break (!fmt) x
let fmt_cut x = pp_print_cut (!fmt) x
let fmt_set_margin x = pp_set_margin (!fmt) x
let fmt_print_newline x = pp_print_newline (!fmt) x
let fmt_print_flush x = pp_print_flush (!fmt) x
let fmt_open_box n = pp_open_box (!fmt) n
let fmt_open_vbox n = pp_open_vbox (!fmt) n
let fmt_open_hbox n = pp_open_hbox (!fmt) n
let fmt_close_box x = pp_close_box (!fmt) x
let fmt_open x = fmt_open_box x
let fmt_close x = fmt_close_box x
(* test cvs commit*)


let pr_int i = fmt_int i

let pr_pair pr_1 pr_2 (a,b) =
  fmt_string "(";
  pr_1 a; fmt_string ",";
  pr_2 b; fmt_string ")"

let pr_opt f x = match x with
    | None -> fmt_string "None"
    | Some v -> (fmt_string "Some("; (f v); fmt_string ")")
  
(** polymorphic conversion to a string with -i- spaces identation*)
let poly_string_of_pr_gen (i:int) (pr: 'a -> unit) (e:'a) : string =
  (* let _ = print_string ("############ commit test") in *)
  let old_fmt = !fmt in
  begin
    (* fmt := str_formatter; *)
    let b = (Buffer.create 80) in
    begin
      fmt := formatter_of_buffer (b);
      fmt_open_box 0;
      fmt_string (String.make i ' ');
      pr e;
      fmt_close();
      fmt_print_flush();
      (* (let s = flush_str_formatter()in *)
      (* fmt := old_fmt; s) *)
      (let s = Buffer.contents(b) in
      fmt := old_fmt; s)
    end
  end    

(** conversion to a string with a 1-space indentation *)    
let poly_string_of_pr (pr: 'a -> unit) (e:'a) : string =
  poly_string_of_pr_gen 1 pr e

(** polymorphic function for debugging printer *)
let poly_printer_of_pr (crt_fmt: Format.formatter) (pr: 'a -> unit) (e:'a) : unit =
  let old_fmt = !fmt in
  begin
    fmt := crt_fmt;
    pr e;
    fmt := old_fmt;
  end    


(** shorter op code used internally *)
let op_add_short = "+" 
let op_sub_short = "-" 
let op_mult_short = "*" 
let op_div_short = "/" 
let op_max_short = "mx" 
let op_min_short = "mi" 
let op_union_short = "U" 
let op_intersect_short = "I" 
let op_diff_short = "D"
let op_and_short = "&"  
let op_or_short = "|"  
let op_not_short = "!"  
let op_star_short = "*"  
let op_phase_short = ";"  
let op_conj_short = "&"  
let op_f_or_short = "or"  
let op_lappend_short = "APP"
let op_cons_short = ":::"

(** op code that will be printed *)
let op_add = "+" 
let op_sub = "-" 
let op_mult = "*" 
let op_div = "/" 
let op_max = "max" 
let op_min = "min" 
let op_union = "union" 
let op_intersect = "intersect" 
let op_diff = "-" 
let op_lt = "<" 
let op_lte = "<=" 
let op_gt = ">" 
let op_gte = ">=" 
let op_eq = "=" 
let op_neq = "!=" 
let op_and = " && "  
let op_or = " | "  
let op_not = "!"  
let op_star = " && "  
let op_phase = " ; "  
let op_conj = " && "  
let op_f_or = "or" 
let op_lappend = "append"
let op_cons = ":::"


(** add a bracket around e if is simple yields false *)
let pr_bracket (isSimple:'a -> bool) (pr_elem:'a -> unit) (e:'a) : unit =
 if (isSimple e) then pr_elem e
 else (fmt_string "("; pr_elem e; fmt_string ")")

(** invoke f_open ; f_elem x1; f_sep .. f_sep; f_elem xn; f_close *)
let pr_list_open_sep (f_open:unit -> unit) 
    (f_close:unit -> unit) (f_sep:unit->unit) (f_empty:unit->unit)
    (f_elem:'a -> unit) (xs:'a list) : unit =
  let rec helper xs = match xs with
    | [] -> failwith "impossible to be [] in pr_list_open_sep"
    | [x] -> (f_elem x)
    | y::ys -> (f_elem y; f_sep(); helper ys) 
  in match xs with
    | [] -> f_empty()
    | xs -> f_open(); (helper xs); f_close() 

let pr_list_open_sep (f_open:unit -> unit) 
    (f_close:unit -> unit) (f_sep:unit->unit) (f_empty:unit->unit)
    (f_elem:'a -> unit) (xs:'a list) : unit =
  Gen.Debug.no_1 "pr_list_open_sep" string_of_int (fun _ -> "?") (fun _ -> pr_list_open_sep  (f_open:unit -> unit) 
    (f_close:unit -> unit) (f_sep:unit->unit) (f_empty:unit->unit)
    (f_elem:'a -> unit) xs) (List.length xs)

(** @param sep = "SAB"-space-cut-after-before,"SA"-space cut-after,"SB" -space-before 
 "AB"-cut-after-before,"A"-cut-after,"B"-cut-before, "S"-space, "" no-cut, no-space*)
let pr_op_sep_gen sep op =
  if sep="A" then (fmt_string op; fmt_cut())
  else if sep="B" then (fmt_cut();fmt_string op)
  else if sep="AB" then (fmt_cut();fmt_string op;fmt_cut())
  else if sep="SB" then (fmt_space();fmt_string op;fmt_string(" "))
  else if sep="SA" then (fmt_string(" "); fmt_string op; fmt_space())
  else if sep="SAB" then (fmt_space();fmt_string op; fmt_space())
  else if sep="S" then fmt_string (" "^op^" ")
  else fmt_string op (* assume sep="" *)

(** print op and a break after *)
let pr_cut_after op = pr_op_sep_gen "SA" op
  (* fmt_string (" "^op); fmt_space()  *)

  (** print op and a break after *)
let pr_cut_before op = pr_op_sep_gen "SB" op
  (* fmt_space(); fmt_string (op^" ") *)

  (** print op and a break after *)
let pr_cut_after_no op =  pr_op_sep_gen "A" op
  (* fmt_string op; fmt_cut() *) 

  (** print op and a break after *)
let pr_cut_before_no op =  pr_op_sep_gen "B" op
  (* fmt_cut(); fmt_string op *)

(** @param box_opt Some(s,i) for boxing options "V" -vertical,"H"-horizontal,"B"-box 
    @param sep_opt (Some s) for breaks at separator where "B"-before, "A"-after, "AB"-both  *) 
let pr_args_gen f_empty box_opt sep_opt op open_str close_str sep_str f xs =
  let f_o x = match x with
    | Some(s,i) -> 
          if s="V" then fmt_open_vbox i
          else if s="H" then fmt_open_hbox ()
          else  fmt_open_box i; (* must be B *)
    | None -> () in
  let f_c x = match x with
    | Some(s,i) -> fmt_close();
    | None -> () in
  let f_s x sep = match x with
    | Some s -> if s="A" then (fmt_string sep_str; fmt_cut())
      else if s="AB" then (fmt_cut(); fmt_string sep_str; fmt_cut()) 
      else (fmt_cut(); fmt_string sep_str)  (* must be Before *)
    | None -> fmt_string sep_str in 
  pr_list_open_sep 
      (fun () -> (f_o box_opt);  fmt_string op; fmt_string open_str)
      (fun () -> fmt_string close_str; (f_c box_opt)) 
      (fun () -> f_s sep_opt sep_str) 
      f_empty  f xs

 (** invoke pr_args_gen  *)   
let pr_args box_opt sep_opt op open_str close_str sep_str f xs =
  pr_args_gen (fun () -> fmt_string (op^open_str^close_str) ) box_opt sep_opt op open_str close_str sep_str f xs

 (** invoke pr_args_gen and print nothing when xs  is empty  *)      
let pr_args_option box_opt sep_opt op open_str close_str sep_str f xs =
  pr_args_gen (fun () -> ()) box_opt sep_opt op open_str close_str sep_str f xs


(** @param box_opt (s,i) wrap a "V" (vertical),"H" (horizontal) or just a box *)    
let wrap_box box_opt f x =  
  let f_o (s,i) = 
    if s="V" then fmt_open_vbox i
    else if s="H" then fmt_open_hbox ()
    else  fmt_open_box i;
  in
    f_o box_opt; f x; fmt_close()

(** if f e  is not true print with a cut in front of  hdr*)    
let pr_wrap_test hdr (e:'a -> bool) (f: 'a -> unit) (x:'a) =
  if (e x) then ()
  else (fmt_cut (); fmt_string hdr; (wrap_box ("B",0) f x))

(** if f e  is not true print without cut in front of  hdr*)      
let pr_wrap_test_nocut hdr (e:'a -> bool) (f: 'a -> unit) (x:'a) =
  if (e x) then ()
  else (fmt_string hdr; (wrap_box ("B",0) f x))


(** print hdr , a cut and a boxed  f a  *)  
let pr_vwrap_naive_nocut hdr (f: 'a -> unit) (x:'a) =
  begin
    fmt_string (hdr); fmt_cut();
    wrap_box ("B",2) f  x
  end

(** call pr_wrap_naive_nocut with a cut in front of *)
let pr_vwrap_naive hdr (f: 'a -> unit) (x:'a) =
  begin
    fmt_cut();
     pr_vwrap_naive_nocut hdr f x;
  end

(** this wrap is to be used in a vbox setting
   if hdr is big and the size of printing exceeds
   margin, it will do a cut and indent before continuing
*)
let pr_vwrap_nocut hdr (f: 'a -> unit) (x:'a) =
  if (String.length hdr)>7 then
    begin
      let s = poly_string_of_pr_gen 0 f x in
      if (String.length s) < 70 then (* to improve *)
        fmt_string (hdr^s)
      else begin
        fmt_string hdr; 
        fmt_cut ();
	    (* fmt_string s; *)
        fmt_string " ";
        wrap_box ("B",0) f  x
      end
    end
  else  begin 
    fmt_string hdr; 
    wrap_box ("B",2) f  x
  end
 
(** call pr_wrap_nocut with a cut in front of*)    
let pr_vwrap hdr (f: 'a -> unit) (x:'a) =
  begin
    fmt_cut();
    pr_vwrap_nocut hdr f x
  end

(** print a tuple with cut after separator*)
let pr_tuple op f xs = pr_args None (Some "A") op "(" ")" "," f xs

(** print an angle list with cut after separator*)  
let pr_angle op f xs = pr_args None (Some "A") op "<" ">" "," f xs
let pr_square op f xs = pr_args None (Some "A") op "[self," "]" "," f xs
let pr_bracket2 op f xs s = pr_args None (Some "A") op ("(" ^ s ^ ",") ")" "," f xs

(** print a sequence with cut after separator*)  
let pr_seq op f xs = pr_args None (Some "A") op "[" "]" "; " f xs

(** print a sequence with cut after separator in a VBOX*)    
let pr_seq_vbox op f xs = pr_args (Some ("V",1)) (Some "A") op "[" "]" ";" f xs

(** print a sequence without cut and box *)    
let pr_seq_nocut op f xs = pr_args None None op "[" "]" ";" f xs

let pr_seq_option op f xs = pr_args_option None (Some "A") op "[" "]" ";" f xs

(** print a list with cut after separator*)    
let pr_list_none f xs = pr_args None (Some "A") "" "" "" "," f xs

 (** print a set with cut after separator*)  
let pr_set f xs = pr_args None (Some "A") "" "{" "}" "," f xs

let pr_coq_list f xs = pr_args None (Some "A") "" "[|" "|]" "," f xs

 (** print a set with cut after separator in a VBOX*)  
let pr_set_vbox f xs = pr_args (Some ("V",1)) (Some "A") "{" "}" "," f xs

(** print prefix op(x1..xn) but use x1 alone if n=1 *)
let pr_fn_args op f xs = match xs with
  | [x] -> f x
  | _ -> (pr_tuple op f xs)

(** print infix form : x1 op .. op xn *)
let pr_list_op sep f xs = pr_args None (Some "A") "" "" "" sep f xs
  
  (** print infix form : x1 op .. op xn *)
let pr_list_op_vbox sep f xs = pr_args (Some ("V",0)) (Some "B") "" "" "" sep f xs

(**a list with a cut before separator *)  
let pr_list_op_none sep f xs = pr_args None (Some "B") "" "" "" sep f xs

(** print a list in a vbox and each element is in a box*)  
let pr_list_vbox_wrap sep f xs =
  if (String.length sep > 3) then
    pr_args (Some ("V",0)) (Some "AB") "" "" "" sep
      (fun x -> fmt_string " "; wrap_box ("B",0) f x) xs
  else   pr_args (Some ("V",0)) (Some "B") "" "" "" sep (wrap_box ("B",0) f) xs

 (**print f_1 op  f_2 and a space *)   
let pr_op_adhoc (f_1:unit -> unit) (op:string) (f_2:unit -> unit) =
  f_1(); fmt_string op ; f_2(); fmt_space()

(**print  f e1  op f e2 and a space *)
let pr_op (f:'a -> unit) (e1:'a) (op:string) (e2:'a)  =
  (f e1); fmt_string op ; (f e2); fmt_space()

let string_of_typed_spec_var x = 
  match x with
    | P.SpecVar (t, id, p) -> id

let string_of_spec_var x = 
(* string_of_typed_spec_var x *)
  match x with
    | P.SpecVar (t, id, p) -> id
      (* An Hoa : handle printing of holes *)
(*      let real_id = if (id.[0] = '#') then "#" else id in *)
(*      real_id (* ^":"^(string_of_typ t) *) ^ (match p with*)
(*        | Primed -> "'"                                   *)
(*        | Unprimed -> "" )                                *)

let string_of_imm imm = 
  if imm then "@I" else "@M"

let pr_spec_var x = fmt_string (string_of_spec_var x)

let pr_typed_spec_var x = fmt_string (string_of_typed_spec_var x)

let pr_list_of_spec_var xs = pr_list_none pr_spec_var xs
  
let pr_imm x = fmt_string (string_of_imm x)

let string_of_ident x = x

let pr_ident x = fmt_string (string_of_ident x)


(** check if top operator of e is associative and 
   return its list of arguments if so *)
let exp_assoc_op (e:P.exp) : (string * P.exp list) option = 
  match e with
    | P.Add (e1,e2,_) -> Some (op_add_short,[e1;e2])
    | P.Mult (e1,e2,_) -> Some (op_mult_short,[e1;e2])
    | P.Max (e1,e2,_) -> Some (op_max_short,[e1;e2])
    | P.Min (e1,e2,_) -> Some (op_min_short,[e1;e2])
    | P.BagUnion (es,_) -> Some (op_union_short,es)
    | P.BagIntersect (es,_) -> Some (op_intersect_short,es)
    | _ -> None

(** check if exp can be printed without a parenthesis,
     e.g. trivial expr and prefix forms *)
let exp_wo_paren (e:P.exp) = 
  match e with
    | P.Null _ 
    | P.Var _ 
    | P.IConst _ 
    | P.FConst _ | P.Max _ |   P.Min _ | P.BagUnion _ | P.BagIntersect _ 
 -> true
    | _ -> false

let b_formula_assoc_op (e:P.b_formula) : (string * P.exp list) option = None

(* check if exp can be printed without a parenthesis,
     e.g. trivial expr and prefix forms *)
let b_formula_wo_paren (e:P.b_formula) =
  let (pf,_) = e in
  match pf with
    | P.BConst _ 
    | P.BVar _ | P.BagMin _ | P.BagMax _ -> true
    | _ -> false

let pure_formula_assoc_op (e:P.formula) : (string * P.formula list) option = 
  match e with
    | P.And (e1,e2,_) -> Some (op_and_short,[e1;e2])
    | P.Or (e1,e2,_,_) -> Some (op_or_short,[e1;e2])
    | _ -> None

(* check if exp can be printed without a parenthesis,
     e.g. trivial expr and prefix forms *)
let pure_formula_wo_paren (e:P.formula) = 
  match e with
    | P.Forall _ 
    | P.Exists _ | P.Not _ -> true
    | P.BForm (e1,_) -> true (* b_formula_wo_paren e1 *)
    | P.And _ -> true 
    | _ -> false

let pure_memoised_wo_paren (e:MP.memo_pure) = false


let h_formula_assoc_op (e:h_formula) : (string * h_formula list) option = 
  match e with
    |Star ({h_formula_star_h1 = h1; h_formula_star_h2 = h2; h_formula_star_pos =_}) ->
       Some (op_star_short,[h1;h2])
    | _ -> None

(* check if exp can be printed without a parenthesis,
     e.g. trivial expr and prefix forms *)
let h_formula_wo_paren (e:h_formula) = 
  match e with
    | Star _ -> true
    | _ -> true


let formula_assoc_op (e:formula) : (string * formula list) option = 
  match e with
    |Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = _}) ->
       Some (op_f_or_short,[f1;f2])
    | _ -> None

(* check if exp can be printed without a parenthesis,
     e.g. trivial expr and prefix forms *)
let formula_wo_paren (e:formula) = 
  match e with
    | Or _ -> true
    | Base _-> true
    | Exists _-> true

let ft_assoc_op (e:fail_type) : (string * fail_type list) option = 
  match e with
    | Or_Reason (f1,f2) -> Some (op_or_short,[f1;f2])
    | And_Reason (f1,f2) -> Some (op_and_short,[f1;f2])
    | Union_Reason (f1,f2) -> Some (op_union_short,[f1;f2])
    | Or_Continuation (f1,f2) -> Some (op_or_short,[f1;f2])
    | _ -> None

(* check if exp can be printed without a parenthesis,
     e.g. trivial expr and prefix forms *)
let ft_wo_paren (e:fail_type) = true

(** print a formula exp to formatter *)
let rec pr_formula_exp (e:P.exp) =
  let f_b e =  pr_bracket exp_wo_paren pr_formula_exp e in
  match e with
    | P.Null l -> fmt_string "null"
    | P.Var (x, l) -> fmt_string (string_of_spec_var x)
    | P.IConst (i, l) -> fmt_int i
    | P.FConst (f, l) -> fmt_float f
    | P.Add (e1, e2, l) -> 
          let args = bin_op_to_list op_add_short exp_assoc_op e in
          pr_list_op op_add f_b args
    | P.Mult (e1, e2, l) -> 
          let args = bin_op_to_list op_mult_short exp_assoc_op e in
          pr_list_op op_mult f_b  args
    | P.Max (e1, e2, l) -> 
          let args = bin_op_to_list op_max_short exp_assoc_op e in
          pr_fn_args op_max pr_formula_exp args
    | P.Min (e1, e2, l) -> 
          let args = bin_op_to_list op_min_short exp_assoc_op e in
          pr_fn_args op_min pr_formula_exp  args
    | P.Bag (elist, l) 	-> pr_set pr_formula_exp elist
    | P.BagUnion (args, l) -> 
          let args = bin_op_to_list op_union_short exp_assoc_op e in
          pr_fn_args op_union pr_formula_exp args
    | P.BagIntersect (args, l) -> 
          let args = bin_op_to_list op_intersect_short exp_assoc_op e in
          pr_fn_args op_intersect pr_formula_exp args
    | P.Subtract (e1, e2, l) ->
          f_b e1; pr_cut_after op_sub; f_b e2
    | P.Div (e1, e2, l) ->
          f_b e1; pr_cut_after op_div ; f_b e2
    | P.BagDiff (e1, e2, l) -> 
          pr_formula_exp e1; pr_cut_after op_diff ; pr_formula_exp e2
    | P.List (elist, l) -> pr_coq_list pr_formula_exp elist 
    | P.ListAppend (elist, l) -> pr_tuple op_lappend pr_formula_exp elist
    | P.ListCons (e1, e2, l)  ->  f_b e1; pr_cut_after op_cons; f_b e2
    | P.ListHead (e, l)     -> fmt_string ("head("); pr_formula_exp e; fmt_string  (")")
    | P.ListTail (e, l)     -> fmt_string ("tail("); pr_formula_exp e; fmt_string  (")")
    | P.ListLength (e, l)   -> fmt_string ("len("); pr_formula_exp e; fmt_string  (")")
    | P.ListReverse (e, l)  -> fmt_string ("rev("); pr_formula_exp e; fmt_string  (")")
		| P.ArrayAt (a, i, l) -> fmt_string (string_of_spec_var a); fmt_string ("[");
		match i with
			| [] -> ()
			| arg_first::arg_rest -> let _ = pr_formula_exp arg_first in 
				let _ = List.map (fun x -> fmt_string (","); pr_formula_exp x) arg_rest
		in fmt_string  ("]") (* An Hoa *)
;;

let pr_slicing_label sl =
  match sl with
	| None -> fmt_string ""
	| Some (il, lbl, el) ->
		fmt_string ("<" ^ (if il then "IL, " else ", ") ^ (string_of_int lbl) ^ ", ");
	    fmt_string ("[");
		pr_list_none pr_formula_exp el;
		fmt_string ("]");
		fmt_string (">")
		  
(** print a b_formula  to formatter *)
let rec pr_b_formula (e:P.b_formula) =
  let f_b e =  pr_bracket exp_wo_paren pr_formula_exp e in
  let f_b_no e =  pr_bracket (fun x -> true) pr_formula_exp e in
  let (pf,il) = e in
  pr_slicing_label il;
  match pf with
    | P.BConst (b,l) -> fmt_bool b 
    | P.BVar (x, l) -> fmt_string (string_of_spec_var x)
    | P.Lt (e1, e2, l) -> f_b e1; fmt_string op_lt ; f_b e2
    | P.Lte (e1, e2, l) -> f_b e1; fmt_string op_lte ; f_b e2
    | P.Gt (e1, e2, l) -> f_b e1; fmt_string op_gt ; f_b e2
    | P.Gte (e1, e2, l) -> f_b e1; fmt_string op_gte ; f_b e2
    | P.Eq (P.Var(P.SpecVar (_,"self",_),_), P.Null _, l) -> fmt_string "self <= 0";
    | P.Eq (P.Null _, P.Var(P.SpecVar (_,"self",_),_), l) -> fmt_string "self <= 0";
(*    | P.Eq (P.Var(P.SpecVar (_,"self",_),_), e2, l) -> fmt_string "self <= 0";*)
(*    | P.Eq (_, P.Var(P.SpecVar (_,"self",_),_), l) -> fmt_string "self <= 0"; *)
    | P.Eq (e1, e2, l) -> f_b_no e1; fmt_string op_eq ; f_b_no e2
    | P.Neq (P.Var(P.SpecVar (_,"self",_),_), e2, l) -> 
			fmt_string "("; fmt_string "("; fmt_string "self < "; f_b_no e2; 
			fmt_string ") || (self > "; f_b_no e2; fmt_string ")"; fmt_string ")";
    | P.Neq (e2, P.Var(P.SpecVar (_,"self",_),_), l) -> 
			fmt_string "("; fmt_string "("; fmt_string "self < "; f_b_no e2; 
			fmt_string ") || (self > "; f_b_no e2; fmt_string ")"; fmt_string ")";
    | P.Neq (e1, e2, l) -> f_b e1; fmt_string op_neq ; f_b e2
    | P.EqMax (e1, e2, e3, l) ->   
          let arg2 = bin_op_to_list op_max_short exp_assoc_op e2 in
          let arg3 = bin_op_to_list op_max_short exp_assoc_op e3 in
          let arg = arg2@arg3 in
          (pr_formula_exp e1); fmt_string("="); pr_fn_args op_max pr_formula_exp arg
    | P.EqMin (e1, e2, e3, l) ->   
          let arg2 = bin_op_to_list op_min_short exp_assoc_op e2 in
          let arg3 = bin_op_to_list op_min_short exp_assoc_op e3 in
          let arg = arg2@arg3 in
          (pr_formula_exp e1); fmt_string("="); pr_fn_args op_min pr_formula_exp arg
    | P.BagIn (v, e, l) -> pr_op_adhoc (fun ()->pr_spec_var v) " <in> "  (fun ()-> pr_formula_exp e)
    | P.BagNotIn (v, e, l) -> pr_op_adhoc (fun ()->pr_spec_var v) " <notin> "  (fun ()-> pr_formula_exp e)
    | P.BagSub (e1, e2, l) -> pr_op pr_formula_exp e1  "<subset> " e2
    | P.BagMin (v1, v2, l) -> pr_op pr_spec_var v1  " = <min> " v2
    | P.BagMax (v1, v2, l) -> pr_op pr_spec_var v1  " = <max> " v2
    | P.ListIn (e1, e2, l) ->  pr_op_adhoc (fun ()->pr_formula_exp e1) " <Lin> "  (fun ()-> pr_formula_exp e2)
    | P.ListNotIn (e1, e2, l) ->  pr_op_adhoc (fun ()->pr_formula_exp e1) " <Lnotin> "  (fun ()-> pr_formula_exp e2)
    | P.ListAllN (e1, e2, l) ->  pr_op_adhoc (fun ()->pr_formula_exp e1) " <allN> "  (fun ()-> pr_formula_exp e2)
    | P.ListPerm (e1, e2, l) -> pr_op_adhoc (fun ()->pr_formula_exp e1) " <perm> "  (fun ()-> pr_formula_exp e2)
			| P.RelForm (r, args, l) -> fmt_string (r ^ "("); let _ = List.map (fun x -> fmt_string (","); pr_formula_exp x) args in fmt_string ")" (* An Hoa *) 
;;

let string_of_int_label (i,s) s2:string = (string_of_int i)^s2
let string_of_int_label_opt h s2:string = match h with | None-> "N "^s2 | Some s -> string_of_int_label s s2
let string_of_formula_label (i,s) s2:string = (* s2 *) ((string_of_int i)^":"^s^":"^s2)
let string_of_formula_label_pr_br (i,s) s2:string = ("("^(string_of_int i)^","^s^"):"^s2)
let string_of_formula_label_opt h s2:string = match h with | None-> s2 | Some s -> (string_of_formula_label s s2)
let string_of_control_path_id (i,s) s2:string = string_of_formula_label (i,s) s2
let string_of_control_path_id_opt h s2:string = string_of_formula_label_opt h s2
let string_of_formula_label_only x :string = string_of_formula_label x ""

let string_of_iast_label_table table =
  let string_of_row row =
    let string_of_label_loc (_, path_label, loc) =
      Printf.sprintf "%d: %s" path_label (string_of_full_loc loc)
    in
    let path_id, desc, labels, loc = row in
    Printf.sprintf "\nid: %s; labels: %s; loc: %s" 
      (string_of_control_path_id_opt path_id desc)
      (List.fold_left (fun s label_loc -> s ^ (string_of_label_loc label_loc) ^ ", ") "" labels)
      (string_of_full_loc loc)
  in
  List.fold_right (fun row res -> (string_of_row row) ^ res) table ""


let pr_formula_label_br l = fmt_string (string_of_formula_label_pr_br l "")
let pr_formula_label l  = fmt_string (string_of_formula_label l "")
let pr_formula_label_list l  = fmt_string ("{"^(String.concat "," (List.map (fun (i,_)-> (string_of_int i)) l))^"}")
let pr_formula_label_opt l = fmt_string (string_of_formula_label_opt l "")

(** print a pure formula to formatter *)
let rec pr_pure_formula  (e:P.formula) = 
  let f_b e =  pr_bracket pure_formula_wo_paren pr_pure_formula e 
  in
  match e with 
    | P.BForm (bf,lbl) -> (*pr_formula_label_opt lbl;*) pr_b_formula bf
    | P.And (f1, f2, l) ->  
          let arg1 = bin_op_to_list op_and_short pure_formula_assoc_op f1 in
          let arg2 = bin_op_to_list op_and_short pure_formula_assoc_op f2 in
          let args = arg1@arg2 in
          pr_list_op op_and f_b args
    | P.Or (f1, f2, lbl,l) -> 
          pr_formula_label_opt lbl; 
          let arg1 = bin_op_to_list op_or_short pure_formula_assoc_op f1 in
          let arg2 = bin_op_to_list op_or_short pure_formula_assoc_op f2 in
          let args = arg1@arg2 in
          pr_list_op op_or f_b args
    | P.Not (f, lbl, l) -> 
          pr_formula_label_opt lbl; 
          fmt_string "!(";f_b f;fmt_string ")"
    | P.Forall (x, f,lbl, l) -> 
          pr_formula_label_opt lbl; 
	      fmt_string "forall("; pr_spec_var x; fmt_string ":";
	      pr_pure_formula f; fmt_string ")"
    | P.Exists (x, f, lbl, l) -> 
          pr_formula_label_opt lbl; 
	      fmt_string "exists("; pr_spec_var x; fmt_string ":";
	      pr_pure_formula f; fmt_string ")"
;;

let pr_prune_status st = match st with
  | MP.Implied_N -> fmt_string "(IN)"
  | MP.Implied_P -> fmt_string "(IP)" 
  | MP.Implied_R -> fmt_string "(IDup)" 
  
let pr_memoise_constraint c = 
  pr_b_formula c.MP.memo_formula ; pr_prune_status c.MP.memo_status
  
let string_of_memoise_constraint c = poly_string_of_pr pr_memoise_constraint c
  
let pr_memoise mem = 
  fmt_string "[";pr_list_op_none "& " pr_memoise_constraint mem; fmt_string "]"

let pr_mem_slice slc = fmt_string "[";pr_pure_formula (P.conj_of_list slc no_pos); fmt_string "]"

let pr_mem_slice_aux slc = fmt_string "[";
 pr_list_op_none "" pr_pure_formula slc ; fmt_string "]"  
 
let pr_memoise_group_vb m_gr = 
  (*if !pr_mem then *)
  fmt_cut();
  wrap_box ("V",1)
      ( fun m_gr -> fmt_string "(";pr_list_op_none "" 
          (fun c-> wrap_box ("H",1) (fun _ -> fmt_string "SLICE["; pr_list_of_spec_var c.MP.memo_group_fv; fmt_string "]["; pr_list_of_spec_var c.MP.memo_group_linking_vars; fmt_string "]:") (); 
              fmt_cut ();fmt_string "  ";
              wrap_box ("B",1) pr_memoise c.MP.memo_group_cons;
              fmt_cut ();fmt_string "  ";
              wrap_box ("B",1) pr_mem_slice c.MP.memo_group_slice;
              fmt_cut ();fmt_string "  alias set:";
              wrap_box ("B",1) fmt_string (P.EMapSV.string_of c.MP.memo_group_aset);
              (* fmt_cut(); *)
          ) m_gr; fmt_string ")") m_gr
  (*else ()*)
  
let pr_memoise_group_standard print_P m_gr = 
  (*if !pr_mem then *)
  fmt_cut();
  wrap_box ("B",1)
      ( fun m_gr -> fmt_string "(";pr_list_op_none " && "     
          (fun c-> 
              let f = MCP.fold_mem_lst (CP.mkTrue no_pos) false print_P (MCP.MemoF [c]) in
(*              fmt_string "[";*)
              wrap_box ("B",1) pr_pure_formula f;
(*              fmt_string "]";*)
              fmt_cut()
          ) m_gr; fmt_string ")") m_gr

let pr_memoise_group m_gr = match !Globals.memo_verbosity with
  | 0 -> pr_memoise_group_vb m_gr (*verbose*)
  | 1 -> pr_memoise_group_standard false  m_gr (*brief*)
  | _ -> pr_memoise_group_standard true  m_gr (*standard*)
      
let pr_remaining_branches s = () 
(*	match s with                                                                                      *)
(*  | None -> () (* fmt_string "None" *)                                                              *)
(*  | Some s ->                                                                                       *)
(*        fmt_cut();                                                                                  *)
(*        wrap_box ("B",1) (fun s->fmt_string "@ rem br[" ; pr_formula_label_list s; fmt_string "]") s*)

let string_of_remaining_branches c = poly_string_of_pr pr_remaining_branches c

let pr_prunning_conditions cnd pcond = match cnd with 
  | None -> ()
  | Some _ -> () (* fmt_cut (); fmt_string "@ prune_cond [" ; wrap_box
                    ("B",1) (fun pcond-> List.iter (fun (c,c2)-> fmt_cut (); fmt_string
                    "( " ; pr_b_formula c; fmt_string" )->"; pr_formula_label_list c2;)
                    pcond;fmt_string "]") pcond *)

let string_of_ms (m:(P.spec_var list) list) : string =
  let wrap s1 = "["^s1^"]" in
  let ls = List.map (fun l -> wrap (String.concat "," (List.map string_of_spec_var l))) m in
  wrap (String.concat ";" ls)

let pr_mem_formula  (e : mem_formula) = 
  fmt_string (string_of_ms e.mem_formula_mset)

let rec pr_h_formula h = 
  let f_b e =  pr_bracket h_formula_wo_paren pr_h_formula e 
  in
  match h with
    | Star ({h_formula_star_h1 = h1; h_formula_star_h2 = h2; h_formula_star_pos = pos}) -> 
	      let arg1 = bin_op_to_list op_star_short h_formula_assoc_op h1 in
          let arg2 = bin_op_to_list op_star_short h_formula_assoc_op h2 in
          let args = arg1@arg2 in
          pr_list_op op_star f_b args
    | Phase ({h_formula_phase_rd = h1; h_formula_phase_rw = h2; h_formula_phase_pos = pos}) -> 
	      let arg1 = bin_op_to_list op_phase_short h_formula_assoc_op h1 in
          let arg2 = bin_op_to_list op_phase_short h_formula_assoc_op h2 in
          let args = arg1@arg2 in
          fmt_string "("; pr_list_op op_phase f_b args; fmt_string ")" 
    | Conj ({h_formula_conj_h1 = h1; h_formula_conj_h2 = h2; h_formula_conj_pos = pos}) -> 
	      let arg1 = bin_op_to_list op_conj_short h_formula_assoc_op h1 in
          let arg2 = bin_op_to_list op_conj_short h_formula_assoc_op h2 in
          let args = arg1@arg2 in
          pr_list_op op_conj f_b args
    | DataNode ({h_formula_data_node = sv;
      h_formula_data_name = c;
	  h_formula_data_imm = imm;
      h_formula_data_arguments = svs;
		h_formula_data_holes = hs; (* An Hoa *)
      h_formula_data_pos = pos;
      h_formula_data_remaining_branches = ann;
      h_formula_data_label = pid})-> 
			(** [Internal] Replace the specvars at positions of holes with '-' **)
			let rec replace_holes svl hs n = 
				if hs = [] then svl
				else let sv = List.hd svl in
						match sv with
							| CP.SpecVar (t,vn,vp) -> 
								if (List.hd hs = n) then
									CP.SpecVar (t,"-",vp) :: (replace_holes (List.tl svl) (List.tl hs) (n+1))
								else
									sv :: (replace_holes (List.tl svl) hs (n+1))
			in
			let svs = replace_holes svs hs 0 in
          fmt_open_hbox ();
          let _ = match sv with
            | P.SpecVar (t, "self", p) -> fmt_string "self > 0";
            | _ -> pr_bracket2 c pr_spec_var svs (string_of_spec_var sv);
          in fmt_close();
    | ViewNode ({h_formula_view_node = sv; 
      h_formula_view_name = c; 
	  h_formula_view_imm = imm;
      h_formula_view_arguments = svs; 
      h_formula_view_origins = origs;
      h_formula_view_original = original;
      h_formula_view_lhs_case = lhs_case;
      h_formula_view_label = pid;
      h_formula_view_remaining_branches = ann;
      h_formula_view_pruning_conditions = pcond;
      h_formula_view_pos =pos}) ->
          fmt_open_hbox ();
          let _ = match sv with
            | P.SpecVar (t, "self", p) -> fmt_string "self > 0";
            | _ -> pr_bracket2 c pr_spec_var svs (string_of_spec_var sv);
          in
          pr_remaining_branches ann; 
          pr_prunning_conditions ann pcond;
          fmt_close()
    | HTrue -> fmt_string "True"
    | HFalse -> fmt_string "False"
    | Hole m -> fmt_string ("Hole[" ^ (string_of_int m) ^ "]")

(** convert formula exp to a string via pr_formula_exp *)
let string_of_formula_exp (e:P.exp) : string =  poly_string_of_pr  pr_formula_exp e

let printer_of_formula_exp (crt_fmt: Format.formatter) (e:P.exp) : unit =
  poly_printer_of_pr crt_fmt pr_formula_exp e

let string_of_memoised_list l : string  = poly_string_of_pr pr_memoise_group l

(* string of a slicing label *)
let string_of_slicing_label sl : string =  poly_string_of_pr  pr_slicing_label sl
  
(** convert b_formula to a string via pr_b_formula *)
let string_of_b_formula (e:P.b_formula) : string =  poly_string_of_pr  pr_b_formula e

let printer_of_b_formula (crt_fmt: Format.formatter) (e:P.b_formula) : unit =
  poly_printer_of_pr crt_fmt pr_b_formula e

(** convert mem_formula  to a string via pr_mem_formula *)
let string_of_mem_formula (e:Cformula.mem_formula) : string =  poly_string_of_pr  pr_mem_formula e

(** convert pure_formula  to a string via pr_pure_formula *)
let string_of_pure_formula (e:P.formula) : string =  poly_string_of_pr  pr_pure_formula e

let printer_of_pure_formula (crt_fmt: Format.formatter) (e:P.formula) : unit =
  poly_printer_of_pr crt_fmt pr_pure_formula e

(** convert h_formula  to a string via pr_h_formula *)
let string_of_h_formula (e:h_formula) : string =  poly_string_of_pr  pr_h_formula e

let printer_of_h_formula (crt_fmt: Format.formatter) (e:h_formula) : unit =
  poly_printer_of_pr crt_fmt pr_h_formula e

let  pr_pure_formula_branches (f, l) =
 (pr_bracket pure_formula_wo_paren pr_pure_formula f); 
   pr_seq_option " && " (fun (l, f) -> fmt_string ("\"" ^ l ^ "\" : "); 
   pr_pure_formula f) l

let  pr_memo_pure_formula f = pr_bracket pure_memoised_wo_paren pr_memoise_group f

let  pr_memo_pure_formula_branches (f, l) =
  (pr_bracket pure_memoised_wo_paren pr_memoise_group f); 
  pr_seq_option " && " (fun (l, f) -> fmt_string ("\"" ^ l ^ "\" : "); 
      pr_pure_formula f) l

let pr_mix_formula f = match f with
  | MCP.MemoF f -> pr_memo_pure_formula f
  | MCP.OnePF f -> pr_pure_formula f


let pr_mix_formula_branches (f,l) = match f with
  | MCP.MemoF f -> pr_memo_pure_formula_branches (f,l)
  | MCP.OnePF f -> pr_pure_formula_branches (f,l)

let rec string_of_flow_formula f c = 
  "{"^f^",("^(string_of_int (fst c.formula_flow_interval))^","^(string_of_int (snd c.formula_flow_interval))^
	  ")="^(Gen.ExcNumbering.get_closest c.formula_flow_interval)^(match c.formula_flow_link with | None -> "" | Some e -> ","^e)^"}"

let rec pr_formula_base e =
  match e with
    | ({formula_base_heap = h;
	  formula_base_pure = p;
	  formula_base_branches = b;
	  formula_base_type = t;
	  formula_base_flow = fl;
    formula_base_label = lbl;
	  formula_base_pos = pos}) ->
			pr_h_formula h ; pr_cut_after "&&" ; pr_mix_formula_branches(p,b)

let rec pr_formula e =
  let f_b e =  pr_bracket formula_wo_paren pr_formula e in
  match e with
    | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) ->
	    let arg1 = bin_op_to_list op_f_or_short formula_assoc_op f1 in
      let arg2 = bin_op_to_list op_f_or_short formula_assoc_op f2 in
      let args = arg1@arg2 in
	    pr_list_vbox_wrap "or " f_b args
    | Base e -> pr_formula_base e
    | Exists ({formula_exists_qvars = svs;
	  formula_exists_heap = h;
	  formula_exists_pure = p;
	  formula_exists_branches = b;
	  formula_exists_type = t;
	  formula_exists_flow = fl;
    formula_exists_label = lbl;
	  formula_exists_pos = pos}) ->
      fmt_string "exists ("; pr_list_of_spec_var svs; fmt_string ": ";
      pr_h_formula h; pr_cut_after "&&" ;
      pr_mix_formula_branches(p,b); fmt_string ")";;

let fixcalc = "fixcalc";;
 
let syscall cmd =
  let ic, oc3 = Unix.open_process cmd in
  let buf = Buffer.create 16 in
  (try
     while true do
       Buffer.add_channel buf ic 1
     done
   with End_of_file -> ());
  let _ = Unix.close_process (ic, oc3) in
  (Buffer.contents buf)

let compute_inv name vars fml pf = 	
	if !Globals.do_infer_inv then
	begin
		pr_square (name ^ ":=" ^ "{")  pr_typed_spec_var vars; 
		fmt_string " -> [] -> []: ";
	  pr_list_op_none "\n|| " (fun (c,_)-> pr_formula c) fml;
	(*	print_newline ();                                         *)
	(*	print_endline "};";                                       *)
	(*	print_endline ("Fix1:=bottomup(" ^ name ^ ",1,SimHeur);");*)
	(*	print_endline ("Fix2:=bottomup(" ^ name ^ ",2,SimHeur);");*)
	(*	print_endline "Fix1; Fix2;";	                            *)
	(*  print_newline ();                                         *)
	(*  Printf.fprintf (!oc) "\n};\n\nFix1:=bottomup(%s,1,SimHeur);\nFix2:=bottomup(%s,2,SimHeur);\nFix1; Fix2;\n\n" name name;*)
	  Printf.fprintf (!oc) "\n};\n\nFix1:=bottomup(%s,1,SimHeur);\nFix1;\n\n" name;
		flush (!oc);
		close_out (!oc);
		let output2 = "fixcalc.out" in
	  let oc2 = open_out output2 in
	  let res = syscall (fixcalc ^ " " ^ output) in
		oc := open_out output;
	  Printf.fprintf oc2 "%s" res;
		close_out oc2;
		let _ = syscall ("sed -i /^#/d " ^ output2) in
		let _ = syscall ("sed -i /^T/d " ^ output2) in
		let _ = syscall ("sed -i /^$/d " ^ output2) in
		let string = syscall ("cat " ^ output2) in
		let new_pf = Parse_fix.parse_fix string in
	(*	print_string res;*)
	(*  print_endline (Cprinter.string_of_pure_formula new_pf ^ "a");*)
	  let check_impl = Omega.imply new_pf pf "1" 100 in
		if check_impl then 
		begin
			Cprinter.fmt_string "LOG : REPLACED INV -> ";
			Cprinter.pr_angle name (fun x -> Cprinter.fmt_string (Cprinter.string_of_typed_spec_var x)) vars;
			Cprinter.fmt_string ("\n -> OLD: " ^ (Cprinter.string_of_pure_formula pf) ^
        " -> NEW: " ^ (Cprinter.string_of_pure_formula new_pf));				
(*			print_endline "INFO : Invariant of " ^ self::lseg<p,n> ^ " has been replaced*)
(*        by a stronger inferred formula n>=0"                                      *)
			new_pf
		end 
		else pf
	end
	else pf

  
	
	



