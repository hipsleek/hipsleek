(** pretty printing for formula and cast *)

open Format
open Globals 
open Lexing 
open Cast 
open Cformula

module P = Cpure
module MP = Mcpure


(* pretty printing for primitive types *)
let string_of_prim_type = function 
  | Bool          -> "boolean"
  | Float         -> "float"
  | Int           -> "int"
  | Void          -> "void"
  | Bag           -> "multiset"
  | List          -> "list"
;;

(* pretty printing for types *)
let string_of_typ = function 
  | P.Prim t -> string_of_prim_type t 
  | P.OType ot -> if ((String.compare ot "") ==0) then "ptr" else ot
;;

(** the formatter that fmt- commands will use *)
let fmt = ref (std_formatter)
let pr_mem = ref true

(** primitive formatter comands *)
let fmt_string x = pp_print_string (!fmt) x
let fmt_bool x = pp_print_bool (!fmt) x
let fmt_int x = pp_print_int (!fmt) x
let fmt_float x = pp_print_float (!fmt) x
let fmt_char x = pp_print_char (!fmt) x
let fmt_space x = pp_print_space (!fmt) x
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

(* let pr_opt lst (f:'a -> ()) x:'a = *)
(*   if not(U.empty lst) then f a *)
(*   else (); *)

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
let op_and = " & "  
let op_or = " | "  
let op_not = "!"  
let op_star = " * "  
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
    | [] -> failwith "cannot be [] (pr_list_open_sep)"
    | [x] -> (f_elem x)
    | y::ys -> (f_elem y; f_sep(); helper ys) 
  in match xs with
    | [] -> f_empty()
    | xs -> f_open(); (helper xs); f_close() 


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

(*   (\* print op and a break after *\) *)
(* let pr_vbrk_after op = (fun () -> fmt_string (op); fmt_cut() ) *)

(* (\* print op and a break before *\) *)
(* let pr_vbrk_before op = (fun () -> fmt_cut(); fmt_string (op);  ) *)

(* (\* print op and a break before *\) *)
(* let pr_brk_before op = (fun () -> (\* fmt_cut() ;  *\)(fmt_string op)) *)

(* let pr_list_sep x = pr_list_open_sep (fun x -> x) (fun x -> x) x  *)

(* let pr_list x = pr_list_sep fmt_space x;; *)

(* let pr_list_comma x = pr_list_sep (fun () -> fmt_string ","; fmt_space()) x  *)

(* let pr_list_args op x = pr_list_open_sep  *)
(*   (fun () -> fmt_open 1; fmt_string op; fmt_string "(") *)
(*   (fun () -> fmt_string ")"; fmt_close();)  *)
(*   fmt_space x *)

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
  pr_args_gen (fun () -> fmt_string (open_str^close_str)) box_opt sep_opt op open_str close_str sep_str f xs

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

(* let pr_args open_str close_str sep_str f xs =  *)
(*   pr_list_open_sep  *)
(*     (fun () -> (\* fmt_open 1; *\) fmt_string open_str) *)
(*     (fun () -> fmt_string close_str; (\* fmt_close(); *\))  *)
(*     (pr_brk_after sep_str) f xs *)

(*  let pr_args_vbox open_str close_str sep_str f xs =  *)
(*   pr_list_open_sep  *)
(*     (fun () -> fmt_open_vbox 1; fmt_string open_str) *)
(*     (fun () -> fmt_string close_str; fmt_close();)  *)
(*     (pr_vbrk_after sep_str) f xs *)

(* let pr_op_args op open_str close_str sep_str f xs =  *)
(*   pr_list_open_sep  *)
(*     (fun () -> (\* fmt_open 1; *\) fmt_string op; fmt_string open_str) *)
(*     (fun () -> fmt_string close_str; (\* fmt_close(); *\))  *)
(*     (pr_brk_after sep_str) f xs *)

(** print a tuple with cut after separator*)
let pr_tuple op f xs = pr_args None (Some "A") op "(" ")" "," f xs

(** print an angle list with cut after separator*)  
let pr_angle op f xs = pr_args None (Some "A") op "<" ">" "," f xs

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


(* let pr_op_sep   *)
(*     (pr_sep: unit -> unit )  *)
(*     (isSimple: 'a -> bool) *)
(*     (pr_elem: 'a -> unit) *)
(*     (x:'a) (y:'a)  *)
(*     =  (pr_bracket isSimple pr_elem x); pr_sep();  *)
(*        (pr_bracket isSimple pr_elem y) *)


(* let pr_op op = pr_op_sep (pr_brk_after op) *)

(* (\* let pr_call  (isSimple:'a->bool) (pr_elem: 'a -> unit) (fn:string) (args:'a list)   *\) *)
(* (\*     = fmt_string fn; (pr_list_args pr_elem args)   *\) *)

(* (\* this op printing has no break *\) *)
(* let pr_op f = pr_op_sep (fun () -> fmt_string " ") f *)

(* let pr_op_no f = pr_op_sep (fun () -> fmt_string " ") (fun x -> true) f *)

(* (\* this op printing allows break *\) *)
(* let pr_op_brk f = pr_op_sep fmt_space f *)

(* (\* this op do not require bracket *\) *)
(* let pr_op_brk_no f = pr_op_sep fmt_space (fun x -> true) f *)

(* let precedence (op:string) : int = *)
(*   match op with *)
(*   | "&" -> 0 *)
(*   | _ -> -1 *)
 

(* let is_no_bracket (op:string) (trivial:'a->bool)  *)
(*     (split:'a -> (string * 'a * 'a) option) (elem:'a) : bool  =  *)
(*   if (trivial elem) then true *)
(*   else  *)
(*     match (split elem) with *)
(*       | None -> false *)
(*       | Some (op2,_,_) ->  *)
(*          if (precedence op2) > (precedence op) then true *)
(*          else false *)
 
let string_of_spec_var x = 
  match x with
    | P.SpecVar (t, id, p) -> id ^(*"."^(string_of_typ t) ^*)(match p with 
	    | Primed -> "'" 
	    | Unprimed -> "" )

let pr_spec_var x = fmt_string (string_of_spec_var x)

let pr_list_of_spec_var xs = pr_list_none pr_spec_var xs
  

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
  match e with
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
    

(** print a b_formula  to formatter *)
let rec pr_b_formula (e:P.b_formula) =
  let f_b e =  pr_bracket exp_wo_paren pr_formula_exp e in
  let f_b_no e =  pr_bracket (fun x -> true) pr_formula_exp e in
    match e with
      | P.BConst (b,l) -> fmt_bool b 
      | P.BVar (x, l) -> fmt_string (string_of_spec_var x)
      | P.Lt (e1, e2, l) -> f_b e1; fmt_string op_lt ; f_b e2
      | P.Lte (e1, e2, l) -> f_b e1; fmt_string op_lte ; f_b e2
      | P.Gt (e1, e2, l) -> f_b e1; fmt_string op_gt ; f_b e2
      | P.Gte (e1, e2, l) -> f_b e1; fmt_string op_gte ; f_b e2
      | P.Eq (e1, e2, l) -> f_b_no e1; fmt_string op_eq ; f_b_no e2
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
      | P.ListIn (e1, e2, l)			  ->  pr_op_adhoc (fun ()->pr_formula_exp e1) " <Lin> "  (fun ()-> pr_formula_exp e2)
      | P.ListNotIn (e1, e2, l)			->  pr_op_adhoc (fun ()->pr_formula_exp e1) " <Lnotin> "  (fun ()-> pr_formula_exp e2)
      | P.ListAllN (e1, e2, l)			->  pr_op_adhoc (fun ()->pr_formula_exp e1) " <allN> "  (fun ()-> pr_formula_exp e2)
      | P.ListPerm (e1, e2, l)			-> pr_op_adhoc (fun ()->pr_formula_exp e1) " <perm> "  (fun ()-> pr_formula_exp e2)
;;
  
let string_of_int_label (i,s) s2:string = (string_of_int i)^s2
let string_of_int_label_opt h s2:string = match h with | None-> s2 | Some s -> string_of_int_label s s2
let string_of_formula_label (i,s) s2:string = s2 (*("("^(string_of_int i)^", "^s^"):"^s2)*)
let string_of_formula_label_pr_br (i,s) s2:string = ("("^(string_of_int i)^", "^s^"):"^s2)
let string_of_formula_label_opt h s2:string = match h with | None-> s2 | Some s -> string_of_formula_label s s2
let string_of_control_path_id (i,s) s2:string = string_of_formula_label (i,s) s2
let string_of_control_path_id_opt h s2:string = string_of_formula_label_opt h s2


let pr_formula_label_br l = fmt_string (string_of_formula_label_pr_br l "")
let pr_formula_label l  = fmt_string (string_of_formula_label l "")
let pr_formula_label_list l  = fmt_string ("{"^(String.concat "," (List.map (fun (i,_)-> (string_of_int i)) l))^"}")
let pr_formula_label_opt l = fmt_string (string_of_formula_label_opt l "")


(** print a pure formula to formatter *)
let rec pr_pure_formula  (e:P.formula) = 
  let f_b e =  pr_bracket pure_formula_wo_paren pr_pure_formula e 
  in
  match e with 
    | P.BForm (bf,lbl) -> pr_formula_label_opt lbl; pr_b_formula bf
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
        fmt_string "!";f_b f 
    | P.Forall (x, f,lbl, l) -> 
        pr_formula_label_opt lbl; 
	    fmt_string "forall("; pr_spec_var x; fmt_string ":";
	    pr_pure_formula f; fmt_string ")"
    | P.Exists (x, f,lbl, l) -> 
        pr_formula_label_opt lbl; 
	    fmt_string "exists1("; pr_spec_var x; fmt_string ":";
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
    wrap_box ("B",1)
    ( fun m_gr -> fmt_string "(";pr_list_op_none "" 
      (fun c-> wrap_box ("H",1) (fun _ -> fmt_string "[";pr_list_of_spec_var c.MP.memo_group_fv ; fmt_string "]:") () ; 
               fmt_cut ();fmt_string "  ";
               wrap_box ("B",1) pr_memoise c.MP.memo_group_cons;
               fmt_cut ();fmt_string "  ";
               wrap_box ("B",1) pr_mem_slice c.MP.memo_group_slice;
               fmt_cut ();fmt_string "  alias set:";
               wrap_box ("B",1) fmt_string (Util.string_of_eq_set string_of_spec_var c.MP.memo_group_aset);
               fmt_cut();
      ) m_gr; fmt_string ")") m_gr
  (*else ()*)
  
let pr_memoise_group_standard print_P m_gr = 
  (*if !pr_mem then *)
    fmt_cut();
    wrap_box ("B",1)
    ( fun m_gr -> fmt_string "(";pr_list_op_none ""     
      (fun c-> 
        let f = MCP.fold_mem_lst (CP.mkTrue no_pos) false print_P (MCP.MemoF [c]) in
        fmt_string "[";
        wrap_box ("B",1) pr_pure_formula f;
        fmt_string "]";
        fmt_cut()
      ) m_gr; fmt_string ")") m_gr

let pr_memoise_group m_gr = match !Globals.memo_verbosity with
  | 0 -> pr_memoise_group_vb m_gr (*verbose*)
  | 1 -> pr_memoise_group_standard false  m_gr (*brief*)
  | _ -> pr_memoise_group_standard true  m_gr (*standard*)
      
let pr_remaining_branches s = match s with 
    | None -> ()
    | Some s -> 
     fmt_cut();
     wrap_box ("B",1) (fun s->fmt_string "@ rem br[" ; pr_formula_label_list s; fmt_string "]") s

let pr_prunning_conditions cnd pcond = match cnd with 
  | None -> ()
  | Some _ -> () (*
  fmt_cut ();
  fmt_string "@ prune_cond [" ; 
    wrap_box ("B",1) (fun pcond->
    List.iter (fun (c,c2)->
      fmt_cut ();
      fmt_string "( " ; pr_b_formula c;
      fmt_string" )->"; 
      pr_formula_label_list c2;) pcond;fmt_string "]") pcond  *)  

let rec pr_h_formula h = 
  let f_b e =  pr_bracket h_formula_wo_paren pr_h_formula e 
  in
    match h with
      | Star ({h_formula_star_h1 = h1; h_formula_star_h2 = h2; h_formula_star_pos = pos}) -> 
	  let arg1 = bin_op_to_list op_star_short h_formula_assoc_op h1 in
          let arg2 = bin_op_to_list op_star_short h_formula_assoc_op h2 in
          let args = arg1@arg2 in
            pr_list_op op_star f_b args
      | DataNode ({h_formula_data_node = sv;
                   h_formula_data_name = c;
                   h_formula_data_arguments = svs;
                   h_formula_data_pos = pos;
                   h_formula_data_remaining_branches = ann;
                   h_formula_data_label = pid})->
           pr_formula_label_opt pid;
              pr_spec_var sv; fmt_string "::";
          pr_angle c pr_spec_var svs ;
          (match ann with | None -> () | Some _ -> fmt_string "[]")
      | ViewNode ({h_formula_view_node = sv; 
                   h_formula_view_name = c; 
                   h_formula_view_arguments = svs; 
                   h_formula_view_origins = _;
                   h_formula_view_label = pid;
                   h_formula_view_remaining_branches = ann;
                   h_formula_view_pruning_conditions = pcond;
                   h_formula_view_pos =pos}) ->
         pr_formula_label_opt pid; 
         pr_spec_var sv; 
         fmt_string "::"; 
         pr_angle c pr_spec_var svs  ;
         pr_remaining_branches ann; 
         pr_prunning_conditions ann pcond
      | HTrue -> fmt_bool true
      | HFalse -> fmt_bool false


(** convert formula exp to a string via pr_formula_exp *)
let string_of_formula_exp (e:P.exp) : string =  poly_string_of_pr  pr_formula_exp e

let printer_of_formula_exp (crt_fmt: Format.formatter) (e:P.exp) : unit =
  poly_printer_of_pr crt_fmt pr_formula_exp e

let string_of_memoised_list l : string  = poly_string_of_pr pr_memoise_group l

(** convert b_formula to a string via pr_b_formula *)
let string_of_b_formula (e:P.b_formula) : string =  poly_string_of_pr  pr_b_formula e

let printer_of_b_formula (crt_fmt: Format.formatter) (e:P.b_formula) : unit =
  poly_printer_of_pr crt_fmt pr_b_formula e


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
   pr_seq_option " & " (fun (l, f) -> fmt_string ("\"" ^ l ^ "\" : "); 
   pr_pure_formula f) l

let  pr_memo_pure_formula f = pr_bracket pure_memoised_wo_paren pr_memoise_group f
   
let  pr_memo_pure_formula_branches (f, l) =
 (pr_bracket pure_memoised_wo_paren pr_memoise_group f); 
   pr_seq_option " & " (fun (l, f) -> fmt_string ("\"" ^ l ^ "\" : "); 
   pr_pure_formula f) l
  (* match l with *)
  (* | [] -> string_of_pure_formula f *)
  (* | _ -> string_of_pure_formula f ^ " & [" ^ (String.concat "; " (List.map (fun (l, f) -> "\"" ^ l ^ "\" : " ^ string_of_pure_formula f) l)) ^ "]" *)
;;

let pr_mix_formula f = match f with
  | MCP.MemoF f -> pr_memo_pure_formula f
  | MCP.OnePF f -> pr_pure_formula f


let pr_mix_formula_branches (f,l) = match f with
  | MCP.MemoF f -> pr_memo_pure_formula_branches (f,l)
  | MCP.OnePF f -> pr_pure_formula_branches (f,l)


let rec string_of_flow_formula f c = 
	"{"^f^",("^(string_of_int (fst c.formula_flow_interval))^","^(string_of_int (snd c.formula_flow_interval))^
	")="^(Util.get_closest c.formula_flow_interval)^","^(match c.formula_flow_link with | None -> "" | Some e -> e)^"}"


let rec pr_formula e =
  let f_b e =  pr_bracket formula_wo_paren pr_formula e in
  match e with
    | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) ->
	let arg1 = bin_op_to_list op_f_or_short formula_assoc_op f1 in
        let arg2 = bin_op_to_list op_f_or_short formula_assoc_op f2 in
        let args = arg1@arg2 in
	 pr_list_vbox_wrap "or " f_b args
    | Base ({formula_base_heap = h;
	  formula_base_pure = p;
	  formula_base_branches = b;
	  formula_base_type = t;
	  formula_base_flow = fl;
    formula_base_label = lbl;
	  formula_base_pos = pos}) ->
        (match lbl with | None -> () | Some l -> fmt_string ("{"^(string_of_int (fst l))^"}->"));
        pr_h_formula h ; pr_cut_after "&" ; pr_mix_formula_branches(p,b);
        pr_cut_after  "&" ;  fmt_string (string_of_flow_formula "FLOW" fl)
    | Exists ({formula_exists_qvars = svs;
	  formula_exists_heap = h;
	  formula_exists_pure = p;
	  formula_exists_branches = b;
	  formula_exists_type = t;
	  formula_exists_flow = fl;
    formula_exists_label = lbl;
	  formula_exists_pos = pos}) ->
        (match lbl with | None -> () | Some l -> fmt_string ("{"^(string_of_int (fst l))^"}->"));
        fmt_string "EXISTS("; pr_list_of_spec_var svs; fmt_string ": ";
        pr_h_formula h; pr_cut_after "&" ;
        pr_mix_formula_branches(p,b); pr_cut_after  "&" ; 
        fmt_string ((string_of_flow_formula "FLOW" fl) ^  ")") 



let string_of_formula (e:formula) : string =  poly_string_of_pr  pr_formula e

let printer_of_formula (fmt: Format.formatter) (e:formula) : unit
    = poly_printer_of_pr fmt pr_formula e

(*let pr_list_formula (e:list_formula) =  pr_seq "" pr_formula e*)    

let pr_list_formula (e:list_formula) = pr_list_op_none " " (wrap_box ("B",0) pr_formula) e

let string_of_list_formula (e:list_formula) : string =  poly_string_of_pr  pr_list_formula e

let printer_of_list_formula (fmt: Format.formatter) (e:list_formula) : unit
    = poly_printer_of_pr fmt pr_list_formula e

let string_of_pure_formula_branches (f, l) : string
    =  poly_string_of_pr  pr_pure_formula_branches (f, l)
    
let string_of_memo_pure_formula_branches (f, l) : string
    =  poly_string_of_pr  pr_memo_pure_formula_branches (f, l)
    
let string_of_memo_pure_formula (f:MP.memo_pure) : string = 
  poly_string_of_pr  pr_memo_pure_formula f

let string_of_mix_formula (f:MP.mix_formula) : string = 
  poly_string_of_pr pr_mix_formula f
  
let string_of_mix_formula_branches (f,l) : string = 
  poly_string_of_pr pr_mix_formula_branches (f,l)

  
let printer_of_pure_formula_branches (fmt: Format.formatter) (f, l) : unit =
  poly_printer_of_pr fmt pr_pure_formula_branches (f, l)

let pr_case_guard c = 
  fmt_string "{";
  pr_seq "\n" (fun (c1,c2)-> pr_b_formula c1 ;fmt_string "->"; pr_seq_nocut "," pr_formula_label c2) c;
  fmt_string "}"

let rec pr_struc_formula (e:struc_formula) =
    pr_list_op_none "|| " (wrap_box ("B",0) pr_ext_formula) e

and pr_ext_formula  (e:ext_formula) =
  match e with
    | ECase { 
        formula_case_exists =ee; formula_case_branches  =  case_list ; formula_case_pos = _} ->
        (* fmt_string "case exists"; *)
        (* pr_seq "" pr_spec_var ee; *)
        pr_args  (Some("V",1)) (Some "A") "case " "{" "}" ";"
          (fun (c1,c2) -> wrap_box ("B",0) (pr_op_adhoc (fun () -> pr_pure_formula c1) " -> " )
                   (fun () -> pr_struc_formula c2)) case_list
    | EBase { formula_ext_implicit_inst = ii; formula_ext_explicit_inst = ei; formula_ext_exists = ee; formula_ext_base = fb;
	      formula_ext_continuation = cont; formula_ext_pos = _ } ->
        fmt_open_vbox 2;
        wrap_box ("B",0) (fun fb ->
			    if not(U.empty(ee@ii@ei)) then
			      begin
				fmt_string "exists ";
				pr_seq "(E)" pr_spec_var ee;
				pr_seq "(I)" pr_spec_var ii;
				pr_seq "(ex)" pr_spec_var ei;
			      end;
			    pr_formula fb) fb;
        if not(U.empty(cont)) then
	  begin
	    fmt_cut();
	    wrap_box ("B",0) pr_struc_formula cont;
          end;
        fmt_close();
    | EAssume (x,b,(y1,y2))->
        wrap_box ("V",2)
          (fun b ->
	     fmt_string "EAssume ";
	     pr_formula_label (y1,y2);
	     if not(U.empty(x)) then pr_seq_nocut "ref " pr_spec_var x;
	     fmt_cut();
	     wrap_box ("B",0) pr_formula b) b
	| EVariance {
			formula_ext_measures = measures;
			formula_ext_escape_clauses = escape_clauses;
	  } ->
		
		let string_of_measures = List.fold_left (fun rs (expr, bound) -> match bound with
																			| None -> rs^(string_of_formula_exp expr)^" "
																			| Some bexpr -> rs^(string_of_formula_exp expr)^"@"^(string_of_formula_exp bexpr)^" ") "" measures in
		let string_of_escape_clauses =  List.fold_left (fun rs f -> rs^(poly_string_of_pr pr_pure_formula f)) "" escape_clauses in
		  fmt_string ("EVariance "^"[ "^string_of_measures^"]"^" ==> "^"[ "^string_of_escape_clauses^" ]" )
;;


let string_of_ext_formula (e:ext_formula) : string =  poly_string_of_pr  pr_ext_formula e

let printer_of_ext_formula (fmt: Format.formatter) (e:ext_formula) : unit =
  poly_printer_of_pr fmt pr_ext_formula e

let string_of_struc_formula (e:struc_formula) : string =  poly_string_of_pr  pr_struc_formula e

let printer_of_struc_formula (fmt: Format.formatter) (e:struc_formula) : unit =
  poly_printer_of_pr fmt pr_struc_formula e
      

let string_of_prior_steps pt =
  (String.concat "\n " (List.rev pt))


let pr_path_trace  pt =
  pr_seq "" (fun (c1,c3)-> fmt_string "("; (pr_op_adhoc (fun () -> pr_formula_label c1)  "," (fun () -> fmt_int c3)); fmt_string ")") pt  
	  
let string_of_path_trace  (pt : path_trace) = poly_string_of_pr  pr_path_trace pt
let printer_of_path_trace (fmt: Format.formatter) (pt : path_trace) =
  poly_printer_of_pr fmt pr_path_trace pt


let summary_list_path_trace l =  String.concat "; " (List.map  (fun (lbl,_) -> string_of_path_trace lbl) l)

let summary_partial_context (l1,l2) =  "("^string_of_int (List.length l1) ^", "^ string_of_int (List.length l2)^" "^(summary_list_path_trace l2)^")"

let summary_failesc_context (l1,l2,l3) =  
	"("^string_of_int (List.length l1) ^", "^ string_of_int (List.length l2) ^", "^ string_of_int (List.length l3) 
	^" "^(summary_list_path_trace l3)^")"

  
let summary_list_partial_context lc =  "["^(String.concat " " (List.map summary_partial_context lc))^"]"

let summary_list_failesc_context lc = "["^(String.concat " " (List.map summary_failesc_context lc))^"]"


  (* if String.length(hdr)>7 then *)
  (*   ( fmt_string hdr;  fmt_cut (); fmt_string "  "; wrap_box ("B",2) f  x) *)
  (* else  (wrap_box ("B",0) (fun x -> fmt_string hdr; f x)  x) *)


let pr_estate (es : entail_state) =
  fmt_open_vbox 0;
  pr_vwrap_nocut "es_formula: " pr_formula  es.es_formula; 
  pr_vwrap "es_pure: " pr_mix_formula_branches es.es_pure; 
  pr_vwrap "es_orig_conseq: " pr_struc_formula es.es_orig_conseq; 
  if (!Debug.devel_debug_print_orig_conseq == true) then pr_vwrap "es_orig_conseq: " pr_struc_formula es.es_orig_conseq  else ();
  pr_vwrap "es_heap: " pr_h_formula es.es_heap;
  pr_wrap_test "es_evars: " U.empty (pr_seq "" pr_spec_var) es.es_evars; 
  pr_wrap_test "es_ivars: "  U.empty (pr_seq "" pr_spec_var) es.es_ivars;
  pr_wrap_test "es_expl_vars: " U.empty (pr_seq "" pr_spec_var) es.es_expl_vars;
  pr_wrap_test "es_gen_expl_vars: " U.empty  (pr_seq "" pr_spec_var) es.es_gen_expl_vars;
  pr_wrap_test "es_gen_impl_vars: " U.empty  (pr_seq "" pr_spec_var) es.es_gen_impl_vars; 
  pr_wrap_test "es_success_pts: " U.empty (pr_seq "" (fun (c1,c2)-> fmt_string "(";(pr_op pr_formula_label c1 "," c2);fmt_string ")")) es.es_success_pts;
  pr_wrap_test "es_residue_pts: " U.empty (pr_seq "" pr_formula_label) es.es_residue_pts;
  pr_wrap_test "es_path_label: " U.empty pr_path_trace es.es_path_label;
  fmt_close ()



      
let string_of_estate (es : entail_state) : string =  poly_string_of_pr  pr_estate es
let printer_of_estate (fmt: Format.formatter) (es: entail_state) : unit =
  poly_printer_of_pr fmt pr_estate es
      
      

let pr_fail_estate (es:fail_context) =
  fmt_open_vbox 1; fmt_string "{";
  pr_wrap_test_nocut "fc_prior_steps: " U.empty (fun x -> fmt_string (string_of_prior_steps x)) es.fc_prior_steps;
  pr_vwrap "fc_message: "  fmt_string es.fc_message;
  pr_vwrap "fc_current_lhs: " pr_estate es.fc_current_lhs;
  pr_vwrap "fc_orig_conseq: " pr_struc_formula es.fc_orig_conseq;
  pr_wrap_test "fc_failure_pts: "U.empty (pr_seq "" pr_formula_label) es.fc_failure_pts;
  fmt_string "}"; 
  fmt_close ()
      
let string_of_fail_estate (es:fail_context) : string =  poly_string_of_pr  pr_fail_estate es
let printer_of_fail_estate (fmt: Format.formatter) (es: fail_context) : unit =
  poly_printer_of_pr fmt pr_fail_estate es
      

let ctx_assoc_op (e:context) : (string * context list) option = 
  match e with
    | OCtx (e1,e2) -> Some ("|",[e1;e2])
    | _ -> None

let rec pr_context (ctx: context) =
  let f_b e =  match e with
    | Ctx es ->  wrap_box ("B",1) pr_estate es
    | _ -> failwith "cannot be an OCtx"
  in match ctx with
    | Ctx es -> f_b ctx
    | OCtx (c1, c2) -> 
          let args = bin_op_to_list "|" ctx_assoc_op ctx in
          pr_list_op_vbox "CtxOR" f_b args
              

let string_of_context (ctx: context): string =  poly_string_of_pr  pr_context ctx
let printer_of_context (fmt: Format.formatter) (ctx: context) : unit =
  poly_printer_of_pr fmt pr_context ctx

let pr_context_list ctx =  pr_seq "" pr_context ctx    
let string_of_context_list ctx : string =  poly_string_of_pr  pr_context_list ctx
let printer_of_context_list (fmt: Format.formatter) (ctx: context list) : unit =
  poly_printer_of_pr fmt pr_context_list ctx  

let rec pr_fail_type (e:fail_type) =
  let f_b e =  pr_bracket ft_wo_paren pr_fail_type e in
  match e with
    | Trivial_Reason s -> fmt_string (" Trivial fail : "^s)
    | Basic_Reason br ->  pr_fail_estate br
    | Or_Reason _ -> 
          let args = bin_op_to_list op_or_short ft_assoc_op e in
          pr_list_vbox_wrap "FAIL_OR " f_b args
    | And_Reason _ -> 
          let args = bin_op_to_list op_and_short ft_assoc_op e in
          pr_list_vbox_wrap "FAIL_AND " f_b args

let string_of_fail_type (e:fail_type) : string =  poly_string_of_pr  pr_fail_type e

let printer_of_fail_type (fmt: Format.formatter) (e:fail_type) : unit =
  poly_printer_of_pr fmt pr_fail_type e



let pr_list_context (ctx:list_context) =
  match ctx with
    | FailCtx ft -> fmt_cut (); fmt_string "Fail Context: "; pr_fail_type ft; fmt_cut () 
    | SuccCtx sc -> fmt_cut (); fmt_string "Success Context: "; pr_context_list sc; fmt_cut ()

          
let string_of_list_context (ctx:list_context): string =  poly_string_of_pr pr_list_context ctx

let printer_of_list_context (fmt: Format.formatter) (ctx: list_context) : unit =
  poly_printer_of_pr fmt pr_list_context ctx 

let pr_esc_stack_lvl ((i,_),e) = 
  fmt_open_vbox 0;
  pr_vwrap_naive ("level"^(string_of_int i)^" :")
    (pr_seq_vbox "" (fun (lbl,fs)-> pr_vwrap_nocut "Label: " pr_path_trace lbl;
		       pr_vwrap "State:" pr_context fs)) e;
  fmt_close_box ()
           
let pr_esc_stack e = match e with
  | [] 
  | [((0,""),[])] -> ()
  | _ ->
    fmt_open_vbox 0;
    pr_vwrap_naive "Escaped States:"
    (pr_seq_vbox "" pr_esc_stack_lvl) e;
    fmt_close_box ()
  
let string_of_esc_stack e = poly_string_of_pr pr_esc_stack e

  
let pr_failesc_context ((l1,l2,l3): failesc_context) =
  fmt_open_vbox 0;
  pr_vwrap_naive_nocut "Failed States:"
    (pr_seq_vbox "" (fun (lbl,fs)-> pr_vwrap_nocut "Label: " pr_path_trace lbl;
		       pr_vwrap "State:" pr_fail_type fs)) l1;
  pr_esc_stack l2;
  pr_vwrap_naive "Successful States:"
    (pr_seq_vbox "" (fun (lbl,fs)-> pr_vwrap_nocut "Label: " pr_path_trace lbl;
		       pr_vwrap "State:" pr_context fs)) l3;
  fmt_close_box ()

let pr_partial_context ((l1,l2): partial_context) =
  fmt_open_vbox 0;
  pr_vwrap_naive_nocut "Failed States:"
    (pr_seq_vbox "" (fun (lbl,fs)-> pr_vwrap_nocut "Label: " pr_path_trace lbl;
		       pr_vwrap "State:" pr_fail_type fs)) l1;
  pr_vwrap_naive "Successful States:"
    (pr_seq_vbox "" (fun (lbl,fs)-> pr_vwrap_nocut "Label: " pr_path_trace lbl;
		       pr_vwrap "State:" pr_context fs)) l2;
  fmt_close_box ()


      
(* let pr_partial_context ((l1,l2): partial_context) = *)
(*   fmt_open_vbox 0; *)
(*   fmt_string "Failed States: "; *)
(*   pr_seq "" (fun (lbl,fs)-> fmt_cut (); fmt_string " Lbl : "; pr_path_trace lbl; fmt_cut (); *)
(* 	       fmt_string " State: "; pr_fail_type fs) l1; *)
(*   fmt_cut (); *)
(*   fmt_string "Succesfull States: "; *)
(*    pr_seq "" (fun (lbl,fs)-> fmt_cut (); fmt_string " Lbl : "; pr_path_trace lbl; fmt_cut (); *)
(* 	       fmt_string " State: "; pr_context fs) l2; *)
(*   fmt_close_box () *)
 

let string_of_partial_context (ctx:partial_context): string =  poly_string_of_pr pr_partial_context ctx

let printer_of_partial_context (fmt: Format.formatter) (ctx: partial_context) : unit =
  poly_printer_of_pr fmt pr_partial_context ctx 


let string_of_failesc_context (ctx:failesc_context): string =  poly_string_of_pr pr_failesc_context ctx

let printer_of_failesc_context (fmt: Format.formatter) (ctx: failesc_context) : unit =
  poly_printer_of_pr fmt pr_failesc_context ctx 
  
let pr_list_failesc_context (lc : list_failesc_context) =
   fmt_string ("List of Failesc Context: "^(summary_list_failesc_context lc));
   fmt_cut (); pr_list_none pr_failesc_context lc
 
	
let pr_list_partial_context (lc : list_partial_context) =
   fmt_string ("List of Partial Context: "^(summary_list_partial_context lc));
   fmt_cut (); pr_list_none pr_partial_context lc
    
let string_of_list_partial_context (lc: list_partial_context) =
    poly_string_of_pr pr_list_partial_context lc

let string_of_list_failesc_context (lc: list_failesc_context) =
    poly_string_of_pr pr_list_failesc_context lc
	
let printer_of_list_partial_context (fmt: Format.formatter) (ctx: list_partial_context) : unit =
  poly_printer_of_pr fmt pr_list_partial_context ctx 


let pr_list_list_partial_context (lc:list_partial_context list) =
fmt_string ("List List of Partial Context: " ^ string_of_int(List.length lc));
 pr_list_none pr_list_partial_context lc
  
    
let string_of_list_list_partial_context (lc:list_partial_context list) =
  poly_string_of_pr pr_list_list_partial_context lc

let printer_of_list_list_partial_context (fmt: Format.formatter) (ctx: list_partial_context list) : unit =
  poly_printer_of_pr fmt pr_list_list_partial_context ctx   


(* pretty printing for a view *)
let pr_view_decl v =
  pr_mem:=false;
  let f bc =
    match bc with
	  | None -> ()
      | Some (s1,(s3,s2)) -> 
            pr_vwrap "base case: "
	            (fun () -> pr_pure_formula s1;fmt_string "->"; pr_mix_formula_branches (s3, s2)) ()
  in
  fmt_open_vbox 1;
  wrap_box ("B",0) (fun ()-> pr_angle  ("view "^v.view_name) pr_spec_var v.view_vars; fmt_string "= ") ();
  fmt_cut (); wrap_box ("B",0) pr_struc_formula v.view_formula; 
  pr_vwrap  "inv: "  pr_mix_formula (fst v.view_user_inv);
  pr_vwrap  "unstructured formula: "  (pr_list_op_none "|| " (wrap_box ("B",0) (fun (c,_)->pr_formula c))) v.view_un_struc_formula;
  pr_vwrap  "xform: " pr_mix_formula (fst v.view_x_formula);
  (match v.view_raw_base_case with 
    | None -> ()
    | Some s -> pr_vwrap  "raw base case: " pr_formula s);  
  f v.view_base_case;
  pr_vwrap  "prune branches: " (fun c-> pr_seq "," pr_formula_label_br c) v.view_prune_branches;
  pr_vwrap  "prune conditions: " pr_case_guard v.view_prune_conditions;
  pr_vwrap  "prune invs: " (fun c-> pr_seq "," (fun (c1,c2)-> 
            let s = String.concat "," (List.map (fun d-> string_of_int_label d "") c1) in
            let d = String.concat ";" (List.map string_of_b_formula c2) in
            fmt_string ("{"^s^"} -> ["^d^"]")) c) v.view_prune_invariants;
  fmt_close_box ();
  pr_mem:=true

let pr_prune_invs inv_lst = 
  "prune invs: " ^ (String.concat "," (List.map 
          (fun c-> (fun (c1,c2)-> 
            let s = String.concat "," (List.map (fun d-> string_of_int_label d "") c1) in
            let d = String.concat ";" (List.map string_of_b_formula c2) in
            ("{"^s^"} -> ["^d^"]")) c) inv_lst))
  
let string_of_prune_invs inv_lst : string = pr_prune_invs inv_lst
  
  
let string_of_view_decl (v: Cast.view_decl): string =  poly_string_of_pr pr_view_decl v

let printer_of_view_decl (fmt: Format.formatter) (v: Cast.view_decl) : unit =
  poly_printer_of_pr fmt pr_view_decl v 
      

  
(* function to print a list of strings *) 
let rec string_of_ident_list l c = match l with 
  | [] -> ""
  | h::[] -> h 
  | h::t -> h ^ c ^ (string_of_ident_list t c)
;;

let string_of_pos p = " "^(string_of_int p.start_pos.Lexing.pos_lnum)^":"^
				(string_of_int (p.start_pos.Lexing.pos_cnum - p.start_pos.Lexing.pos_bol));;

let string_of_constraint_relation m = match m with
  | Cpure.Unknown -> " ?  "
  | Cpure.Subsumed -> " <  "
  | Cpure.Subsuming -> " >  "
  | Cpure.Equal -> " =  "
  | Cpure.Contradicting -> "!= "
  
  
(* pretty printing for a list of pure formulae *)
let rec string_of_formula_exp_list l = match l with 
  | [] -> ""
  | h::[] -> string_of_formula_exp h
  | h::t -> (string_of_formula_exp h) ^ ", " ^ (string_of_formula_exp_list t)
;;
 

(* pretty printing for a cformula *)                                                         (*NOT DONE*)

let string_of_flow_store l = (String.concat " " (List.map (fun h-> (h.formula_store_name^"= "^
						(let rr = h.formula_store_value.formula_flow_interval in
							(string_of_int (fst rr))^"-"^(string_of_int (snd rr)))^" ")) l))




let rec string_of_t_formula = function
(* commented on 09.06.08
 | TypeExact ({t_formula_sub_type_var = v;
				t_formula_sub_type_type = c}) -> 
	  (string_of_spec_var v) ^ " = " ^ c
  | TypeSub ({t_formula_sub_type_var = v;
			  t_formula_sub_type_type = c}) -> 
	  (string_of_spec_var v) ^ " <: " ^ c
  | TypeSuper ({t_formula_sub_type_var = v;
				t_formula_sub_type_type = c}) -> 
	  (string_of_spec_var v) ^ " > " ^ c*)
  | TypeAnd ({t_formula_and_f1 = f1;
			  t_formula_and_f2 = f2}) -> 
	  (string_of_t_formula f1) ^ " & " ^ (string_of_t_formula f2)
  | TypeTrue -> "TypeTrue"
  | TypeFalse -> "TypeFalse"


(* function to print a list of type F.formula * F.formula *)
let rec string_of_formulae_list l = match l with 
  | [] -> ""
  | (f1, f2)::[] -> "\nrequires " ^ (string_of_formula f1) ^ "\nensures " ^ (string_of_formula f2)  
  | (f1, f2)::t -> "\nrequires " ^ (string_of_formula f1) ^ "\nensures " ^ (string_of_formula f2) ^ (string_of_formulae_list t)
;;

(* pretty printing for a spec_var list *)
let rec string_of_spec_var_list l = match l with 
  | [] -> ""
  | h::[] -> string_of_spec_var h 
  | h::t -> (string_of_spec_var h) ^ "," ^ (string_of_spec_var_list t)
;;



(*
let rec string_of_spec = function
	| SCase {scase_branches= br;} ->
		 (List.fold_left (fun a (c1,c2)->a^"\n"^(string_of_pure_formula c1)^"-> "^
		( List.fold_left  (fun a c -> a ^"\n "^(string_of_spec c )) "" c2)) "case { " br)^"}\n"
	| SRequires 	{
			srequires_implicit_inst = ii;
			srequires_explicit_inst = ei;
			srequires_base = fb;
			srequires_continuation = cont;
			}	 ->
				let l2 = List.fold_left (fun a c -> a^ " " ^(string_of_spec_var c)) "" ei in
				let l1 = List.fold_left (fun a c -> a^ " " ^(string_of_spec_var c)) "" ii in
				let b = string_of_formula fb in				
				"requires ["^l1^"]["^l2^"]"^b^" "^((List.fold_left (fun a d -> a^"\n"^(string_of_spec d)) "{" cont)^"}")
	| SEnsure{ sensures_base = fb } -> ("ensures "^(string_of_formula fb))
;;


let string_of_specs d =  List.fold_left  (fun a c -> a ^" "^(string_of_spec c )) "" d 
;;*)


(* functions to decide if an expression needs parenthesis *)
(* let need_parenthesis e = match e with  *)
(*   | BConst _ | Bind _ | FConst _ | IConst _ | Unit _ | Var _ -> false  *)
(*   | _ -> true *)
(* ;; *)

let string_of_sharp st = match st with
	| Sharp_ct t -> string_of_flow_formula "" t
	| Sharp_v  f -> "flow_var "^f

(* pretty printing for expressions *)
let rec string_of_exp = function 
  | Label l-> "LABEL! "^( (string_of_int_label_opt (fst  l.exp_label_path_id) (","^((string_of_int (snd l.exp_label_path_id))^": "^(string_of_exp l.exp_label_exp)))))
  | Java ({exp_java_code = code}) -> code
  | CheckRef _ -> ""
  | Assert ({exp_assert_asserted_formula = f1o; exp_assert_assumed_formula = f2o; exp_assert_pos = l; exp_assert_path_id = pid}) -> 
      let s = 
	begin
	  let str1 = 
	    match f1o with
	      | None -> ""
	      | Some f1 -> "assert " ^(string_of_control_path_id pid (":"^(string_of_struc_formula f1))) in
	  let str2 =
	    match f2o with
	      | None -> ""
	      | Some f2 -> "assume " ^ (string_of_formula f2) in
	    str1 ^ " " ^ str2
	end in
	string_of_formula_label pid s 
  | Assign ({exp_assign_lhs = id; exp_assign_rhs = e; exp_assign_pos = l}) -> 
      id ^ " = " ^ (string_of_exp e)
  | BConst ({exp_bconst_val = b; exp_bconst_pos = l}) -> 
      string_of_bool b 
  | Bind ({exp_bind_type = _; 
	   exp_bind_bound_var = (_, id); 
	   exp_bind_fields = idl;
	   exp_bind_body = e;
	   exp_bind_path_id = pid;
	   exp_bind_pos = l}) -> 
      string_of_control_path_id_opt pid ("bind " ^ id ^ " to (" ^ (string_of_ident_list (snd (List.split idl)) ",") ^ ") in \n{" ^ (string_of_exp e) ^ "\n}")
  | Block ({exp_block_type = _;
	    exp_block_body = e;
	    exp_block_local_vars = _;
	    exp_block_pos = _}) -> "{\n" ^ (string_of_exp e) ^ "\n}"
  | ICall ({exp_icall_type = _;
	    exp_icall_receiver = r;
	    exp_icall_method_name = id;
	    exp_icall_arguments = idl;
	    exp_icall_path_id = pid;
	    exp_icall_pos = l;
		exp_icall_is_rec = is_rec}) -> 
      string_of_control_path_id_opt pid (r ^ "." ^ id ^ "(" ^ (string_of_ident_list idl ",") ^ ")" ^ (if (is_rec) then " rec" else ""))
  | Cast ({exp_cast_target_type = t;
	   exp_cast_body = body}) -> begin
      "(" ^ (string_of_typ t) ^ " )" ^ string_of_exp body
    end
 | Catch b->   
     let c = b.exp_catch_flow_type in
	"\n catch ("^ (string_of_int (fst c))^","^(string_of_int (snd c))^")="^(Util.get_closest c)^ 
	  (match b.exp_catch_flow_var with 
	     | Some c -> (" @"^c^" ")
	     | _ -> " ")^
	  (match b.exp_catch_var with 
	     | Some (a,b) -> ((string_of_typ a)^":"^b^" ")
	     | _ -> " ")^") \n\t"^(string_of_exp b.exp_catch_body)
  | Cond ({exp_cond_type = _;
	   exp_cond_condition = id;
	   exp_cond_then_arm = e1;
	   exp_cond_else_arm = e2;
	   exp_cond_path_id = pid;
	   exp_cond_pos = l}) -> 
      string_of_control_path_id_opt pid ("if (" ^ id ^ ") " ^(string_of_exp e1) ^ "\nelse " ^ (string_of_exp e2) ^ "\n" )
  | Debug ({exp_debug_flag = b; exp_debug_pos = l}) -> if b then "debug" else ""
  | Dprint _ -> "dprint"
  | FConst ({exp_fconst_val = f; exp_fconst_pos = l}) -> string_of_float f 
      (*| FieldRead (_, (v, _), (f, _), _) -> v ^ "." ^ f*)
      (*| FieldWrite ((v, _), (f, _), r, _) -> v ^ "." ^ f ^ " = " ^ r*)
  | IConst ({exp_iconst_val = i; exp_iconst_pos = l}) -> string_of_int i 
  | New ({exp_new_class_name = id;
	  exp_new_arguments = idl;
	  exp_new_pos = l}) -> 
      "new" ^ id ^ "(" ^ (string_of_ident_list (snd (List.split idl)) ",") ^ ")"
  | Null l -> "null"
  | Print (i, l)-> "print " ^ (string_of_int i) 
  | Sharp ({exp_sharp_flow_type = st;
	    exp_sharp_val = eo;
	    exp_sharp_path_id =pid;
	    exp_sharp_pos = l}) ->begin
      string_of_control_path_id_opt pid (
	match st with
	  | Sharp_ct f ->  if (Cformula.equal_flow_interval f.formula_flow_interval !ret_flow_int) then
	      (match eo with 
		 |Sharp_prog_var e -> "return " ^ (snd e)
		 | _ -> "return")
	    else  (match eo with 
		     | Sharp_prog_var e -> "throw " ^ (snd e)
		     | Sharp_finally e -> "throw " ^ e ^":"^(string_of_sharp st)
		     | _ -> "throw "^(string_of_sharp st))
	  | _ -> (match eo with 
		    | Sharp_prog_var e -> "throw " ^ (snd e)
		    | Sharp_finally e -> "throw " ^ e ^":" ^(string_of_sharp st)
		    | _ -> "throw "^(string_of_sharp st)))end 
  | SCall ({exp_scall_type = _;
	    exp_scall_method_name = id;
	    exp_scall_arguments = idl;
	    exp_scall_path_id = pid;
	    exp_scall_pos = l;
		exp_scall_is_rec = is_rec}) ->
      string_of_control_path_id_opt pid (id ^ "(" ^ (string_of_ident_list idl ",") ^ ")" ^ (if (is_rec) then " rec" else ""))
  | Seq ({exp_seq_type = _;
	  exp_seq_exp1 = e1;
	  exp_seq_exp2 = e2;
	  exp_seq_pos = l}) -> 
      (string_of_exp e1) ^ ";\n" ^ (string_of_exp e2)
  | This _ -> "this"
  | Time (b,s,_) -> ("Time "^(string_of_bool b)^" "^s)
  | Var ({exp_var_type = _;
	  exp_var_name = id;
	  exp_var_pos = l}) -> id 
  | VarDecl ({exp_var_decl_type = t;
	      exp_var_decl_name = id;
	      exp_var_decl_pos = _}) -> 
      (string_of_typ t) ^" "^ id (*^ (string_of_exp e1) ^ ";\n" ^ (string_of_exp e2)*)
  | Unit l -> ""
  | While ({exp_while_condition = id;
	    exp_while_body = e;
	    exp_while_spec = fl;
	    exp_while_path_id = pid;
	    exp_while_pos = l}) -> 
      string_of_control_path_id_opt pid ("while " ^ id ^ (string_of_struc_formula fl) ^ "\n{\n" ^ (string_of_exp e) ^ "\n}\n")
  | Unfold ({exp_unfold_var = sv}) -> "unfold " ^ (string_of_spec_var sv)
  | Try b -> string_of_control_path_id b.exp_try_path_id  "try \n"^(string_of_exp b.exp_try_body)^(string_of_exp b.exp_catch_clause )
;;


(* pretty printing for one data declaration*)
let string_of_decl d = match d with 
 | (t, id) -> (string_of_typ t) ^ " " ^ id 
;;           

(* function to print a list of typed_ident *) 
let rec string_of_decl_list l c = match l with 
  | [] -> ""
  | h::[] -> "  " ^ string_of_decl h 
  | h::t -> "  " ^ (string_of_decl h) ^ c ^ (string_of_decl_list t c)
;;

(* pretty printing for a data declaration *)
let string_of_data_decl d = "data " ^ d.data_name ^ " {\n" ^ (string_of_decl_list d.data_fields "\n") ^ "\n}"
;;

let string_of_coerc c lft = (string_of_formula c.coercion_head)^(if lft then "<=" else "=>")^(string_of_formula c.coercion_body) ;;

(* pretty printing for a procedure *)
let string_of_proc_decl p = 
  let locstr = (string_of_full_loc p.proc_loc)  
  in  (string_of_typ p.proc_return) ^ " " ^ p.proc_name ^ "(" ^ (string_of_decl_list p.proc_args ",") ^ ")\n" 
  ^ "static " ^ (string_of_struc_formula p.proc_static_specs) ^ "\n"
  ^ "dynamic " ^ (string_of_struc_formula p.proc_dynamic_specs) ^ "\n"
  ^ (if U.empty p.proc_by_name_params then "" 
	 else ("\nref " ^ (String.concat ", " (List.map string_of_spec_var p.proc_by_name_params)) ^ "\n"))
  ^ (match p.proc_body with 
       | Some e -> (string_of_exp e) ^ "\n\n"
	   | None -> "\n") ^ locstr
;; 

(* pretty printing for a list of data_decl *)
let rec string_of_data_decl_list l = match l with 
 | [] -> ""
 | h::[] -> (string_of_data_decl h) 
 | h::t -> (string_of_data_decl h) ^ "\n" ^ (string_of_data_decl_list t)
;;

(* pretty printing for a list of proc_decl *)
let rec string_of_proc_decl_list l = match l with 
 | [] -> ""
 | h::[] -> (string_of_proc_decl h) 
 | h::t -> (string_of_proc_decl h) ^ "\n" ^ (string_of_proc_decl_list t)
;;

(* pretty printing for a list of view_decl *)
let rec string_of_view_decl_list l = match l with 
 | [] -> ""
 | h::[] -> (string_of_view_decl h) 
 | h::t -> (string_of_view_decl h) ^ "\n" ^ (string_of_view_decl_list t)
;;

let rec string_of_coerc_decl_list l lft = match l with
  | [] -> ""
  | h::[] -> string_of_coerc h lft
  | h::t -> (string_of_coerc h lft) ^ "\n" ^ (string_of_coerc_decl_list t lft)
;;

(* pretty printing for a program written in core language *)
let string_of_program p = "\n" ^ (string_of_data_decl_list p.prog_data_decls) ^ "\n\n" ^ 
                          (string_of_view_decl_list p.prog_view_decls) ^ "\n\n" ^ 
                          (string_of_coerc_decl_list p.prog_left_coercions true)^"\n\n"^
                          (string_of_coerc_decl_list p.prog_right_coercions false)^"\n\n"^
                          (string_of_proc_decl_list p.prog_proc_decls) ^ "\n"
;;


(*
  Created 22-Feb-2006

  Pretty printing fo the AST for the core language
*)


let string_of_label_partial_context (fs,_) : string =
if (U.empty fs) then "" else string_of_path_trace(fst(List.hd fs))

let string_of_label_list_partial_context (cl:Cformula.list_partial_context) : string =
if (U.empty cl) then "" else string_of_label_partial_context (List.hd cl)
   
let string_of_label_failesc_context (fs,_,_) : string =
if (U.empty fs) then "" else string_of_path_trace(fst(List.hd fs))

(*let get_label_list_partial_context (cl:Cformula.list_partial_context) : string =
if (U.empty cl) then "" else get_label_partial_context (List.hd cl)
;;*)

let string_of_label_list_failesc_context (cl:Cformula.list_failesc_context) : string =
if (U.empty cl) then "" else string_of_label_failesc_context (List.hd cl)
;;

Mcpure.print_mp_f := string_of_memo_pure_formula ;;
Mcpure.print_mc_f := string_of_memoise_constraint ;;
Mcpure.print_sv_f := string_of_spec_var ;; 
Mcpure.print_bf_f := string_of_b_formula ;;
Mcpure.print_p_f_f := string_of_pure_formula ;;
Mcpure.print_exp_f := string_of_formula_exp;;
Mcpure.print_mix_f := string_of_mix_formula;;
(*Tpdispatcher.print_pure := string_of_pure_formula ;;*)
Cpure.print_b_formula := string_of_b_formula;;
Cpure.print_exp := string_of_formula_exp;;
Cformula.print_formula :=string_of_formula;;
Cformula.print_struc_formula :=string_of_struc_formula;;
Cvc3.print_pure := string_of_pure_formula;;
