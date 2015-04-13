#include "xdebug.cppo"
open VarGen
open Globals
open Format

module P = Cpure

(* the formatter that fmt_ commands will use *)
let fmt = ref (std_formatter)

let fmt_string x = pp_print_string (!fmt) x
let fmt_space x = pp_print_space (!fmt) x
let fmt_break x = pp_print_break (!fmt) x
let fmt_cut x = pp_print_cut (!fmt) x

let fmt_open_box n = pp_open_box (!fmt) n
let fmt_close_box x = pp_close_box (!fmt) x

let fmt_open x = fmt_open_box x
let fmt_close x = fmt_close_box x

(* shorter op code used internally *)
let op_add_short = "+" 
let op_sub_short = "-" 
let op_mult_short = "*" 
let op_div_short = "/" 
let op_max_short = "mx" 
let op_min_short = "mi" 
let op_union_short = "U" 
let op_intersect_short = "I" 
let op_diff_short = "I" 

(* op code that will be printed *)
let op_add = "+" 
let op_sub = "-" 
let op_mult = "*" 
let op_div = "/" 
let op_max = "max" 
let op_min = "min" 
let op_union = "union" 
let op_intersect = "intersect" 
let op_diff = "-" 


(* this command will add a bracket around e if
   is simple yields false *)
let pr_bracket (isSimple:'a -> bool) (pr_elem:'a -> unit) (e:'a) : unit =
 if (isSimple e) then pr_elem e
 else (fmt_string "("; pr_elem e; fmt_string ")")

(* this command invokes
    f_open ; f_elem x1; f_sep .. f_sep; f_elem xn; f_close
*)
let pr_list_open_sep (f_open:unit -> unit)
    (f_close:unit -> unit)
    (f_sep:unit->unit)
    (f_elem:'a -> unit) (xs:'a list) : unit =
  let rec helper xs = match xs with
    | [x] -> (f_elem x)
    | y::ys -> (f_elem y; f_sep(); helper ys)
  in match xs with
    | [] -> f_open();f_close()
    | xs -> f_open(); (helper xs); f_close()

(* print op and a break after *)
let pr_brk_after op = (fun () -> fmt_string (op); fmt_cut() )

(* print op and a break before *)
let pr_brk_before op = (fun () -> fmt_cut() ; (fmt_string op))

(* let pr_list_sep x = pr_list_open_sep (fun x -> x) (fun x -> x) x  *)

(* let pr_list x = pr_list_sep fmt_space x;; *)

(* let pr_list_comma x = pr_list_sep (fun () -> fmt_string ","; fmt_space()) x  *)

(* let pr_list_args op x = pr_list_open_sep  *)
(*   (fun () -> fmt_open 1; fmt_string op; fmt_string "(") *)
(*   (fun () -> fmt_string ")"; fmt_close();)  *)
(*   fmt_space x *)


let pr_args open_str close_str sep_str f xs = pr_list_open_sep 
  (fun () -> fmt_open 1; fmt_string open_str)
  (fun () -> fmt_string close_str; fmt_close();) 
  (pr_brk_after sep_str) f xs

let pr_op_args op open_str close_str sep_str f xs = pr_list_open_sep 
  (fun () -> fmt_open 1; fmt_string op; fmt_string open_str)
  (fun () -> fmt_string close_str; fmt_close();) 
  (pr_brk_after sep_str) f xs

let pr_tuple op f xs = pr_op_args op "(" ")" "," f xs

let pr_set f xs = pr_args "{" "}" "," f xs

(* print op(x1..xn) but argument alone if n=1 *)
let pr_fn_args op f xs = match xs with
  | [x] -> f x
  | _ -> (pr_tuple op f xs)

(* print in infix form : x1 op .. op xn *)
let pr_list_op op f xs = pr_list_open_sep 
  (fun () -> fmt_open 1) fmt_close 
  (pr_brk_after op) f xs

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
 
let string_of_specvar x = match x with
  | P.SpecVar (t, id, p) -> id ^ (match p with 
	  | Primed    -> "'" 
	  | Unprimed  -> "" )

(* check if top operator of e is associative and 
   return its list of arguments if so *)
let exp_assoc_op (e:P.exp) : (string * P.exp list) option = match e with
  | P.Add (e1,e2,_) -> Some (op_add_short,[e1;e2])
  | P.Mult (e1,e2,_) -> Some (op_mult_short,[e1;e2])
  | P.Max (e1,e2,_) -> Some (op_max_short,[e1;e2])
  | P.Min (e1,e2,_) -> Some (op_min_short,[e1;e2])
  | P.BagUnion (es,_) -> Some (op_union_short,es)
  | P.BagIntersect (es,_) -> Some (op_intersect_short,es)
  | _ -> None

(* check if exp can be without a parenthesis,
     e.g. trivial expr and prefix form
*)
let exp_wo_paren (e:P.exp) = match e with
  | P.Null _ 
  | P.Var _ 
  | P.IConst _ 
  | P.FConst _ | P.Max _ | P.Min _ | P.BagUnion _ | P.BagIntersect _ 
    -> true
  | _ -> false

(* print a formula exp to formatter *)
let rec pr_formula_exp (e:P.exp) =
  let pr_opt_bracket e =  pr_bracket exp_wo_paren pr_formula_exp e in
  match e with
  | P.Null l -> fmt_string "null"
  | P.Var (x, l) -> fmt_string (string_of_specvar x)
  | P.IConst (i, l) -> fmt_string (string_of_int i)
  | P.FConst (f, l) -> fmt_string (string_of_float f)
  | P.Add (e1, e2, l) -> 
      let args = bin_op_to_list op_add_short exp_assoc_op e in
      pr_list_op op_add pr_opt_bracket args
  | P.Mult (e1, e2, l) -> 
      let args = bin_op_to_list op_mult_short exp_assoc_op e in
      pr_list_op op_mult pr_opt_bracket  args
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
      pr_opt_bracket e1; pr_brk_after op_sub (); pr_opt_bracket e2
  | P.Div (e1, e2, l) ->
      pr_opt_bracket e1; pr_brk_after op_div (); pr_opt_bracket e2
  | P.BagDiff (e1, e2, l)     -> pr_formula_exp e1; pr_brk_after op_diff (); pr_formula_exp e2

(* convert formula exp to a string via pr_formula_exp *)
let string_of_formula_exp (e:P.exp) =
  let old_fmt = !fmt in
  begin
    fmt := str_formatter;
    pr_formula_exp e;
    (let s = flush_str_formatter()in
    fmt := old_fmt; s)
  end    
  


