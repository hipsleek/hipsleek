open Globals
open Format

module P = Cpure

let fmt = ref (std_formatter)

let fmt_string x = pp_print_string (!fmt) x
let fmt_space x = pp_print_space (!fmt) x
let fmt_break x = pp_print_break (!fmt) x

let fmt_open_box n = pp_open_box (!fmt) n
let fmt_close_box x = pp_close_box (!fmt) x

let fmt_open x = fmt_open_box x
let fmt_close x = fmt_close_box x

let pr_bracket_one pr_elem e =
 (fmt_string "("; pr_elem e; fmt_string ")")

let pr_bracket isSimple pr_elem e =
 if (isSimple e) then pr_elem e
 else (fmt_string "("; pr_elem e; fmt_string ")")

let pr_list_open_sep (pr_open:unit -> unit) 
    (pr_close:unit -> unit) 
    (pr_sep:unit->unit)
    (pr_elem:'a -> unit) (xs:'a list) : unit =
  let rec helper xs = match xs with
    | [x] -> (pr_elem x)
    | y::ys -> (pr_elem y; pr_sep(); helper ys) 
  in match xs with
    | [] -> ()
    | [x] -> (pr_elem x)
    | xs -> pr_open(); (helper xs); pr_close() 

let pr_brk_after op = (fun () -> fmt_string op; fmt_space ())
let pr_brk_before op = (fun () ->   fmt_space (); (fmt_string op))

let pr_list_sep x = pr_list_open_sep (fun x -> x) (fun x -> x) x 

let pr_list x = pr_list_sep fmt_space x;;

let pr_list_comma x = pr_list_sep (fun () -> fmt_string ","; fmt_space()) x 

let pr_list_args x = pr_list_open_sep 
  (fun () -> fmt_open 1; fmt_string "(")
  (fun () -> fmt_string ")"; fmt_close();) 
  fmt_space x

let pr_args open_str close_str sep_str = pr_list_open_sep 
  (fun () -> fmt_open 1; fmt_string open_str)
  (fun () -> fmt_string close_str; fmt_close();) 
  (pr_brk_after sep_str)

let pr_tuple x = pr_args "(" ")" "," x

let pr_set x = pr_args "{" "}" "," x

let pr_fn_args f op args = match args with
  | [x] -> f x
  | _ -> fmt_string op; (pr_tuple f args)

let pr_list_op op = pr_list_open_sep 
  (fun () -> fmt_open 1) fmt_close 
  (fun () -> fmt_string op; fmt_space ()) 

let pr_op_sep  
    (pr_sep: unit -> unit ) 
    (isSimple: 'a -> bool)
    (pr_elem: 'a -> unit)
    (x:'a) (y:'a) 
    =  (pr_bracket isSimple pr_elem x); pr_sep(); 
       (pr_bracket isSimple pr_elem y)


let pr_op op = pr_op_sep (pr_brk_after op)

let pr_call  (isSimple:'a->bool) (pr_elem: 'a -> unit) (fn:string) (args:'a list)  
    = fmt_string fn; (pr_list_args pr_elem args)  

(* this op printing has no break *)
let pr_op f = pr_op_sep (fun () -> fmt_string " ") f

let pr_op_no f = pr_op_sep (fun () -> fmt_string " ") (fun x -> true) f

(* this op printing allows break *)
let pr_op_brk f = pr_op_sep fmt_space f

(* this op do not require bracket *)
let pr_op_brk_no f = pr_op_sep fmt_space (fun x -> true) f






let precedence (op:string) : int =
  match op with
  | "&" -> 0
  | _ -> -1

 
let is_no_bracket (op:string) (trivial:'a->bool) 
    (split:'a -> (string * 'a * 'a) option) (elem:'a) : bool  = 
  if (trivial elem) then true
  else 
    match (split elem) with
      | None -> false
      | Some (op2,_,_) -> 
         if (precedence op2) > (precedence op) then true
         else false
 
let string_of_specvar x = match x with
  | P.SpecVar (t, id, p) -> id ^ (match p with 
	  | Primed    -> "'" 
	  | Unprimed  -> "" )

let exp_assoc_op (e:P.exp) = match e with
  | P.Add (e1,e2,_) -> Some ("+",e1,e2)
  | P.Mult (e1,e2,_) -> Some ("*",e1,e2)
  | P.Max (e1,e2,_) -> Some ("max",e1,e2)
  | P.Min (e1,e2,_) -> Some ("min",e1,e2)
  | _ -> None

let exp_need_paren (e:P.exp) = match e with
  | P.Null _ 
  | P.Var _ 
  | P.IConst _ 
  | P.FConst _ | P.Max _ | P.Min _
    -> true
  | _ -> false

let rec pr_formula_exp (e:P.exp) =
  let pr_bk e =  pr_bracket exp_need_paren pr_formula_exp e in
  match e with
  | P.Null l -> fmt_string "null"
  | P.Var (x, l) -> fmt_string (string_of_specvar x)
  | P.IConst (i, l) -> fmt_string (string_of_int i)
  | P.FConst (f, l) -> fmt_string (string_of_float f)
  | P.Add (e1, e2, l) -> 
      let args = bin_op_to_list "+" exp_assoc_op e in
      pr_list_op "+" pr_bk args
  | P.Mult (e1, e2, l) -> 
      let args = bin_op_to_list "*" exp_assoc_op e in
      pr_list_op "*" pr_bk  args
  | P.Max (e1, e2, l) -> 
      let args = bin_op_to_list "max" exp_assoc_op e in
      pr_fn_args pr_formula_exp "max"  args
  | P.Min (e1, e2, l) -> 
      let args = bin_op_to_list "min" exp_assoc_op e in
      pr_fn_args pr_formula_exp "min"  args
  | P.Bag (elist, l) 	-> pr_set pr_formula_exp elist
  | P.BagUnion (args, l) -> 
      let args = bin_op_to_list "union" exp_assoc_op e in
      pr_fn_args pr_formula_exp "union"  args
  | P.BagIntersect (args, l) -> 
      let args = bin_op_to_list "intersect" exp_assoc_op e in
      pr_fn_args pr_formula_exp "intersect"  args
  | P.Subtract (e1, e2, l) ->
      pr_bk e1; pr_brk_after "-"; pr_bk e2
  | P.Div (e1, e2, l) ->
      pr_bk e1; pr_brk_after "/"; pr_bk e2
  | P.BagDiff (e1, e2, l)     -> pr_formula_exp e1; pr_brk_after "-"; pr_formula_exp e2

let string_of_formula_exp_new (e:P.exp) =
  let old_fmt = !fmt in
  begin
    fmt := str_formatter;
    pr_formula_exp e;
    (let s = flush_str_formatter in
    fmt := old_fmt; s)
  end    
  


