open Format

let fmt = ref (std_formatter)

let fmt_string = pp_print_string (!fmt)
let fmt_space = pp_print_space (!fmt)
let fmt_break = pp_print_break (!fmt)

let fmt_open_box n = pp_open_box (!fmt) n
let fmt_close_box = pp_close_box (!fmt)

let fmt_open = fmt_open_box
let fmt_close = fmt_close_box


let pr_bracket_one pr_elem e =
 (fmt_string "("; pr_elem e; fmt_string ")")

let pr_bracket isSimple pr_elem e =
 if (isSimple e) then pr_elem e
 else (fmt_string "("; pr_elem e; fmt_string ")")

let pr_list_open_sep (pr_open:unit -> unit) 
    (pr_close:unit -> unit) 
    (pr_sep:unit->unit)
    (isSimple: 'a -> bool) (pr_elem:'a -> unit) (xs:'a list) : unit =
  let rec helper xs = match xs with
    | [x] -> (pr_elem x)
    | y::ys -> begin
        pr_bracket isSimple pr_elem y;
        pr_sep(); helper ys
      end
  in 
  match xs with
    | [] -> ()
    | [x] -> (pr_elem x)
b    | xs -> pr_open(); (helper xs); pr_close() 

let pr_list_sep x = pr_list_open_sep (fun x -> x) (fun x -> x) x 

let pr_list x = pr_list_sep fmt_space x;;

let pr_list_comma f = pr_list_sep (fun () -> fmt_string ","; fmt_space()) 
  (fun x -> true) f ;;

let pr_list_args f = pr_list_open_sep 
  (fun () -> fmt_open 1; fmt_string "(")
  (fun () -> fmt_string ")"; fmt_close();) 
  fmt_space f

let pr_list_op f = pr_list_open_sep 
  (fun () -> fmt_open 1) fmt_close 
  (fmt () -> fmt_string op; fmt_space) 

let pr_op_sep  
    (pr_sep: unit -> unit ) 
    (isSimple: 'a -> bool)
    (pr_elem: 'a -> unit)
    (x:'a) (op:string) (y:'a) 
    =  (pr_bracket isSimple pr_elem x); pr_sep(); fmt_string op; pr_sep(); 
       (pr_bracket isSimple pr_elem y)
;;

let pr_call  (isSimple:'a->bool) (pr_elem: 'a -> unit) (fn:string) (args:'a list)  
    = fmt_string fn; (pr_list_args isSimple pr_elem args)  
;;


(* this op printing has no break *)
let pr_op f = pr_op_sep (fun () -> fmt_string " ") f

let pr_op_no f = pr_op_sep (fun () -> fmt_string " ") (fun x -> true) f

(* this op printing allows break *)
let pr_op_brk f = pr_op_sep fmt_space f

(* this op do not require bracket *)
let pr_op_brk_no f = pr_op_sep fmt_space (fun x -> true) f


let pr_and isS pr x y = pr_op_brk isS pr x "&&" y

let pr_or isS pr x y = pr_op_brk isS pr x "||" y

let pr_eq pr x y = pr_op_brk_no pr x "=" y
let pr_gt pr x y = pr_op_brk_no pr x ">" y
let pr_geq pr x y = pr_op_brk_no pr x ">=" y
let pr_lt pr x y = pr_op_brk_no pr x "<" y
let pr_leq pr x y = pr_op_brk_no pr x "<=" y
let pr_neq pr x y = pr_op_brk_no pr x "!=" y

let pr_not isS pr xs = pr_call isS pr "not" xs

let pr_plus isS pr x y = pr_op isS 
pr x "+" y

let pr_minus isS pr x y = pr_op isS pr x "-" y

(* convert a tree-like binary object into a list of objects *)
let bin_op_to_list (op:string)
  (fn : 'a -> (string * 'a * 'a) option) 
  (t:'a) : string * ('a list) =
  let rec helper t =
    match (fn t) with
      | None -> op,[t]
      | Some (op2, a1, a2) -> 
          if (op=op2) then 
            let (_,r1)=(helper a1) in
            let (_,r2)=(helper a2) in
            op,(r1@r1)
          else op,[t]
  in (helper t)

let bin_to_list (fn : 'a -> (string * 'a * 'a) option) 
  (t:'a) : string * ('a list) =
  match (fn t) with
    | None -> "", [t]
    | Some (op, a1, a2) -> bin_op_to_list op fn t




(*

should we make this more general by using formatter?
can we avoid a ref type?



e1+e2+e3

e1 & e2 & e3 
e1 | e2 | e3

a+b+c=a*2+3+d 
e1<e2


*)

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
         else falccse
 
  


