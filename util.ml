(** Utility module with miscellaneous functions,
    including string functions and operating system functions.

  TODO: Sort functions by category, clean up.
 *)

exception Bad_string
exception Bail

let rec restart f arg =
  try f arg with Unix.Unix_error(Unix.EINTR,_,_) -> print_string"#!Unix_error#";(restart f arg)

type 'a tag_elem = ('a * (int list))

type 'a tag_list = ('a tag_elem) list

type ('a,'b) stackable =  ('a * (('b list) list))

type ('a,'b) list_of_stackable =  (('a,'b) stackable) list

let fnone (c:'a):'a option = None

let empty l = match l with [] -> true | _ -> false

(* this imp_list is not pop-pable *)

type 'a ilist = ('a list) ref

let new_ilist () : 'a ilist 
 = ref []

let add_ilist (x:'a list) (imp:'a ilist) : 'a ilist
= imp := x@(!imp) ; imp

let init_level ((i,stk):('a,'b) stackable) : ('a,'b) stackable
  = (i,[]::stk)

let pushf_add_level (f:'a -> 'a * ('b list))  ((i,stk):('a,'b) stackable) : ('a,'b) stackable
  = match stk with
    | [] -> Error.report_error {Error.error_loc = Globals.no_pos; Error.error_text = ("pushf_add_level on empty stack")}
    | lvl::stk -> let (new_i,v)=f i 
                 in (new_i,(v@lvl)::stk)

let add_level (lst:'b list)  ((i,stk):('a,'b) stackable) : ('a,'b) stackable
  = match stk with
    | [] -> Error.report_error {Error.error_loc = Globals.no_pos; Error.error_text = ("pushf_add_level on empty stack")}
    | lvl::stk -> (i,(lst@lvl)::stk)

let close_level ((i,stk):('a,'b) stackable) : ('a,'b) stackable
  = match stk with
    | lvl::(lvl2::stk) -> (i, (lvl@lvl2)::stk)
    | _ -> Error.report_error {Error.error_loc = Globals.no_pos; Error.error_text = ("close level requires at least two levels")}

let collapsef_stack  (f:'a -> ('b list) -> 'a)  ((i,stk):('a,'b) stackable) : 'a
  = f i (List.concat stk)

let popf_level (f:'a -> ('b list) -> ('a * ('b list))) ((i,stk):('a,'b) stackable) : ('a,'b) stackable
  = match stk with
    | lvl::stk -> let (newi,lst)=(f i lvl) in
      if (empty lst) then (newi, stk)
      else (add_level lst (newi,stk))
    | _ -> Error.report_error {Error.error_loc = Globals.no_pos; Error.error_text = ("popf_level on empty stack")}

let init_level_list (xs : ('a,'b) list_of_stackable) : ('a,'b) list_of_stackable
  = List.map (init_level) xs

let pushf_add_level_list (f:'a -> 'a * ('b list))  (xs : ('a,'b) list_of_stackable) : ('a,'b) list_of_stackable
  = List.map (pushf_add_level f) xs


let collapsef_stack_list (f:'a ->'b list -> 'a) (xs : ('a,'b) list_of_stackable) : 'a list
  = List.map (collapsef_stack f) xs

let close_level_list  (xs : ('a,'b) list_of_stackable) : ('a,'b) list_of_stackable
  = List.map (close_level) xs


let popf_level_list  (f:'a -> ('b list) -> ('a * ('b list))) (xs : ('a,'b) list_of_stackable) : ('a,'b) list_of_stackable
  = List.map (popf_level f) xs

(*
let pushf (f:'a -> 'a * 'b)  ((i,stk):('a,'b) stackable) : ('a,'b) stackable
  = let (new_i,v)=f i 
    in (new_i,[v]::stk)

let popf (f:'a -> 'b -> 'a) ((i,stk):('a,'b) stackable) : ('a,'b) stackable
  = match stk with
    | [v]::stk -> (f i v, stk)
    | _ -> Error.report_error {Error.error_loc = Globals.no_pos; Error.error_text = ("popf on empty stack")}

let pushf_list (f:'a -> 'a * 'b) (xs : ('a,'b) list_of_stackable) : ('a,'b) list_of_stackable
  = List.map (pushf f) xs

let popf_list (f:'a -> 'b -> 'a)  (xs : ('a,'b) list_of_stackable) : ('a,'b) list_of_stackable
  = List.map (popf f) xs
*)

let push_tag (xs : 'a tag_list) : ('a tag_list) =
  let rec helper xs (n:int) =
    match xs with
      | [] ->  []
      | (x,t) :: xs -> (x,(n::t))::(helper xs (n+1))
  in (helper xs 1)

let check_sorted_tag (xs: 'a tag_list) : bool =
  let rec helper xs no =
    match xs with
      | [] -> true
      | ((x,[])::xs1) -> Error.report_error {Error.error_loc = Globals.no_pos; Error.error_text = ("tag missing during ehc_sorted_tag")}
      | ((x,n::t)::xs1) -> 
        if (n<no) then false
        else if (n==no) then helper xs1 no
        else helper xs1 n
  in helper xs 1
 

(* if check_sorted_tag fail, will need to sort the tag before grouping *)
let group_tag (xs: 'a tag_list) (acc:'a tag_list) : ('a tag_list * int) list =
  let rec helper xs acc no =
    match xs with
      | [] -> if (empty acc) then [] else [(List.rev acc,no)]
      | ((x,[])::xs1) -> Error.report_error {Error.error_loc = Globals.no_pos; Error.error_text = ("cannot happen!")}
      | ((x,n::t)::xs1) -> 
        if (n==no) then helper xs1 ((x,t)::acc) no
        else 
          let rs=helper xs [] (no+1) in
          if (empty acc) then rs
          else (List.rev acc,no)::rs
  in let r=check_sorted_tag xs in
     if r then helper xs acc 1 
     else Error.report_error {Error.error_loc = Globals.no_pos; Error.error_text = ("need to sort group_tag!")}

let zip_tag (f: 'a -> 'b -> 'c) (xs: ('a * int) list) (ys:('b * int) list) : ('c list) =
  let rec helper xs ys =
    match xs with
      | [] -> []
      | ((x,n1)::xs1) -> 
            match ys with
              | [] -> []
              | ((y,n2)::ys1) -> 
                    if (n1==n2) then (f x y)::helper xs ys1
                    else if (n1<n2) then helper xs1 ys
                    else helper xs ys1
  in helper xs ys


(* Qualify helper file name *)
(* if you want to install the executable in one directory (e.g. /usr/bin),
 * but put helper files in another (/usr/share/module-language),
   here's what you need to change! *)

let qualify_helper_fn n =
  let d =  Filename.dirname Sys.executable_name ^ "/" in
  Sys.getcwd() ^ "/" ^ d ^ n


let lib_name n =
  try (let d = Filename.dirname Sys.executable_name ^ "/../lib/" in
	 Sys.getcwd() ^ "/" ^ d ^ n)
  with Sys_error _ -> n

let tmp_name n =
  try (let d = Filename.dirname Sys.executable_name ^ "/../tmp/" in    
	 Sys.getcwd() ^ "/" ^ d ^ n)
  with Sys_error _ -> n

(** filename handling; returns the inverse of Filename.chop_extension *)
let extension n =
  let d = String.rindex n '.' in
  String.sub n d (String.length n - d)

let get_path s = 
  if String.contains s '/' then
    let i = String.rindex s '/' in
    String.sub s 0 (i+1)
  else ""

(* List-handling stuff *)
let remove_elem e l = List.filter (fun x -> x != e) l

let rec remove_dups n = 
  match n with
    [] -> []
  | q::qs -> if (List.mem q qs) then remove_dups qs else q::(remove_dups qs)

let mem f x l = List.exists (f x) l
  
  (* from cpure
and mem (sv : spec_var) (svs : spec_var list) : bool =
  List.exists (fun v -> eq_spec_var sv v) svs

and disjoint (svs1 : spec_var list) (svs2 : spec_var list) =
  List.for_all (fun sv -> not (mem sv svs2)) svs1

and subset (svs1 : spec_var list) (svs2 : spec_var list) =
  List.for_all (fun sv -> mem sv svs2) svs1

and difference (svs1 : spec_var list) (svs2 : spec_var list) =
  List.filter (fun sv -> not (mem sv svs2)) svs1

and intersect (svs1 : spec_var list) (svs2 : spec_var list) =
  List.filter (fun sv -> mem sv svs2) svs1
*)
  
  
  
let rec remove_dups_f n f= 
  match n with
    [] -> []
  | q::qs -> if (List.exists (fun c-> f q c) qs) then remove_dups_f qs f else q::(remove_dups_f qs f)
  
let rec find_dups n = 
  match n with
    [] -> []
  | q::qs -> if (List.mem q qs) then q::(find_dups qs) else find_dups qs

let rec find_dups_f f n = 
  match n with
    [] -> []
  | q::qs -> if (List.exists (f q) qs) then q::(find_dups_f f qs) else find_dups_f f qs

  
let rec find_one_dup (eqf : 'a -> 'a -> bool) (xs : 'a list) =
  match xs with
	| [] -> []
	| x::rest -> if List.exists (eqf x) rest then [x] else find_one_dup eqf rest

let subset l1 l2 = 
  List.for_all (fun x -> (List.mem x l2)) l1

let disjoint l1 l2 = 
  List.for_all (fun x -> not (List.mem x l2)) l1

let mem_eq eq x ls =
  List.exists (fun e -> eq x e) ls

let overlap_eq eq l1 l2 = 
  List.exists (fun x -> (mem_eq eq x l2)) l1

let overlap eq l1 l2 = 
 List.exists (fun x -> (List.mem x l2)) l1
 
let intersect l1 l2 =
  List.filter (fun x -> List.mem x l2) l1

let intersect_fct f l1 l2 =
  List.filter (fun x -> List.exists (f x) l2) l1  
  
let difference l1 l2 =
  List.filter (fun x -> not (List.mem x l2)) l1

let difference_f f l1 l2 =
  List.filter (fun x -> not (List.exists (f x) l2)) l1
  
let list_equal l1 l2 = 
  let l = (List.length (intersect l1 l2)) in
  ((List.length l1) =  l) && (l = (List.length l2))
  
let difference_fct f l1 l2 =
  List.filter (fun x -> not (List.exists (f x) l2)) l1
  
let spacify i = 
  let s' z = List.fold_left (fun x y -> x ^ i ^ y) "" z in
  function [] -> ""
  | [x] -> x
  | x::xs -> x ^ (s' xs)

let find_index (f : 'a -> bool) (xs0 : 'a list) : (int * 'a) = 
  let rec helper xs n = match xs with
	| e :: rest -> 
		if f e then (n, e)
		else helper rest (n + 1)
	| _ -> raise Not_found
  in
	helper xs0 0

let rec list_last l = match l with
	| h::[] -> h
	| _::t -> (list_last t)
	| [] -> failwith "Util.list_last: empty list"
	
(** Split the list of length k>=1 into a pair consisting of
   the list of first k-1 elements and the last element. *)
let rec firsts_last xs = match xs with
| [] -> failwith "Util.first_lasts: empty list"
| [x] -> ([],x)
| x::xs1 ->
    let (fs,l) = firsts_last xs1 in
    (x::fs,l)

let rec take n l  = if n<=0 then []
  else match l with
    | h::t -> h::(take (n-1) t)
    | [] -> []
    
let rec drop n l  = if n<=0 then l
  else match l with
    | h::t -> (drop (n-1) t)
    | [] -> []

let force_backtrace () : string =
  try raise Exit 
  with e -> Printexc.record_backtrace true;("xxx"^Printexc.get_backtrace ())

let ho_debug_1_opt (s:string) (pr_i:'a->string) (pr_o:'z->string) (test:'z -> bool) (f:'a -> 'z) (e:'a) : 'z =
  let r = try
    f e 
  with ex -> 
      let _ = print_string (s^" inp :"^(pr_i e)^"\n") in
      let _ = print_string (s^" Exception"^(Printexc.to_string ex)^"Occurred!\n") in
      raise ex in
  if not(test r) then r else
  let _ = print_string (s^" inp :"^(pr_i e)^"\n") in
  let _ = print_string (s^" out :"^(pr_o r)^"\n") in
  (* let _ = print_string (s^" backtrace:"^(force_backtrace ())^"\n") in *)
  r

let ho_debug_1 (s:string) (pr_i:'a->string) (pr_o:'z->string) (f:'a -> 'z) (e:'a) : 'z =
  ho_debug_1_opt s pr_i pr_o (fun _ -> true) f e

    
let string_of_option (f:'a->string) (e:'a option) : string = 
  match e with
    | Some x -> f x
    | None -> "None" 

let ho_debug_1_option (s:string) (pr_i:'a->string) (pr_o:'z->string) (f:'a -> 'z option) (e:'a) : 'z option =
  ho_debug_1 s pr_i (string_of_option pr_o) f e 

let string_of_list (f:'a->string) (ls:'a list) : string = 
  ("["^(String.concat "," (List.map f ls))^"]")

let ho_debug_1_list (s:string) (pr_i:'a->string) (pr_o:'z->string) (f:'a -> 'z list) (e:'a) : 'z list =
  ho_debug_1 s pr_i (string_of_list pr_o) f e 

let ho_debug_2_opt (s:string) (pr1:'a->string) (pr2:'b->string) (pr_o:'z->string) (test:'z -> bool) (f:'a -> 'b -> 'z) (e1:'a) (e2:'b) : 'z =
  let r = try
    f e1 e2 
  with ex -> 
      let _ = print_string (s^" inp1 :"^(pr1 e1)^"\n") in
      let _ = print_string (s^" inp2 :"^(pr2 e2)^"\n") in
      let _ = print_string (s^" Exception"^(Printexc.to_string ex)^"Occurred!\n") in
      raise ex in
  if not(test r) then r else
  let _ = print_string (s^" inp1 :"^(pr1 e1)^"\n") in
  let _ = print_string (s^" inp2 :"^(pr2 e2)^"\n") in
  let _ = print_string (s^" out :"^(pr_o r)^"\n") in
  r

let ho_debug_2 (s:string) (pr1:'a->string) (pr2:'b->string) (pr_o:'z->string) (f:'a -> 'b -> 'z) (e1:'a) (e2:'b) : 'z =
  ho_debug_2_opt s pr1 pr2 pr_o (fun _ -> true) f e1 e2
 

let ho_debug_3 (s:string) (pr1:'a->string) (pr2:'b->string) (pr3:'c->string) (pr_o:'z->string) (f:'a -> 'b -> 'c -> 'z) (e1:'a) (e2:'b) (e3:'c) : 'z =
  let r = try
    f e1 e2 e3
  with ex -> 
      let _ = print_string (s^" inp1 :"^(pr1 e1)^"\n") in
      let _ = print_string (s^" inp2 :"^(pr2 e2)^"\n") in
      let _ = print_string (s^" inp3 :"^(pr3 e3)^"\n") in
      let _ = print_string (s^" Exception"^(Printexc.to_string ex)^"Occurred!\n") in
      raise ex in
  let _ = print_string (s^" inp1 :"^(pr1 e1)^"\n") in
  let _ = print_string (s^" inp2 :"^(pr2 e2)^"\n") in
  let _ = print_string (s^" inp3 :"^(pr3 e3)^"\n") in
  let _ = print_string (s^" out :"^(pr_o r)^"\n") in
  r
  
let ho_debug_4 (s:string) (pr1:'a->string) (pr2:'b->string) (pr3:'c->string) (pr4:'d->string) (pr_o:'z->string) (test:'z->bool)
    (f:'a -> 'b -> 'c -> 'd-> 'z) (e1:'a) (e2:'b) (e3:'c) (e4:'d): 'z =
  let r = try
    f e1 e2 e3 e4
  with ex -> 
      let _ = print_string (s^" inp1 :"^(pr1 e1)^"\n") in
      let _ = print_string (s^" inp2 :"^(pr2 e2)^"\n") in
      let _ = print_string (s^" inp3 :"^(pr3 e3)^"\n") in
      let _ = print_string (s^" inp4 :"^(pr4 e4)^"\n") in
      let _ = print_string (s^" Exception"^(Printexc.to_string ex)^"Occurred!\n") in
      raise ex in
  if (test r) then
    let _ = print_string (s^" inp1 :"^(pr1 e1)^"\n") in
    let _ = print_string (s^" inp2 :"^(pr2 e2)^"\n") in
    let _ = print_string (s^" inp3 :"^(pr3 e3)^"\n") in
    let _ = print_string (s^" inp4 :"^(pr4 e4)^"\n") in
    let _ = print_string (s^" out :"^(pr_o r)^"\n") in
    r
  else
    r
let ho_debug_5 (s:string) (pr1:'a->string) (pr2:'b->string) (pr3:'c->string) (pr4:'d->string)
               (pr5:'e->string) (pr_o:'z->string) (test:'z->bool)
    (f:'a -> 'b -> 'c -> 'd -> 'e -> 'z) (e1:'a) (e2:'b) (e3:'c) (e4:'d) (e5:'e) : 'z =
  let r = try
    f e1 e2 e3 e4 e5
  with ex -> 
      let _ = print_string (s^" inp1 :"^(pr1 e1)^"\n") in
      let _ = print_string (s^" inp2 :"^(pr2 e2)^"\n") in
      let _ = print_string (s^" inp3 :"^(pr3 e3)^"\n") in
      let _ = print_string (s^" inp4 :"^(pr4 e4)^"\n") in
      let _ = print_string (s^" inp5 :"^(pr5 e5)^"\n") in
      let _ = print_string (s^" Exception"^(Printexc.to_string ex)^"Occurred!\n") in
      raise ex in
  if (test r) then
    let _ = print_string (s^" inp1 :"^(pr1 e1)^"\n") in
    let _ = print_string (s^" inp2 :"^(pr2 e2)^"\n") in
    let _ = print_string (s^" inp3 :"^(pr3 e3)^"\n") in
    let _ = print_string (s^" inp4 :"^(pr4 e4)^"\n") in
    let _ = print_string (s^" inp5 :"^(pr5 e5)^"\n") in
    let _ = print_string (s^" out :"^(pr_o r)^"\n") in
    r  
  else 
    r

let ho_debug_3a_list (s:string) (pr:'a->string) f e1 e2 e3 : 'z =
  ho_debug_3 s (string_of_list pr) (string_of_list pr) (fun _ -> "?") (fun _ -> "?") f e1 e2 e3 

(** String-handling utility functions. *)

let trim_quotes s = 
  let trim_last s' = if String.get s' ((String.length s')-1) = '"' then
    String.sub s' 0 ((String.length s')-1) else s' in
  if String.get s 0 = '"' then 
    (trim_last (String.sub s 1 ((String.length s) - 1)))
  else
    trim_last s

let unescaped s =
  let n = ref 0 in
    for i = 0 to String.length s - 1 do
      n := !n +
        (match String.unsafe_get s i with
           '\\' when String.unsafe_get s (i+1) != '\\' ->
             (match String.unsafe_get s (i+1) with
               'n' -> 0
             | 't' -> 0
             | _ -> 1)
        | _ -> 1)
    done;
    if !n = String.length s then s else begin
      let s' = String.create !n in
      n := 0;
      let skip = ref 0 in
      (try (for i = 0 to String.length s - 1 do
        begin
          if (i + !skip) = String.length s then raise Bail;
          match String.unsafe_get s (i + !skip) with
          | '\\' when String.unsafe_get s (i+ !skip+1) != '\\' ->
              (match String.unsafe_get s (i+ !skip+1) with
                'n' -> String.unsafe_set s' !n '\n'; incr skip
              | 'r' -> String.unsafe_set s' !n '\r'; incr skip
              | 't' -> String.unsafe_set s' !n '\t'; incr skip
              | '\\' -> String.unsafe_set s' !n '\\'; incr skip;
              | _ -> raise Bad_string)
          | c -> String.unsafe_set s' !n c
        end;
        incr n
      done) with Bail -> ());
      Str.first_chars s' (String.length s - !skip)
    end

let trim_str input =
  let start_idx = ref 0 in
  let len = String.length input in
  let _ = 
	while (!start_idx < len) && ((String.get input !start_idx) = ' ') do
	  start_idx := !start_idx + 1
	done in
  let end_idx = ref (len - 1) in
  let _ = 
	while (!end_idx > !start_idx) && ((String.get input !end_idx) = ' ') do
	  end_idx := !end_idx - 1
	done in
  let res = String.sub input !start_idx (!end_idx - !start_idx + 1) in
	res


(** namespace mangling stuff *)

let qualify_if_needed mname n =
  if String.contains n '.' then n else (mname ^ "." ^ n)

let unqualify_getting_module s =
  if String.contains s '.' then
    let i = String.rindex s '.' in
    String.sub s 0 i
  else ""

let unqualify s =
  if String.contains s '.' then
    let i = String.rindex s '.' in
    String.sub s (i+1) (String.length s - i - 1)
  else s

let unprime s =
  let l = String.length s in 
  if l = 0 then s else 
  if (String.get s (l-1)) = '\'' then
    String.sub s 0 (l-1) else s

let is_primed s =
  let l = String.length s in 
  if l = 0 then false else 
  (String.get s (l-1) = '\'')

let replace_dot_with_uscore s =
  let dot = Str.regexp "\\." in
  let caret = Str.regexp "\\^" in
  Str.global_replace dot "_" 
    (Str.global_replace caret "$" s)

let replace_minus_with_uscore s =
  let minus = Str.regexp "-" in
  let caret = Str.regexp "\\^" in
  Str.global_replace minus "_" 
    (Str.global_replace caret "$" s)

let replace_path_sep_with_uscore s =
  let path_sep = Str.regexp "/" in
  let caret = Str.regexp "\\^" in
  Str.global_replace path_sep "_" 
    (Str.global_replace caret "$" s)

let split_by sep s =
  let sep_regexp = Str.regexp (Str.quote sep) in
  Str.split sep_regexp s

(** Error-handling functions. *)

let error_list = ref []
let no_errors () = (List.length !error_list = 0)

let err loc msg = 
  error_list := !error_list @
    [loc ^ ": error: "^msg]

let error msg = (print_string (msg ^"\n"); flush_all(); err "" msg)
let print_errors () = 
  List.iter (function x -> print_string (x ^ "\n")) !error_list;
  print_string (string_of_int (List.length !error_list)^" errors.\n");
  print_string "The program is INVALID\n";
  exit 2

let (warning_no : int ref) = ref 0
let warn msg = 
  (warning_no := !warning_no + 1);
  print_string ("*** Warning: "^ msg ^ "\n"); flush_all()

let warn_if_none ov msg = match ov with
  | None -> warn msg
  | Some _ -> ()

let fail s =   
  print_string (s ^ "\n"); 
  Printf.printf "There were %d warnings.\n" !warning_no;
  flush_all();
  failwith s

(** Printing notifications [msg, amsg, etc] *)
let verbose = ref false

(** always print this message *)
let amsg s = print_string s; flush_all ()

(** print only if -v *)
let msg s = if !verbose then amsg s

  
(** removing 'option' types *)
let unsome : 'a option -> 'a = 
  function
	| Some x -> x
	| None   -> failwith "[util] tried to deoptionify None"

let is_some : 'a option -> bool =
  function
	| Some x -> true
	| None -> false


(** Read the given file into a string. *)
let string_of_file (fname : string) =
  if Sys.file_exists fname then
    let chn = open_in fname in
    let len = in_channel_length chn in
    let str = String.make len ' ' in
    let _ = really_input chn str 0 len in
    (close_in chn; str)
  else
    (warn ("Could not read file " ^ fname ^ "; assuming empty content.");
     "")

let fileLine (fn:string) : string =
  begin
    let chn = open_in fn in
      let str = input_line chn in
      close_in chn;
      str
  end

(** Use timed_command utility to run an external process with a timeout. *)

let timed_command = qualify_helper_fn "timed_command"

let run_with_timeout (prog : string) (seconds : int) : int =
  (* msg ("Running with timeout: " ^ prog ^ "\n"); *)
  Sys.command (timed_command ^ Printf.sprintf " %d " seconds ^ prog)

let is_breakable c =  match c with
  | '(' | ')' | ' ' | '+' | ':' -> true
  | _ -> false

let new_line_str = "\n"
(*
  if Sys.os_type = "Cygwin" then
	let t = Buffer.create 1 in
	  Buffer.add_char t (char_of_int 0x0A);
	  let tmp = Buffer.contents t in
		tmp
  else "\n"
*)

let break_lines (input : string) : string =
  let buf = Buffer.create 4096 in
  let i = ref 0 in
  let cnt = ref 0 in
  let l = String.length input in
    while !i < l do
      Buffer.add_char buf input.[!i];
      cnt := !cnt + 1;
      if !cnt > 80 && (is_breakable input.[!i]) then begin
		Buffer.add_string buf new_line_str;
		cnt := 0
	  end;
      i := !i + 1
    done;
    Buffer.contents buf
	  
let rec gen_list (n : int) (v : 'a) : 'a list =
  if n = 0 then
	[]
  else
	v :: (gen_list (n-1) v)

(*
  first component of returned value contains the first i values from the list
  second component contains the rest
*)
let rec split_at (xs : 'a list) (i : int) : ('a list * 'a list) =
  if i = 0 then ([], xs)
  else
	let a, b = split_at (List.tl xs) (i-1) in
	  ((List.hd xs) :: a, b) 

let rec split3 (l : ('a * 'b * 'c) list) : 'a list * 'b list * 'c list = match l with
  | (h1, h2, h3) :: rest ->
	  let l1, l2, l3 = split3 rest in
		(h1::l1, h2::l2, h3::l3)
  | [] -> ([], [], [])

let rec combine3 a b c = match (a, b, c) with
  | (ah::arest, bh::brest, ch::crest) ->
	  let l = combine3 arest brest crest in
		(ah, bh, ch)::l
  | ([], [], []) -> []
  | _ -> failwith ("combine3: combining lists with different lengths")

let rec map3 (f : 'a -> 'b -> 'c -> 'd) (a0 : 'a list) (bs : 'b list) (cs : 'c list) : 'd list = 
  match (a0, bs, cs) with
	| (a :: r1, b :: r2, c :: r3) ->
		let r = map3 f r1 r2 r3 in
		  (f a b c) :: r
	| [], [], [] -> []
	| _ -> failwith ("map3: mapping lists with different lengths.")

let rec map4 (f : 'a -> 'b -> 'c -> 'd -> 'e) (a0 : 'a list) (bs : 'b list) (cs : 'c list) (ds : 'd list) : 'e list = 
  match (a0, bs, cs, ds) with
	| (a :: r1, b :: r2, c :: r3, d:: r4) ->
		let r = map4 f r1 r2 r3 r4 in
		  (f a b c d) :: r
	| [], [], [], [] -> []
	| _ -> failwith ("map4: mapping lists with different lengths.")


let rec repeat (v : 'a) (n : int) : 'a list =
  if n <= 0 then []
  else v :: (repeat v (n-1))

(* Hashtable stuff *)

let copy_keys (keys : 'a list) (fr_tab : ('a, 'b) Hashtbl.t) (to_tab : ('a, 'b) Hashtbl.t) =
  let cp_key (k : 'a) = 
	try
	  let v = Hashtbl.find fr_tab k in
		Hashtbl.add to_tab k v
	with
	  | Not_found -> () 
  in
	ignore (List.map cp_key keys)

let list_of_hash_values (tab : ('a, 'b) Hashtbl.t) : 'b list =
  let append_val k v vl = v::vl in
	Hashtbl.fold append_val tab []

let counters = ref (Hashtbl.create 10)

let add_to_counter (s:string) i = 
  if !Globals.enable_counters then
  try
    let r = Hashtbl.find !counters s in
    Hashtbl.replace !counters s (r+i)
  with
  | Not_found -> Hashtbl.add !counters s i
  else ()
let inc_counter (s:string) = add_to_counter s 1
  
let string_of_counters () = 
  let s = Hashtbl.fold (fun k v a-> (k,v)::a) !counters [] in
  let s = List.sort (fun (a1,_) (a2,_)-> String.compare a1 a2) s in
  "Counters: \n "^ (String.concat "\n" (List.map (fun (k,v) -> k^" = "^(string_of_int v)) s))^"\n"
	
let profiling_stack = ref []
let tasks = ref (Hashtbl.create 10)  

let get_time () = 
	let r = Unix.times () in
	(*let _ = print_string ("\n"^(string_of_float r.Unix.tms_utime)^"-"^(string_of_float r.Unix.tms_stime)^"-"^(string_of_float r.Unix.tms_cutime)^"\n") in*)
	(*time_list := (r.Unix.tms_utime , r.Unix.tms_stime , r.Unix.tms_cutime , r.Unix.tms_cstime):: !time_list ;*)
	r.Unix.tms_utime +. r.Unix.tms_stime +. r.Unix.tms_cutime +. r.Unix.tms_cstime
	
let add_task_instance msg time = 	
 try 
	let (t1,cnt1,max1) = Hashtbl.find !tasks msg in
	Hashtbl.replace !tasks msg (t1+.time,cnt1+1, (if (time>Globals.profile_threshold) then  time::max1 else max1))
 with Not_found -> 
	Hashtbl.add !tasks msg (time,1,(if (time>Globals.profile_threshold) then  [time] else []))
let push_time_no_cnt msg = 
if (!Globals.profiling) then
 let timer = get_time () in
	profiling_stack := (msg, timer,true) :: !profiling_stack
else ()

let push_time msg = 
if (!Globals.profiling) then
 (inc_counter ("cnt_"^msg);
 let timer = get_time () in
	profiling_stack := (msg, timer,true) :: !profiling_stack)
else ()
	
let pop_time msg = 
	if (!Globals.profiling) then
		let m1,t1,_ = List.hd !profiling_stack in
		if (String.compare m1 msg)==0 then 
			let t2 = get_time () in
			 if (t2-.t1)< 0. then Error.report_error {Error.error_loc = Globals.no_pos; Error.error_text = ("negative time")}
			else
			profiling_stack := List.tl !profiling_stack;
			if (List.exists (fun (c1,_,b1)-> (String.compare c1 msg)=0) !profiling_stack) then begin
				(* if (List.exists (fun (c1,_,b1)-> (String.compare c1 msg)=0&&b1) !profiling_stack) then begin *)
				(* 	profiling_stack :=List.map (fun (c1,t1,b1)->if (String.compare c1 msg)=0 then (c1,t1,false) else (c1,t1,b1)) !profiling_stack; *)
				(* 	print_string ("\n double accounting for "^msg^"\n") *)
                (* print_string ("\n skip double accounting for "^msg^"\n")  *)
				end	
            else add_task_instance m1 (t2-.t1) 
			 
		else 
			Error.report_error {Error.error_loc = Globals.no_pos; Error.error_text = ("Error poping "^msg^"from the stack")}
	else ()
  
let prof_1 (s:string) (f:'a -> 'z) (e:'a) : 'z =
  try
    push_time s;
      let r=f e in
      (pop_time s; r)
  with ex -> (pop_time s; raise ex)

let prof_2 (s:string) (f:'a1 -> 'a2 -> 'z) (e1:'a1) (e2:'a2) : 'z =
  try
    push_time s;
      let r=f e1 e2 in
      (pop_time s; r)
  with ex -> (pop_time s; raise ex)

let prof_3 (s:string) (f:'a1 -> 'a2 -> 'a3 -> 'z) (e1:'a1) (e2:'a2) (e3:'a3) : 'z =
  try
    push_time s;
      let r=f e1 e2 e3 in
      (pop_time s; r)
  with ex -> (pop_time s; raise ex)

let prof_4 (s:string) (f:'a1 -> 'a2 -> 'a3 -> 'a4 -> 'z) (e1:'a1) (e2:'a2) (e3:'a3) (e4:'a4) : 'z =
  try
    push_time s;
      let r=f e1 e2 e3 e4 in
      (pop_time s; r)
  with ex -> (pop_time s; raise ex)

let prof_5 (s:string) (f:'a1 -> 'a2 -> 'a3 -> 'a4 -> 'a5 -> 'z) (e1:'a1) (e2:'a2) (e3:'a3) (e4:'a4)(e5:'a5) : 'z =
  try
    push_time s;
      let r=f e1 e2 e3 e4 e5 in
      (pop_time s; r)
  with ex -> (pop_time s; raise ex)

let prof_6 (s:string) (f:'a1 -> 'a2 -> 'a3 -> 'a4 -> 'a5 -> 'a6 -> 'z) (e1:'a1) (e2:'a2) (e3:'a3) (e4:'a4)(e5:'a5) (e6:'a6) : 'z =
  try
    push_time s;
      let r=f e1 e2 e3 e4 e5 e6 in
      (pop_time s; r)
  with ex -> (pop_time s; raise ex)


let pop_spec_counter = ref 1
let gen_time_msg _  = 
  pop_spec_counter := !pop_spec_counter+1;
  "time_stk_"^ (string_of_int !pop_spec_counter)
  
let pop_time_to_s_no_count  msg = 
	if (!Globals.profiling) then
		let rec helper l = match l with
      | [] -> Error.report_error {Error.error_loc = Globals.no_pos; Error.error_text = ("Error special poping "^msg^"from the stack")}
      | (m1,_,_)::t ->  if not ((String.compare m1 msg)==0) then helper t			
			else t in
    profiling_stack := helper !profiling_stack 
	else ()
	
let print_tasks unit : unit  = 
  let str_list = Hashtbl.fold (fun c1 (t,cnt,l) a-> (c1,t,cnt,l)::a) !tasks [] in
  let str_list = List.sort (fun (c1,_,_,_)(c2,_,_,_)-> String.compare c1 c2) str_list in
    let (_,ot,_,_) = List.find (fun (c1,_,_,_)-> (String.compare c1 "Overall")=0) str_list in
    let f a = (string_of_float ((floor(100. *.a))/.100.)) in
    let fp a = (string_of_float ((floor(10000. *.a))/.100.)) in
    let (cnt,str) = List.fold_left (fun (a1,a2) (c1,t,cnt,l)  -> 
      let r = (a2^" \n("^c1^","^(f t)^","^(string_of_int cnt)^","^ (f (t/.(float_of_int cnt)))^",["^
      (if (List.length l)>0 then 
        let l = (List.sort compare l) in		
        (List.fold_left (fun a c -> a^","^(f c)) (f (List.hd l)) (List.tl l) )
      else "")^"],  "^(fp (t/.ot))^"%)") in
    ((a1+1),r) 
    ) (0,"") str_list in
  print_string ("\n profile results: there where " ^(string_of_int cnt)^" keys \n"^str^"\n" ) 
  
	
let add_index l = 
	let rec ff i l = match l with
		| [] -> []
		| a::b-> (i,a)::(ff (i+1) b) in
	(ff 0 l)

	

(*hairy stuff for excep tion numbering*)
			
 let exc_list = ref ([]:(string * string * Globals.nflow ) list)
  			 
 let get_hash_of_exc (f:string): Globals.nflow = 
	if ((String.compare f Globals.stub_flow)==0) then 
		Error.report_error {Error.error_loc = Globals.no_pos; Error.error_text = ("Error found stub flow")}
	else
	let rec get (lst:(string*string*Globals.nflow)list):Globals.nflow = match lst with
		| [] -> Globals.false_flow_int
		| (a,_,(b,c))::rst -> if (String.compare f a)==0 then (b,c)
						else get rst in
    (get !exc_list)
	
	
  (*t1 is a subtype of t2*)
 let exc_sub_type (t1 : Globals.constant_flow) (t2 : Globals.constant_flow): bool = 
	let r11,r12 = get_hash_of_exc t1 in
	if ((r11==0) && (r12==0)) then false
	else
	let r21,r22 = get_hash_of_exc t2 in
	if ((r21==0) && (r22==0)) then true
	else
	((r11>=r21)&&(r12<=r22))
	
(*let exc_int_sub_type ((t11,t12):Globals.nflow)	((t21,t22):Globals.nflow):bool = if (t11==0 && t12==0) then true else ((t11>=t21)&&(t12<=t22))*)

let get_closest ((min,max):Globals.nflow):(string) = 
	 let rec get (lst:(string*string*Globals.nflow) list):string*Globals.nflow = match lst  with
		| [] -> (Globals.false_flow,Globals.false_flow_int)
		| (a,b,(c,d)):: rest-> if (c==min && d==max) then (a,(c,d)) (*a fits perfect*)
							else let r,(minr,maxr) = (get rest) in
										if (minr==c && maxr==d)||(c>min)||(d<max) then (r,(minr,maxr)) (*the rest fits perfect or a is incompatible*)
											else if (minr>min)||(maxr<max) then (a,(c,d)) (*the rest is incompatible*)
											else if ((min-minr)<=(min-c) && (maxr-max)<=(d-max)) then (r,(minr,maxr))
											else (a,(c,d)) in
	let r,_ = (get !exc_list) in r
 
 (*constructs the mapping between class/data def names and interval types*) 
 let c_h () = 								
	let rec lrr (f1:string)(f2:string):(((string*string*Globals.nflow) list)*Globals.nflow) =
		let l1 = List.find_all (fun (_,b1,_)-> ((String.compare b1 f1)==0)) !exc_list in
		if ((List.length l1)==0) then let i = (Globals.fresh_int()) in let j = (Globals.fresh_int()) in ([(f1,f2,(i,j))],(i,j))
			else let ll,(mn,mx) = List.fold_left (fun (t,(o_min,o_max)) (a,b,(c,d))-> let temp_l,(n_min, n_max) = (lrr a b) in 
																			(temp_l@t,((if ((o_min== -1)||(n_min<o_min)) then n_min else o_min),(if (o_max<n_max) then n_max else o_max)))			
			) ([],(-1,-1)) l1 in
				( ((f1,f2,(mn,mx))::ll) ,(mn,mx)) in
	let r,_ = (lrr Globals.top_flow "") in
	let _ = exc_list := r in
	Globals.n_flow_int := (get_hash_of_exc Globals.n_flow);
	Globals.ret_flow_int := (get_hash_of_exc Globals.ret_flow);	
	Globals.spec_flow_int := (get_hash_of_exc Globals.spec_flow);	
	Globals.top_flow_int := (get_hash_of_exc Globals.top_flow);
	Globals.exc_flow_int := (get_hash_of_exc Globals.abnormal_flow)
	(*let _ = print_string ((List.fold_left (fun a (c1,c2,(c3,c4))-> a ^ " (" ^ c1 ^ " : " ^ c2 ^ "="^"["^(string_of_int c3)^","^(string_of_int c4)^"])\n") "" r)) in*)
	 
 let add_edge(n1:string)(n2:string):bool =
	let _ =  exc_list := !exc_list@ [(n1,n2,Globals.false_flow_int)] in
	true
	
 let clean_duplicates ()= 
	exc_list := remove_dups !exc_list

let has_cycles ():bool =
	let rec cc (crt:string)(visited:string list):bool = 
		let sons = List.fold_left (fun a (d1,d2,_)->if ((String.compare d2 crt)==0) then d1::a else a) [] !exc_list in
		if (List.exists (fun c-> (List.exists (fun d->((String.compare c d)==0)) visited)) sons) then true
			else (List.exists (fun c-> (cc c (c::visited))) sons) in	
	(cc Globals.top_flow [Globals.top_flow])
  
  
  
let print_profiling_info () = if (!Globals.profiling) then  print_tasks () else ()
  
  
(*aliasing structures*)
type ('a,'k) e_map =  ('a * 'k) list
type 'a e_set =  ('a,'a list) e_map
type 'a e_name = ('a * string) list (* map of name to string used *)
type 'a e_set_str =  (string e_set * ('a -> string) * 'a e_name )

type 'a eq_set =  ('a,'a list) e_map * ('a -> 'a -> bool)

let string_of_a_list (f:'a->string) (el:'a list) : string =
  "["^ (String.concat ", "(List.map f el))^"]\n"
         
let string_of_a_list_no_newline (f:'a->string) (el:'a list) : string =
  "["^ (String.concat ", "(List.map f el))^"]"

let string_of_a_list (f:'a->string) (el:'a list) : string =
  (string_of_a_list_no_newline f el)^"\n"

let string_of_a_list_of_list (f:'a->string) (el:'a list list) : string =
  "["^ (String.concat ", "(List.map (string_of_a_list_no_newline f) el))^"]\n"

(* converts (a e_set) to [[a]] *)
let partition (s: 'a e_set) : 'a list list =
 let rec insert (a,k) lst = match lst with
      | [] -> [(k,[a])]
      | (k2,ls)::xs -> 
        if k==k2 then (k,a::ls)::xs
          else (k2,ls)::(insert (a,k) xs) in
 let r = List.fold_left (fun lst x ->  insert x lst) [] s in
 List.map ( fun (_,b) -> b) r

let string_of_e_set (f:'a->string) (e:'a e_set) : string =
  let ll=partition e in 
  "[@"^ (String.concat " \n " (List.map (fun cl -> "{"^(String.concat ", "(List.map f cl))^"}") ll))^"]"

let string_of_eq_set (f:'a->string) ((e,_):'a eq_set) : string = string_of_e_set f e


(* converts (a eq_set) to [[a]] *)
let partition_eq ((s,_): 'a eq_set) : 'a list list =
  partition s

let partition_eq_debug (f:'a->string) ((s,eq): 'a eq_set) : 'a list list =
 let ax = partition s in
 let _ = print_string ("partition_eq inp1 :"^(string_of_e_set f s)^"\n") in
 let _ = print_string ("partition_eq out2 :"^(string_of_a_list_of_list f ax)^"\n") in
 (ax)

(* converts [[a]] to (a e_set) *)
let un_partition (ll:'a list list) : 'a e_set =
  let flat xs y = 
    if (List.length xs>1) then List.map (fun x -> (x,y)) xs 
    else [] in
  List.concat (List.map (fun x -> flat x x) ll)



let empty_aset  : 'a e_set = []

let empty_a_set () : 'a e_set = empty_aset 

let empty_a_set_eq (eq) : 'a eq_set = ([],eq)

let is_empty_aset s = s=[]

let is_empty_aset_eq ((s,_):'a eq_set)  = s=[]

let empty_a_set_str f : 'a e_set_str = ([],f,[])

let find_aux_eq (eq:'a->'a->bool) (s: ('a,'k) e_map) (e:'a) (d:'k) : 'k =
  try
     snd(List.find (fun (e1,_) -> eq e e1) s)
  with
     _ -> d

let find_aux (s: ('a,'k) e_map) (e:'a) (d:'k) : 'k = find_aux_eq (=) s e d
(*
  try
     List.assoc e s
  with
     _ -> d
*)

(* find key of e in s, returning [] if not found *)
let find_eq2 (eq:'a->'a->bool)  (s : 'a e_set) (e:'a) : 'a list  
      = find_aux_eq eq s e []

(* find key of e in s *)
let find (s : 'a e_set) (e:'a) : 'a list  = find_eq2 (=) s e

(* find key of e in eq_set s *)
let find_eq ((s,eq) : 'a eq_set) (e:'a) : 'a list  = find_eq2 eq s e 


(* find key of e in s and return remainder after
   all elements equivalent to e is removed *)
let find_remove_eq2 (eq:'a->'a->bool) (s : 'a e_set) (e:'a) : ('a list) * ('a e_set)  = 
  let r1 = find_aux_eq eq s e [] in
  (r1, if r1==[] then s else List.filter (fun (e2,_)-> not(eq e e2)) s)

(* find key of e in s and return remainder after
   all elements equivalent to e is removed *)
let find_remove (s : 'a e_set) (e:'a) : 'a list * ('a e_set)  = 
  find_remove_eq2 (=) s e 


let find_remove_eq ((s,eq) : 'a eq_set) (e:'a) : 'a list * ('a eq_set)  = 
  let (k,s)=find_remove_eq2 eq s e in
  (k,(s,eq))

let find_str ((s,f,_) : 'a e_set_str) (e:'a) : string list  
      = find_aux s (f e) []

(* returns s |- x=y *)
let is_equiv_eq2 (eq:'a->'a->bool) (s: 'a e_set)  (x:'a) (y:'a) : bool =
  if (eq x y) then true
  else
    let r1 = find_eq2 eq s x in
    let r2 = find_eq2 eq s y in
    (r1==r2 && not(empty r1))

(* returns s |- x=y *)
let is_equiv (s: 'a e_set)  (x:'a) (y:'a) : bool =
  is_equiv_eq2 (=) s x y

(* returns s |- x=y *)
let is_equiv_eq ((s,eq): 'a eq_set)  (x:'a) (y:'a) : bool =
  is_equiv_eq2 eq s x y


(* returns s |- x=y *)
let is_equiv_str ((s,f,_): 'a e_set_str)  (x:'a) (y:'a) : bool =
  is_equiv s (f x) (f y)

(* add x=y to e-set s and returning a new e-set with
   extra elements added *)
let add_equiv_eq2_raw  (eq:'a->'a->bool) (s: 'a e_set) (x:'a) (y:'a) : 'a e_set = 
  if (eq x y) then s
  else
    let r1 = find_eq2 eq s x in
    let r2 = find_eq2 eq s y in
    if empty r1 then
      if empty r2 then
        let r3 = [x;y] in
        (x,r3)::((y,r3)::s)
      else (x,r2)::s
    else
      if empty r2 then (y,r1)::s
      else
        if r1==r2 then s
        else 
          let r3=r1@r2 in
          List.map (fun (a,b) -> if (b==r1 or b==r2) then (a,r3) else (a,b)) s

(* add x=y to e-set s *)
let add_equiv_raw (s: 'a e_set) (x:'a) (y:'a) : 'a e_set = 
  add_equiv_eq2_raw (=) s x y

(* add x=y to e-set s *)
let add_equiv_eq_raw  ((s,eq): 'a eq_set) (x:'a) (y:'a) : 'a eq_set = 
  let ns=add_equiv_eq2_raw eq s x y in (ns,eq)

let find_name_str (f:'a->string) (nmap:'a e_name) (e:'a) : (string * 'a e_name) =
  try 
     (List.assoc e nmap,nmap)
  with _ -> let s=f e in (s,(e,s)::nmap)

let find_elem_str (nmap:'a e_name) (n:string)  : 'a =
  try 
     fst(List.find (fun (_,s) -> n=s) nmap)
  with _ -> Error.report_error {Error.error_loc = Globals.no_pos; 
                  Error.error_text = ("find_elem_str : elem not found")}

(* add x=y to e-set_str *)
let add_equiv_str ((s,f,nm): 'a e_set_str) (x:'a) (y:'a) : 'a e_set_str =
  let (s1,nm1) = find_name_str f nm x in
  let (s2,nm2) = find_name_str f nm1 y in
  (add_equiv_raw s s1 s2, f, nm2)


(* this method is used to merge two partitions 
   which may have different keys *)
(* split out sub-lists in l which overlaps with x *)
let split_partition (eq:'a->'a->bool) (x:'a list) (l:'a list list): ('a list list * 'a list list) =
 List.fold_left ( fun (r1,r2) y -> if (overlap_eq eq x y) then (y::r1,r2) else (r1,y::r2)) ([],[]) l
 
(* merge l1 /\ l2 to [[a]] *)
let rec merge_partition (eq:'a->'a->bool) (l1:'a list list) (l2:'a list list) : 'a list list = match l1 with
  | [] -> l2
  | x::xs ->
    let (y,ys)=split_partition eq x l2 in
    if empty y then x::(merge_partition eq xs l2)
    else merge_partition eq xs ((x@(List.concat y))::ys)
   (*remove dupl of x*)
         
(* return the domain of e-set *)
let domain (s: ('a,'k) e_map) : 'a list = List.map fst s

(* return list of elements in e_set *)
let get_elems (s:'a e_set) : 'a list = domain s

(* return list of elements in eq_set *)
let get_elems_eq_raw ((s,_):'a eq_set) : 'a list = domain s

(* return pairs of equivalent elements from e_set *)
let get_equiv_raw (s:'a e_set) : ('a *'a) list = 
  let ll = partition s in
  let make_p l = match l with
    | [] -> []
    | x::xs -> List.map (fun b -> (x,b)) xs in
  List.concat (List.map make_p ll)

(* return pairs of equivalent elements from e_set *)
let get_equiv_eq_raw ((s,_):'a eq_set) : ('a *'a) list = get_equiv_raw s 

let order_two (l1:'a list) (l2:'a list) : ('a list * 'a list) =
  if (List.length l1)>(List.length l2) then (l2,l1)
  else (l1,l2)

(* merge two equivalence sets s1 /\ s2 *)
let merge_set_eq2 (eq:'a->'a->bool) (s1: 'a e_set) (s2: 'a e_set): 'a e_set =
  let (t1,t2) = order_two s1 s2 in
  List.fold_left (fun a (p1,p2) -> add_equiv_eq2_raw eq a p1 p2) t2 (get_equiv_raw t1)


let merge_set_eq  ((s1,eq): 'a eq_set) ((s2,_): 'a eq_set): 'a eq_set =
 let ax = merge_set_eq2 eq s1 s2 in
 (ax,eq)

let merge_set_eq_debug (f:'a->string) ((s1,eq): 'a eq_set) ((s2,_): 'a eq_set): 'a eq_set =
 let ax = merge_set_eq2 eq s1 s2 in
 let _ = print_string ("merge_set_eq inp1 :"^(string_of_e_set f s1)^"\n") in
 let _ = print_string ("merge_set_eq inp2 :"^(string_of_e_set f s2)^"\n") in
 let _ = print_string ("merge_set_eq out :"^(string_of_e_set f ax)^"\n") in
 (ax,eq)

let merge_set (s1: 'a e_set) (s2: 'a e_set): 'a e_set =
  merge_set_eq2 (=) s1 s2

(* merge two equivalence set_str s1 /\ s2 *)
let merge_set_str ((s1,f,nm1): 'a e_set_str) ((s2,_,nm2): 'a e_set_str): 'a e_set_str =
 (merge_set s1 s2,f,nm1@nm2)


(* remove vs elements from e_set - used by existential elimination 
let elim_elems_list (s:'a e_set) (vs:'a list) : 'a e_set = 
  List.filter (fun (a,_) -> not(List.mem a vs)) s
  *)

(* remove all entries with same key k from e_set 
let elim_elems_key (s:'a e_set) (k) : 'a e_set = 
  List.filter (fun (a,k2) -> not(k==k2)) s
  *)

(* remove key e from e_set  *)
let elim_elems_one_eq2 (eq:'a->'a->bool) (s:'a e_set) (e:'a) : 'a e_set = 
  List.filter (fun (a,k2) -> not(eq a e)) s

(* remove key e from e_set  *)
let elim_elems_one (s:'a e_set) (e:'a) : 'a e_set = 
  elim_elems_one_eq2 (=) s e

(* remove key e from e_set  *)
let elim_elems_one_eq ((s,eq):'a eq_set) (e:'a) : 'a eq_set = 
  let ns=elim_elems_one_eq2 eq s e in (ns,eq)

(* return all elements equivalent to e, including itself *)
let find_equiv_all_eq2_raw  (eq:'a->'a->bool) (e:'a) (s:'a e_set) : 'a list  =
  let r1 = find_eq2 eq s e in
  if (r1==[]) then []
  else List.map fst (List.filter (fun (a,k) -> k==r1) s) 


(* return a distinct element equal to e *)
let find_equiv_eq2  (eq:'a->'a->bool) (e:'a) (s:'a e_set) : 'a option  =
  let ls=find_equiv_all_eq2_raw eq e s in
  try 
    let p = List.find (fun x -> not(eq x e)) ls in
    Some p
  with _ -> None
(* 
  old implementation
 let r1 = find_eq2 eq s e in
  if (r1==[]) then None
  else let ls = List.filter (fun (a,k) -> k==r1 && not(eq a e) ) s in
  match ls with
    | [] -> None 
    | (x,_)::_ -> Some x
*)


(* return a distinct element equal to e *)
let find_equiv  (eq:'a->'a->bool) (e:'a) (s:'a e_set) : 'a option  = find_equiv_eq2 (=) e s 

(* return all elements in eq_set equivalent to e, including itself *)
let find_equiv_all_eq_raw (e:'a) ((s,eq):'a eq_set) : 'a list  =
  find_equiv_all_eq2_raw eq e s

(* return a distinct element equal to e *)
let find_equiv_eq  (e:'a) ((s,eq):'a eq_set) : 'a option  = find_equiv_eq2 (eq) e s
 
(* return an element r that is equiv to e but distinct from it, and elim e from e_set *)
let find_equiv_elim_sure_eq2 (eq:'a->'a->bool) (e:'a) (s:'a e_set) : 'a option * ('a e_set)  =
  let r1,s1 = find_remove_eq2 eq s e in
  if (r1==[]) then (None,s)
  else let (ls,ls2) = List.partition (fun (a,k) -> k==r1 ) s1 in
  match ls with
    | [] -> (None,s1)
    | [(x,_)] -> (Some x, ls2)
    | (x,_)::_ -> (Some x, s1)


(* return an element r that is equiv to e but distinct from it, and elim e from e_set *)
let find_equiv_elim_sure (e:'a) (s:'a e_set) : 'a option * ('a e_set)  = find_equiv_elim_sure_eq2 (=) e s 

(* return an element r that is equiv to e but distinct from it, and elim e from e_set *)
let find_equiv_elim_sure_eq (e:'a) ((s,eq):'a eq_set) : 'a option * ('a eq_set)  =
  let (a1,a2)=find_equiv_elim_sure_eq2 eq e s in
  (a1,(a2,eq))

(* return a distinct element equal to e and elim e from e_set if found *)
let find_equiv_elim_eq2 (eq:'a->'a->bool) (e:'a) (s:'a e_set) : ('a * 'a e_set) option  =
  let (ne,ns) = find_equiv_elim_sure_eq2 eq e s in
  match ne with
    | None -> None
    | Some x -> Some (x, ns) 

(* return a distinct element equal to e and elim e from e_set if found *)
let find_equiv_elim (e:'a) (s:'a e_set) : ('a * 'a e_set) option  = find_equiv_elim_eq2 (=) e s

(* return a distinct element equal to e and elim e from e_set if found *)
let find_equiv_elim_eq (e:'a) ((s,eq):'a eq_set) : ('a * 'a eq_set) option  = 
  let (ne,ns) = find_equiv_elim_sure_eq2 eq e s in
  match ne with
    | None -> None
    | Some x -> Some (x, (ns,eq)) 


(* make fv=tv and then eliminate fv *)
(* fv should never be constant *)
let subs_eset_eq2 (eq:'a->'a->bool)  ((fv,tv):'a * 'a) (s:'a e_set) : 'a e_set = 
  if (eq fv tv) then s
  else
    let r1 = find_eq2 eq s fv in
    if (r1==[]) then s
    else 
      let ns = add_equiv_eq2_raw eq s fv tv in
      elim_elems_one_eq2 eq ns fv

(* make fv=tv and then eliminate fv *)
let subs_eset  (t:'a * 'a) (s:'a e_set) : 'a e_set = 
  subs_eset_eq2 (=) t s

(* make fv=tv and then eliminate fv *)
let subs_eset_eq (t:'a * 'a) ((s,eq):'a eq_set) : 'a eq_set = 
  let ns=subs_eset_eq2 (eq) t s in
  (ns,eq)

(* make fv=tv and then eliminate fv *)
let subs_eset_eq_debug (f:'a->string)  (t:'a * 'a) ((s,eq):'a eq_set) : 'a eq_set = 
  let r=subs_eset_eq2 (eq) t s in
  let svar = f (fst t) in
  let _ = print_string ("subs_eset_eq inp1 :"^svar^"->"^(f (snd t))^"\n") in
  let _ = print_string ("subs_eset_eq inp2 :"^(string_of_e_set f s)^"\n") in
  let _ = print_string ("subs_eset_eq out :"^(string_of_e_set f r)^"\n") in
  (if (List.length r)<(List.length s) then print_string ("subs_eset_eq : WARNING lost source var : "^svar^"\n"));
  (r,eq)


(*
let subs_eset ((fv,tv):'a * 'a) (s:'a e_set) : 'a e_set = 
  let r1 = find s fv in
  if (r1==[]) then s
  else 
    let ns = add_equiv s fv tv in
    elim_elems_one ns fv
*)
 
(* returns true if s contains no duplicates *)
let check_no_dupl_eq eq (s:'a list) : bool =
  let rec helper s = match s with
    | [] -> true
    | x::xs -> 
          if mem_eq eq x xs then false
          else helper xs in
  helper s

(* returns true if s contains no duplicates *)
let check_no_dupl (s:'a list) : bool = check_no_dupl_eq (=) s

(* check f is 1-to-1 map assuming s contains no duplicates *)
let is_one2one_eq (pr:'a->string) (eq:'a->'a->bool) (f:'a -> 'a) (s:'a list) : bool =
  let l = List.map f s in
    if (check_no_dupl_eq eq l) then true
    else (print_string ("duplicates here :"^(string_of_a_list pr l)^"\n") ; false) 

(* check f is 1-to-1 map assuming s contains no duplicates *)
let is_one2one (f:'a -> 'a) (s:'a list) : bool = is_one2one_eq (fun x -> "?") (=) f s

(* rename the elements of e_set *)
(* pre : f must be 1-to-1 map *)
let rename_eset_eq2 (pr:'a->string) (eq:'a->'a->bool) (f:'a -> 'a) (s:'a e_set) : 'a e_set = 
  let b = is_one2one_eq pr eq f (get_elems s) in
  if b then  List.map (fun (e,k) -> (f e,k)) s
  else Error.report_error {Error.error_loc = Globals.no_pos; 
                  Error.error_text = ("rename_eset : f is not 1-to-1 map")}

let rename_eset (f:'a -> 'a) (s:'a e_set) : 'a e_set = 
  rename_eset_eq2 (fun _ -> "?") (=) f s

let rename_eset_eq (f:'a -> 'a) ((s,eq):'a eq_set) : 'a eq_set = 
  let r=rename_eset_eq2 (fun _ -> "?") (eq) f s in
  (r,eq)

let rename_eset_eq_debug (pr:'a-> string) (f:'a -> 'a) ((s,eq):'a eq_set) : 'a eq_set = 
  let r=rename_eset_eq2 pr (eq) f s in
 let _ = print_string ("rename_eset_eq inp1 :"^(string_of_e_set pr s)^"\n") in
 let _ = print_string ("rename_eset_eq out :"^(string_of_e_set pr r)^"\n") in
  (r,eq)


(* return list of elements in e_set_str *)
let get_elems_str ((_,_,nm):'a e_set_str) : 'a list = List.map (fst) nm

(* return pairs of equivalent elements from e_set_str *)
let get_equiv_str ((s,_,nm):'a e_set_str) : ('a *'a) list = 
  let fe = find_elem_str nm in
  let ll = partition s in
  let make_p l = match l with
    | [] -> []
    | x::xs -> List.map (fun b -> (fe x,fe b)) xs in
  List.concat (List.map make_p ll)

(* remove vs elements from e_set_str - used by existential elimination *)
let elim_elems_str ((s,f,nm):'a e_set_str) (vs:'a list) : 'a e_set_str = 
  let vstr=List.map f vs in
  let s1=List.filter (fun (a,_) -> not(List.mem a vstr)) s in
  let nm1=List.filter (fun (_,a) -> not(List.mem a vstr)) nm in
  (s1,f,nm1)

(* rename the elements of e_set *)
(* pre : f must be 1-to-1 map *)
let rename_eset_str (re:'a -> 'a) ((s,f,nm):'a e_set_str) : 'a e_set_str = 
  let s_new=List.map (fun (e,k) -> (f(re(find_elem_str nm e)),k)) s in
  let nm_new=List.map (fun (a,s) -> let new_e=re a in (new_e,f new_e)) nm in
  (s_new,f,nm_new)




(* disjointness structures*)
type 'a d_set =  ('a list) list

(* below will help convert to string representation*)
type 'a d_set_str =  (string d_set * ('a -> string)) 

(* an empty difference set *)
let empty_dset () : 'a d_set = []

(* an empty difference set *)
let empty_dset_str (f:'a->string) : 'a d_set_str = ([],f)

(* a singleton difference set *)
let singleton_dset (e:'a) : 'a d_set = [[e]]

(* a singleton difference set *)
let singleton_dset_str (f:'a->string) (e:'a) : 'a d_set_str = ([[f e]],f)

(* returns a list of difference sets for element e *)
let find_diff (eq:'a->'a->bool) (s: 'a d_set) (e:'a) : 'a d_set =
  (List.filter (fun l -> List.exists (fun x -> eq e x) l) s)

(* returns a list of difference sets for element e *)
let find_diff_str (eq_str:string->string->bool) ((s,f): 'a d_set_str) (e:'a) : 'a d_set_str =
  (find_diff (eq_str) s (f e),f)

(* returns checks if l1/\l2 !=null based on physical equality *)
let overlap_q l1 l2 = 
  List.exists (fun x -> (List.memq x l2)) l1

(* checks s |- x!=y *)
let is_disj (eq:'a->'a->bool)  (s: 'a d_set)  (x:'a) (y:'a) : bool =
  if (eq x y) then false 
  else
    let l1 = find_diff eq s x in
    let l2 = find_diff eq s y in
    (overlap_q l1 l2)

(* checks s |- x!=y *)
let is_disj_str (eq_str:string->string->bool)  ((s,f): 'a d_set_str)  (x:'a) (y:'a) : bool =
 is_disj eq_str s (f x) (f y)

(*  returns s1/\s2 *)
let merge_disj_set (s1: 'a d_set) (s2: 'a d_set): 'a d_set =
 s1@s2

(*  returns s1/\s2 *)
let merge_disj_set_str ((s1,f1): 'a d_set_str) ((s2,_): 'a d_set_str): 'a d_set_str =
  (merge_disj_set s1 s2, f1)

(*  returns s1*s2 *)
let star_disj_set (s1: 'a d_set) (s2: 'a d_set): 'a d_set =
  if empty s1 then s2
  else if empty s2 then s1
  else List.concat (List.map (fun x1 -> List.map (fun x2-> x1@x2) s2) s1) 

(*  returns s1*s2 *)
let star_disj_set_str ((s1,f1): 'a d_set_str) ((s2,_): 'a d_set_str): 'a d_set_str = (star_disj_set s1 s2,f1)

(*  returns s1\/s2 *)
let or_disj_set (s1: 'a d_set) (s2: 'a d_set): 'a d_set =
  List.concat (List.map (fun x1 -> List.map (fun x2-> intersect x1 x2) s2) s1) 

(*  returns s1\/s2 *)
let or_disj_set_str ((s1,f): 'a d_set_str) ((s2,_): 'a d_set_str): 'a d_set_str =
  (or_disj_set s1 s2,f)

(* check if there was a conflict in a difference list *)
let  is_conflict_list (eq:'a -> 'a -> bool) (l:'a list) :bool =
  let rec helper l =
    match l with
      | [] -> false
      | x::xs -> let b=List.exists (eq x) xs in
        if b then true
        else helper xs
  in helper l

(* check if there was a conflict in a set of difference lists *)
let is_conflict (eq:'a -> 'a -> bool) (s: 'a d_set) : bool =
 List.exists (is_conflict_list eq) s

(* check if there was a conflict in a set of difference lists *)
let is_conflict_str (eq_str:string -> string -> bool) ((s,_): 'a d_set_str) : bool =
 is_conflict eq_str s

let rec list_find (f:'a -> 'b option) l = match l with 
    | [] -> None
    | x::xs -> match f x with
      | None -> list_find f xs
      | Some s -> Some s
