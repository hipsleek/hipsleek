(** Utility module with miscellaneous functions,
    including string functions and operating system functions.

  TODO: Sort functions by category, clean up.
 *)

exception Bad_string
exception Bail

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

let rec remove_dups_f n f= 
  match n with
    [] -> []
  | q::qs -> if (List.exists (fun c-> f q c) qs) then remove_dups_f qs f else q::(remove_dups_f qs f)
  
let rec find_dups n = 
  match n with
    [] -> []
  | q::qs -> if (List.mem q qs) then q::(find_dups qs) else find_dups qs

let rec find_one_dup (eqf : 'a -> 'a -> bool) (xs : 'a list) =
  match xs with
	| [] -> []
	| x::rest -> if List.exists (eqf x) rest then [x] else find_one_dup eqf rest

let subset l1 l2 = 
  List.for_all (fun x -> (List.mem x l2)) l1

let disjoint l1 l2 = 
  List.for_all (fun x -> not (List.mem x l2)) l1

let intersect l1 l2 =
  List.filter (fun x -> List.mem x l2) l1

let difference l1 l2 =
  List.filter (fun x -> not (List.mem x l2)) l1
  
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

(** Split the list of length k>=1 into a pair consisting of
   the list of first k-1 elements and the last element. *)
let rec firsts_last xs = match xs with
| [] -> failwith "Util.first_lasts: empty list"
| [x] -> ([],x)
| x::xs1 ->
    let (fs,l) = firsts_last xs1 in
    (x::fs,l)

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

let empty l = match l with [] -> true | _ -> false

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
let push_time msg = 
if (!Globals.profiling) then
 let timer = get_time () in
	profiling_stack := (msg, timer,true) :: !profiling_stack 
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
				if (List.exists (fun (c1,_,b1)-> (String.compare c1 msg)=0&&b1) !profiling_stack) then begin
					profiling_stack :=List.map (fun (c1,t1,b1)->if (String.compare c1 msg)=0 then (c1,t1,false) else (c1,t1,b1)) !profiling_stack;
					print_string ("\n double accounting for "^msg^"\n")
				end	else ()
				end else add_task_instance m1 (t2-.t1) 
			 
		else 
			Error.report_error {Error.error_loc = Globals.no_pos; Error.error_text = ("Error poping "^msg^"from the stack")}
	else ()
	
	
let add_index l = 
	let rec ff i l = match l with
		| [] -> []
		| a::b-> (i,a)::(ff (i+1) b) in
	(ff 0 l)
	
	
	
(*hairy stuff for exception numbering*)
			
 let exc_list = ref ([]:(string * string * Globals.nflow ) list)
  			 
 let get_hash_of_exc (f:string): Globals.nflow = 
	(*if ((String.compare f Globals.top_flow)==0) then !Globals.top_flow_int
	else*)
	let rec get (lst:(string*string*Globals.nflow)list):Globals.nflow = match lst with
		| [] -> Globals.false_flow_int
		| (a,_,(b,c))::rst -> if (String.compare f a)==0 then (b,c)
						else get rst in
    (get !exc_list)
	
	
  (*t2 is a subtype of t1*)
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